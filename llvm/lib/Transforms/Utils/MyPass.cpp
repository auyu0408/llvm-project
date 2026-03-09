#include "llvm/Transforms/Utils/MyPass.h"
#include "llvm/Transforms/Utils/MyFunction.h"

using namespace llvm;

PreservedAnalyses MyPass::run(Function &F, FunctionAnalysisManager &AM){
    if (F.isDeclaration()) return PreservedAnalyses::all();
    if (F.getName().empty()) return PreservedAnalyses::all();
    if(F.getName().ends_with("cloned")) return PreservedAnalyses::none(); //已經split的不可再次處理

    // 如果這個function有地方需要inline
    bool inlined_flag = 0;
    for(auto *U:F.users()){
        if(auto *CB = dyn_cast<CallBase>(U)){
            auto *Callee = CB->getCalledFunction();
            auto *Caller = CB->getCaller();
            if(!Callee) continue;
            if(!Caller) continue;
            if(Callee->isIntrinsic()) continue;
            if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                if(!hasPassVal(CB)) continue;
                auto res = getPassVal(CB);
                if((Callee == &F) && res){
                    inlined_flag = 1;
                    break;
                }
            }
        }
    }
    if(!inlined_flag) return PreservedAnalyses::all();
    
    //不切割可變參數的function
    FunctionType *FT = F.getFunctionType();
    if(FT->isVarArg()){
        return PreservedAnalyses::all();
    }

    // 先建立以instruction為主的cfg，建立FlowGraph並找到SCC（loop）
    std::unordered_map<Value *, std::vector<Value *>> CFG = buildGraph(F);
    //指令太多的function不利於切割/找到正確答案，會跳過
    if(CFG.size() >= 1400){
	    return PreservedAnalyses::all();
    }
    FlowGraph FG(CFG);
    GraphTraits<FlowGraph>::G = &FG;
    std::vector<std::vector<Value *>> SCCs; //儲存找到的SCC
    std::vector<std::vector<Value *>> alone; //儲存單獨一條指令

    //把 argument 也整理成 node，為了配合 argument 所以把儲存結構改成 Value * 目前把argument當成一個SCC
    std::vector<Value *> temp;
    for(auto &arg:F.args()){
        Value *V = &arg;
        temp.push_back(V);
    }
    SCCs.push_back(temp);

    for(auto I = scc_begin(FG); I != scc_end(FG); ++I){
        std::vector<Value *> SCC = *I;
        std::vector<Value *> temp;

        // 真正的循環（大小 > 1 或自循環）
        if (SCC.size() > 1 ||
            (SCC.size() == 1 && CFG[SCC[0]].size() > 0 && CFG[SCC[0]][0] == SCC[0])) {
            // Enumerate the SCCs of a directed graph in reverse topological order of the SCC DAG
            std::reverse(SCC.begin(), SCC.end());
            for(auto Inst:SCC){
                temp.push_back(Inst);
                //errs() << "Inst: " << *Inst << "\n";
            }
            SCCs.push_back(temp);
        }
        else alone.push_back({SCC[0]});
    }

    mappingNode(SCCs, alone);

    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> cap = buildCapacity1(F);
    //errs() << "finished build capacity.\n";
    // 建立可切割Graph
    InstGraph IG(To_Node, CFG, cap);
    //errs() << "finished build InstGraph.\n";
    //exportCFG(IG, F.getName()); // 印出Graph來看
    
    // Minimum Cut
    std::unordered_set<NodeNo> rfs;
    Value *source = F.args().begin();

    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
    Instruction *target = getLatestReturn(F, PDT);

    int maxFlow = fordFulkerson(IG, source, target, rfs);
    //errs() << F.getName() << ", MaximumFlow: " << maxFlow << "\n"; 
    if(maxFlow != 0){
        std::vector<Instruction *> sepInsts;
        findMinCut(IG, rfs, sepInsts);

        bool res = splitFunction(sepInsts, F, AM);
        if(res){
            for(auto *U:F.users()){
                if(auto *CI = dyn_cast<CallInst>(U)){
                    auto *CB = dyn_cast<CallBase>(U);
                    auto *Callee = CB->getCalledFunction();//CallInst 有繼承 CallBase
                    auto *Caller = CB->getCaller();
                    if(!Callee) continue;
                    if(!Caller) continue;
                    if(Callee->isIntrinsic()) continue;
                    if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                        if(!hasPassVal(CB)) continue;
                        auto res =  getPassVal(CB);
                        if((Callee == &F) && res){
                            InlineFunctionInfo IFI;
                            InlineFunction(*CI, IFI);//這邊會用到CI，前面是用到CB所以兩個都要
                        }
                    }
                }
            }
            F.addFnAttr("MyPass"); // 避免被再次 inline
        }
    }
    else return PreservedAnalyses::all();

    bool broken = verifyFunction(F, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
    }

    return PreservedAnalyses::none();
}

std::unordered_map<std::pair<Value *, Value *>, int, PairHash> buildCapacity1(Function &F){
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> Cap;
    
    Cap.clear();

    //幫Inst編號
    std::vector<Instruction *> InstLists;
    for(auto &BB:F){
        for(auto &I:BB){
            if(isa<Instruction>(I)){
                InstLists.push_back(&I);
            }
        }
    }
    int total = InstLists.size();

    std::vector<int> CutCounts(InstLists.size(), 0);
    DenseSet<std::pair<Value *, Value *>> rec;
    //data dependency
    for(Instruction *I : InstLists){
        for(Use &U : I->operands()){
            Value *V = U.get();
            Instruction *Def = dyn_cast<Instruction>(V);
            if(!Def) continue; // 如果不是指令就跳過
            auto def_it = std::find(InstLists.begin(), InstLists.end(), Def);
            auto use_it = std::find(InstLists.begin(), InstLists.end(), I);
            if(def_it == InstLists.end() || use_it == InstLists.end()) continue; // 如果找不到就跳過
            size_t def_idx = std::distance(InstLists.begin(), def_it);
            size_t use_idx = std::distance(InstLists.begin(), use_it);
            for(size_t i = def_idx; i < use_idx; i++){
                if(rec.count({Def, InstLists[i]})) continue; // 如果已經處理過就跳過
                rec.insert({Def, InstLists[i]});
                CutCounts[i]++;
            }
        }
    }

    //argument dependency
    rec.clear();
    std::vector<int> ValueCounts(InstLists.size(), 0);
    for(auto &arg:F.args()){
        Value *src = &arg;
        int center = (total + 1) / 2;
        addDependency(src, InstLists[0], center, Cap);
        for(auto U:src->users()){
            Instruction *I = dyn_cast<Instruction>(U);
            auto use_it = std::find(InstLists.begin(), InstLists.end(), I);
            if(use_it == InstLists.end()) continue;
            size_t use_idx = std::distance(InstLists.begin(), use_it);

            for(size_t i = 0; i < use_idx; i++){
                if(rec.count({src, InstLists[i]})) continue;
                rec.insert({src, InstLists[i]});
                ValueCounts[i]++;
            } 
        }
    }

    for(int i = 0; i < total - 1; i++){
        addDependency(InstLists[i], InstLists[i+1], 1, Cap);
    }

    if(F.getReturnType()->isVoidTy()){
        if(total-2 >= 0){
            addDependency(InstLists[total-2], InstLists[total-1], 1, Cap); // 如果是void function，最後一個指令會是return void
        }
    }

    return Cap;
}