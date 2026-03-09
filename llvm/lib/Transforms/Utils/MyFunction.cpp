#include "llvm/Transforms/Utils/MyFunction.h"

using namespace llvm;

cl::opt<std::string> InputFilePath(
    "input-file",
    cl::desc("Path to the input file for decision."),
    cl::value_desc("filename"),
    cl::init(""));

namespace llvm{
    std::unordered_map<Value *, NodeNo> To_Node;
    std::unordered_map<NodeNo, std::vector<Value *>> To_Value;
    const FlowGraph* GraphTraits<FlowGraph>::G = nullptr;

    InstGraph::InstGraph(std::unordered_map<Value *, NodeNo> Node_map, std::unordered_map<Value *, std::vector<Value *>>& CFG,
        std::unordered_map<std::pair<Value *, Value *>, int, PairHash>& Cap){
        capacity.clear();
        DenseSet<std::pair<Value *, Value *>> rec;
        
        for(auto &ele:CFG){
            Value *u_V = ele.first;
            NodeNo u_num = Node_map[u_V];
            
            for(auto *v_V:ele.second){
                NodeNo v_num = Node_map[v_V];

                if(!adjList[u_num].count(v_num)){
                    adjList[u_num].insert(v_num); //把u插入v，相同node會因為v_num已經存在而不會重複插入
                }
            }
        }

        for(auto &ele:Cap){
            Value *u_V = ele.first.first;
            Value *v_V = ele.first.second;
            NodeNo u_num = Node_map[u_V];
            NodeNo v_num = Node_map[v_V];

            if(!rec.count({u_V, v_V}) && u_num!=v_num){
                capacity[{u_num, v_num}] += Cap[{u_V, v_V}];
                //errs() << "Edge: " << *(u_V) << "->" << *(v_V) << "\n";
                flow[{u_num, v_num}] = 0;
                rec.insert({u_V, v_V});
            }
        }
    }

}

size_t getCallBaseId(const CallBase *CB) {
    auto *N = CB->getMetadata("callbase.id");
    assert(N && "CallBase does not carry metadata.\n");
    Constant *C = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))
                      ->getValue();
    return cast<ConstantInt>(C)->getZExtValue();
}

bool hasCallBaseId(const CallBase *CB) {
    auto *N = CB->getMetadata("callbase.id");
    if(!N) return false;
    if(!dyn_cast<MDNode>(N)) return false;
    if(!dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))) return false;

    auto *CM = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0));
    if(!CM) return false;
    if(!dyn_cast<ConstantInt>(CM->getValue())) return false;

    return true;
}

bool hasPassVal(const CallBase *CB) {
    auto *N = CB->getMetadata("goPass");
    if(!N) return false;
    if(!dyn_cast<MDNode>(N)) return false;
    if(!dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))) return false;

    auto *CM = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0));
    if(!CM) return false;
    if(!dyn_cast<ConstantInt>(CM->getValue())) return false;

    return true;
}

bool getPassVal(const CallBase *CB) {
    auto *N = CB->getMetadata("goPass");
    assert(N && "CallBase does not carry metadata.\n");
    Constant *C = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))
                        ->getValue();
    return cast<ConstantInt>(C)->isOne();
}

void setPassVal(CallBase *CB, bool val) {
    auto &Ctx = CB->getContext();
    ConstantInt *CI = ConstantInt::get(Type::getInt1Ty(Ctx), val ? 1 : 0);
    MDNode *N = MDNode::get(Ctx, {ConstantAsMetadata::get(CI)});
    CB->setMetadata("goPass", N);
}

int fordFulkerson(InstGraph& G, Value* source, Value* target,
                    std::unordered_set<NodeNo>& reachableFromSource){ //target = sink
    if(source == nullptr || target == nullptr) return 0;

    int maxFlow = 0;
    while(true){
        //errs() << "calculating: " << "\n";
        std::unordered_map<NodeNo, NodeNo> parent;
        std::queue<NodeNo> q;
        q.push(To_Node[source]);

        //use BFS to find path p
        while(!q.empty()){
            NodeNo u = q.front();
            q.pop();

            for(auto v:G.adjList[u]){
                if(parent.find(v) == parent.end() && G.capacity[{u, v}] > G.flow[{u, v}]){
                    parent[v] = u; //parent[child] = parent;
                    if(v == To_Node[target]) break;//已經到target了
                    q.push(v);
                }
            }
        }

        //如果找不到可以到target的路徑
        if(parent.find(To_Node[target]) == parent.end()) break;

        //errs() << "step 2" << "\n";
        int pathFlow = INT_MAX;
        for(NodeNo v = To_Node[target]; v!= To_Node[source]; v = parent[v]){
            NodeNo u = parent[v];
            pathFlow = std::min(pathFlow, G.capacity[{u, v}] - G.flow[{u, v}]);
            //errs() << pathFlow << "\n";
        }

        //update flow
        //errs() << "step 3" << "\n";
        for(NodeNo v = To_Node[target]; v!= To_Node[source]; v = parent[v]){
            NodeNo u = parent[v];
            G.flow[{u, v}] += pathFlow;
            G.flow[{v, u}] -= pathFlow;
        }

        maxFlow += pathFlow;
    }

    std::queue<NodeNo> q;
    q.push(To_Node[source]);
    reachableFromSource.insert(To_Node[source]);

    while(!q.empty()){
        NodeNo u = q.front();
        //errs() << "reacheable:" << u << " " << "\n";
        q.pop();

        for(auto v:G.adjList[u]){
            if(reachableFromSource.find(v) == reachableFromSource.end() && 
                G.capacity[{u, v}] > G.flow[{u, v}]){
                reachableFromSource.insert(v);
                q.push(v);
            }
        }
    }

    return maxFlow;
}

void findMinCut(InstGraph& G, const std::unordered_set<NodeNo> &reachableFromSource, std::vector<Instruction *> &sepInsts){
    //errs() << "Minimum Cut edges:" << "\n";

    for(auto& [u,neighbors]:G.adjList){
        if(reachableFromSource.count(u)){
            for(NodeNo v : neighbors){
                if(!reachableFromSource.count(v) && G.capacity[{u, v}] > 0){
                    auto *u_v = To_Value[u].back();
                    auto *v_v = To_Value[v][0];
                    //errs() << "get u, v Value\n";
                    if(u_v && dyn_cast<Instruction>(u_v)){
                        auto *u_I = dyn_cast<Instruction>(u_v);
                        sepInsts.push_back(u_I);
                        /***
                        errs() << "push u: ";
                        u_I->dump();
                        errs() << "\n";
                        ***/
                    }
                    if(v_v && dyn_cast<Instruction>(v_v)){
                        auto *v_I = dyn_cast<Instruction>(v_v);
                        sepInsts.push_back(v_I);
                        /***
                        errs() << "push v: ";
                        v_I->dump();
                        errs() << "\n";
                        ***/
                    }
                }
            }
        }
    }
}


std::unordered_map<Value *, std::vector<Value *>> buildGraph(Function &F){
    std::unordered_map<Value *, std::vector<Value *>> G;
    G.clear();

    // 處理argument 
    for(auto &arg:F.args()){
        Value *src = &arg;
        std::vector<Value *> temp;
        Instruction *dest = &(F.getEntryBlock().front()); // 這邊的dest是指向第一個指令
        temp.push_back(dest);
        G[src] = temp;
    }

    //處理指令
    for(BasicBlock &BB : F){
        Instruction *prevInst = nullptr;
        std::vector<Value *> Successors;
        
        for(Instruction &I : BB){
            if(prevInst){
                G[prevInst].push_back(&I);
            }
            prevInst = &I;
        }

        if(Instruction *TInst = BB.getTerminator()){
            for(unsigned i=0; i < TInst -> getNumSuccessors(); i++){
                BasicBlock *SuccBB = TInst -> getSuccessor(i);
                if(!SuccBB -> empty()){
                    G[TInst].push_back(&SuccBB->front());
                }
            }
        }
    }

    return G;
}

void addDependency(Value* src, Value* dest, int w, 
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> &Cap){

    if(src == nullptr || dest == nullptr) return;
    Cap[{src, dest}] = w;
    return;
}

std::vector<ReturnInst*> getAllReturnInsts(Function &F){
    std::vector<ReturnInst *> returns;
    for(auto &BB:F){
        if (ReturnInst *retInst = dyn_cast<ReturnInst>(BB.getTerminator())) {
            returns.push_back(retInst);
        }
    }
    return returns;
}

Instruction* getLatestReturn(Function &F, PostDominatorTree &PDT){
    std::vector<ReturnInst *> returns = getAllReturnInsts(F);
    if(returns.empty()) return nullptr;

    BasicBlock *lastBB = returns[0] -> getParent();
    for(ReturnInst* ret:returns){
        lastBB = PDT.findNearestCommonDominator(lastBB, ret->getParent());
    }

    return lastBB->getTerminator();
}

void mappingNode(std::vector<std::vector<Value *>> &SCCs, std::vector<std::vector<Value *>> &alone){
    //先清除避免不想混用在一起的混用到
    To_Node.clear();
    To_Value.clear();

    NodeNo node_idx = 0;

    for(auto Insts:alone){
        for(auto Inst:Insts){
            To_Node[Inst] = node_idx;
            To_Value[node_idx].push_back(Inst);
            node_idx++;
        }
    }

    for(auto SCC:SCCs){
        for(auto Val:SCC){
            To_Node[Val] = node_idx;
            To_Value[node_idx].push_back(Val);
        }
        node_idx++;
    }

    return;
}

bool splitFunction(std::vector<Instruction *> sepInsts, Function &F, FunctionAnalysisManager &AM){
    /***
    errs() << "Function: " << F.getName() << "\n";
    /***
    for(auto &BB:F){
        errs() << BB;
    }
    ***/
     
    // 1. get Function info
    Module *M = F.getParent();
    Instruction *cutI;
    if(sepInsts.size() < 2){
        errs() << "No enough Instructions to split\n";
        return false;
    }
    else cutI = sepInsts[1];
    
    if(isa<PHINode>(cutI)){
        cutI = cutI -> getNextNode(); // PHI node 不能被切割，所以要往後找
    }
    if(sepInsts[0]->isTerminator()){
        errs() << "Cut Instruction is Terminator\n";
        return false;
    }
    //errs() << "check ret\n";
    if(isa<ReturnInst>(sepInsts[0])||(sepInsts.size() > 1 && isa<ReturnInst>(sepInsts[1]))){
        errs() << "We don't need to split return instruction\n";
        return false;
    }

    BasicBlock *cutBB = cutI->getParent();
    BasicBlock *newCutBB = cutBB->splitBasicBlock(cutI, cutBB->getName() + ".split"); // build new BB
    Instruction *splitP = cutBB->getTerminator(); // 抓住cutI前一個指令作為 split 點，負責 call function 和 安插新 return

    /***
    errs() << "Cut Instruction: ";
    //cutI->dump();
    /***
    errs() << "\nAfter split\n";
    errs() << "Cut BB: " << *cutBB << "\n";
    errs() << "New Cut BB: " << *newCutBB << "\n";
    ***/

    // 2. 蒐集要移出去的 BB
    std::vector<BasicBlock *> BlocksToMove;
    std::queue<BasicBlock *> BBQueue;
    std::vector<PHINode *> PHIs; // 用來檢查是否有 PHI node
    //bool PHIfound = false;
    
    BlocksToMove.push_back(newCutBB);
    BBQueue.push(newCutBB);
    while(BBQueue.size() > 0){
        BasicBlock *BB = BBQueue.front();
        BBQueue.pop();
        //errs() << "BB: " << *BB << "\n";
        for (BasicBlock *Succ : successors(BB)) {
            for(auto &I: *Succ){
                if(isa<PHINode>(I)){
                    //PHIfound = true;
                    PHIs.push_back(dyn_cast<PHINode>(&I));
                }
            }
            if (std::find(BlocksToMove.begin(), BlocksToMove.end(), Succ) == BlocksToMove.end()) {
                BlocksToMove.push_back(Succ);
                BBQueue.push(Succ);
            }
        }   
    }

    if(!PHIs.empty()){
        //errs() << "No PHI split, merge\n";
        MergeBlockIntoPredecessor(newCutBB);
        return false;
    }

    // 2.5 紀錄入口，避免有多個
    std::unordered_map<BasicBlock *, std::vector<BasicBlock *>> entryBlocks;
    std::unordered_map<BasicBlock *, BranchInst *> BRcallers;
    for(auto &BB:BlocksToMove){
        for(BasicBlock *Pred : predecessors(BB)){
            // BB: 一定要移動的 BasicBlock，Pred: 會跳到 BB 的 BasicBlock，BI: Branch 本人
            if(find(BlocksToMove.begin(), BlocksToMove.end(), Pred) == BlocksToMove.end()){
                entryBlocks[BB].push_back(Pred);
            }
        }
    }

    ///***
    if(entryBlocks.size() > 1){
        //errs() << "Skip Branch, merge\n";
        MergeBlockIntoPredecessor(newCutBB);
        return false;
    }
    //***/

    // 3. 分析 LiveOuts
    // 找到所有 cutI 前的 Instruction，分析切割後程式 Live Range
    /***
    我只想看在BlocksToMove中，且被BlocksToMove後面用到的指令
    但比如說包含了%12 = phi i32 [ %4, %2 ], [ %10, %9 ]的話，我應該只有要 %12而不需要%4 %2 %10 %9
    ***/
    std::set<Value *> LiveOuts;
    for(auto &BB:F){
        if(std::find(BlocksToMove.begin(), BlocksToMove.end(), &BB) == BlocksToMove.end()){
            for(auto &I:BB){
                for(Use &U:I.uses()){
                    if(Instruction *useInst = dyn_cast<Instruction>(U.getUser())){
                        //useInst->dump();
                        BasicBlock *useB = useInst->getParent();
                        if(std::find(BlocksToMove.begin(), BlocksToMove.end(), useB) != BlocksToMove.end()){
                            unsigned opIdx = U.getOperandNo();
                            Value *operand = U.getUser()->getOperand(opIdx);   
                            
                            LiveOuts.insert(operand);
                        }
                    }
                }
            }
        }
    }

    for(auto &arg:F.args()){
        for(Use &U:arg.uses()){
            if(Instruction *useInst = dyn_cast<Instruction>(U.getUser())){
                BasicBlock *useB = useInst->getParent();
                if(std::find(BlocksToMove.begin(), BlocksToMove.end(), useB) != BlocksToMove.end()){
                    LiveOuts.insert(&arg);
                }
            }
        }
    }

    if(LiveOuts.empty()){
        //errs() << "No LiveOuts found, nothing to split, merge\n";
        MergeBlockIntoPredecessor(newCutBB);
        return false;
    }

    // 4. 建立 function 
    // 4-1 取得 LiveOuts variable 型態，這會是新 function 的 argument type
    FunctionType *FTy = F.getFunctionType();
    std::vector<Type *> argTypes;
    for(Value *LiveOut : LiveOuts){
        Type *argType = LiveOut->getType();
        argTypes.push_back(argType);
    }

    // 4-2. 取得return type，並與 argument type 建立 function type
    FunctionType *newFTy = FunctionType::get(FTy->getReturnType(), argTypes, false);
    //4-3. 建立新的 function
    std::string newFuncName = F.getName().str() + "_cloned";
    Function *newFunc = Function::Create(newFTy, F.getLinkage(), newFuncName, M);
    if(F.hasPersonalityFn()){
        newFunc->setPersonalityFn(F.getPersonalityFn());
    }

    // 5. 建立對應參數(ValueMap)
    ValueToValueMapTy VMap;
    unsigned argCount = 0;
    auto argIt = newFunc->arg_begin();
    //Value *select_val = nullptr;
    for(Value *V : LiveOuts){
        Value *arg = &*argIt++;
        //errs() << V->getName()  << "\n";
        arg->setName("arg" + std::to_string(argCount++) + ".moved"); // 
        //errs() << "New Argument: " << arg->getName() << "\n";
        VMap[V] = arg;
    }

    // 6. 替換新function 的變數
    // 不能直接用 replaceAllUsesWith()，會有風險（可能一部分被 split point 的 front 用，一部分被 back 用）
    for(auto &BB : BlocksToMove){
        for(auto &I : *BB){
            //errs() << "I: " << I << "\n";
            for(unsigned i = 0; i < I.getNumOperands(); i++){
                Value *Op = I.getOperand(i);
                if(VMap.count(Op)){
                    I.setOperand(i, VMap[Op]);
                }
            }
        }
    }
    
    // 7. 建立新函數的 entry
    BasicBlock* entry;
    entry = BasicBlock::Create(M->getContext(), "entry", newFunc);
    IRBuilder<> Builder(entry);
    Builder.CreateBr(newCutBB);

    //8. 移動 basic block
    for(auto &BB : BlocksToMove){
        BB->removeFromParent();
        BB->insertInto(newFunc);
    }

    // 9. 將原函數插入 Call, return
    IRBuilder<> FBuilder(splitP);
    std::vector<Value *> args;
    for(Value *LiveOut : LiveOuts){
        args.push_back(LiveOut);
    }
    Value *CallResult = FBuilder.CreateCall(newFunc, args);
    if(FTy->getReturnType()->isVoidTy()){
        FBuilder.CreateRetVoid();
    }
    else{
        FBuilder.CreateRet(CallResult);
    }  
    splitP->eraseFromParent(); // 刪除原本的指令
    newFunc->addFnAttr(Attribute::NoInline);
    errs() << "Function: " << F.getName() << " split to " << newFunc->getName() << "\n";

    /***
    errs() << "Ori Function:\n";
    for(auto &BB : F){
        errs() << BB;
    }
    ***/

    /***
    errs() << "New Function:\n";
    for(auto &BB : *newFunc){
        errs() << BB;
    }
    ***/

    //auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
    //errs() << "Verify\n";
    bool broken = verifyFunction(*newFunc, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
        return false;
    }

    return true;
}
