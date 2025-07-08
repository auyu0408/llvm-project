//#include "lib/Transforms/Utils/CloneFunction.cpp"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/BreadthFirstIterator.h" // 使用內建BFS來協助 fordFulkerson
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h" // EntryBlock.front
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h" // errs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Hello.h"
#include <fstream> // 輸出到檔案
#include <limits.h> //INT_MAX
#include <queue>
#include <utility> // pair
#include <unordered_map>
#include <unordered_set> // reachable from source
#include <vector>

using namespace llvm;
#define NodeNo unsigned

namespace llvm{
    struct VectorHash{
        template<class T>
        std::size_t operator() (const std::vector<T>& vec) const{
            std::size_t ret = 0;
            for(auto i:vec){
                ret ^= std::hash<T>{}(i);
            }
            return ret;
        }
    };

    struct PairHash{
        template<class T1, class T2>
        std::size_t operator() (const std::pair<T1, T2>& p) const{
            auto h1 = std::hash<T1>{}(p.first);
            auto h2 = std::hash<T2>{}(p.second);
            return h1 ^ h2;
        }
    };

    struct FlowGraph{
        std::unordered_map<Value *, std::vector<Value *>> adjList; // 原本的圖
        FlowGraph(std::unordered_map<Value *, std::vector<Value *>>& G)
            : adjList(G){}
    };

    std::unordered_map<Value *, NodeNo> To_Node;
    std::unordered_map<NodeNo, std::vector<Value *>> To_Value;
    struct InstGraph{
        std::unordered_map<NodeNo, std::unordered_set<NodeNo>> adjList;
        std::unordered_map<std::pair<NodeNo, NodeNo>, int, PairHash> capacity;
        std::unordered_map<std::pair<NodeNo, NodeNo>, int, PairHash> flow;
        InstGraph(std::unordered_map<Value *, NodeNo> Node_map, std::unordered_map<Value *, std::vector<Value *>>& CFG,
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


    };

    template<> struct GraphTraits<FlowGraph>{
        using NodeRef = Value *;
        using ChildIteratorType = std::vector<Value *>::const_iterator;

        //不管是 getEntryNode, child_begin 和 child_end 都需要注意 map 到空 instruction 的部份（可能是尾端）
        static Value* getEntryNode(const FlowGraph &G){
            if(G.adjList.empty()) return nullptr;
            else{
                if(Instruction *I = dyn_cast<Instruction>(G.adjList.begin()->first)){
                    return &(I->getFunction()->getEntryBlock().front());
                }
                else return nullptr;
            }
            // G.adjList.begin()->first 可以拿到指令，看這個指令在哪個function並且該function的first inst是誰
        }

        static ChildIteratorType child_begin(NodeRef N){
            auto it = G->adjList.find(N);
            if(it == G->adjList.end()){
                static const std::vector<Value*> empty_vec;
                return empty_vec.begin();
            }
            return it->second.begin();
        }

        static ChildIteratorType child_end(NodeRef N){
            auto it = G->adjList.find(N);
            if(it == G->adjList.end()){
                static const std::vector<Value *> empty_vec;
                return empty_vec.begin();
            }
            return it->second.end();
        }

        static auto nodes_begin(const FlowGraph &G) { return G.adjList.begin(); }
        static auto nodes_end(const FlowGraph &G) { return G.adjList.end(); }

        static const FlowGraph* G;
    };

    const FlowGraph* GraphTraits<FlowGraph>::G = nullptr;
}

std::string getInstructionString(NodeNo I){
    std::string str;
    raw_string_ostream rso(str);
    To_Value[I][0]->print(rso);
    return rso.str();
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
                        //errs() << "push u: ";
                        //u_I->dump();
                        //errs() << "\n";
                        
                    }
                    if(v_v && dyn_cast<Instruction>(v_v)){
                        auto *v_I = dyn_cast<Instruction>(v_v);
                        sepInsts.push_back(v_I);
                        //errs() << "push v: ";
                        //v->dump();
                        //errs() << "\n";
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

void addDependency(Value* src, Value* dest, std::unordered_map<Value *, std::vector<Value *>>& G, 
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> &Cap){
    if(src == nullptr || dest == nullptr) return;
    
    std::queue<std::vector<Value *>> q;
    q.push({src});
    int dep = 0;

    while(!q.empty()){
        std::vector<Value *> path = q.front();
        q.pop();
        if(dep > 280) {
            break;
        }

        Value* last = path.back();
        if(last == dest){
            for(size_t i = 0; i < path.size() - 1; i++){
                //errs() << *(path[i]) << "->";
                Cap[{path[i], path[i+1]}] += 1;
            }
            //errs() << *(path.back()) << "\n";
            continue;
        }

        for(Value* next : G[last]){
            if(find(path.begin(), path.end(), next) == path.end()){
                std::vector<Value *> newPath = path;
                newPath.push_back(next);
                q.push(newPath);
            }
        }
        dep++;
    }

    return;
}

std::unordered_map<std::pair<Value *, Value *>, int, PairHash> buildCapacity(Function &F, std::unordered_map<Value *, std::vector<Value *>>& G){
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> Cap;
    Cap.clear();
    
    // find parameter dependency
    DenseSet<std::pair<Value *, Value *>> rec;
    for(BasicBlock &BB : F){
        for(Instruction &Inst : BB){
            Value *src = &Inst;
            //errs() << "src: " << *src << "\n";
            for (auto dest : src->users()) {
                //errs() << "dest: " << *dest << "\n";
                //避免store探索到相同指令
                if(rec.count({src, dest}))
                    continue;
                else{
                    addDependency(src, dest, G, Cap);
                    rec.insert({src, dest});
                }
            }  
        }
    }
    //errs() << "finished param capacity\n";

    //argument dependency
    for(auto &arg:F.args()){
        Value *src = &arg;
        for(auto dest:src->users()){
            if(rec.count({src, dest}))
                continue;
            else{
                addDependency(src, dest, G, Cap);
                rec.insert({src, dest});
            } 
        }
    }
    //errs() << "finished argument capacity\n";

    return Cap;
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

void exportCFG(InstGraph &G, StringRef name){
    //建立檔案並進行輸出導向
    std::string fileName(name.data());
    fileName.append(".dot"); 
    std::ofstream dotFile(fileName);

    if(!dotFile.is_open()){
        errs() << "Error open file: " << name << "\n";
        return;
    }

    dotFile << "digraph CFG {\n";

    for (const auto &pair : G.adjList) {
        NodeNo src = pair.first;

        for (NodeNo dest : pair.second) {

            std::pair<NodeNo, NodeNo> edge = {src, dest};
            dotFile << "\"" << src << "\" -> \"" << dest << "\"" << "[label = \" " << G.capacity[edge] << " \"];\n";
        }
    }

    dotFile << "}\n";
    dotFile.close();

    return;
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

void splitFunc(std::vector<Instruction *> sepInsts, Function &F, FunctionAnalysisManager &AM){
    
    //DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F); // 分析使用位置的 DominatorTree 
    //PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);

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
        //errs() << "No enough Instructions to split\n";
        return;
    }
    else cutI = sepInsts[1];
    
    if(isa<PHINode>(cutI)){
        cutI = cutI -> getNextNode(); // PHI node 不能被切割，所以要往後找
    }
    if(sepInsts[0]->isTerminator()){
        //errs() << "Cut Instruction is Terminator\n";
        return;
    }
    //errs() << "check ret\n";
    if(isa<ReturnInst>(sepInsts[0])||(sepInsts.size() > 1 && isa<ReturnInst>(sepInsts[1]))){
        //errs() << "We don't need to split return instruction\n";
        return;
    }

    BasicBlock *cutBB = cutI->getParent();
    BasicBlock *newCutBB = cutBB->splitBasicBlock(cutI, cutBB->getName() + ".split"); // build new BB
    Instruction *splitP = cutBB->getTerminator(); // 抓住cutI前一個指令作為 split 點，負責 call function 和 安插新 return

    /***
    errs() << "Cut Instruction: ";
    cutI->dump();
    /***
    errs() << "\nAfter split\n";
    errs() << "Cut BB: " << *cutBB << "\n";
    errs() << "New Cut BB: " << *newCutBB << "\n";
    ***/

    // 2. 蒐集要移出去的 BB
    std::vector<BasicBlock *> BlocksToMove;
    
    BlocksToMove.push_back(newCutBB);
    for (BasicBlock *Succ : successors(newCutBB)){
        //errs() << "Successor of newCutBB: " << *Succ << "\n";
        BlocksToMove.push_back(Succ);
    }
    /***
    for(auto &BB : F){
        if(&BB != newCutBB && &BB != cutBB && DT.dominates(cutBB, &BB)){
            BlocksToMove.push_back(&BB);
        }
    }  
    ***/

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
        //errs() << "Skip Branch\n";
        MergeBlockIntoPredecessor(newCutBB);
        return;
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
        //errs() << "No LiveOuts found, nothing to split.\n";
        MergeBlockIntoPredecessor(newCutBB);
        return;
    }

    // 4. 建立 function 
    // 4-1 取得 LiveOuts variable 型態，這會是新 function 的 argument type
    FunctionType *FTy = F.getFunctionType();
    std::vector<Type *> argTypes;
    for(Value *LiveOut : LiveOuts){
        Type *argType = LiveOut->getType();
        argTypes.push_back(argType);
    }
    // 如果有多個 entry block，則需要 selector argument，沒有加這個 argument 數量會錯
    /***
    if(entryBlocks.size() > 1){
        argTypes.push_back(Type::getInt32Ty(M->getContext())); // selector type
    }
    ***/

    // 4-2. 取得return type，並與 argument type 建立 function type
    FunctionType *newFTy = FunctionType::get(FTy->getReturnType(), argTypes, false);
    //4-3. 建立新的 function
    std::string newFuncName = F.getName().str() + "_cloned";
    Function *newFunc = Function::Create(newFTy, F.getLinkage(), newFuncName, M);

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
    /***
    std::unordered_map<BasicBlock*, int> caseTable;
    if(entryBlocks.size() > 1){
        errs() << "Multiple entry blocks found for BlocksToMove.\n";
        // 有多個 entry 所以需要 selector
        entry = BasicBlock::Create(M->getContext(), "entry", newFunc);
        // default block
        BasicBlock *defaultBB = BasicBlock::Create(M->getContext(), "default", newFunc);
        IRBuilder<> DBuilder(defaultBB);
        DBuilder.CreateUnreachable();
        
        //selector 處理
        Argument *selector = newFunc->getArg(argCount); //本來就是放在argument最後面
        selector->setName("select_arg");
        SwitchInst *switchInst = SwitchInst::Create(selector, defaultBB, entryBlocks.size()+1, entry);

        //8. 移動 basic block
        int caseIdx = 0;
        IRBuilder<> EBuilder(entry);
        for(auto &BB : BlocksToMove){
            BB->removeFromParent();
            BB->insertInto(newFunc, defaultBB);
            if(entryBlocks.count(BB) != 0){
                caseTable[BB] = caseIdx;
                switchInst->addCase(ConstantInt::get(Type::getInt32Ty(M->getContext()), caseIdx++), BB);
            }
        }

        ///***
        // 9. 將原函數插入 Call, return
        IRBuilder<> FBuilder(splitP);
        std::vector<Value *> args;
        for(Value *LiveOut : LiveOuts){
            args.push_back(LiveOut);
        }
        args.push_back(FBuilder.getInt32(caseTable[newCutBB])); // selector argument
        Value *CallResult = FBuilder.CreateCall(newFunc, args);
        if(FTy->getReturnType()->isVoidTy()){
            FBuilder.CreateRetVoid();
        }
        else{
            FBuilder.CreateRet(CallResult);
        } 
        splitP->eraseFromParent(); // 刪除原本的指令

        for(auto ele:entryBlocks){
            BasicBlock *BB = ele.first;
            if(BB == newCutBB) continue; // 不需要處理 newCutBB
            std::vector<BasicBlock *> &Preds = ele.second;
            for(BasicBlock *Pred : Preds){
                BranchInst *BI = BRcallers[Pred];
                Value *orCond = BI->getCondition();
                BasicBlock *label0 = BI->getSuccessor(0);
                BasicBlock *label1 = BI->getSuccessor(1);
                BasicBlock *callBlock = BasicBlock::Create(M->getContext(), "call_"+std::to_string(caseTable[BB]), &F);
                BasicBlock *continueBlock = nullptr;
                if(label0 == BB){
                    continueBlock = label1;
                }
                else if(label1 == BB){
                    continueBlock = label0;
                }

                FBuilder.SetInsertPoint(BI);
                FBuilder.CreateCondBr(orCond, callBlock, continueBlock);
                BI->eraseFromParent(); // 刪除原本的指令

                std::vector<Value *> args;
                for(Value *LiveOut : LiveOuts){
                    args.push_back(VMap[LiveOut]); // 使用映射的值
                }
                args.push_back(FBuilder.getInt32(caseTable[BB])); // selector argument
                FBuilder.SetInsertPoint(callBlock);
                Value *CallResult = FBuilder.CreateCall(newFunc, args);
                if(FTy->getReturnType()->isVoidTy()){
                    FBuilder.CreateRetVoid();
                }
                else{
                    FBuilder.CreateRet(CallResult);
                }
            }
        }

        
        for(auto &BB : F){
            errs() << BB;
        }
        
    }
    else{
    ***/
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
    //}

    /***
    errs() << "Ori Function:\n";
    for(auto &BB : *newFunc){
        errs() << BB;
    }
    ***/

    /***
    errs() << "New Function:\n";
    for(auto &BB : *newFunc){
        errs() << BB;
    }
    ***/

    //errs() << "Verify\n";
    bool broken = verifyFunction(*newFunc, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
        return;
    }

    return;
}

PreservedAnalyses HelloPass::run(Function &F, FunctionAnalysisManager &AM){
    if(F.hasFnAttribute("hello-inline")) return PreservedAnalyses::none();
    //if(F.getName() != "PerlIOVia_flush") return PreservedAnalyses::none();
    // 檢查是不是要分開的function
    if(F.getName().ends_with("cloned")) return PreservedAnalyses::none();
    //errs() << F.getName() << "\n";
    /***
    errs() << "all IR\n";
    for(auto &BB:F){
        errs() << BB << "\n";
    }
    ***/
    // 可變參數
    FunctionType *FT = F.getFunctionType();
    if(FT->isVarArg()){
        return PreservedAnalyses::all();
    }

    // 先建立以instruction為主的cfg，建立FlowGraph並找到SCC（loop）
    std::unordered_map<Value *, std::vector<Value *>> CFG = buildGraph(F);
    if(CFG.size() >= 1500){
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
        else{
            alone.push_back({SCC[0]});
        }
    }

    //errs() << "finished classfied SCC and alone.\n";
    mappingNode(SCCs, alone);

    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> cap = buildCapacity(F, CFG);
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

        //errs() << "create new basic block\n";
        splitFunc(sepInsts, F, AM);
        //errs() << "Inline function\n";
        for(auto *U:F.users()){
            if(auto *call = dyn_cast<CallInst>(U)){
                if(call->getCalledFunction() == &F){
                    InlineFunctionInfo IFI;
                    InlineFunction(*call, IFI);
                }
            }
        }
        F.addFnAttr("hello-inline"); // 避免被再次 inline
    }

    bool broken = verifyFunction(F, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
    }

    return PreservedAnalyses::none();
}
