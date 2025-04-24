//#include "lib/Transforms/Utils/CloneFunction.cpp"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/BreadthFirstIterator.h" // 使用內建BFS來協助 fordFulkerson
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/BasicBlock.h" // EntryBlock.front
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Use.h"
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
            //errs() << "In node " << To_Value[u] << "\n";
            q.pop();

            for(auto v:G.adjList[u]){
                if(parent.find(v) == parent.end() && G.capacity[{u, v}] > G.flow[{u, v}]){
                    parent[v] = u; //parent[child] = parent;
                    //errs() << "parent[" << To_Value[v] << "] = " << To_Value[u] << "\n";
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
    errs() << "Minimum Cut edges:" << "\n";

    for(auto& [u,neighbors]:G.adjList){
        if(reachableFromSource.count(u)){
            for(NodeNo v : neighbors){
                if(!reachableFromSource.count(v) && G.capacity[{u, v}] > 0){
                    Value *u_v = To_Value[u].back();
                    Value *v_v = To_Value[v][0];
                    errs() << *u_v << "->" << *v_v << "\n";
                    if(Instruction *I = dyn_cast<Instruction>(v_v)){
                        sepInsts.push_back(I);
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

    while(!q.empty()){
        std::vector<Value *> path = q.front();
        q.pop();

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
    }
}

std::unordered_map<std::pair<Value *, Value *>, int, PairHash> buildCapacity(Function &F, std::unordered_map<Value *, std::vector<Value *>>& G){
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> Cap;
    Cap.clear();
    
    // find parameter dependency
    DenseSet<std::pair<Value *, Value *>> rec;
    for(BasicBlock &BB : F){
        for(Instruction &Inst : BB){
            Value *src = &Inst;
            for (auto dest : src->users()) {
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
    Instruction *cutI = sepInsts[0];
    BasicBlock *cutIBB = cutI->getParent();
    DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F); // 分析使用位置的 DominatorTree 
    // build new basic block
    BasicBlock *newCutBB = SplitBlock(cutIBB, cutI); // SplitBlock() [4/4]

    // 分析切割後程式 Live Range
    // 找到所有 cutI 前的 Instruction
    std::vector<BasicBlock *> blocksToMove;
    std::queue<BasicBlock *> worklist;
    SmallPtrSet<BasicBlock *, 8> visited;
    worklist.push(newCutBB);
    visited.insert(newCutBB);

    while(!worklist.empty()){
        BasicBlock *cur = worklist.front();
        worklist.pop();
        blocksToMove.push_back(cur);

        for(auto *succ:successors(cur)){
            if(visited.insert(succ).second){
                worklist.push(succ);
            }
        }
    }

    std::set<Value *> defBeforeCut;
    for(auto &BB:F){
        for(auto &I:BB){
            if(&I == cutI){
                break;
            }
            defBeforeCut.insert(&I);
        }
    }
    

    // 對每個 defBeforeCut 的指令列出使用者
    std::set<Value *> LiveOut;
    for(Value *V:defBeforeCut){
        for(Use &U:V->uses()){
            if(Instruction *useInst = dyn_cast<Instruction>(U.getUser())){
                if(DT.dominates(cutI, useInst)){ //透過 cutI 是否支配 useInst，可以知道 useInst 是否一定在 cutI 之後執行
                    unsigned opIdx = U.getOperandNo();
                    Value *operand = U.getUser()->getOperand(opIdx);   
                    
                    LiveOut.insert(operand);
                }
            }
        }
    }

    /***
    errs() << "Live-Out values:\n";
    for (Value *V : LiveOut) {
        llvm::errs() << *V << "\n";
    }
        ***/
    
    // 建立新 function，先 clone 整個 function 
    Function *newFunc = Function::Create(F.getFunctionType(), GlobalValue::LinkageTypes::ExternalLinkage, 
                                F.getName() + "_split", F.getParent());
    assert(newFunc && "newFunc is null!");

    ValueToValueMapTy VMap;
    Function::arg_iterator argIter = newFunc->arg_begin();
    for(auto &arg:F.args()){
        VMap[&arg] = &*argIter++;
    }
    
    for(auto *BB:blocksToMove){
        BasicBlock *clonedBB = BasicBlock::Create(BB->getContent(), "", newFunc);
        VMap[BB] = clonedBB;
    }

    for(auto &BB:blocksToMove){
        BasicBlock *clonedBB = cast<BasicBlock>(VMap[BB]);

        for(auto &I:BB){
            Instruction *newInst = I.clone();
            
            for(unsigned i=0; i<newInst->getNumOperands(); i++){
                Value *op = I->getOperand(i);
                auto it = VMap.find(op);
                if(it != VMap.end()){
                    newInst->setOperand(i, it->second);
                }
            }
            VMap[&I] = cnewInst;
            clonedBB->getInstList().push_back(newInst);
        }
    }

    Builder.SetInsertPoint(cutI);
    // 根據 newFunc 的參數，傳入原來的值
    Builder.CreateCall(newFunc, args);

    /***
    for(auto &BB:*newFunc){
        for(auto &I:BB){
            if(Instruction *Inst = dyn_cast<Instruction>(&I)){
                errs() << "Inst: " << *Inst << "\n";
            }
        }
    }

    /***
    // 刪除不需要的 BB
    Instuction *oldCut = cutI;
    Instruction *newCut = cast<Instruction>(VMap[cutI]);
    BasicBlock *newCutBB = newCut->getParent();

    std::set<BasicBlock *> KeepBB;
    std::vector<BasicBlock *> worklist = { newBB };
    for(!worklist.empty()){
        BasicBlock *cur = worklist.back();
        worklist.pop_back();

        if(!keepBB.insert(cur).second) 
            continue;

        for(succ_iterator SI = succ_begin(cur), SE = succ_end(cur); SI != SE; ++SI){
            worklist.push_back(*SI);
        }
    }

    std::vector<BasicBlock *> toDelete;
    for(auto &BB:*newFunc){
        if(KeepBB.find(&BB) == KeepBB.end()){
            toDelete.push_back(&BB);
        }
    }

    /***
    for(auto &BB:toDelete){
        while(!BB->empty()){
            BB->back().eraseFromParent();
        }
        BB->eraseFromParent();
    }
    ***/

    return;
}

PreservedAnalyses HelloPass::run(Function &F, FunctionAnalysisManager &AM){
    // 先建立以instruction為主的cfg，建立FlowGraph並找到SCC（loop）
    std::unordered_map<Value *, std::vector<Value *>> CFG = buildGraph(F);
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

    mappingNode(SCCs, alone);
    // mapping後顯示每個node的長相（SCC已經印在同個node）
    /***
    for(auto ele:IG.adjList){
        NodeNo u = ele.first;
        errs() << "Node #" << u << ": " << "\n";
        for(auto v:To_Value[u]){
            errs() << "\t" << *v << "\n";
        }
    }
    ***/
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> cap = buildCapacity(F, CFG);
    // 建立可切割Graph
    InstGraph IG(To_Node, CFG, cap);
    //exportCFG(IG, F.getName()); // 印出Graph來看
    
    // Minimum Cut
    std::unordered_set<NodeNo> rfs;
    Value *source = F.args().begin();

    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
    Instruction *target = getLatestReturn(F, PDT);
    //errs() << "target: " << *target << "\n";

    int maxFlow = fordFulkerson(IG, source, target, rfs);
    errs() << "MaximumFlow: " << maxFlow << "\n";
    if(maxFlow != 0){
        std::vector<Instruction *> sepInsts;
        findMinCut(IG, rfs, sepInsts);

        errs() << "create new basic block\n";
        splitFunc(sepInsts, F, AM);
    }

    // 印出現在的 IR 來看
    /***
    for(auto &BB:F){
        for(auto &I:BB){
            errs() << I << "\n";
        }
        errs() << BB << "\n";
    }
    ***/
    return PreservedAnalyses::all();
}