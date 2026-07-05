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

bool hasPartialInlineVal(const CallBase *CB) {
    auto *N = CB->getMetadata("goPartialInline");
    if(!N) return false;
    if(!dyn_cast<MDNode>(N)) return false;
    if(!dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))) return false;

    auto *CM = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0));
    if(!CM) return false;
    if(!dyn_cast<ConstantInt>(CM->getValue())) return false;

    return true;
}

bool getPartialInlineVal(const CallBase *CB) {
    auto *N = CB->getMetadata("goPartialInline");
    assert(N && "CallBase does not carry goPartialInline metadata.\n");
    Constant *C = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))
                        ->getValue();
    return cast<ConstantInt>(C)->isOne();
}

void setPartialInlineVal(CallBase *CB, bool val) {
    auto &Ctx = CB->getContext();
    ConstantInt *CI = ConstantInt::get(Type::getInt1Ty(Ctx), val ? 1 : 0);
    MDNode *N = MDNode::get(Ctx, {ConstantAsMetadata::get(CI)});
    CB->setMetadata("goPartialInline", N);
}

int fordFulkerson(InstGraph& G, Value* source, Value* target,
                    std::unordered_set<NodeNo>& reachableFromSource){ //target = sink
    if(source == nullptr || target == nullptr) return 0;

    int maxFlow = 0;
    while(true){
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

        int pathFlow = INT_MAX;
        for(NodeNo v = To_Node[target]; v!= To_Node[source]; v = parent[v]){
            NodeNo u = parent[v];
            pathFlow = std::min(pathFlow, G.capacity[{u, v}] - G.flow[{u, v}]);
        }

        //update flow
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

    for(auto& [u,neighbors]:G.adjList){
        if(reachableFromSource.count(u)){
            for(NodeNo v : neighbors){
                if(!reachableFromSource.count(v) && G.capacity[{u, v}] > 0){
                    auto *u_v = To_Value[u].back();
                    auto *v_v = To_Value[v][0];
                    if(u_v && dyn_cast<Instruction>(u_v)){
                        auto *u_I = dyn_cast<Instruction>(u_v);
                        sepInsts.push_back(u_I);
                    }
                    if(v_v && dyn_cast<Instruction>(v_v)){
                        auto *v_I = dyn_cast<Instruction>(v_v);
                        sepInsts.push_back(v_I);
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
        if(!lastBB) return nullptr;
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
    // 1. 基本檢查
    if(sepInsts.size() < 2){
        return false;
    }
    Instruction *cutI = sepInsts[1];
    
    if(isa<PHINode>(cutI)){
        cutI = cutI -> getNextNode(); // PHI node 不能被切割，所以要往後找
    }
    if(sepInsts[0]->isTerminator()){
        return false;
    }
    if(isa<ReturnInst>(sepInsts[0])||(sepInsts.size() > 1 && isa<ReturnInst>(sepInsts[1]))){
        return false;
    }

    // 2. 在切割點把 BasicBlock 切開
    BasicBlock *cutBB = cutI->getParent();
    BasicBlock *newCutBB = cutBB->splitBasicBlock(cutI, cutBB->getName() + ".split");

    // 3. 從 newCutBB 開始 BFS 收集所有要提取的 BasicBlocks
    SmallVector<BasicBlock *, 16> BlocksToExtract;
    SmallPtrSet<BasicBlock *, 16> Visited;
    std::queue<BasicBlock *> BBQueue;
    BBQueue.push(newCutBB);
    Visited.insert(newCutBB);
    while(!BBQueue.empty()){
        BasicBlock *BB = BBQueue.front();
        BBQueue.pop();
        BlocksToExtract.push_back(BB);
        for (BasicBlock *Succ : successors(BB)) {
            if (Visited.insert(Succ).second) {
                BBQueue.push(Succ);
            }
        }
    }

    // 4. 用 CodeExtractor 提取
    DominatorTree *DT = AM.getCachedResult<DominatorTreeAnalysis>(F);
    CodeExtractor CE(BlocksToExtract, DT, /*AggregateArgs=*/false,
                     /*BFI=*/nullptr, /*BPI=*/nullptr, /*AC=*/nullptr,
                     /*AllowVarArgs=*/false, /*AllowAlloca=*/false,
                     /*AllocationBlock=*/nullptr, /*Suffix=*/"cloned");

    if (!CE.isEligible()) {
        // 不適合提取，還原 split
        MergeBlockIntoPredecessor(newCutBB);
        return false;
    }

    CodeExtractorAnalysisCache CEAC(F);
    Function *newFunc = CE.extractCodeRegion(CEAC);
    if (!newFunc) {
        return false;
    }

    // 5. 設定提取出來的 function 屬性（與原本行為一致）
    newFunc->addFnAttr(Attribute::NoInline);
    // 移除 alwaysinline（避免跟 noinline 衝突）
    newFunc->removeFnAttr(Attribute::AlwaysInline);

    bool broken = verifyFunction(*newFunc, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
        return false;
    }

    return true;
}
