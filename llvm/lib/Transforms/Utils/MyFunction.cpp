#include "llvm/Transforms/Utils/MyFunction.h"
#include "llvm/IR/InstIterator.h"

#include <limits>
#include <optional>

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

                if (u_num == v_num)
                    continue;

                // Residual traversal needs both directions in the adjacency
                // graph. The reverse direction starts with zero capacity unless
                // it is also a real CFG edge whose capacity is populated below.
                adjList[u_num].insert(v_num);
                adjList[v_num].insert(u_num);
                originalEdges[{u_num, v_num}].push_back({u_V, v_V});
            }
        }

        for(auto &ele:Cap){
            Value *u_V = ele.first.first;
            Value *v_V = ele.first.second;
            NodeNo u_num = Node_map[u_V];
            NodeNo v_num = Node_map[v_V];

            if(!rec.count({u_V, v_V}) && u_num!=v_num){
                capacity[{u_num, v_num}] += Cap[{u_V, v_V}];
                rec.insert({u_V, v_V});
            }
        }

        // Materialize every residual edge. Real forward (and possible
        // anti-parallel CFG) capacities were accumulated above; synthetic
        // reverse edges retain the default zero capacity.
        for (auto &[u, Neighbors] : adjList) {
            for (NodeNo v : Neighbors) {
                capacity.try_emplace({u, v}, 0);
                flow[{u, v}] = 0;
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
        std::unordered_set<NodeNo> visited;
        std::queue<NodeNo> q;
        NodeNo sourceNode = To_Node[source];
        q.push(sourceNode);
        visited.insert(sourceNode);

        //use BFS to find path p
        while(!q.empty()){
            NodeNo u = q.front();
            q.pop();

            for(auto v:G.adjList[u]){
                if(!visited.count(v) &&
                   G.capacity[{u, v}] > G.flow[{u, v}]){
                    visited.insert(v);
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

namespace {
using InstructionEdge = std::pair<Instruction *, Instruction *>;

static std::optional<unsigned>
evaluateSplitCandidate(Instruction *CutI, Function &F) {
    unsigned CutIndex = 0;
    bool Found = false;
    for (Instruction &I : instructions(F)) {
        if (&I == CutI) {
            Found = true;
            break;
        }
        ++CutIndex;
    }
    if (!Found)
        return std::nullopt;

    // Evaluate on a clone because splitting return blocks and discovering the
    // exact CodeExtractor interface mutates the function.
    std::unique_ptr<Module> Clone = CloneModule(*F.getParent());
    Function *CloneF = Clone->getFunction(F.getName());
    if (!CloneF)
        return std::nullopt;

    Instruction *CloneCutI = nullptr;
    unsigned Index = 0;
    for (Instruction &I : instructions(*CloneF)) {
        if (Index++ == CutIndex) {
            CloneCutI = &I;
            break;
        }
    }
    if (!CloneCutI)
        return std::nullopt;

    BasicBlock *CutBB = CloneCutI->getParent();
    BasicBlock *NewCutBB =
        CutBB->splitBasicBlock(CloneCutI, CutBB->getName() + ".split.eval");

    SmallVector<BasicBlock *, 16> BlocksToExtract;
    SmallPtrSet<BasicBlock *, 16> Visited;
    std::queue<BasicBlock *> Queue;
    Queue.push(NewCutBB);
    Visited.insert(NewCutBB);
    while (!Queue.empty()) {
        BasicBlock *BB = Queue.front();
        Queue.pop();
        BlocksToExtract.push_back(BB);
        for (BasicBlock *Succ : successors(BB))
            if (Visited.insert(Succ).second)
                Queue.push(Succ);
    }

    DominatorTree DT(*CloneF);
    CodeExtractor CE(BlocksToExtract, &DT, /*AggregateArgs=*/false,
                     /*BFI=*/nullptr, /*BPI=*/nullptr, /*AC=*/nullptr,
                     /*AllowVarArgs=*/false, /*AllowAlloca=*/false,
                     /*AllocationBlock=*/nullptr, /*Suffix=*/"candidate");
    if (!CE.isEligible())
        return std::nullopt;

    CodeExtractorAnalysisCache CEAC(*CloneF);
    SetVector<Value *> Inputs, Outputs;
    Function *Outlined = CE.extractCodeRegion(CEAC, Inputs, Outputs);
    if (!Outlined)
        return std::nullopt;

    // AggregateArgs is false, so each exact CodeExtractor input and output
    // corresponds to one parameter in the outlined function.
    return Outlined->arg_size();
}
} // namespace

Instruction *findBestSplitPoint(
    InstGraph &G,
    const std::unordered_set<NodeNo> &reachableFromSource,
    Function &F) {
    DenseMap<Instruction *, unsigned> InstructionOrder;
    unsigned NextOrder = 0;
    for (Instruction &I : instructions(F))
        InstructionOrder[&I] = NextOrder++;

    SmallVector<InstructionEdge, 16> CutEdges;
    DenseSet<InstructionEdge> Seen;

    // Recover every real instruction-level edge crossing the complete S/T
    // partition. Synthetic reverse residual edges are intentionally excluded.
    for (auto &[NodeEdge, Edges] : G.originalEdges) {
        NodeNo U = NodeEdge.first;
        NodeNo V = NodeEdge.second;
        if (!reachableFromSource.count(U) || reachableFromSource.count(V) ||
            G.capacity[{U, V}] <= 0)
            continue;

        for (auto [SourceV, DestV] : Edges) {
            auto *SourceI = dyn_cast<Instruction>(SourceV);
            auto *DestI = dyn_cast<Instruction>(DestV);
            if (!SourceI || !DestI)
                continue;
            InstructionEdge Edge{SourceI, DestI};
            if (Seen.insert(Edge).second)
                CutEdges.push_back(Edge);
        }
    }

    // Stable order and tie-breaker: destination instruction order first, then
    // source instruction order.
    llvm::sort(CutEdges, [&](const InstructionEdge &L,
                             const InstructionEdge &R) {
        unsigned LDest = InstructionOrder.lookup(L.second);
        unsigned RDest = InstructionOrder.lookup(R.second);
        if (LDest != RDest)
            return LDest < RDest;
        return InstructionOrder.lookup(L.first) <
               InstructionOrder.lookup(R.first);
    });

    Instruction *Best = nullptr;
    unsigned BestArgumentCount = std::numeric_limits<unsigned>::max();
    for (auto [SourceI, DestI] : CutEdges) {
        NodeNo DestNode = To_Node[DestI];

        // The current transformation supports a single instruction boundary
        // within a block. Cross-block edges have terminator sources and are not
        // valid single splitBasicBlock points.
        if (SourceI->isTerminator() || isa<ReturnInst>(SourceI) ||
            isa<PHINode>(DestI) || isa<ReturnInst>(DestI) ||
            G.loopNodes.count(DestNode) ||
            SourceI->getParent() != DestI->getParent() ||
            SourceI->getNextNode() != DestI)
            continue;

        std::optional<unsigned> ArgumentCount =
            evaluateSplitCandidate(DestI, F);
        if (!ArgumentCount)
            continue;

        // CutEdges is already in deterministic instruction order, so retaining
        // the first equal-cost candidate implements the required tie-breaker.
        if (*ArgumentCount < BestArgumentCount) {
            BestArgumentCount = *ArgumentCount;
            Best = DestI;
        }
    }

    return Best;
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

bool splitFunction(Instruction *cutI, Function &F, FunctionAnalysisManager &AM){
    // 1. 基本檢查
    if (!cutI) {
        return false;
    }
    
    if (isa<PHINode>(cutI)) {
        cutI = cutI->getNextNode(); // PHI node 不能被切割，所以要往後找
        if (!cutI)
            return false;
    }
    if (isa<ReturnInst>(cutI)) {
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
        // extractCodeRegion currently returns null before performing extraction
        // when eligibility fails. Defensively restore the block split so a
        // failed transformation leaves the original CFG unchanged.
        if (!MergeBlockIntoPredecessor(newCutBB))
            errs() << "Failed to restore split block after extraction failure.\n";
        return false;
    }

    // 5. Keep the outlined suffix out of later inlining and make its
    // downstream optimization policy explicitly size-oriented.
    newFunc->addFnAttr(Attribute::NoInline);
    newFunc->addFnAttr(Attribute::MinSize);
    newFunc->addFnAttr(Attribute::OptimizeForSize);
    // 移除 alwaysinline（避免跟 noinline 衝突）
    newFunc->removeFnAttr(Attribute::AlwaysInline);

    bool broken = verifyFunction(*newFunc, &errs());
    if(broken){
        errs() << "Function Verified failed.\n";
        return false;
    }

    return true;
}
