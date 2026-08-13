#include "llvm/Transforms/Utils/MyPass.h"
#include "llvm/Transforms/Utils/MyFunction.h"

using namespace llvm;

PreservedAnalyses MyPass::run(Function &F, FunctionAnalysisManager &AM){
    if (F.isDeclaration()) return PreservedAnalyses::all();
    if (F.getName().empty()) return PreservedAnalyses::all();
    if (F.hasFnAttribute(Attribute::AlwaysInline)) return PreservedAnalyses::all();
    if(F.getName().ends_with("cloned")) return PreservedAnalyses::none(); //已經split的不可再次處理

    // 收集所有需要 partial inline 的 call site
    SmallVector<CallInst*, 4> InlineCalls;
    for(auto *U:F.users()){
        if(auto *CI = dyn_cast<CallInst>(U)){
            auto *CB = dyn_cast<CallBase>(U);
            auto *Callee = CB->getCalledFunction();
            auto *Caller = CB->getCaller();
            if(!Callee) continue;
            if(!Caller) continue;
            if(Callee->isIntrinsic()) continue;
            if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                if(!hasPartialInlineVal(CB)) continue;
                auto res = getPartialInlineVal(CB);
                if((Callee == &F) && res){
                    InlineCalls.push_back(CI);
                }
            }
        }
    }
    if(InlineCalls.empty()) return PreservedAnalyses::all();
    
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
            }
            SCCs.push_back(temp);
        }
        else alone.push_back({SCC[0]});
    }

    mappingNode(SCCs, alone);

    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> cap = buildCapacity(F);
    // 建立可切割Graph
    InstGraph IG(To_Node, CFG, cap);
    // SCCs[0] is the collapsed argument source. The remaining SCC entries are
    // real cycles and are excluded from destination split candidates.
    for (size_t I = 1; I < SCCs.size(); ++I)
        if (!SCCs[I].empty())
            IG.loopNodes.insert(To_Node[SCCs[I].front()]);
    
    // Minimum Cut
    if(F.arg_empty()) return PreservedAnalyses::all();
    std::unordered_set<NodeNo> rfs;
    Value *source = F.args().begin();

    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
    Instruction *target = getLatestReturn(F, PDT);

    int maxFlow = fordFulkerson(IG, source, target, rfs);
    if(maxFlow != 0){
        Instruction *CutI = findBestSplitPoint(IG, rfs, F);

        bool res = splitFunction(CutI, F, AM);
        if(res){
            // The experiment must be able to evaluate the selected custom
            // partial-inlining decision even when Clang was invoked with
            // -fno-inline (or the original function was otherwise marked
            // noinline). Temporarily override both the callee and call-site
            // barriers only for these explicitly selected calls. The outlined
            // cold function remains noinline as established by splitFunction.
            bool RestoreCalleeNoInline =
                F.hasFnAttribute(Attribute::NoInline);
            if (RestoreCalleeNoInline)
                F.removeFnAttr(Attribute::NoInline);

            for(auto *CI : InlineCalls){
                bool RestoreCallNoInline =
                    CI->hasFnAttr(Attribute::NoInline);
                if (RestoreCallNoInline)
                    CI->removeFnAttr(Attribute::NoInline);

                InlineFunctionInfo IFI;
                InlineResult Result = InlineFunction(*CI, IFI);
                if (!Result.isSuccess()) {
                    // A failed InlineFunction leaves the call well-defined, so
                    // restore its original policy before rejecting/diagnosing
                    // the transformation at the enclosing module transaction.
                    if (RestoreCallNoInline)
                        CI->addFnAttr(Attribute::NoInline);
                    errs() << "Custom partial inline failed at call site: "
                           << Result.getFailureReason() << "\n";
                }
            }

            if (RestoreCalleeNoInline)
                F.addFnAttr(Attribute::NoInline);
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

std::unordered_map<std::pair<Value *, Value *>, int, PairHash> buildCapacity(Function &F){
    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> Cap;
    using LiveSet = std::unordered_set<Value *>;

    // Only local SSA values can become arguments of an outlined region.
    // Constants and globals remain directly usable and must not increase the
    // boundary-argument cost.
    auto IsLocalSSAValue = [&F](Value *V) {
        if (isa<Argument>(V))
            return cast<Argument>(V)->getParent() == &F;
        if (auto *I = dyn_cast<Instruction>(V))
            return I->getFunction() == &F && !I->getType()->isVoidTy();
        return false;
    };

    std::unordered_map<BasicBlock *, LiveSet> Use, Def, LiveIn, LiveOut;

    // Build block Use/Def sets. PHI operands are deliberately excluded here:
    // an incoming PHI value is used on its predecessor edge, not in the PHI's
    // block.
    for (BasicBlock &BB : F) {
        LiveSet &BBUse = Use[&BB];
        LiveSet &BBDef = Def[&BB];
        for (Instruction &I : BB) {
            if (!isa<PHINode>(I)) {
                for (Value *V : I.operands())
                    if (IsLocalSSAValue(V) && !BBDef.count(V))
                        BBUse.insert(V);
            }
            if (!I.getType()->isVoidTy())
                BBDef.insert(&I);
        }
    }

    // Values live on Pred -> Succ. LiveIn[Succ] accounts for ordinary uses;
    // PHI definitions are removed and the incoming operands associated with
    // this exact predecessor edge are added.
    auto ComputeEdgeLive = [&](BasicBlock *Pred, BasicBlock *Succ) {
        LiveSet EdgeLive = LiveIn[Succ];
        for (PHINode &PN : Succ->phis()) {
            EdgeLive.erase(&PN);
            for (unsigned I = 0, E = PN.getNumIncomingValues(); I != E; ++I) {
                if (PN.getIncomingBlock(I) != Pred)
                    continue;
                Value *Incoming = PN.getIncomingValue(I);
                if (IsLocalSSAValue(Incoming))
                    EdgeLive.insert(Incoming);
            }
        }
        return EdgeLive;
    };

    // Standard backward CFG liveness fixed point:
    //   LiveOut[B] = union EdgeLive(B, Succ)
    //   LiveIn[B]  = Use[B] union (LiveOut[B] - Def[B])
    bool Changed;
    do {
        Changed = false;
        for (BasicBlock &BB : reverse(F)) {
            LiveSet NewOut;
            for (BasicBlock *Succ : successors(&BB)) {
                LiveSet EdgeLive = ComputeEdgeLive(&BB, Succ);
                NewOut.insert(EdgeLive.begin(), EdgeLive.end());
            }

            LiveSet NewIn = Use[&BB];
            for (Value *V : NewOut)
                if (!Def[&BB].count(V))
                    NewIn.insert(V);

            if (NewOut != LiveOut[&BB] || NewIn != LiveIn[&BB]) {
                LiveOut[&BB] = std::move(NewOut);
                LiveIn[&BB] = std::move(NewIn);
                Changed = true;
            }
        }
    } while (Changed);

    // Assign a capacity to every real instruction-flow edge. Within a block,
    // the cost is the number of values live immediately after the source
    // instruction. Across blocks, it is the edge-specific live set, including
    // the correct incoming operands of successor PHIs.
    unsigned InstructionCount = 0;
    for (BasicBlock &BB : F) {
        InstructionCount += BB.size();
        LiveSet Live = LiveOut[&BB];
        for (Instruction &I : reverse(BB)) {
            Instruction *Next = I.getNextNode();
            if (Next)
                addDependency(&I, Next, 1 + Live.size(), Cap);

            if (!I.getType()->isVoidTy())
                Live.erase(&I);
            if (!isa<PHINode>(I))
                for (Value *V : I.operands())
                    if (IsLocalSSAValue(V))
                        Live.insert(V);
        }

        Instruction *Term = BB.getTerminator();
        for (BasicBlock *Succ : successors(&BB)) {
            LiveSet EdgeLive = ComputeEdgeLive(&BB, Succ);
            addDependency(Term, &Succ->front(), 1 + EdgeLive.size(), Cap);
        }
    }

    // All arguments are collapsed into the source node. Distribute the entry
    // capacity over their parallel source edges so InstGraph's aggregation
    // yields exactly 1 + the number of live function arguments at entry.
    if (!F.empty() && !F.getEntryBlock().empty()) {
        Instruction *Entry = &F.getEntryBlock().front();
        bool AddedBaseCost = false;
        for (Argument &Arg : F.args()) {
            int Weight = LiveIn[&F.getEntryBlock()].count(&Arg) ? 1 : 0;
            if (!AddedBaseCost) {
                ++Weight;
                AddedBaseCost = true;
            }
            addDependency(&Arg, Entry, Weight, Cap);
        }
    }

    // Keep the existing policy of discouraging a useless split immediately
    // before "ret void". Invalid return-adjacent cuts are also filtered later.
    if (F.getReturnType()->isVoidTy()) {
        for (BasicBlock &BB : F) {
            auto *RI = dyn_cast<ReturnInst>(BB.getTerminator());
            if (!RI)
                continue;
            if (Instruction *Prev = RI->getPrevNode())
                addDependency(
                    Prev, RI,
                    std::max<int>(Cap[{Prev, RI}], InstructionCount), Cap);
        }
    }

    return Cap;
}
