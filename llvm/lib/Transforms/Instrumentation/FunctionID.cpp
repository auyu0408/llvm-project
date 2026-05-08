#include "llvm/Transforms/Instrumentation/FunctionID.h"

#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/CFG.h"
#include <set>
#include <map>

using namespace llvm;

PreservedAnalyses FunctionIDPass::run(Module &M, ModuleAnalysisManager &AM) {
  size_t CallBaseID = 1;
  std::map<Function*, std::vector<Function*>> Callees;
  std::map<Function*, int> Indegrees;
  
  std::map<BasicBlock*, std::vector<CallBase*>> CBs;
  std::vector<Function*> SortedFuncs;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        // overwrite original callbase id
        auto &Ctx = M.getContext();
        auto *N = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(
                                      Ctx, APInt{64, 0, false})));
        CB->setMetadata("callbase.id", N);
        // steal from computeFunctionSummary
        auto *CalledValue = CB->getCalledOperand();
        auto *CalledFunction = CB->getCalledFunction();
        if (CalledValue && !CalledFunction) {
          CalledValue = CalledValue->stripPointerCasts();
          // Stripping pointer casts can reveal a called function.
          CalledFunction = dyn_cast<Function>(CalledValue);
        }
        // Check if this is an alias to a function. If so, get the
        // called aliasee for the checks below.
        if (auto *GA = dyn_cast<GlobalAlias>(CalledValue)) {
          assert(!CalledFunction && "Expected null called function in callsite for alias");
          CalledFunction = dyn_cast<Function>(GA->getAliaseeObject());
        }
        if (CalledFunction) {
          if (!Indegrees.count(&F))
            Indegrees[&F] = 0;
          Callees[&F].push_back(CalledFunction);
          Indegrees[CalledFunction] += 1;
          CBs[&BB].push_back(CB);
        }
      } 
    }
  }

  // topological sort on functions (using M iteration for determinism)
  std::set<Function*> CallerConsidered;
  while (!Indegrees.empty()) {
    std::vector<Function*> ZeroIndeegrees;
    std::vector<Function*> FallbackCandidates;
    
    // Iterate deterministically using Module M
    for (auto &F : M) {
      if (!Indegrees.count(&F)) continue;
      if (Indegrees[&F] == 0)
        ZeroIndeegrees.push_back(&F);
      else if (CallerConsidered.count(&F))
        FallbackCandidates.push_back(&F);
    }
    
    if (ZeroIndeegrees.size() == 0) {
      for (auto Func : FallbackCandidates)
        ZeroIndeegrees.push_back(Func);
    }
    
    if (ZeroIndeegrees.size() == 0) {
      int MinIndegree = 100000;
      // Deterministic tie breaker for MinIndegree
      Function* Chosen = nullptr;
      for (auto &F : M) {
        if (!Indegrees.count(&F)) continue;
        if (Indegrees[&F] < MinIndegree) {
          MinIndegree = Indegrees[&F];
          Chosen = &F;
        }
      }
      if (Chosen)
        ZeroIndeegrees.push_back(Chosen);
    }
    
    assert(ZeroIndeegrees.size() > 0 && "Should find a function!");
    for (auto Func : ZeroIndeegrees) {
      Indegrees.erase(Func);
      SortedFuncs.push_back(Func);
      for (auto Callee : Callees[Func]) {
        if (Indegrees.count(Callee))
          Indegrees[Callee] -= 1;
        CallerConsidered.insert(Callee);
      }
    }
  }

  // topological sort on basic blocks
  for (auto Func : SortedFuncs) {
    if (Func->isDeclaration())
      continue;
    std::map<BasicBlock*, int> Indegrees;
    for (auto &BB : *Func) {
      if (!Indegrees.count(&BB))
        Indegrees[&BB] = 0;
      for (BasicBlock *Succ : successors(&BB))
        Indegrees[Succ] += 1;
    }

    std::set<BasicBlock*> PredecessorConsidered;
    while (!Indegrees.empty()) {
      std::vector<BasicBlock*> ZeroIndeegrees;
      std::vector<BasicBlock*> FallbackCandidates;
      
      // Iterate deterministically using Func
      for (auto &BB : *Func) {
        if (!Indegrees.count(&BB)) continue;
        if (Indegrees[&BB] == 0)
          ZeroIndeegrees.push_back(&BB);
        else if (PredecessorConsidered.count(&BB))
          FallbackCandidates.push_back(&BB);
      }
      
      if (ZeroIndeegrees.size() == 0) {
        for (auto BB : FallbackCandidates)
          ZeroIndeegrees.push_back(BB);
      }
      
      if (ZeroIndeegrees.size() == 0) {
        // Fallback robust breaker
        for (auto &BB : *Func) {
          if (Indegrees.count(&BB)) {
            ZeroIndeegrees.push_back(&BB);
            break;
          }
        }
      }
      
      assert(ZeroIndeegrees.size() > 0 && "Should find a basic block!");
      for (auto BB : ZeroIndeegrees) {
        Indegrees.erase(BB);
        if (CBs.count(BB)) {
          // modify callbase id (start from 1)
          for (auto CB : CBs[BB]) {
            auto &Ctx = M.getContext();
            auto *N = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(
                                           Ctx, APInt{64, CallBaseID++, false})));
            CB->setMetadata("callbase.id", N);
          }
        }
        for (auto Succ : successors(BB)) {
          if (Indegrees.count(Succ))
            Indegrees[Succ] -= 1;
          PredecessorConsidered.insert(Succ);
        }
      }
    }
  }
  
  return PreservedAnalyses::all();
}