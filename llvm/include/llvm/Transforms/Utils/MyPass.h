#pragma once

#include "llvm/Transforms/Utils/MyFunction.h"

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
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h" // errs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"

using namespace llvm;

namespace llvm{
    class MyPass: public PassInfoMixin<MyPass>{
        public://runOnFunction是舊的 legacy PM
            PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
    };
}//namespace llvm

std::unordered_map<std::pair<Value *, Value *>, int, PairHash> buildCapacity(Function &F);
