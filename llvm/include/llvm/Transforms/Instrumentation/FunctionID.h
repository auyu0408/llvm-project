#pragma once

#include "llvm/IR/PassManager.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/ModuleSummaryIndex.h"


namespace llvm {

class FunctionIDPass : public PassInfoMixin<FunctionIDPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm