#pragma once

#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/MyFunction.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace llvm {
  extern cl::opt<std::string> OutFilePath;

  class CallsiteInfoPass : public PassInfoMixin<CallsiteInfoPass> {
    public:
      PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };
} // namespace llvm