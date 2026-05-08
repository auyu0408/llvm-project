#pragma once

#include "llvm/IR/PassManager.h"

namespace llvm {

class GeneralFunctionInfoPass : public PassInfoMixin<GeneralFunctionInfoPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm