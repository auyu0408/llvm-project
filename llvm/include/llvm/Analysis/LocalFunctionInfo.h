#pragma once

#include "llvm/IR/PassManager.h"

namespace llvm {

class LocalFunctionInfoPass : public PassInfoMixin<LocalFunctionInfoPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm
