#pragma once

#include "llvm/IR/PassManager.h"

namespace llvm {

class RecordAvailableExternallyFuncitonPass : public PassInfoMixin<RecordAvailableExternallyFuncitonPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm