#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/IR/InstrTypes.h"

namespace llvm {

class CallsiteInfoPass : public PassInfoMixin<CallsiteInfoPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  size_t getCallBaseId(const CallBase &CB);
  bool hasCallBaseId(const CallBase &CB);
};

} // namespace llvm