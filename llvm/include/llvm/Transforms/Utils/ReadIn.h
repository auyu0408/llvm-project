#pragma once

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"

namespace llvm {
    class ReadInPass : public PassInfoMixin<ReadInPass> {
        public:
            PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };
}