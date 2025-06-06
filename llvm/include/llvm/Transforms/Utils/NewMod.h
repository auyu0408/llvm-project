#pragma once

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

namespace llvm{
    class NewModPass: public PassInfoMixin<NewModPass>{
        public://runOnFunction是舊的 legacy PM
            PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
        };
}//namespace llvm
