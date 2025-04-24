#ifndef LLVM_TRANSFORMS_HELLONEW_HELLO_H
#define LLVM_TRANSFORMS_HELLONEW_HELLO_H

#include "llvm/IR/PassManager.h"

namespace llvm{
    class HelloPass: public PassInfoMixin<HelloPass>{
        public://runOnFunction是舊的 legacy PM
            PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
        };
}//namespace llvm

#endif // LLVM_TRANSFORMS_HELLONEW_HELLO_H