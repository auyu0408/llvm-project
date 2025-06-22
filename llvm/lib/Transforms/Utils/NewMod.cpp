#include "llvm/Transforms/Utils/NewMod.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
using namespace llvm;

PreservedAnalyses NewModPass::run(Module &M, ModuleAnalysisManager &AM){

    std::vector<Function *> toDelete;
    for(auto &F:M){
        if(F.isDeclaration()) continue;//沒有定義的話不能檢查attributes
        if(F.getName() == "main") continue;
        if(F.hasFnAttribute("noinline")) continue;
        
        if(F.use_empty() && F.hasFnAttribute("hello-inline")){//已經被inline而且有attribute
            toDelete.push_back(&F);
        }
    }

    for(Function *F:toDelete){
        F->eraseFromParent();
    }    

    return PreservedAnalyses::none();
}