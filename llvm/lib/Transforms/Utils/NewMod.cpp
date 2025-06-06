#include "llvm/Transforms/Utils/NewMod.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
using namespace llvm;

PreservedAnalyses NewModPass::run(Module &M, ModuleAnalysisManager &AM){
    
    //errs() << "enter NewPass\n";

    std::vector<Function *> toDelete;
    for(auto &F:M){
        if(F.isDeclaration()){
            assert(!F.isDeclaration() && "Function is a declaration, no attributes!");
            continue;
        }
        if(F.getName() == "main") continue;
        if(F.hasFnAttribute("noinline")) continue;
        
        if(F.use_empty() && !F.isDeclaration()){
            toDelete.push_back(&F);
        }
    }

    for(Function *F:toDelete){
        //errs() << "Function: " << F->getName() << " deleted\n";
        F->eraseFromParent();
    }    

    return PreservedAnalyses::none();
}