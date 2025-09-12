#include "llvm/Transforms/Utils/NewMod.h"

#include <cassert>
#include <fstream>
#include <string>

using namespace llvm;

PreservedAnalyses NewModPass::run(Module &M, ModuleAnalysisManager &AM){

    /***
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
    ***/

    if(OutFilePath.empty()) return PreservedAnalyses::none();
    else{
        std::ofstream outfile(OutFilePath);
        if(!outfile){
            errs() << "open outputfile failed.\n";
            return PreservedAnalyses::none();
        }
        
        for(auto &F : M){
            for(auto &BB : F){
                for(auto &I : BB){
                    auto *CB = dyn_cast<CallBase>(&I);
                    if(!CB)
                        continue;

                    auto *Callee = CB->getCalledFunction();
                    auto *Caller = CB->getCaller();
                    if(Callee->isIntrinsic()) continue;
                    if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                        auto CBID = getCallBaseId(CB);
                        auto res =  getPassVal(CB);
                        if(res)
                            outfile << (Caller->getName()).str() << "," << (Callee->getName()).str() << "," << CBID << "," << "inlined\n";
                        else
                            outfile << (Caller->getName()).str() << "," << (Callee->getName()).str() << "," << CBID << "," << "not_inlined\n";
                    }
                }
            }
        }

    }
    
    return PreservedAnalyses::none();
}