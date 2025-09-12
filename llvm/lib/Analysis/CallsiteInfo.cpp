#include "llvm/Analysis/CallsiteInfo.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/MyFunction.h"

#include <fstream>
#include <string>

using namespace llvm;

PreservedAnalyses CallsiteInfoPass::run(Module &M, ModuleAnalysisManager &AM) {
    std::ofstream outfile;
    if(OutFilePath.empty()) outfile.open("output.decisions");
    else outfile.open(OutFilePath);

    if(!outfile){
        errs() << "open outputfile failed.\n";
        return PreservedAnalyses::none();
    }
      
    for(auto &F : M){
        for(auto &BB : F){
            for(auto &I : BB){
                auto *CB = dyn_cast<CallBase>(&I);
                if(!CB) continue;
                if(!hasCallBaseId(CB))
                    continue;
                
                auto *Callee = CB->getCalledFunction();
                auto *Caller = CB->getCaller();
                if(!Callee) continue;
                if(!Caller) continue;
                if(Callee->isIntrinsic()) continue;
                if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                    auto CBID = getCallBaseId(CB);
                    if(!hasPassVal(CB)){
                        outfile << (Caller->getName()).str() << "," << (Callee->getName()).str() << "," << CBID << "," << "not_inlined\n";
                        continue;
                    }

                    auto res = getPassVal(CB);
                    if(res)
                        outfile << (Caller->getName()).str() << "," << (Callee->getName()).str() << "," << CBID << "," << "inlined\n";
                    else
                        outfile << (Caller->getName()).str() << "," << (Callee->getName()).str() << "," << CBID << "," << "not_inlined\n";
                }
            }
        }
    }

    return PreservedAnalyses::all();
}