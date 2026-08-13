#pragma once

// estimateModuleSize / estimateTextSize
#include "llvm/ADT/SmallVector.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Object/ObjectFile.h"

// OnePassPIPass
#include "llvm/Transforms/Instrumentation/FunctionID.h"
#include "llvm/Analysis/CallsiteInfo.h"
#include "llvm/Transforms/Utils/ReadIn.h"
#include "llvm/Transforms/Utils/MyPass.h"

// Analysis Manager include
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Path.h" 

namespace llvm{
    
class OnePassPIPass: public PassInfoMixin<OnePassPIPass>{
    public:
        PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

size_t estimateModuleSize(Module &M);
size_t estimateTextSize(Module &M);
}//namespace llvm
