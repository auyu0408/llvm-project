#include "llvm/Analysis/CallsiteInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Metadata.h"
#include <cstdlib>
#include <string>

using namespace llvm;

PreservedAnalyses CallsiteInfoPass::run(Module &M, ModuleAnalysisManager &AM) {
  const char *RecordFileName = std::getenv("RECORD_CALLSITE_INFO");
  if (!RecordFileName)
    return PreservedAnalyses::all();

  std::string RecordFile;
  raw_string_ostream RecordStream{RecordFile};
  for (auto &F : M) {
    for (auto &BB : F) {
      for (Instruction &I : BB) {
        if (auto *CB = dyn_cast<CallBase>(&I)) {
          if (!hasCallBaseId(*CB))
            continue;
          if (Function *Callee = CB->getCalledFunction()) {
            auto Id = getCallBaseId(*CB);
            if (!Callee->isDeclaration())
              RecordStream << F.getName() << ',' << Callee->getName() << ',' << Id << '\n';
          }
        }
      }
    }
  }

  std::error_code EC;
  raw_fd_ostream FStream{RecordFileName, EC};
  if (!EC)
    FStream << RecordStream.str();
  else
    errs() << "LLVM Warning: Could not open file " << RecordFileName << " (" << EC.message() << ")\n";

  return PreservedAnalyses::all();
}

size_t CallsiteInfoPass::getCallBaseId(const CallBase &CB) {
  auto *N = CB.getMetadata("callbase.id");
  assert(N && "CallBase does not carry metadata.\n");
  Constant *C = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0))
                    ->getValue();
  return cast<ConstantInt>(C)->getZExtValue();
}

bool CallsiteInfoPass::hasCallBaseId(const CallBase &CB) {
  auto *N = CB.getMetadata("callbase.id");
  if (not N)
    return false;

  if (not dyn_cast<MDNode>(N))
    return false;

  if (not dyn_cast<MDNode>(N)->getOperand(0))
    return false;

  auto *CM = dyn_cast<ConstantAsMetadata>(dyn_cast<MDNode>(N)->getOperand(0));
  if (not CM)
    return false;
  if (not CM->getValue())
    return false;

  return true;
}