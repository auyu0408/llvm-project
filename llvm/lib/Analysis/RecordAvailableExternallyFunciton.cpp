#include "llvm/Analysis/RecordAvailableExternallyFunciton.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

PreservedAnalyses RecordAvailableExternallyFuncitonPass::run(Module &M, ModuleAnalysisManager &AM) {
  const char *FunctionFileName = std::getenv("RECORD_AVAILABLE_EXTERNALLY_FUNCTIONS");
  if (!FunctionFileName)
    return PreservedAnalyses::all();

  std::string FunctionString;
  raw_string_ostream FunctionStream{FunctionString};
  for (auto &F : M) {
    if (F.hasAvailableExternallyLinkage())
      FunctionStream << F.getName() << '\n';
  }

  std::error_code EC;
  raw_fd_ostream FStream{FunctionFileName, EC};
  if (!EC)
    FStream << FunctionStream.str();
  else
    errs() << "LLVM Warning: Could not open file " << FunctionFileName << " (" << EC.message() << ")\n";

  return PreservedAnalyses::all();
}