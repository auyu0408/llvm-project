#include "llvm/Transforms/Utils/OnePassPI.h"

#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include <fstream>
#include <string>

using namespace llvm;

size_t llvm::estimateModuleSize(Module &M){
    SmallVector<char, 0> buf;
    raw_svector_ostream OS(buf);
    WriteBitcodeToFile(M, OS);
    return buf.size();
}

/// Helper: 為一個獨立的 Module 建立完整的 analysis manager 並跑 Oz pipeline，
/// 回傳 estimated bitcode size。
static size_t runOzAndMeasure(Module &M) {
    // 每個 cloned module 需要自己的一整套 analysis managers
    LoopAnalysisManager   LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager  CGAM;
    ModuleAnalysisManager MAM_local;

    PassBuilder PB;
    PB.registerModuleAnalyses(MAM_local);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM_local);

    ModulePassManager OzPipeline =
        PB.buildPerModuleDefaultPipeline(OptimizationLevel::Oz);
    OzPipeline.run(M, MAM_local);

    return estimateModuleSize(M);
}

PreservedAnalyses OnePassPIPass::run(Module &M, ModuleAnalysisManager &MAM){
    // 1. 讀檔案
    ModulePassManager MyRead;
    MyRead.addPass(FunctionIDPass());
    MyRead.addPass(CallsiteInfoPass());
    MyRead.addPass(ReadInPass());
    MyRead.run(M, MAM);

    // 2. baseline: clone → Oz → 量 size
    {
        std::unique_ptr<Module> M_baseline = CloneModule(M);
        size_t sizeBaseline = runOzAndMeasure(*M_baseline);
        errs() << "baseline size: " << sizeBaseline << "\n";

        // 3. 對每個 function 獨立試跑 MyPass，不影響原始 M
        SmallVector<std::string, 16> FuncNames;
        for (Function &F : M) {
            if (!F.isDeclaration())
                FuncNames.push_back(F.getName().str());
        }

        for (const auto &FName : FuncNames) {
            // (a) Clone 整個 module
            std::unique_ptr<Module> M_comp = CloneModule(M);

            // (b) 在 cloned module 中找到對應的 function
            Function *F_comp = M_comp->getFunction(FName);
            if (!F_comp || F_comp->isDeclaration()) continue;

            // (c) 為 cloned module 建立獨立的 FAM，對 cloned function 跑 MyPass
            {
                LoopAnalysisManager   LAM_c;
                FunctionAnalysisManager FAM_c;
                CGSCCAnalysisManager  CGAM_c;
                ModuleAnalysisManager MAM_c;

                PassBuilder PB_c;
                PB_c.registerModuleAnalyses(MAM_c);
                PB_c.registerCGSCCAnalyses(CGAM_c);
                PB_c.registerFunctionAnalyses(FAM_c);
                PB_c.registerLoopAnalyses(LAM_c);
                PB_c.crossRegisterProxies(LAM_c, FAM_c, CGAM_c, MAM_c);

                FunctionPassManager MyFPM;
                MyFPM.addPass(MyPass());
                MyFPM.run(*F_comp, FAM_c);
            }

            // (d) Oz pipeline + 量 size（又是一套獨立的 managers）
            size_t sizeComp = runOzAndMeasure(*M_comp);

            errs() << "function name: " << FName
                   << ", size: " << sizeComp
                   << ", diff from baseline: "
                   << (int64_t)(sizeComp - sizeBaseline)
                   << "\n";
        }
    }

    //寫入檔案

    return PreservedAnalyses::all();

}


void registerMyPass(PassBuilder &PB) {
    // 1. 註冊一個分析 Pass (如果 OnePassPI 需要 FunctionIDPass 的結果)
    /*** 寫過了
    PB.registerAnalysisRegistrationCallback([](ModuleAnalysisManager &MAM) {
        MAM.registerPass([&] { return FunctionIDPass(); });
    });
    ***/

    // 2. 將主 Pass 掛載到管線中 (例如：在優化管線開始時執行)
    PB.registerPipelineStartEPCallback(
        [](ModulePassManager &MPM, OptimizationLevel Level) {
            MPM.addPass(llvm::OnePassPIPass());
        });
}