#include "llvm/Transforms/Utils/OnePassPI.h"
#include "llvm/Transforms/Utils/MyFunction.h"

#include <fstream>
#include <string>

using namespace llvm;

size_t llvm::estimateModuleSize(Module &M){
    SmallVector<char, 0> buf;
    raw_svector_ostream OS(buf);
    WriteBitcodeToFile(M, OS);
    return buf.size();
}

size_t llvm::estimateTextSize(Module &M) {
    // 取得 target triple
    const std::string &TripleStr = M.getTargetTriple();
    if (TripleStr.empty()) {
        errs() << "estimateObjectSize: no target triple, fallback to bitcode\n";
        return estimateModuleSize(M);
    }

    // 找到對應的 Target
    std::string Error;
    const Target *TheTarget = TargetRegistry::lookupTarget(TripleStr, Error);
    if (!TheTarget) {
        errs() << "estimateObjectSize: " << Error << ", fallback to bitcode\n";
        return estimateModuleSize(M);
    }

    // 建立 TargetMachine
    TargetOptions Options;
    std::unique_ptr<TargetMachine> TM(
        TheTarget->createTargetMachine(TripleStr, "generic", "", Options,
                                       Reloc::PIC_));
    if (!TM) {
        errs() << "estimateObjectSize: cannot create TM, fallback to bitcode\n";
        return estimateModuleSize(M);
    }

    // 用 legacy PassManager 把 module 編譯成 .o 到記憶體 buffer
    SmallVector<char, 0> ObjBuf;
    raw_svector_ostream OS(ObjBuf);

    legacy::PassManager PM;
    if (TM->addPassesToEmitFile(PM, OS, nullptr,
                                CodeGenFileType::ObjectFile)) {
        errs() << "estimateObjectSize: emit not supported, fallback to bitcode\n";
        return estimateModuleSize(M);
    }
    PM.run(M);
    // 到這邊如果使用 ObjBuf.size(); 會得到 object file 的大小

    // 從 .o buffer 中 parse 出 .text section 大小
    auto BufRef = MemoryBufferRef(
        StringRef(ObjBuf.data(), ObjBuf.size()), "in-memory.o");
    auto ObjOrErr = object::ObjectFile::createObjectFile(BufRef);
    if (!ObjOrErr) {
        consumeError(ObjOrErr.takeError());
        errs() << "estimateTextSize: cannot parse .o, fallback to obj size\n";
        return ObjBuf.size();
    }

    size_t textSize = 0;
    for (const auto &Sec : (*ObjOrErr)->sections()) {
        auto NameOrErr = Sec.getName();
        if (!NameOrErr) {
            consumeError(NameOrErr.takeError());
            continue;
        }
        if (*NameOrErr == ".text") {
            textSize += Sec.getSize();
        }
    }
    return textSize;
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

    return estimateTextSize(M);
}

// 防止無限遞迴：runOzAndMeasure 呼叫 buildPerModuleDefaultPipeline
// 會再觸發 OnePassPIPass，需要 guard 擋住內層呼叫
static bool InsideOnePassPI = false;

PreservedAnalyses OnePassPIPass::run(Module &M, ModuleAnalysisManager &MAM){
    // Re-entrance guard: 如果已經在 OnePassPI 內部（例如 runOzAndMeasure
    // 建的 pipeline 又包含了這個 pass），直接跳過
    if (InsideOnePassPI)
        return PreservedAnalyses::all();
    InsideOnePassPI = true;

    // 1. 讀檔案
    // 若是沒有給檔案名的話，預設檔案名為 xxx.c -> xxx_c.decisions（放在當前目錄）
    if (InputFilePath.empty()) {
        StringRef SrcFile = M.getSourceFileName();
        std::string BaseName = sys::path::filename(SrcFile).str();
        std::replace(BaseName.begin(), BaseName.end(), '.', '_');
        InputFilePath = BaseName + ".decisions";
    }
    
    // read decision file
    ModulePassManager MyRead;
    MyRead.addPass(FunctionIDPass());
    MyRead.addPass(ReadInPass());
    MyRead.run(M, MAM);

    {
        // 2. baseline: clone → Oz → 量 size
        std::unique_ptr<Module> M_baseline = CloneModule(M);
        size_t sizeBaseline = runOzAndMeasure(*M_baseline); // 如果需要的話可以分成在clang內或是單獨跑這個pass

        // 3. 收集所有 candidate call sites（有 callbase.id 且 goPass == false）
        struct Candidate {
            size_t id;
            std::string calleeName;
        };
        SmallVector<Candidate, 32> candidates;
        for (Function &F : M) {
            for (BasicBlock &BB : F) {
                for (Instruction &I : BB) {
                    auto *CB = dyn_cast<CallBase>(&I);
                    if (!CB) continue;
                    if (!hasCallBaseId(CB)) continue;
                    
                    auto *Callee = CB->getCalledFunction();
                    auto *Caller = CB->getCaller();
                    if(!Callee) continue;
                    if(!Caller) continue;
                    if(Callee->isIntrinsic()) continue;
                    if(Callee->hasInternalLinkage()||Callee->isDSOLocal()){
                        if (!hasPassVal(CB)) continue;
                        if (getPassVal(CB)) continue; // 已經 inlined 的跳過
                        if (!Callee || Callee->isDeclaration()) continue;
                        candidates.push_back({getCallBaseId(CB), Callee->getName().str()});
                    }
                }
            }
        }

        SmallVector<size_t, 16> Func_inlined_id;

        // 4. Greedy: 維護一個累積的 module，成功的改動會帶到下一個 candidate
        //    M_current = 目前最好的狀態，每次 clone 來源是 M_current
        std::unique_ptr<Module> M_current = CloneModule(M);

        for (const auto &cand : candidates) {
            // (a) 從目前最佳狀態 clone
            std::unique_ptr<Module> M_comp = CloneModule(*M_current);

            // (b) 在 cloned module 中，用 callbase.id 找到對應的 CallBase，只把這一個設成 true
            Function *F_callee = M_comp->getFunction(cand.calleeName);
            if (!F_callee || F_callee->isDeclaration()) continue;

            bool found = false;
            for (Function &F_c : *M_comp) {
                for (BasicBlock &BB : F_c) {
                    for (Instruction &I : BB) {
                        auto *CB = dyn_cast<CallBase>(&I);
                        if (!CB) continue;
                        if (!hasCallBaseId(CB)) continue;
                        if (getCallBaseId(CB) == cand.id) {
                            setPassVal(CB, true);
                            found = true;
                            break;
                        }
                    }
                    if (found) break;
                }
                if (found) break;
            }
            if (!found) continue;

            // (c) 在 cloned module 上跑 MyPass + Oz
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
                MyFPM.run(*F_callee, FAM_c);

                ModulePassManager OzPipeline =
                    PB_c.buildPerModuleDefaultPipeline(OptimizationLevel::Oz);
                OzPipeline.run(*M_comp, MAM_c);
            }

            // (d) 量 size，跟 baseline 比較
            size_t sizeComp = estimateTextSize(*M_comp);
            if (sizeComp < sizeBaseline) {
                Func_inlined_id.push_back(cand.id);
                // Greedy: 更新 baseline 和 M_current，保留這次的改動
                sizeBaseline = sizeComp;
                // 在 M_current 上也標記這個 call site 為 true
                for (Function &F_c : *M_current) {
                    bool done = false;
                    for (BasicBlock &BB : F_c) {
                        for (Instruction &I : BB) {
                            auto *CB = dyn_cast<CallBase>(&I);
                            if (!CB) continue;
                            if (!hasCallBaseId(CB)) continue;
                            if (getCallBaseId(CB) == cand.id) {
                                setPassVal(CB, true);
                                done = true;
                                break;
                            }
                        }
                        if (done) break;
                    }
                    if (done) break;
                }
            }
        }

        // (e) 修改標籤回原 module
        for (const auto &id : Func_inlined_id) {
            for (Function &F : M) {
                bool done = false;
                for (BasicBlock &BB : F) {
                    for (Instruction &I : BB) {
                        auto *CB = dyn_cast<CallBase>(&I);
                        if (!CB) continue;
                        if (!hasCallBaseId(CB)) continue;
                        if (getCallBaseId(CB) == id) {
                            setPassVal(CB, true);
                            done = true;
                            break;
                        }
                    }
                    if (done) break;
                }
                if (done) break;
            }
        }
    }

    // (f) 寫入檔案
    ModulePassManager MyOut;
    MyOut.addPass(CallsiteInfoPass());
    MyOut.run(M, MAM);
    errs() << "Finished writeout\n";

    // (f) split 原本 module、後續opt
    ModulePassManager MySplit;
    FunctionPassManager MyFPM;
    MyFPM.addPass(MyPass());
    MySplit.addPass(createModuleToFunctionPassAdaptor(std::move(MyFPM)));
    MySplit.run(M, MAM);

    InsideOnePassPI = false;
    return PreservedAnalyses::none();

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
