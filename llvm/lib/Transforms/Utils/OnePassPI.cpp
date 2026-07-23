#include "llvm/Transforms/Utils/OnePassPI.h"
#include "llvm/Transforms/Utils/MyFunction.h"
#include "llvm/Transforms/IPO/SCCP.h"
#include "llvm/Transforms/IPO/DeadArgumentElimination.h"

#include <csignal>
#include <cstdlib>
#include <fstream>
#include <string>

using namespace llvm;

// ── Signal‑safe snapshot of in‑progress tuning results ──────────────────
namespace {
struct TuningSnapshot {
    Module *M = nullptr;                        // 原始 module（唯讀）
    SmallVector<size_t, 16> AcceptedIDs;         // 到目前為止被 greedy 接受的 call‑site IDs
    bool Active = false;                         // 是否正在 tuning loop 中
};
static TuningSnapshot GSnapshot;

/// 把目前已經接受的 partial‑inline 決策寫到 RECORD_PARTIAL_INLINE 指定的檔案
static void dumpCurrentResults() {
    if (!GSnapshot.Active || !GSnapshot.M)
        return;

    const char *RecordFileName = std::getenv("RECORD_PARTIAL_INLINE");
    if (!RecordFileName)
        return;

    // 收集目前被接受的 id set，方便查詢
    DenseSet<size_t> Accepted;
    for (size_t id : GSnapshot.AcceptedIDs)
        Accepted.insert(id);

    std::string RecordStr;
    raw_string_ostream RecordOS(RecordStr);
    for (Function &F : *GSnapshot.M) {
        for (BasicBlock &BB : F) {
            for (Instruction &I : BB) {
                auto *CB = dyn_cast<CallBase>(&I);
                if (!CB) continue;
                if (!hasCallBaseId(CB)) continue;
                Function *Callee = CB->getCalledFunction();
                if (!Callee || Callee->isDeclaration()) continue;
                if (Callee->isIntrinsic()) continue;
                size_t id = getCallBaseId(CB);
                bool pi = Accepted.count(id);
                F.printAsOperand(RecordOS, false);
                RecordOS << ",";
                Callee->printAsOperand(RecordOS, false);
                RecordOS << ',' << id << ','
                         << (pi ? "inlined" : "not_inlined") << '\n';
            }
        }
    }

    // 加上 ".partial" 後綴表示這是被中斷的不完整結果
    std::string PartialName = std::string(RecordFileName) + ".partial";
    std::error_code EC;
    raw_fd_ostream FStream(PartialName, EC);
    if (!EC)
        FStream << RecordOS.str();
    errs() << "[Signal] Dumped partial tuning results (" 
           << GSnapshot.AcceptedIDs.size() << " accepted) to " 
           << PartialName << "\n";
}

static void signalHandler(int Sig) {
    dumpCurrentResults();
    // 恢復預設 handler 並重新發送 signal，讓程式以正常的 exit code 結束
    std::signal(Sig, SIG_DFL);
    std::raise(Sig);
}
} 
//──────────────────

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

/// Helper: 為一個獨立的 Module 建立完整的 analysis manager 並跑完整 Oz pipeline，
/// 回傳 estimated text size。
/// buildPerModuleDefaultPipeline 會經過 buildModuleOptimizationPipeline，
/// 其中因為 cl::opt RunMyCustomPartialInlining 為 true 會再次加入 OnePassPIPass，
/// 但 InsideOnePassPI guard 會讓遞迴呼叫直接返回。
static size_t ModuleOpt(Module &M) {
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

    // 跑完剩下的 Oz pipeline
    ModulePassManager MPM =
        PB.buildModuleOptimizationPipeline(OptimizationLevel::Oz, ThinOrFullLTOPhase::None);
    MPM.run(M, MAM_local);

    return estimateTextSize(M);
}

// Guard: 防止遞迴呼叫。fullOpt 會經過 buildModuleOptimizationPipeline
// 會因 cl::opt RunMyCustomPartialInlining 為 true 而再次加入 OnePassPIPass
// 此 guard 確保遞迴呼叫直接返回。
static bool InsideOnePassPI = false;

PreservedAnalyses OnePassPIPass::run(Module &M, ModuleAnalysisManager &MAM){
    // Re-entrance guard
    if (InsideOnePassPI)
        return PreservedAnalyses::all();
    InsideOnePassPI = true;

    // 1. 讀檔案
    // decision 檔會跟 .o 放在同一個工作目錄
    if (InputFilePath.empty()) {
        StringRef ModId = M.getModuleIdentifier();
        std::string BaseName = sys::path::filename(ModId).str();
        std::replace(BaseName.begin(), BaseName.end(), '.', '_');
        InputFilePath = BaseName + ".partial.decision";
    }
    
    // read decision file
    ModulePassManager MyRead;
    MyRead.addPass(ReadInPass());
    MyRead.run(M, MAM);

    {
        // 2. baseline: clone → 完整 Oz → 量 size
        // MyPass() 在沒有任何 goPartialInline=true 的 call site 時會直接 return PreservedAnalyses::all()，不做任何 CFG 改動，
        std::unique_ptr<Module> M_baseline = CloneModule(M);
        size_t sizeBaseline = ModuleOpt(*M_baseline);

        // 3. 收集所有 candidate call sites（有 callbase.id 且 goPartialInline == false）
        struct Candidate {
            size_t id;
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
                        // 已經在 Inliner 之後，被 inline 的 call sites 已不存在
                        // 只跳過已經標記為 partial inline 的
                        if (hasPartialInlineVal(CB) && getPartialInlineVal(CB)) continue;
                        if (!Callee || Callee->isDeclaration()) continue;
                        candidates.push_back({getCallBaseId(CB)});
                    }
                }
            }
        }

        SmallVector<size_t, 16> Func_inlined_id;

        // ── 設定 signal handler，讓中斷時也能輸出當前結果 ──
        GSnapshot.M = &M;
        GSnapshot.AcceptedIDs.clear();
        GSnapshot.Active = true;
        auto PrevSIGINT  = std::signal(SIGINT,  signalHandler);
        auto PrevSIGTERM = std::signal(SIGTERM, signalHandler);

        // 4. Greedy: 維護一個累積的 module，成功的改動會帶到下一個 candidate
        //    M_current = 目前最好的狀態，每次 clone 來源是 M_current
        std::unique_ptr<Module> M_current = CloneModule(M);

        for (const auto &cand : candidates) {
            // (a) 從目前最佳狀態 clone
            std::unique_ptr<Module> M_comp = CloneModule(*M_current);

            // (b) 在 cloned module 中，用 callbase.id 找到對應的 CallBase，只把這一個設成 true

            bool found = false;
            Function *F_callee = nullptr;
            for (Function &F_c : *M_comp) {
                for (BasicBlock &BB : F_c) {
                    for (Instruction &I : BB) {
                        auto *CB = dyn_cast<CallBase>(&I);
                        if (!CB) continue;
                        if (!hasCallBaseId(CB)) continue;
                        if (getCallBaseId(CB) == cand.id) {
                            F_callee = CB->getCalledFunction();
                            if (!F_callee || F_callee->isDeclaration()) break;
                            setPartialInlineVal(CB, true);
                            found = true;
                            break;
                        }
                    }
                    if (found) break;
                }
                if (found) break;
            }
            if (!found) continue;

            // (c) 在 cloned module 上跑 MyPass + 完整 Oz pipeline
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

                // 先做 function splitting
                FunctionPassManager MyFPM;
                MyFPM.addPass(MyPass());
                MyFPM.run(*F_callee, FAM_c);

                // Simplification → Optimization
                ModulePassManager MPM_c;
                MPM_c.addPass(IPSCCPPass());
                MPM_c.addPass(DeadArgumentEliminationPass());

                MPM_c.addPass(createModuleToFunctionPassAdaptor(
                    PB_c.buildFunctionSimplificationPipeline(
                        OptimizationLevel::Oz, ThinOrFullLTOPhase::None)));
                // InsideOnePassPI guard 會阻止遞迴
                MPM_c.addPass(std::move(
                    PB_c.buildModuleOptimizationPipeline(
                        OptimizationLevel::Oz, ThinOrFullLTOPhase::None)));
                MPM_c.run(*M_comp, MAM_c);
            }

            // (d) 量 size，跟 baseline 比較
            size_t sizeComp = estimateTextSize(*M_comp);
            errs() << "sizeBaseline = " << sizeBaseline << ", sizeComp = " << sizeComp << "\n";
            if (sizeComp < sizeBaseline) {
                Func_inlined_id.push_back(cand.id);
                GSnapshot.AcceptedIDs.push_back(cand.id);  // 同步更新 snapshot
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
                                setPartialInlineVal(CB, true);
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
                            setPartialInlineVal(CB, true);
                            done = true;
                            break;
                        }
                    }
                    if (done) break;
                }
                if (done) break;
            }
        }

        // ── 還原 signal handler ──
        GSnapshot.Active = false;
        std::signal(SIGINT,  PrevSIGINT);
        std::signal(SIGTERM, PrevSIGTERM);
    }

    // (f) 寫入決策檔
    bool anyChange = false; // 標記是否真的有 partial inline 發生
    const char *EnvRecord = std::getenv("RECORD_PARTIAL_INLINE");
    std::string RecordFileName;
    if (EnvRecord && EnvRecord[0] != '\0') {
        RecordFileName = EnvRecord;
    } else {
        StringRef ModId = M.getModuleIdentifier();
        std::string BaseName = sys::path::filename(ModId).str();
        std::replace(BaseName.begin(), BaseName.end(), '.', '_');
        RecordFileName = BaseName + ".p_decision";
    }
    if (!RecordFileName.empty()) {
        std::string RecordStr;
        raw_string_ostream RecordOS(RecordStr);
        for (Function &F : M) {
            for (BasicBlock &BB : F) {
                for (Instruction &I : BB) {
                    auto *CB = dyn_cast<CallBase>(&I);
                    if (!CB) continue;
                    if (!hasCallBaseId(CB)) continue;
                    Function *Callee = CB->getCalledFunction();
                    if (!Callee || Callee->isDeclaration()) continue;
                    if (Callee->isIntrinsic()) continue;
                    size_t id = getCallBaseId(CB);
                    bool pi = hasPartialInlineVal(CB) && getPartialInlineVal(CB);
                    F.printAsOperand(RecordOS, false);
                    RecordOS << ",";
                    Callee->printAsOperand(RecordOS, false);
                    RecordOS << ',' << id << ','
                             << (pi ? "inlined" : "not_inlined") << '\n';
                    if(pi) anyChange = true;
                }
            }
        }
        std::error_code EC;
        raw_fd_ostream FStream(RecordFileName, EC);
        if (!EC)
            FStream << RecordOS.str();
        else
            errs() << "Warning: Could not open " << RecordFileName
                   << " (" << EC.message() << ")\n";
    }

    // (g) final split
    ModulePassManager MySplit;
    FunctionPassManager MyFPM;
    MyFPM.addPass(MyPass());
    MySplit.addPass(createModuleToFunctionPassAdaptor(std::move(MyFPM)));
    MySplit.run(M, MAM);

    InsideOnePassPI = false;
    // 執行function simplification
    if(anyChange){
        LoopAnalysisManager   LAM_cu;
        FunctionAnalysisManager FAM_cu;
        CGSCCAnalysisManager  CGAM_cu;
        ModuleAnalysisManager MAM_cu;
        PassBuilder PB_cu;
        PB_cu.registerModuleAnalyses(MAM_cu);
        PB_cu.registerCGSCCAnalyses(CGAM_cu);
        PB_cu.registerFunctionAnalyses(FAM_cu);
        PB_cu.registerLoopAnalyses(LAM_cu);
        PB_cu.crossRegisterProxies(LAM_cu, FAM_cu, CGAM_cu, MAM_cu);

        ModulePassManager CleanUpMPM;
        CleanUpMPM.addPass(IPSCCPPass());
        CleanUpMPM.addPass(DeadArgumentEliminationPass());

        CleanUpMPM.addPass(createModuleToFunctionPassAdaptor(
            PB_cu.buildFunctionSimplificationPipeline(
                OptimizationLevel::Oz, ThinOrFullLTOPhase::None)));
        CleanUpMPM.run(M, MAM_cu);

        return PreservedAnalyses::none();
    }

    return PreservedAnalyses::all(); // 沒有任何 split 發生，回傳 all() 避免不必要的 analysis 失效

}


void registerMyPass(PassBuilder &PB) {
    PB.registerPipelineStartEPCallback(
        [](ModulePassManager &MPM, OptimizationLevel Level) {
            MPM.addPass(llvm::OnePassPIPass());
        });
}