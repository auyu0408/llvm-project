#include "llvm/Transforms/Utils/OnePassPI.h"
#include "llvm/Transforms/Utils/MyFunction.h"
#include "llvm/Transforms/Instrumentation/FunctionID.h"
#include "llvm/Transforms/IPO/DeadArgumentElimination.h"
#include "llvm/Transforms/IPO/GlobalDCE.h"
#include "llvm/Transforms/IPO/GlobalOpt.h"
#include "llvm/Transforms/IPO/MergeFunctions.h"
#include "llvm/Transforms/IPO/SCCP.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Support/FileSystem.h"

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

    // Parse every section classified as executable text by LLVM's object-file
    // abstraction. This includes target/object-format-specific text subsections
    // such as ELF .text.foo, rather than only a section named exactly ".text".
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
        if (Sec.isText() && !Sec.isVirtual())
            textSize += Sec.getSize();
    }
    return textSize;
}

/// Add the common size-optimization pipeline used after partial inlining.
/// The initial baseline intentionally uses only LLVM's standard Oz tail; every
/// materialized partial-inlining candidate uses this complete treatment.
static void addSizeOptimizationPipeline(ModulePassManager &MPM,
                                        PassBuilder &PB) {
    MPM.addPass(IPSCCPPass());

    FunctionPassManager FPM;
    FPM.addPass(SimplifyCFGPass());
    FPM.addPass(InstCombinePass());
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));

    MPM.addPass(DeadArgumentEliminationPass());
    MPM.addPass(GlobalOptPass());
    MPM.addPass(GlobalDCEPass());

    // Run the complete Oz pipeline after the targeted post-PI cleanup. The
    // InsideOnePassPI guard prevents this nested pipeline from tuning again.
    MPM.addPass(PB.buildModuleOptimizationPipeline(
        OptimizationLevel::Oz, ThinOrFullLTOPhase::None));

    // Oz may make independently outlined functions identical. Merge them only
    // after the complete pipeline has exposed those equivalences, then remove
    // functions/aliases made dead by the merge.
    MPM.addPass(MergeFunctionsPass());
    MPM.addPass(GlobalDCEPass());
}

/// Build the standard LLVM Oz module-optimization tail and measure its text
/// size. This is intentionally used only for the initial baseline: the
/// experiment compares LLVM Oz against the complete proposed treatment
/// (partial inlining plus its post-PI cleanup pipeline).
/// buildPerModuleDefaultPipeline 會經過 buildModuleOptimizationPipeline，
/// 其中因為 cl::opt RunMyCustomPartialInlining 為 true 會再次加入 OnePassPIPass，
/// 但 InsideOnePassPI guard 會讓遞迴呼叫直接返回。
static size_t measureOzBaseline(Module &M) {
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

    ModulePassManager MPM = PB.buildModuleOptimizationPipeline(
        OptimizationLevel::Oz, ThinOrFullLTOPhase::None);
    MPM.run(M, MAM_local);

    return estimateTextSize(M);
}

// Guard: 防止遞迴呼叫。fullOpt 會經過 buildModuleOptimizationPipeline
// 會因 cl::opt RunMyCustomPartialInlining 為 true 而再次加入 OnePassPIPass
// 此 guard 確保遞迴呼叫直接返回。
static bool InsideOnePassPI = false;

/// Materialize every marked partial-inlining decision on \p M and verify the
/// complete module. This is used transactionally on clones before a tuning
/// candidate is measured and before accepted decisions are applied to the real
/// module.
static bool materializeAndVerify(Module &M, bool RunCleanup) {
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager CGAM;
    ModuleAnalysisManager MAM;

    PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    FunctionPassManager FPM;
    FPM.addPass(MyPass());
    ModulePassManager SplitMPM;
    SplitMPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
    SplitMPM.run(M, MAM);

    if (verifyModule(M, &errs())) {
        return false;
    }

    if (RunCleanup) {
        ModulePassManager CleanupMPM;
        addSizeOptimizationPipeline(CleanupMPM, PB);
        CleanupMPM.run(M, MAM);

        if (verifyModule(M, &errs())) {
            return false;
        }
    }
    return true;
}

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
    
    // 清除舊的 callbase.id metadata，重新分配
    for (Function &F : M)
        for (BasicBlock &BB : F)
            for (Instruction &I : BB)
                if (auto *CB = dyn_cast<CallBase>(&I))
                    CB->setMetadata("callbase.id", nullptr);

    // 跑 FunctionIDPass 重新賦予 callbase.id
    ModulePassManager MyIDPM;
    MyIDPM.addPass(FunctionIDPass());
    MyIDPM.run(M, MAM);

    // read decision file
    ModulePassManager MyRead;
    MyRead.addPass(ReadInPass());
    MyRead.run(M, MAM);


    {
        // 2. Initial baseline: clone → standard LLVM Oz optimization tail
        // → measure. Do not run the proposed post-PI cleanup pipeline here;
        // candidates represent the complete PI+cleanup treatment versus Oz.
        // MyPass() 在沒有任何 goPartialInline=true 的 call site 時會直接 return PreservedAnalyses::all()，不做任何 CFG 改動，
        std::unique_ptr<Module> M_baseline = CloneModule(M);
        size_t sizeBaseline = measureOzBaseline(*M_baseline);

        // 3. 收集 candidate call sites，以 callee function 為單位分組。
        //    candidates 保留 callee 第一次出現在 module/BB/instruction traversal
        //    中的順序；DenseMap 只用來查詢既有 candidate 的 index。
        struct FuncCandidate {
            Function *Callee;                    // 原 module 中的 callee 指標
            SmallVector<size_t, 4> ids;           // 該 callee 的所有 call site id
        };
        SmallVector<FuncCandidate, 16> candidates;
        DenseMap<Function*, size_t> CalleeToCandidateIndex;
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
                        if (hasPartialInlineVal(CB) && getPartialInlineVal(CB)) continue;
                        if (!Callee || Callee->isDeclaration()) continue;
                        auto [It, Inserted] = CalleeToCandidateIndex.try_emplace(
                            Callee, candidates.size());
                        if (Inserted)
                            candidates.push_back({Callee, {}});
                        candidates[It->second].ids.push_back(getCallBaseId(CB));
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

        // 4. Greedy: 以 callee function 為單位
        std::unique_ptr<Module> M_current = CloneModule(M);

        for (const auto &cand : candidates) {
            // (a) 從目前最佳狀態 clone
            std::unique_ptr<Module> M_comp = CloneModule(*M_current);

            // (b) 在 cloned module 中，把該 callee 的所有 call site 都標記為 true
            DenseSet<size_t> candIdSet(cand.ids.begin(), cand.ids.end());
            int markCount = 0;
            for (Function &F_c : *M_comp) {
                for (BasicBlock &BB : F_c) {
                    for (Instruction &I : BB) {
                        auto *CB = dyn_cast<CallBase>(&I);
                        if (!CB) continue;
                        if (!hasCallBaseId(CB)) continue;
                        if (candIdSet.count(getCallBaseId(CB))) {
                            Function *Callee = CB->getCalledFunction();
                            if (!Callee || Callee->isDeclaration())
                                continue;
                            setPartialInlineVal(CB, true);
                            markCount++;
                        }
                    }
                }
            }
            if (markCount == 0) continue;

            // (c) Transactionally materialize all accepted decisions plus the
            // current candidate on the clone. A verifier failure rejects this
            // candidate before optimization or size comparison.
            if (!materializeAndVerify(*M_comp, /*RunCleanup=*/true))
                continue;

            // (d) 量 size，跟 baseline 比較
            size_t sizeComp = estimateTextSize(*M_comp);
            if (sizeComp < sizeBaseline) {
                // 接受該 callee 的所有 call site
                for (size_t id : cand.ids) {
                    Func_inlined_id.push_back(id);
                    GSnapshot.AcceptedIDs.push_back(id);
                }
                sizeBaseline = sizeComp;
                // 在 M_current 上也標記這些 call site 為 true
                for (Function &F_c : *M_current) {
                    for (BasicBlock &BB : F_c) {
                        for (Instruction &I : BB) {
                            auto *CB = dyn_cast<CallBase>(&I);
                            if (!CB) continue;
                            if (!hasCallBaseId(CB)) continue;
                            if (candIdSet.count(getCallBaseId(CB))) {
                                setPartialInlineVal(CB, true);
                            }
                        }
                    }
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

        // ── 統計摘要 ──
        {
            int totalFunctions = 0;
            for (Function &F : M)
                if (!F.isDeclaration())
                    totalFunctions++;

            std::error_code EC;
            raw_fd_ostream DbgOS("onepasspi_stats.log", EC, sys::fs::OF_Append);
            if (!EC) {
                DbgOS << M.getModuleIdentifier()
                       << ",functions=" << totalFunctions
                       << ",candidates=" << candidates.size()
                       << ",inlined=" << Func_inlined_id.size() << "\n";
            }
        }
    }

    // Validate the complete accepted set on a disposable clone before writing
    // decisions or mutating the real module. A failure therefore rolls back by
    // discarding the clone and aborting final materialization.
    bool anyChange = false;
    for (Function &F : M)
        for (BasicBlock &BB : F)
            for (Instruction &I : BB)
                if (auto *CB = dyn_cast<CallBase>(&I))
                    anyChange |= hasPartialInlineVal(CB) &&
                                 getPartialInlineVal(CB);

    if (anyChange) {
        std::unique_ptr<Module> FinalCheck = CloneModule(M);
        if (!materializeAndVerify(*FinalCheck, /*RunCleanup=*/true)) {
            InsideOnePassPI = false;
            return PreservedAnalyses::none();
        }
    }

    // (f) 寫入決策檔
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

    // (g) The same verified procedure is now safe to apply to the real module.
    // Verification is repeated after materialization and after cleanup.
    if (anyChange) {
        bool FinalValid = materializeAndVerify(M, /*RunCleanup=*/true);
        InsideOnePassPI = false;
        if (!FinalValid) {
            errs() << "Unexpected final partial-inlining verification failure "
                      "after successful transactional preflight.\n";
        }
        return PreservedAnalyses::none();
    }

    InsideOnePassPI = false;
    return PreservedAnalyses::all(); // 沒有任何 split 發生，回傳 all() 避免不必要的 analysis 失效

}


void registerMyPass(PassBuilder &PB) {
    PB.registerPipelineStartEPCallback(
        [](ModulePassManager &MPM, OptimizationLevel Level) {
            MPM.addPass(llvm::OnePassPIPass());
        });
}
