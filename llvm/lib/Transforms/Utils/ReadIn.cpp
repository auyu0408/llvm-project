#include "llvm/Transforms/Utils/ReadIn.h"

#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace llvm;

static cl::opt<std::string> InputFilePath(
    "input-file",
    cl::desc("Path to the input file for decision."),
    cl::value_desc("filename"),
    cl::init(""));

PreservedAnalyses ReadInPass::run(Module &M, ModuleAnalysisManager &AM) {
    std::set<CallBase *> CBs;
    std::map<MDNode *, CallBase *> CBs_id;
    for(auto &F : M){
        for(auto &BB : F){
            for(auto &I : BB){
                auto *CB = dyn_cast<CallBase>(&I);
                if(!CB)
                    continue;
                // build MDNode, 要不要partial inline的初始值選不要
                auto &Ctx = M.getContext();
                unsigned MyMetaID = Ctx.getMDKindID("goPass");
                auto *N = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::getBool(
                                    Ctx, false)));// 常數bool

                // get Function/callbase
                CB->setMetadata(MyMetaID, N);

                //不需要紀錄間接函數調用，還有指標函數等，在給FunctionID的時候有做一樣的事情（但怕改壞原本的程式所以沒有放在同個Pass裡面）
                auto *CalledValue = CB -> getCalledOperand();
                auto *CalledFunction = CB -> getCalledFunction();
                if(CalledValue && !CalledFunction){
                    CalledValue = CalledValue -> stripPointerCasts();
                    // Stripping pointer casts can reveal a called function.
                    CalledFunction = dyn_cast<Function>(CalledValue);
                }
                // Check if this is an alias to a function. If so, get the
                // called aliasee for the checks below.
                if(auto *GA = dyn_cast<GlobalAlias>(CalledValue)){
                    assert(!CalledFunction && "Expected null called function in callsite for alias");
                    CalledFunction = dyn_cast<Function>(GA->getAliaseeObject());
                }
                if(CalledFunction){
                    CBs.insert(CB);
                    auto *CBID = CB->getMetadata("callbase.id");
                    CBs_id[CBID] = CB;
                }
            }
        }
    }

    // read decision file
    if(InputFilePath.empty()){
        //沒有提供input，全部inline？（可能修改）
        errs() << "No decision file.\n";
        return PreservedAnalyses::all();
    }

    std::ifstream infile(InputFilePath);
    if(!infile){
        errs() << "Failed to open file:" << InputFilePath << "\n";
        return PreservedAnalyses::all();
    }

    std::string line;
    while(std::getline(infile, line)){
        // line的形式 Caller,Callee,callbase.id,inline
        std::vector<std::string> arr;
        std::string::size_type begin, end;
        end = line.find(",");
        begin = 0;
        int cnt = 0;

        while(end != std::string::npos){
            if(end - begin != 0){
                arr.push_back(line.substr(begin, end-begin));
                cnt++;
            }
            begin = end + 1;
            end = line.find(",", begin);
        }
        arr.push_back(line.substr(begin, line.size()));
        cnt++;

        if(cnt == 3) // 如果只有 Caller,Callee,callbase.id 的話代表沒有決定要不要 inline
            continue;

        int id = std::stoi(arr[2]);
        auto &Ctx = M.getContext();
        auto temp_MDNode = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(
                        Ctx, APInt{64, id, false})));
        auto *CB = CBs_id[temp_MDNode];
        auto *NewMD = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt1Ty(
                                      Ctx), 0)));
        if(arr[3] == "inlined"){
            errs() << arr[0] << " " << arr[1] << "\n";
            NewMD = MDNode::get(Ctx, ConstantAsMetadata::get(ConstantInt::get(Type::getInt1Ty(
                                      Ctx), 1)));
        }
        CB->setMetadata("goPass", NewMD);
    }

    return PreservedAnalyses::all();
}