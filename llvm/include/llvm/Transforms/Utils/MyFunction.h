#pragma once

#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/BreadthFirstIterator.h" // 使用內建BFS來協助 fordFulkerson
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h" // EntryBlock.front
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h" // errs()
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"

#include <fstream> // 輸出到檔案
#include <limits.h> //INT_MAX
#include <queue>
#include <utility> // pair
#include <unordered_map>
#include <unordered_set> // reachable from source
#include <vector>

using namespace llvm;
#define NodeNo unsigned

namespace llvm{
    struct VectorHash{
        template<class T>
        std::size_t operator() (const std::vector<T>& vec) const{
            std::size_t ret = 0;
            for(auto i:vec){
                ret ^= std::hash<T>{}(i);
            }
            return ret;
        }
    };

    struct PairHash{
        template<class T1, class T2>
        std::size_t operator() (const std::pair<T1, T2>& p) const{
            auto h1 = std::hash<T1>{}(p.first);
            auto h2 = std::hash<T2>{}(p.second);
            return h1 ^ h2;
        }
    };

    struct FlowGraph{
        std::unordered_map<Value *, std::vector<Value *>> adjList; // 原本的圖
        FlowGraph(std::unordered_map<Value *, std::vector<Value *>>& G)
            : adjList(G){}
    };
    extern std::unordered_map<Value *, NodeNo> To_Node;
    extern std::unordered_map<NodeNo, std::vector<Value *>> To_Value;

    struct InstGraph{
        std::unordered_map<NodeNo, std::unordered_set<NodeNo>> adjList;
        std::unordered_map<std::pair<NodeNo, NodeNo>, int, PairHash> capacity;
        std::unordered_map<std::pair<NodeNo, NodeNo>, int, PairHash> flow;
        std::unordered_map<std::pair<NodeNo, NodeNo>,
                           std::vector<std::pair<Value *, Value *>>, PairHash>
            originalEdges;
        std::unordered_set<NodeNo> loopNodes;
        InstGraph(std::unordered_map<Value *, NodeNo> Node_map, std::unordered_map<Value *, std::vector<Value *>>& CFG,
            std::unordered_map<std::pair<Value *, Value *>, int, PairHash>& Cap);
    };

    template<> struct GraphTraits<FlowGraph>{
        using NodeRef = Value *;
        using ChildIteratorType = std::vector<Value *>::const_iterator;

        //不管是 getEntryNode, child_begin 和 child_end 都需要注意 map 到空 instruction 的部份（可能是尾端）
        static Value* getEntryNode(const FlowGraph &G){
            if(G.adjList.empty()) return nullptr;
            else{
                if(Instruction *I = dyn_cast<Instruction>(G.adjList.begin()->first)){
                    return &(I->getFunction()->getEntryBlock().front());
                }
                else return nullptr;
            }
            // G.adjList.begin()->first 可以拿到指令，看這個指令在哪個function並且該function的first inst是誰
        }

        static ChildIteratorType child_begin(NodeRef N){
            auto it = G->adjList.find(N);
            if(it == G->adjList.end()){
                static const std::vector<Value*> empty_vec;
                return empty_vec.begin();
            }
            return it->second.begin();
        }

        static ChildIteratorType child_end(NodeRef N){
            auto it = G->adjList.find(N);
            if(it == G->adjList.end()){
                static const std::vector<Value *> empty_vec;
                return empty_vec.begin();
            }
            return it->second.end();
        }

        static auto nodes_begin(const FlowGraph &G) { return G.adjList.begin(); }
        static auto nodes_end(const FlowGraph &G) { return G.adjList.end(); }

        static const FlowGraph* G;
    };

    extern const FlowGraph* G;
}//namespace llvm

extern cl::opt<std::string> InputFilePath;
bool hasPassVal(const CallBase *CB);
bool getPassVal(const CallBase *CB);
void setPassVal(CallBase *CB, bool val);
bool hasPartialInlineVal(const CallBase *CB);
bool getPartialInlineVal(const CallBase *CB);
void setPartialInlineVal(CallBase *CB, bool val);
size_t getCallBaseId(const CallBase *CB);
bool hasCallBaseId(const CallBase *CB);
int fordFulkerson(InstGraph& G, Value* source, Value* target,
                    std::unordered_set<NodeNo>& reachableFromSource);
Instruction *findBestSplitPoint(
    InstGraph &G,
    const std::unordered_set<NodeNo> &reachableFromSource,
    Function &F);
std::unordered_map<Value *, std::vector<Value *>> buildGraph(Function &F);
void addDependency(Value* src, Value* dest, int w, 
                    std::unordered_map<std::pair<Value *, Value *>, int, PairHash> &Cap);
//兩個pass會不一樣
std::vector<ReturnInst*> getAllReturnInsts(Function &F);
Instruction* getLatestReturn(Function &F, PostDominatorTree &PDT);
void mappingNode(std::vector<std::vector<Value *>> &SCCs, std::vector<std::vector<Value *>> &alone);
bool splitFunction(Instruction *cutI, Function &F, FunctionAnalysisManager &AM);
