


#include <unordered_map>
#include <unordered_set>


#include "clang/Analysis/CFG.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"





namespace clang {

namespace ento {




//

class PathState{

  typedef BumpVector<CFGBlock*>  CFGBlockListTy;

  const CFGBlock *headBlock;
  const CFGBlock *tailBlock;

  ExplodedNode *preNode;
  ExplodedNode *curState;


  CFGBlockListTy path;
  


  BumpVectorContext BVC;

  public:

    PathState(const CFGBlock *block1, ExplodedNode* src, BumpVectorContext &C, CFGBlock* block2 = nullptr)
      :headBlock(block1), tailBlock(block2), preNode(src), curState(src), path(C, 4), BVC(C) {
        path.push_back(const_cast<CFGBlock*>(headBlock), C);
      }

    void updatePS(ExplodedNode *dst, CFGBlock* block) {
      assert(block != headBlock && "path should end");
      curState = dst;
      path.push_back(block, BVC);
    }

    const CFGBlock* getHeadBlock() {
      return headBlock;
    }

    void SetTailBlock(CFGBlock* block) {
      tailBlock = block;
    }

    const CFGBlock* getTailBlock() {
      return tailBlock;
    }




  
    //TODO
    void dumpCfg() {

    }
};

class PathStateWList{

  SmallVector<PathState,20> Stack;

  public:
    PathStateWList(ExplodedNode *node, CFGBlock *block, BumpVectorContext &C){
      Stack.push_back(PathState(block, node, C));
    }

    void enqueue(PathState pathState){
      Stack.push_back(pathState);
    }

    PathState dequeue(){
          assert (!Stack.empty());
          const PathState& U = Stack.back();
          Stack.pop_back(); // This technically "invalidates" U, but we are fine.
          return U;          
    }

    bool hasWork(){
      return !Stack.empty();
    }


};


class SymFunSummary {

  ExprEngine& eng;
  Decl *funDecl;

  LocationContext *stackLocationContext;

public:

  class LoopSummary {

    ExprEngine &eng;

    const Decl *funDecl;
    const Stmt *loopStmt;

    //循环路径（状态）
    PathState *initPathState; 
    std::unordered_set<PathState*> pathStateSet;
    std::unordered_set<PathState*> termPathStateSet;
    PathState* exitPateSate;


    

    //循环头部head
    const CFGBlock *headBlock;

    //循环退出块Exit
    const CFGBlock *exitBlock;

    //循环前状态
    ExplodedNode *preNode;

    //循环工作列表
    std::unique_ptr<PathStateWList> WList;

    BumpVectorContext &C;


  public:
    LoopSummary(const Decl *decl, const Stmt *stmt, const CFGBlock *block,
                ExplodedNode *pred, ExprEngine& engine, BumpVectorContext &C1)
        : eng(engine), funDecl(decl->getAsFunction()), loopStmt(stmt), headBlock(block),
          exitBlock(*(headBlock->succ_begin() + 1)), preNode(pred), C(C1) {
            initPathState = new PathState(block, pred, C);
          }

    const FunctionDecl *getFunctionDecl() { return funDecl->getAsFunction(); }

    ExplodedNode *getPreNode() { return preNode; }

    const CFGBlock *getHeadBlock() { return headBlock; }

    const CFGBlock *getExitBlock() { return exitBlock; }

    void enqueue(PathState &pathState) {
         WList->enqueue(pathState);
      
    }

    //处理循环Stmt
    const Stmt* solveLoopStmt();

    //循环路径状态分类
    void genPathState();
  
  
  };
private:
  //函数体循环摘要map
  std::unordered_map<Stmt *, LoopSummary *> loopSummaryMap;
  BumpVectorContext& C;

public:
  //构造函数
  SymFunSummary(ExprEngine &engine, Decl *decl,
                LocationContext *locationContext, BumpVectorContext& C1)
      : eng(engine), funDecl(decl->getAsFunction()),stackLocationContext(locationContext),
      C(C1){}

  //判断函数体某个循环摘要是否总结
  bool isLoopSummary(Stmt *stmt) { return loopSummaryMap.count(stmt); }

  //创建循环摘要
  LoopSummary *addLoopSummary(Stmt *stmt, CFGBlock *block, ExplodedNode *pred) {
    assert(!isLoopSummary(stmt));
    LoopSummary *loopStmt = new LoopSummary(funDecl, stmt, block, pred, eng, C);
    //TODO开始进行循环摘要生成

    loopSummaryMap.insert(std::pair<Stmt *, LoopSummary *>(stmt, loopStmt));
    return loopStmt;
  }
};



// 符号化摘要管理器
class SymFunSummayManange {

  ExprEngine &eng;

  LocationContext *stackLocationContext;

  BumpVectorContext C = BumpVectorContext();

  //符号化函数摘要map
  std::unordered_map<FunctionDecl *, SymFunSummary *> funSummaryMap;

public:
  SymFunSummayManange(ExprEngine &engine, LocationContext *locationContext)
      : eng(engine), stackLocationContext(locationContext){};

  //得到函数摘要
  SymFunSummary *getSymFunSummary(Decl *decl) {
    assert(isFunSummary(decl) && "this function has not funSummary");
    FunctionDecl *funDecl = decl->getAsFunction();
    return funSummaryMap[funDecl];
  }

  //创建初始化函数摘要
  SymFunSummary *addFunSummay(Decl *decl) {
    SymFunSummary *symFunSummary =
        new SymFunSummary(eng, decl, stackLocationContext, C);
    FunctionDecl *funDecl = decl->getAsFunction();
    funSummaryMap.insert(
        std::pair<FunctionDecl *, SymFunSummary *>(funDecl, symFunSummary));
    return symFunSummary;
  }

  //是否有符号化函数摘要
  bool isFunSummary(Decl *decl) {
    FunctionDecl *funDecl = decl->getAsFunction();
    if (funSummaryMap.count(funDecl)) {
      return true;
    }
    return false;
  }

  //函数体内某循环摘要是否总结
  bool isLoopSummary(Decl *decl, Stmt *loopStmt) {
    FunctionDecl *funDecl = decl->getAsFunction();
    return isFunSummary(decl) ||
           funSummaryMap[funDecl]->isLoopSummary(loopStmt);
  }
};



//ExprEngine file






}; // namespace ento
}; // namespace clang
