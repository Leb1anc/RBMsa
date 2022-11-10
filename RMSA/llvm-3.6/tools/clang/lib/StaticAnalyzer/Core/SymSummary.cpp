

#include "clang/StaticAnalyzer/Core/PathSensitive/SymSummary.h"

namespace clang {

namespace ento {

static const Stmt *getRightmostLeaf(const Stmt *Condition);
static const Stmt *ResolveCondition(const Stmt *Condition, const CFGBlock *B);  
static SVal RecoverCastedSymbol(ProgramStateManager &StateMgr,
                                ProgramStateRef state, const Stmt *Condition,
                                const LocationContext *LCtx, ASTContext &Ctx);
                              


//SymFunSummary::LoopSummary 各类函数实现

const Stmt *SymFunSummary::LoopSummary::solveLoopStmt() {
  switch (loopStmt->getStmtClass()) {
  default:
    llvm_unreachable("Analysis for this LoopStmt not implemented.");
  case Stmt::ForStmtClass:
    return cast<ForStmt>(loopStmt)->getCond();
  case Stmt::WhileStmtClass:
    return cast<WhileStmt>(loopStmt)->getCond();
  case Stmt::DoStmtClass:
    return cast<DoStmt>(loopStmt)->getCond();
  }
}

void SymFunSummary::LoopSummary::genPathState() {
  
}

















// ExprEngine.cpp

static const Stmt *getRightmostLeaf(const Stmt *Condition) {
  while (Condition) {
    const BinaryOperator *BO = dyn_cast<BinaryOperator>(Condition);
    if (!BO || !BO->isLogicalOp()) {
      return Condition;
    }
    Condition = BO->getRHS()->IgnoreParens();
  }
  return nullptr;
}
static const Stmt *ResolveCondition(const Stmt *Condition, const CFGBlock *B) {
  if (const Expr *Ex = dyn_cast<Expr>(Condition))
    Condition = Ex->IgnoreParens();

  const BinaryOperator *BO = dyn_cast<BinaryOperator>(Condition);
  if (!BO || !BO->isLogicalOp())
    return Condition;

  assert(!B->getTerminator().isTemporaryDtorsBranch() &&
         "Temporary destructor branches handled by processBindTemporary.");

  // For logical operations, we still have the case where some branches
  // use the traditional "merge" approach and others sink the branch
  // directly into the basic blocks representing the logical operation.
  // We need to distinguish between those two cases here.

  // The invariants are still shifting, but it is possible that the
  // last element in a CFGBlock is not a CFGStmt.  Look for the last
  // CFGStmt as the value of the condition.
  CFGBlock::const_reverse_iterator I = B->rbegin(), E = B->rend();
  for (; I != E; ++I) {
    CFGElement Elem = *I;
    Optional<CFGStmt> CS = Elem.getAs<CFGStmt>();
    if (!CS)
      continue;
    const Stmt *LastStmt = CS->getStmt();
    assert(LastStmt == Condition || LastStmt == getRightmostLeaf(Condition));
    return LastStmt;
  }
  llvm_unreachable("could not resolve condition");
}

static SVal RecoverCastedSymbol(ProgramStateManager &StateMgr,
                                ProgramStateRef state, const Stmt *Condition,
                                const LocationContext *LCtx, ASTContext &Ctx) {

  const Expr *Ex = dyn_cast<Expr>(Condition);
  if (!Ex)
    return UnknownVal();

  uint64_t bits = 0;
  bool bitsInit = false;

  while (const CastExpr *CE = dyn_cast<CastExpr>(Ex)) {
    QualType T = CE->getType();

    if (!T->isIntegralOrEnumerationType())
      return UnknownVal();

    uint64_t newBits = Ctx.getTypeSize(T);
    if (!bitsInit || newBits < bits) {
      bitsInit = true;
      bits = newBits;
    }

    Ex = CE->getSubExpr();
  }

  // We reached a non-cast.  Is it a symbolic value?
  QualType T = Ex->getType();

  if (!bitsInit || !T->isIntegralOrEnumerationType() ||
      Ctx.getTypeSize(T) > bits)
    return UnknownVal();

  return state->getSVal(Ex, LCtx);
}
}; // namespace ento
}; // namespace clang