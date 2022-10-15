

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
  const Stmt *cond = solveLoopStmt();

  assert(headBlock->succ_size() == 2);
  NodeBuilderContext Ctx(eng.getCoreEngine(), headBlock, preNode);
  ExplodedNodeSet Dst;

  CFGBlock *trueBlock = *(headBlock->succ_begin());
  CFGBlock *falseBlock = *(headBlock->succ_begin() + 1);

  assert((!cond || !isa<CXXBindTemporaryExpr>(cond)) &&
         "CXXBindTemporaryExprs are handled by processBindTemporary.");
  const LocationContext *LCtx = preNode->getLocationContext();
  PrettyStackTraceLocationContext StackCrashInfo(LCtx);

  if (!cond) {
    BranchNodeBuilder NullCondBldr(preNode, Dst, Ctx, trueBlock, falseBlock);
    NullCondBldr.markInfeasible(false);
    NullCondBldr.generateNode(preNode->getState(), true, preNode);
    PathState *truePathState = new PathState(headBlock, *Dst.end(), C);
    enqueue(*truePathState);
  }

  if (const Expr *Ex = dyn_cast<Expr>(cond))
    cond = Ex->IgnoreParens();

  cond = ResolveCondition(cond, Ctx.getBlock());
  PrettyStackTraceLoc CrashInfo(eng.getContext().getSourceManager(),
                                cond->getLocStart(), "Error evaluating branch");
  ExplodedNodeSet CheckersOutSet;
  eng.getCheckerManager().runCheckersForBranchCondition(cond, CheckersOutSet,
                                                        preNode, eng);
  if (CheckersOutSet.empty())
    return;

  BranchNodeBuilder builder(CheckersOutSet, Dst, Ctx, trueBlock, falseBlock);
  for (NodeBuilder::iterator I = CheckersOutSet.begin(),
                             E = CheckersOutSet.end();
       E != I; ++I) {
    ExplodedNode *PredI = *I;

    if (PredI->isSink())
      continue;

    ProgramStateRef PrevState = PredI->getState();
    SVal X = PrevState->getSVal(cond, PredI->getLocationContext());

    if (X.isUnknownOrUndef()) {
      // Give it a chance to recover from unknown.
      if (const Expr *Ex = dyn_cast<Expr>(cond)) {
        if (Ex->getType()->isIntegralOrEnumerationType()) {
          // Try to recover some path-sensitivity.  Right now casts of
          // symbolic integers that promote their values are currently not
          // tracked well. If 'Condition' is such an expression, try and
          // recover the underlying value and use that instead.
          SVal recovered = RecoverCastedSymbol(
              eng.getStateManager(), PrevState, cond,
              PredI->getLocationContext(), eng.getContext());

          if (!recovered.isUnknown()) {
            X = recovered;
          }
        }
      }
    }

    // If the condition is still unknown, give up.
    if (X.isUnknownOrUndef()) {

      builder.generateNode(PrevState, true, PredI);
      PathState *truePathState = new PathState(headBlock, *Dst.end(), C);
      enqueue(*truePathState);

      builder.generateNode(PrevState, false, PredI);
      PathState *falsePathState = new PathState(headBlock, *Dst.end(), C,
                                                *(headBlock->succ_begin() + 1));
      enqueue(*falsePathState);
      exitPateSate = new PathState(headBlock, *Dst.end(), C,
                                   *(headBlock->succ_begin() + 1));
      continue;
    }

    DefinedSVal V = X.castAs<DefinedSVal>();

    ProgramStateRef StTrue, StFalse;
    std::tie(StTrue, StFalse) = PrevState->assume(V);

    // Process the true branch.
    if (builder.isFeasible(true)) {
      if (StTrue)
        builder.generateNode(StTrue, true, PredI);
      else
        builder.markInfeasible(true);
    }

    // Process the false branch.
    if (builder.isFeasible(false)) {
      if (StFalse)
        builder.generateNode(StFalse, false, PredI);
      else
        builder.markInfeasible(false);
    }
  }
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