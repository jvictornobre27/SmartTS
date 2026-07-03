module SmartTS.CodeGen.CompileLLTZ where

import qualified SmartTS.IR.AST as A
import qualified SmartTS.IR.LLTZ as L

translateType :: A.Type -> L.Type
translateType A.TInt             = L.TInt
translateType A.TBool            = L.TBool
translateType A.TUnit            = L.TUnit
translateType A.TNever           = L.TNever
translateType (A.TRecord fields) = L.TTuple (L.RowNode (map toLeaf fields))
  where
    toLeaf (name, ty) = L.RowLeaf (Just (L.Label name)) (translateType ty)

-- Basic Expressions
translateExpression :: A.TypedExpr -> L.Expr
translateExpression (A.CInt  ty value) = mkExpr (L.Const (L.CInt value)) ty
translateExpression (A.CBool ty value) = mkExpr (L.Const (L.CBool value)) ty
translateExpression (A.Var   ty name)  = mkExpr (L.Variable (L.Var name)) ty
-- Boolean Expressions
translateExpression (A.And ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimAnd
translateExpression (A.Or  ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimOr
translateExpression (A.Not ty e)     = translateUnaryExpression e ty L.PrimNot
-- TODO: Write here the translation of the remaining expressions.

translateExpression (A.FailWith ty payload) = mkExpr (L.Prim L.PrimFailwith [payload']) ty
  where payload' = translateExpression payload

-- | Translate a SmartTS block (a list of statements) into a nested LLTZ let-expression.
--
-- LLTZ is an expression-based language derived from the Lambda calculus.
-- A statement sequence is encoded as a chain of LetIn / LetMutIn nodes where
-- each binding carries the rest of the block as its continuation.  The type of
-- the whole chain is propagated from the innermost expression, so a block that
-- ends in a ReturnStmt carries the return type all the way to the top.
--
-- TODO: Reason about the effect of 'return statements'
translateBlock :: [A.TypedStmt] -> L.Expr
translateBlock [] = L.Expr L.Skip L.TUnit
translateBlock (s:ss) =
  case s of
    (A.VarDeclStmt name _ty expr) -> L.Expr (L.LetMutIn (L.MutVar name) (translateExpression expr) block) ty
    (A.ValDeclStmt name _ty expr) -> L.Expr (L.LetIn    (L.Var  name)   (translateExpression expr) block) ty
    -- For effectful statements whose value is not bound, we sequence them by
    -- discarding the result via a wildcard binding.
    _                             -> L.Expr (L.LetIn (L.Var "_") (translateStatement s) block) ty
  where
    block = translateBlock ss
    ty    = L.exprType block

-- | Translate a single SmartTS statement into an LLTZ expression.
translateStatement :: A.TypedStmt -> L.Expr
-- Translate the variable assignment statement.
-- TODO: Deal with the remaining LValues (storage and record field).
translateStatement (A.AssignmentStmt (A.LVar name) expr) =
  L.Expr (L.Assign (L.MutVar name) (translateExpression expr)) L.TUnit
-- Translate the if-then-else statement.
translateStatement (A.IfStmt cond s1 (Just s2)) =
  let cond' = translateExpression cond
      s1'   = translateStatement s1
      s2'   = translateStatement s2
  in
    -- Branch type equality is guaranteed by the type checker; the assert
    -- is a defensive check that catches any inconsistency in this pass.
    assert
      (L.exprType s1' == L.exprType s2')
      "[Impossible] Inconsistent branch types."
      (L.Expr (L.IfBool cond' s1' s2') (L.exprType s1'))
-- Translate the if-then statement (no else branch).
translateStatement (A.IfStmt cond s1 Nothing) =
  let cond' = translateExpression cond
      s1'   = translateStatement s1
  in L.Expr (L.IfBool cond' s1' (L.Expr L.Skip L.TUnit)) (L.exprType s1')
-- Translate the while statement.
-- The result type is TUnit because Michelson's LOOP instruction does not produce
-- a value: when the loop exits the stack is in the same state as before the
-- condition was first evaluated, so no value escapes the loop.
translateStatement (A.WhileStmt cond block) =
  let cond'  = translateExpression cond
      block' = translateStatement block
  in L.Expr (L.While cond' block') L.TUnit
-- In LLTZ (an expression-based IR) there is no explicit return construct:
-- the value of the last expression in a block is the return value.
translateStatement (A.ReturnStmt expr) = translateExpression expr
-- Translate a nested block of statements.
translateStatement (A.SequenceStmt stmts) = translateBlock stmts
-- require(cond, payload): reuse the same require -> fail_with rewrite the
-- interpreter uses (SmartTS.IR.AST.desugarRequire) and re-dispatch through
-- the existing IfStmt case above, instead of duplicating the translation.
translateStatement (A.RequireStmt cond payload) =
  translateStatement (A.desugarRequire cond payload)
    
-- Auxiliary functions for translating expressions.

mkExpr :: L.ExprDesc -> A.Type -> L.Expr
mkExpr e t = L.Expr e $ translateType t

translateUnaryExpression :: A.TypedExpr -> A.Type -> L.Primitive -> L.Expr
translateUnaryExpression e ty prim = mkExpr (L.Prim prim [e']) ty
  where e' = translateExpression e

translateBinaryExpression :: A.TypedExpr -> A.TypedExpr -> A.Type -> L.Primitive -> L.Expr
translateBinaryExpression left right ty prim = mkExpr (L.Prim prim [left', right']) ty
  where left'  = translateExpression left
        right' = translateExpression right

assert :: Bool -> String -> a -> a
assert False msg _ = error msg
assert True  _   v = v
