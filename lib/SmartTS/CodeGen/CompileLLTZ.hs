module SmartTS.CodeGen.CompileLLTZ where

import qualified SmartTS.IR.AST as A
import qualified SmartTS.IR.LLTZ as L

translateType :: A.Type -> L.Type
translateType A.TInt             = L.TInt
translateType A.TBool            = L.TBool
translateType A.TUnit            = L.TUnit
translateType (A.TRecord fields) = L.TTuple (L.RowNode (map toLeaf fields))
  where
    toLeaf (name, ty) = L.RowLeaf (Just (L.Label name)) (translateType ty)

-- Basic Expressions
translateExpression :: A.TypedExpr -> L.Expr
translateExpression (A.CInt  ty value) = mkExpr (L.Const (L.CInt value)) ty
translateExpression (A.CBool ty value) = mkExpr (L.Const (L.CBool value)) ty
translateExpression (A.Var   ty name)  = mkExpr (L.Variable (L.Var name)) ty
translateExpression (A.Unit  ty)       = mkExpr (L.Const L.CUnit) ty
-- Boolean Expressions
translateExpression (A.And ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimAnd
translateExpression (A.Or  ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimOr
translateExpression (A.Not ty e)     = translateUnaryExpression e ty L.PrimNot
-- Comparison Expressions
translateExpression (A.Eq  ty e1 e2) = translateComparison e1 e2 ty L.PrimEq
translateExpression (A.Neq ty e1 e2) = translateComparison e1 e2 ty L.PrimNeq
translateExpression (A.Lt  ty e1 e2) = translateComparison e1 e2 ty L.PrimLt
translateExpression (A.Lte ty e1 e2) = translateComparison e1 e2 ty L.PrimLe
translateExpression (A.Gt  ty e1 e2) = translateComparison e1 e2 ty L.PrimGt
translateExpression (A.Gte ty e1 e2) = translateComparison e1 e2 ty L.PrimGe
translateExpression (A.FailWith _ _) =
  error "[Impossible] FailWith cannot appear as an expression in a well-typed AST."
-- TODO: Write here the translation of the remaining expressions.

-- | Translate a SmartTS block (a list of statements) into a nested LLTZ let-expression.
--
-- LLTZ is an expression-based language derived from the Lambda calculus.
-- A statement sequence is encoded as a chain of LetIn / LetMutIn nodes where
-- each binding carries the rest of the block as its continuation.  The type of
-- the whole chain is propagated from the innermost expression, so a block that
-- ends in a ReturnStmt carries the return type all the way to the top.
translateBlock :: [A.TypedStmt] -> L.Expr
translateBlock [] = L.Expr L.Skip L.TUnit
translateBlock (A.ReturnStmt expr : _) = translateExpression expr
translateBlock (s@(A.FailWithStmt _) : _) = translateStatement s
translateBlock [s] | not (bindsName s) = translateStatement s
  where
    bindsName A.VarDeclStmt {} = True
    bindsName A.ValDeclStmt {} = True
    bindsName _                = False
translateBlock (s:ss) =
  case s of
    (A.VarDeclStmt name _ty expr) -> L.Expr (L.LetMutIn (L.MutVar name) (translateExpression expr) block) ty
    (A.ValDeclStmt name _ty expr) -> L.Expr (L.LetIn    (L.Var  name)   (translateExpression expr) block) ty
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
  in case (isFailing s1', isFailing s2') of
       (True, True) ->
         L.Expr (L.IfBool cond' (withResultType L.TUnit s1')
                                (withResultType L.TUnit s2')) L.TUnit
       (True, False) ->
         let ty = L.exprType s2'
          in L.Expr (L.IfBool cond' (withResultType ty s1') s2') ty
       (False, True) ->
         let ty = L.exprType s1'
          in L.Expr (L.IfBool cond' s1' (withResultType ty s2')) ty
       (False, False) ->
         assert
           (L.exprType s1' == L.exprType s2')
           "[Impossible] Inconsistent branch types."
           (L.Expr (L.IfBool cond' s1' s2') (L.exprType s1'))
-- Translate the if-then statement (no else branch).
translateStatement (A.IfStmt cond s1 Nothing) =
  let cond' = translateExpression cond
      s1'   = translateStatement s1
      s1''  = if isFailing s1' then withResultType L.TUnit s1' else s1'
  in L.Expr (L.IfBool cond' s1'' (L.Expr L.Skip L.TUnit)) (L.exprType s1'')
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
-- Project 5: fail_with and require
translateStatement (A.FailWithStmt payload) =
  L.Expr (L.Prim L.PrimFailwith [translateExpression payload]) L.TUnit
translateStatement (A.RequireStmt cond payload) =
  translateStatement
    (A.IfStmt (A.Not A.TBool cond) (A.FailWithStmt payload) Nothing)

isFailing :: L.Expr -> Bool
isFailing (L.Expr (L.Prim L.PrimFailwith _) _) = True
isFailing (L.Expr (L.LetIn _ _ k) _)           = isFailing k
isFailing (L.Expr (L.LetMutIn _ _ k) _)        = isFailing k
isFailing (L.Expr (L.IfBool _ t f) _)          = isFailing t && isFailing f
isFailing _                                    = False

withResultType :: L.Type -> L.Expr -> L.Expr
withResultType ty (L.Expr d@(L.Prim L.PrimFailwith _) _) = L.Expr d ty
withResultType ty (L.Expr (L.LetIn v b k) _) =
  let k' = withResultType ty k in L.Expr (L.LetIn v b k') (L.exprType k')
withResultType ty (L.Expr (L.LetMutIn v b k) _) =
  let k' = withResultType ty k in L.Expr (L.LetMutIn v b k') (L.exprType k')
withResultType ty (L.Expr (L.IfBool c t f) _) =
  L.Expr (L.IfBool c (withResultType ty t) (withResultType ty f)) ty
withResultType _ e = e

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

translateComparison :: A.TypedExpr -> A.TypedExpr -> A.Type -> L.Primitive -> L.Expr
translateComparison left right ty prim =
  mkExpr (L.Prim prim [compared]) ty
  where
    compared = L.Expr (L.Prim L.PrimCompare [left', right']) L.TInt
    left'    = translateExpression left
    right'   = translateExpression right

assert :: Bool -> String -> a -> a
assert False msg _ = error msg
assert True  _   v = v
