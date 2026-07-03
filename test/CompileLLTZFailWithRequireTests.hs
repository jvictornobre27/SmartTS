{-# LANGUAGE OverloadedStrings #-}

-- Unit tests for Project 5 (Milestone 3): LLTZ code generation for
-- fail_with and require.
module CompileLLTZFailWithRequireTests (compileLLTZFailWithRequireTests) where

import Test.Tasty
import Test.Tasty.HUnit

import SmartTS.IR.AST
import qualified SmartTS.IR.LLTZ as L
import SmartTS.CodeGen.CompileLLTZ (translateExpression, translateStatement)
import SmartTS.Parser (parseContractFromString)
import SmartTS.TypeCheck (typeCheckContract)

-- Top-level export

compileLLTZFailWithRequireTests :: TestTree
compileLLTZFailWithRequireTests =
  testGroup
    "Project 5 (Milestone 3): LLTZ code generation for fail_with and require"
    ( failWithCodegenTests : requireCodegenTests : mempty )

-- Shared helpers

parseIO :: String -> IO ParsedContract
parseIO src = case parseContractFromString src of
  Left err -> assertFailureIO ( "Parse error: " ++ show err )
  Right c  -> return c

tcIO :: ParsedContract -> IO TypedContract
tcIO c = case typeCheckContract c of
  Left err -> assertFailureIO ( "Type error: " ++ err )
  Right tc -> return tc

assertFailureIO :: String -> IO a
assertFailureIO msg = assertFailure msg >> error "unreachable"

-- Total helper to safely extract the single element of a list of length 1, avoiding partial function warnings
getSingle :: [a] -> a
getSingle (x:_) = x
getSingle _     = error "empty list"

-- | Type-check `src` and return the (single) method body named `methodNm`.
typedBodyOf :: String -> String -> IO TypedStmt
typedBodyOf src methodNm = do
  c  <- parseIO src
  tc <- tcIO c
  let ms = filter (\m -> methodName m == methodNm) (contractMethods tc)
  if null ms
    then assertFailureIO ( "No method named `" ++ methodNm ++ "`." )
    else if length ms > 1
      then assertFailureIO ( "Multiple methods named `" ++ methodNm ++ "`." )
      else return (methodBody (getSingle ms))

-- 1. fail_with codegen

failWithCodegenTests :: TestTree
failWithCodegenTests =
  testGroup "fail_with"
  ( testCase "fail_with(42) compiles to Prim PrimFailwith with a literal payload" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { return fail_with(42); } }"
        "f"
      case body of
        SequenceStmt stmts ->
          if length stmts == 1
            then case getSingle stmts of
                   ReturnStmt fw@(FailWith _ (CInt _ 42)) ->
                     translateExpression fw @?=
                       L.Expr
                         (L.Prim L.PrimFailwith (L.Expr (L.Const (L.CInt 42)) L.TInt : mempty))
                         L.TNever
                   _ -> assertFailure ( "Unexpected statement: " ++ show (getSingle stmts) )
            else assertFailure ( "Expected 1 statement, got: " ++ show (length stmts) )
        other -> assertFailure ( "Unexpected typed body: " ++ show other ))
  : testCase "fail_with type-translates to LLTZ TNever" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { return fail_with(42); } }"
        "f"
      case body of
        SequenceStmt stmts ->
          if length stmts == 1
            then case getSingle stmts of
                   ReturnStmt fw@(FailWith _ _) ->
                     L.exprType (translateExpression fw) @?= L.TNever
                   _ -> assertFailure ( "Unexpected statement: " ++ show (getSingle stmts) )
            else assertFailure ( "Expected 1 statement, got: " ++ show (length stmts) )
        other -> assertFailure ( "Unexpected typed body: " ++ show other ))
  : testCase "fail_with payload can be a computed expression" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: bool): int { return fail_with(!v); } }"
        "f"
      case body of
        SequenceStmt stmts ->
          if length stmts == 1
            then case getSingle stmts of
                   ReturnStmt fw@(FailWith _ (Not _ (Var _ "v"))) ->
                     translateExpression fw @?=
                       L.Expr
                         (L.Prim L.PrimFailwith
                           ( L.Expr
                               (L.Prim L.PrimNot (L.Expr (L.Variable (L.Var "v")) L.TBool : mempty))
                               L.TBool
                           : mempty
                           ))
                         L.TNever
                   _ -> assertFailure ( "Unexpected statement: " ++ show (getSingle stmts) )
            else assertFailure ( "Expected 1 statement, got: " ++ show (length stmts) )
        other -> assertFailure ( "Unexpected typed body: " ++ show other ))
  : mempty
  )

-- 2. require codegen

requireCodegenTests :: TestTree
requireCodegenTests =
  testGroup "require"
  ( testCase "require(cond, payload) compiles identically to its hand-desugared if" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: bool): bool { require(!v, 99); return v; } }"
        "f"
      case body of
        SequenceStmt stmts ->
          if length stmts >= 1
            then let req = getSingle stmts in
              case req of
                RequireStmt cond payload -> do
                  let compiled    = translateStatement req
                      handDesugar = translateStatement
                        (IfStmt (Not TBool cond) (ReturnStmt (FailWith TNever payload)) Nothing)
                  compiled @?= handDesugar
                _ -> assertFailure ( "First statement is not a RequireStmt: " ++ show req )
            else assertFailure "Expected at least 1 statement"
        other -> assertFailure ( "Unexpected typed body: " ++ show other ))
  : testCase "require compiles to an IfBool whose 'then' branch fails with the payload" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: bool): bool { require(!v, 99); return v; } }"
        "f"
      case body of
        SequenceStmt stmts ->
          if length stmts >= 1
            then let req = getSingle stmts in
              case req of
                RequireStmt {} ->
                  case translateStatement req of
                    L.Expr (L.IfBool _ (L.Expr (L.Prim L.PrimFailwith args) L.TNever) _) L.TNever ->
                      if length args == 1
                        then return ()
                        else assertFailure "Expected exactly 1 argument to PrimFailwith"
                    other -> assertFailure ( "Unexpected compiled shape: " ++ show other )
                _ -> assertFailure ( "Expected RequireStmt, got: " ++ show req )
            else assertFailure "Expected at least 1 statement"
        other -> assertFailure ( "Unexpected typed body: " ++ show other ))
  : testCase "require followed by other statements still produces a LetIn chain" (do
      body <- typedBodyOf
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: bool): bool { require(!v, 1); return v; } }"
        "f"
      case translateStatement body of
        L.Expr (L.LetIn (L.Var "_") reqCompiled _continuation) _ ->
          case reqCompiled of
            L.Expr (L.IfBool {}) L.TNever -> return ()
            other -> assertFailure ( "require was not compiled as expected: " ++ show other )
        other -> assertFailure ( "Unexpected block shape: " ++ show other ))
  : mempty
  )