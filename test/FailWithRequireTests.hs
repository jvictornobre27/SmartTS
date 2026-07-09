{-# LANGUAGE OverloadedStrings #-}

-- Unit tests for Project 5: fail_with and require.
--
-- Per the project spec, both `fail_with` and `require` are STATEMENTS, not
-- expressions: `fail_with(payload);` unconditionally aborts, and
-- `require(cond, payload);` desugars to `if (!cond) { fail_with(payload); }`.
-- Neither can be nested inside another expression (e.g. `return fail_with(x);`
-- and `1 + fail_with(x)` are both parse errors) -- that is precisely what
-- makes them valid in any statement position regardless of the enclosing
-- method's declared return type, without needing a general subtyping story
-- for a bottom-typed *expression*.
--
-- Covers:
--   * Parser        - new syntax produces correct AST nodes (FailWithStmt / RequireStmt)
--   * Type checker  - fail_with's payload is checked but unconstrained by context
--   * Interpreter   - abort semantics, short-circuiting, transactional rollback,
--                      require's desugaring, propagation through @private calls
module FailWithRequireTests (failWithRequireTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Aeson (object, (.=))
import qualified Data.Map.Strict as M

import SmartTS.IR.AST
import SmartTS.Parser        (parseContractFromString)
import SmartTS.TypeCheck     (typeCheckContract)
import SmartTS.Interpreter
  ( ContractInstance (..)
  , RepositoryState
  , originateWithJsonArgs
  , callEntrypointWithJsonArgs
  , instanceStorage
  )

-- Top-level export

failWithRequireTests :: TestTree
failWithRequireTests =
  testGroup
    "Project 5: fail_with and require"
    [ p5ParserTests
    , p5TypeCheckTests
    , p5InterpreterTests
    ]

-- Shared helpers

parseOk :: String -> (ParsedContract -> Assertion) -> Assertion
parseOk src f = case parseContractFromString src of
  Left err -> assertFailure $ "Parse failed: " ++ show err
  Right c  -> f c

parseFails :: String -> Assertion
parseFails src = case parseContractFromString src of
  Left _  -> return ()
  Right _ -> assertFailure "Expected parse failure but got success"

tcOk :: String -> Assertion
tcOk src = parseOk src $ \c ->
  case typeCheckContract c of
    Left err -> assertFailure $ "Type check failed: " ++ err
    Right _  -> return ()

tcFails :: String -> Assertion
tcFails src = parseOk src $ \c ->
  case typeCheckContract c of
    Left _   -> return ()
    Right _  -> assertFailure "Expected type error but checking succeeded"

-- Originate a contract from source using empty JSON args.
originate :: String -> IO (String, RepositoryState)
originate src = do
  c <- parseIO src
  tc <- tcIO c
  case originateWithJsonArgs M.empty tc src (object []) of
    Left err           -> assertFailureIO $ "Originate error: " ++ err
    Right (addr, repo) -> return (addr, repo)

parseIO :: String -> IO ParsedContract
parseIO src = case parseContractFromString src of
  Left err -> assertFailureIO $ "Parse error: " ++ show err
  Right c  -> return c

tcIO :: ParsedContract -> IO TypedContract
tcIO c = case typeCheckContract c of
  Left err -> assertFailureIO $ "Type error: " ++ err
  Right tc -> return tc

-- assertFailure lifted to IO a so it can be used before a return.
assertFailureIO :: String -> IO a
assertFailureIO msg = assertFailure msg >> error "unreachable"

-- 1. Parser tests
-- Pattern matches use wildcards (_) for the annotation slot,
-- since the parser produces () and we do not care about its value.

p5ParserTests :: TestTree
p5ParserTests =
  testGroup "Parser"
  [ testCase "fail_with(payload); produces a FailWithStmt node" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { fail_with(42); } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" [] TInt
                (SequenceStmt [FailWithStmt (CInt _ 42)])] ->
                  return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "fail_with payload can be an expression" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int { fail_with(v + 1); } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" [FormalParameter "v" TInt] TInt
                (SequenceStmt
                  [FailWithStmt (Add _ (Var _ "v") (CInt _ 1))])] ->
                      return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "fail_with is a statement - NOT usable inside `return`" $
      parseFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { return fail_with(42); } }"

  , testCase "fail_with is a statement - NOT usable nested in an expression" $
      parseFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { return 1 + fail_with(2); } }"

  , testCase "require(cond, payload) produces RequireStmt" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int { require(v > 0, 99); return v; } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" [FormalParameter "v" TInt] TInt
                (SequenceStmt
                  [ RequireStmt (Gt _ (Var _ "v") (CInt _ 0)) (CInt _ 99)
                  , ReturnStmt (Var _ "v")
                  ])] -> return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "require with && condition parses correctly" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(a: int, b: int): int \
        \   { require((a > 0) && (b > 0), 1); return a + b; } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" _ TInt
                (SequenceStmt (RequireStmt {} : _))] -> return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "multiple requires parse as multiple RequireStmt nodes" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(a: int, b: int): int \
        \   { require(a > 0, 1); require(b > 0, 2); return a + b; } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" _ TInt
                (SequenceStmt
                  [ RequireStmt (Gt _ (Var _ "a") (CInt _ 0)) (CInt _ 1)
                  , RequireStmt (Gt _ (Var _ "b") (CInt _ 0)) (CInt _ 2)
                  , ReturnStmt _
                  ])] -> return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "fail_with inside if-then branch parses" $
      parseOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(b: bool): int \
        \   { if (b) { fail_with(1); } else { return 0; } } }"
        $ \c -> case c of
            Contract _ _
              [MethodDecl EntryPoint "f" _ TInt
                (SequenceStmt
                  [IfStmt (Var _ "b")
                    (SequenceStmt [FailWithStmt (CInt _ 1)])
                    (Just (SequenceStmt [ReturnStmt (CInt _ 0)]))])] ->
                      return ()
            _ -> assertFailure $ "Unexpected AST: " ++ show c

  , testCase "fail_with is a reserved word - cannot be used as identifier" $
      parseFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { val fail_with: int = 1; return fail_with; } }"

  , testCase "require is a reserved word - cannot be used as identifier" $
      parseFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { val require: int = 1; return require; } }"

  , testCase "fail_with with no trailing semicolon is a parse error" $
      parseFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { fail_with(1) } }"
  ]

-- 2. Type-checker tests

p5TypeCheckTests :: TestTree
p5TypeCheckTests =
  testGroup "Type Checker"
  [ testCase "fail_with type-checks in an int-returning method" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(b: bool): int \
        \   { if (b) { fail_with(99); } else { return 0; } } }"

  , testCase "fail_with type-checks in a bool-returning method" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(b: bool): bool \
        \   { if (b) { return true; } else { fail_with(0); } } }"

  , testCase "fail_with type-checks in a unit-returning method" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @originate init(): unit { fail_with(0); } }"

  , testCase "fail_with's payload type has no bearing on the return type" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(b: bool): int \
        \   { if (b) { fail_with(true); } else { return 0; } } }"

  , testCase "fail_with nested in if/else does not cause a false positive" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int \
        \   { if (v > 10) { return 100; } \
        \     else { if (v > 0) { return v; } else { fail_with(42); } } } }"

  , testCase "fail_with payload is still type-checked on its own terms" $
      tcFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { fail_with(true + 1); } }"

  , testCase "fail_with payload referencing an unknown variable is rejected" $
      tcFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(): int { fail_with(doesNotExist); } }"

  , testCase "require with bool condition is well-typed" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int { require(v > 0, 100); return v; } }"

  , testCase "require condition must be bool - rejects int condition" $
      tcFails
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int { require(v, 1); return v; } }"

  , testCase "require payload may be any well-typed expression" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(v: int): int { require(v > 0, v * 2 + 1); return v; } }"

  , testCase "multiple requires in sequence are well-typed" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(a: int, b: int): int \
        \   { require(a > 0, 1); require(b > 0, 2); return a + b; } }"

  , testCase "require inside while body is well-typed" $
      tcOk
        "contract C { storage: { x: int }; \
        \ @entrypoint f(n: int): int \
        \   { var i: int = 0; \
        \     while (i < n) { require(i != 5, 99); i = i + 1; } \
        \     return i; } }"
  ]

-- 3. Interpreter tests

p5InterpreterTests :: TestTree
p5InterpreterTests =
  testGroup "Interpreter"
  [ testCase "fail_with taken branch - reports FailWith with the payload" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 0; return (); }"
            , "  @entrypoint f(b: bool): int"
            , "    { if (b) { fail_with(99); } else { return storage.x; } }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["b" .= True]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (FailWith _ (CInt _ 99)), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected FailWith(99), got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "fail_with not taken - normal return value" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 7; return (); }"
            , "  @entrypoint f(b: bool): int"
            , "    { if (b) { fail_with(99); } else { return storage.x; } }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["b" .= False]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (CInt _ 7), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected CInt 7, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "fail_with short-circuits - later statements in the block do not run" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 0; return (); }"
            , "  @entrypoint f(): int"
            , "    { storage.x = 1; fail_with(0); storage.x = 999; return storage.x; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      case callEntrypointWithJsonArgs repo tc addr "f" src (object []) of
        Right (Just (FailWith _ (CInt _ 0)), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected abort, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "fail_with rolls back storage mutations made earlier in the SAME call" $ do
      -- This is the key transactional property: unlike a plain early return,
      -- fail_with must undo *everything* the call did, not just whatever
      -- happens to textually follow it. `storage.x = 1;` runs before the
      -- abort, so a naive "just stop running statements" interpreter would
      -- incorrectly persist it.
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 0; return (); }"
            , "  @entrypoint f(): int"
            , "    { storage.x = 1; fail_with(0); }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      case callEntrypointWithJsonArgs repo tc addr "f" src (object []) of
        Right (Just (FailWith _ (CInt _ 0)), repo') ->
          case M.lookup addr repo' of
            Nothing -> assertFailure "Address not found in repo"
            Just ci -> case instanceStorage ci of
              Record _ [("x", CInt _ 0)] -> return ()
              other -> assertFailure $ "Storage was mutated despite abort: " ++ show other
        Right (v, _) -> assertFailure $ "Expected abort, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "fail_with inside a called @private method aborts the whole entrypoint" $ do
      -- The abort must propagate out of the Call expression, not be treated
      -- as if the helper had simply "returned" its payload as a value.
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 0; return (); }"
            , "  @entrypoint f(v: int): int"
            , "    { storage.x = 1; return 10 + guard(v); }"
            , "  @private guard(v: int): int"
            , "    { if (v < 0) { fail_with(7); } return v; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= ((-1) :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (FailWith _ (CInt _ 7)), repo') ->
          case M.lookup addr repo' of
            Nothing -> assertFailure "Address not found in repo"
            Just ci -> case instanceStorage ci of
              Record _ [("x", CInt _ 0)] -> return ()
              other -> assertFailure $ "Storage was mutated despite abort: " ++ show other
        Right (v, _) -> assertFailure $ "Expected abort, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "@private call succeeding normally still returns its value" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 0; return (); }"
            , "  @entrypoint f(v: int): int"
            , "    { return 10 + guard(v); }"
            , "  @private guard(v: int): int"
            , "    { if (v < 0) { fail_with(7); } return v; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= (5 :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (CInt _ 15), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected CInt 15, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "require passing - execution continues, result returned" $ do
      let src = unlines
            [ "contract C { storage: { counter: int };"
            , "  @originate init(): unit { storage.counter = 0; return (); }"
            , "  @entrypoint inc(v: int): int"
            , "    { require(v > 0, 200);"
            , "      storage.counter = storage.counter + v;"
            , "      return storage.counter; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= (5 :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "inc" src args of
        Right (Just (CInt _ 5), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected CInt 5, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "require failing - returns FailWith with correct payload" $ do
      let src = unlines
            [ "contract C { storage: { counter: int };"
            , "  @originate init(): unit { storage.counter = 0; return (); }"
            , "  @entrypoint inc(v: int): int"
            , "    { require(v > 0, 200);"
            , "      storage.counter = storage.counter + v;"
            , "      return storage.counter; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= ((-3) :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "inc" src args of
        Right (Just (FailWith _ (CInt _ 200)), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected FailWith(200), got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "require failing - storage is NOT modified" $ do
      let src = unlines
            [ "contract C { storage: { counter: int };"
            , "  @originate init(): unit { storage.counter = 0; return (); }"
            , "  @entrypoint inc(v: int): int"
            , "    { require(v > 0, 200);"
            , "      storage.counter = 999;"
            , "      return storage.counter; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= ((-1) :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "inc" src args of
        Right (Just (FailWith _ _), repo') ->
          case M.lookup addr repo' of
            Nothing -> assertFailure "Address not found in repo"
            Just ci -> case instanceStorage ci of
              Record _ [("counter", CInt _ 0)] -> return ()
              other -> assertFailure $ "Storage was mutated: " ++ show other
        Right (v, _) -> assertFailure $ "Expected abort, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "first require passes, second fails - correct payload" $ do
      let src = unlines
            [ "contract C { storage: { n: int };"
            , "  @originate init(): unit { storage.n = 0; return (); }"
            , "  @entrypoint f(x: int, y: int): int"
            , "    { require(x > 0, 300);"
            , "      require(y > 0, 400);"
            , "      return x + y; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["x" .= (5 :: Int), "y" .= ((-1) :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (FailWith _ (CInt _ 400)), _) -> return ()
        Right (Just (FailWith _ p), _) ->
          assertFailure $ "Expected payload CInt 400, got: " ++ show p
        Right (v, _) -> assertFailure $ "Expected abort, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "require inside if-else - only fires on the taken branch" $ do
      let src = unlines
            [ "contract C { storage: { counter: int };"
            , "  @originate init(): unit { storage.counter = 0; return (); }"
            , "  @entrypoint f(flag: bool, v: int): int"
            , "    { if (flag) {"
            , "        require(v > 0, 500);"
            , "        storage.counter = 999;"
            , "      } else {"
            , "        storage.counter = v;"
            , "      }"
            , "      return storage.counter; }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["flag" .= False, "v" .= (3 :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (CInt _ 3), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected CInt 3, got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "fail_with payload expression is fully evaluated before abort" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(): unit { storage.x = 10; return (); }"
            , "  @entrypoint f(v: int): int"
            , "    { fail_with(v * 3 + 1); }"
            , "}"
            ]
      (addr, repo) <- originate src
      tc <- parseIO src >>= tcIO
      let args = object ["v" .= (4 :: Int)]
      case callEntrypointWithJsonArgs repo tc addr "f" src args of
        Right (Just (FailWith _ (CInt _ 13)), _) -> return ()
        Right (v, _) -> assertFailure $ "Expected FailWith(CInt 13), got: " ++ show v
        Left  err    -> assertFailure $ "Unexpected error: " ++ err

  , testCase "an @originate method that aborts fails origination outright" $ do
      let src = unlines
            [ "contract C { storage: { x: int };"
            , "  @originate init(n: int): unit"
            , "    { require(n > 0, 1); storage.x = n; return (); }"
            , "}"
            ]
      c <- parseIO src
      tc <- tcIO c
      let args = object ["n" .= ((-5) :: Int)]
      case originateWithJsonArgs M.empty tc src args of
        Left _  -> return ()
        Right _ -> assertFailure "Expected origination to fail when init() aborts"
  ]