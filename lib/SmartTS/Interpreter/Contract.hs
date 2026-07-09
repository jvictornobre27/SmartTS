-- | Contract origination and entrypoint invocation.
--
-- The CLI runs "SmartTS.TypeCheck.typeCheckContract" on source before interpretation.
-- Persisted storage is decoded with "SmartTS.Interpreter.Codec.jsonToExprByType".
-- After those steps, expression shapes that contradict the static types are treated as
-- internal bugs ("interpretBug") rather than user-facing "Left" errors.
module SmartTS.Interpreter.Contract where

import Control.Monad.State (runStateT)
import Data.Aeson (Value (..))
import qualified Data.Map.Strict as M
import SmartTS.IR.AST
import SmartTS.Interpreter.Codec
import SmartTS.Interpreter.Eval
import SmartTS.Interpreter.Runtime

-- | Build the map of callable private methods for a contract.
buildMethodMap :: TypedContract -> M.Map Name (MethodDecl Type)
buildMethodMap c =
  M.fromList [(methodName m, m) | m <- contractMethods c, methodKind m == Private]

execMethod :: TypedContract -> MethodDecl Type -> M.Map Name TypedExpr -> Either String Runtime
execMethod c m params = do
  let initialRt =
        Runtime
          { rtStorage = Nothing
          , rtParams  = params
          , rtLocals  = M.empty
          , rtMethods = buildMethodMap c
          }
  case runStateT (execStmt (methodBody m)) initialRt of
    Left (RuntimeError msg) -> Left msg
    Left (Aborted payload)  ->
      Left $ "Origination aborted via fail_with/require with payload: " ++ show payload
    Right (_, rt')          -> Right rt'

execMethodWithInitialStorage ::
  TypedContract ->
  TypedExpr ->
  MethodDecl Type ->
  M.Map Name TypedExpr ->
  Either String (Maybe TypedExpr, Runtime)
execMethodWithInitialStorage c initialStorage m params =
  let initialRt =
        Runtime
          { rtStorage = Just initialStorage
          , rtParams  = params
          , rtLocals  = M.empty
          , rtMethods = buildMethodMap c
          }
   in case runStateT (execStmt (methodBody m)) initialRt of
        Left (RuntimeError msg) -> Left msg
        Left (Aborted payload)  -> Right (Just (FailWith (exprAnn payload) payload), initialRt)
        Right (mRet, rt')       -> Right (mRet, rt')

findEntryPointByName :: TypedContract -> Name -> Either String (MethodDecl Type)
findEntryPointByName c name =
  case filter (\m -> isEntryPointMethod m && methodName m == name) (contractMethods c) of
    []  -> Left $ "No @entrypoint named \"" ++ name ++ "\"."
    [m] -> Right m
    _   -> Left $ "Multiple @entrypoint methods named \"" ++ name ++ "\"."

originateWithJsonArgs ::
  RepositoryState ->
  TypedContract ->
  String ->
  Value ->
  Either String (Address, RepositoryState)
originateWithJsonArgs repo c sourceText argsJson = do
  m <- case findMethods Originate c of
    []   -> Left "Contract must have exactly one @originate method."
    [mm] -> Right mm
    _    -> Left "Contract must have exactly one @originate method."
  params <- bindArgsByName (methodArgs m) argsJson
  rt <- execMethod c m params
  storageExpr <-
    case rtStorage rt of
      Nothing -> Left "Originate method did not initialize `storage`."
      Just s  -> Right s
  let address = generateAddress sourceText (M.size repo)
      repo'   =
        M.insert
          address
          (ContractInstance (contractName c) storageExpr)
          repo
  Right (address, repo')

callEntrypointWithJsonArgs ::
  RepositoryState ->
  TypedContract ->
  Address ->
  Name ->
  String ->
  Value ->
  Either String (Maybe TypedExpr, RepositoryState)
callEntrypointWithJsonArgs repo c addr entryName sourceText argsJson = do
  ci <-
    case M.lookup addr repo of
      Nothing -> Left $ "Unknown address: " ++ addr
      Just x  -> Right x
  assertAddressMatchesSource addr sourceText
  if instanceContractName ci /= contractName c
    then
      Left $
        "Contract name mismatch: instance is "
          ++ instanceContractName ci
          ++ " but loaded source is "
          ++ contractName c
          ++ "."
    else do
      m      <- findEntryPointByName c entryName
      params <- bindArgsByName (methodArgs m) argsJson
      (ret, rt') <- execMethodWithInitialStorage c (instanceStorage ci) m params
      newStorage <-
        case rtStorage rt' of
          Nothing -> Left "Entrypoint cleared `storage`; not allowed."
          Just s  -> Right s
      let ci'   = ci {instanceStorage = newStorage}
          repo' = M.insert addr ci' repo
      Right (ret, repo')
