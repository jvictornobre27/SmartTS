module SmartTS.Interpreter.Runtime where

import Control.Monad.State
import Data.ByteString.Lazy (fromStrict)
import Data.Char (isDigit, isHexDigit, toLower)
import Data.Digest.Pure.SHA (sha256, showDigest)
import Data.List (stripPrefix)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import SmartTS.IR.AST

type Address = Name

data ContractInstance = ContractInstance
  { instanceContractName :: Name
  , instanceStorage :: TypedExpr
  }
  deriving (Eq, Show)

type RepositoryState = M.Map Address ContractInstance

data Binding = Binding
  { bindingMutable :: Bool
  , bindingValue :: TypedExpr
  }
  deriving (Eq, Show)

data Runtime = Runtime
  { rtStorage :: Maybe TypedExpr
  , rtParams  :: M.Map Name TypedExpr
  , rtLocals  :: M.Map Name Binding
  , rtMethods :: M.Map Name (MethodDecl Type)
  }
  deriving (Eq, Show)

-- | Everything that can stop expression evaluation / statement execution
-- short of a normal result.
data EvalError
  = RuntimeError String
  | Aborted TypedExpr
  deriving (Eq, Show)

type EvalM = StateT Runtime (Either EvalError)

-- NOTE: I expect the students should not have to read / update the following
-- function definitions.
interpretBug :: String -> a
interpretBug msg =
  error $ "SmartTS internal error (please report): " ++ msg

sourceHashPrefix16 :: String -> String
sourceHashPrefix16 sourceText =
  let bs = encodeUtf8 (T.pack sourceText)
      digest = sha256 (fromStrict bs)
   in take 16 (showDigest digest)

parseEmbeddedSourceHashPrefix :: Address -> Maybe String
parseEmbeddedSourceHashPrefix addr = do
  rest <- stripPrefix "KT1" addr
  case break (== '_') rest of
    (hexPart, '_' : numStr)
      | length hexPart == 16,
        all isHexDigit hexPart,
        not (null numStr),
        all isDigit numStr ->
          Just (map toLower hexPart)
    _ -> Nothing

assertAddressMatchesSource :: Address -> String -> Either String ()
assertAddressMatchesSource addr sourceText =
  case parseEmbeddedSourceHashPrefix addr of
    Nothing -> Right ()
    Just embedded ->
      let actual = map toLower (sourceHashPrefix16 sourceText)
       in if embedded == actual
            then Right ()
            else
              Left $
                "Contract source on disk does not match the code hash in the address "
                  ++ "(embedded "
                  ++ embedded
                  ++ "...; file hashes to "
                  ++ actual
                  ++ "...). Restore the original source or originate a new instance."

generateAddress :: String -> Int -> Address
generateAddress sourceText instanceId =
  "KT1" ++ sourceHashPrefix16 sourceText ++ "_" ++ show instanceId
