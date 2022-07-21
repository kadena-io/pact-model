{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC "-Wno-orphans" #-}

module Pact (
  module Ty,
  module Value,
  -- module Exp,
  module Lang,
  module Types,
  evalExp,
  evalInModuleExp,
  eval,
  evalInModule

) where

import qualified Eval
import Util.Types as Types
import Exp hiding (Err)
import qualified Exp
import Lang
import Value hiding (Any, __, reifyTy)
import Ty hiding (__)
import qualified CapabilityType

-- deriving instance Show Ty.PrimType
-- deriving instance Show Ty.Ty
-- deriving instance Show Value.ValueTy
-- deriving instance Show Value.Value
-- deriving instance Show Exp.Err
-- deriving instance Show CapabilityType.CapSig
-- deriving instance Show CapabilityType.CapError
-- deriving instance Show Lang.Err
-- deriving instance Show Lang.PactLog

deriving instance Eq Ty.PrimType
deriving instance Eq Ty.Ty
deriving instance Eq Value.ValueTy
deriving instance Eq Value.Value
deriving instance Eq Exp.Err
deriving instance Eq CapabilityType.CapSig
deriving instance Eq CapabilityType.CapError
deriving instance Eq Lang.Err
deriving instance Eq Lang.PactLog

-- instance Show CapabilityType.Cap where
--   show (CapabilityType.Token name _x _y) =
--     "(Cap " ++ name ++ " " ++ "_" ++ " " ++ "_" ++ ")"

instance Eq CapabilityType.Cap where
  CapabilityType.Token name1 _ _ == CapabilityType.Token name2 _ _ =
    name1 == name2

evalExp
  :: Ty.Ty
  -> Exp.Exp
  -> Either Lang.Err (Value.Value, Lang.PactLog)
evalExp = Eval.eval

evalInModuleExp
  :: String
  -> Ty.Ty
  -> Exp.Exp
  -> Either Lang.Err (Value.Value, Lang.PactLog)
evalInModuleExp = Eval.evalInModule

eval
  :: forall t. ReifyTy t
  => Types.Exp '[] t
  -> Either Lang.Err (Value.Value, Lang.PactLog)
eval e = evalExp (reifyTy @t) (forgetExp e)

evalInModule
  :: forall t. ReifyTy t
  => String
  -> Types.Exp '[] t
  -> Either Lang.Err (Value.Value, Lang.PactLog)
evalInModule name e = evalInModuleExp name (reifyTy @t) (forgetExp e)
