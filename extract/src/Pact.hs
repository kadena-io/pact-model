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
  eval,
  evalInModule,
  Eval.PactLog(..)

) where

import qualified Eval
import Util.Types as Types
import Lang
import Value hiding (Any, __, reifyTy, unsafeCoerce)
import Ty
import qualified CapabilityType

deriving instance Show Ty.PrimType
deriving instance Show Ty.Ty
deriving instance Show Value.ValueTy
deriving instance Show CapabilityType.CapSig
deriving instance Show CapabilityType.CapError
deriving instance Show Lang.Err
deriving instance Show Eval.PactLog

deriving instance Eq Ty.PrimType
deriving instance Eq Ty.Ty
deriving instance Eq Value.ValueTy
deriving instance Eq CapabilityType.CapSig
deriving instance Eq CapabilityType.CapError
deriving instance Eq Lang.Err
deriving instance Eq Eval.PactLog

instance Show CapabilityType.Cap where
  show (CapabilityType.Token name _x _y) =
    "(Cap " ++ name ++ " " ++ "_" ++ " " ++ "_" ++ ")"

instance Eq CapabilityType.Cap where
  CapabilityType.Token name1 _ _ == CapabilityType.Token name2 _ _ =
    name1 == name2

eval
  :: forall t. ReifyTy t
  => Types.Exp '[] t
  -> Either Lang.Err (SemTy t, Eval.PactLog)
eval e = unsafeCoerce $ Eval.eval (reifyTy @t) (forgetExp e)

evalInModule
  :: forall t. ReifyTy t
  => String
  -> Types.Exp '[] t
  -> Either Lang.Err (SemTy t, Eval.PactLog)
evalInModule name e =
  unsafeCoerce $ Eval.evalInModule name (reifyTy @t) (forgetExp e)
