{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC "-Wno-orphans" #-}

module Pact (
  module Ty,
  module Exp,
  module Lang,
  eval

) where

import qualified Eval
import Exp hiding (Err)
import qualified Exp
import Lang
import Ty
import qualified Value
import qualified CapabilityType

deriving instance Show Ty.PrimType
deriving instance Show Ty.Ty
deriving instance Show Value.ValueTy
deriving instance Show Value.Value
deriving instance Show Exp.Err
deriving instance Show CapabilityType.CapSig
deriving instance Show CapabilityType.CapError
deriving instance Show Lang.Err
deriving instance Show Lang.PactLog

instance Show CapabilityType.Cap where
  show (CapabilityType.Token name _ _) = "Cap " ++ name

eval
  :: Ty.Ty
  -> Exp.Exp
  -> Either Lang.Err (Value.Value, Lang.PactLog)
eval = Eval.eval
