{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Pact where

import qualified Prelude
import qualified Applicative
import qualified CapabilityType
import qualified Classes
import qualified Exp
import qualified Functor
import qualified Lib
import qualified Monad
import qualified RWSE

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

data Err =
   Err_Exp Exp.Err
 | Err_Capability CapabilityType.CapSig CapabilityType.Cap CapabilityType.CapError

data EvalContext =
   RegularEvaluation
 | InWithCapability
 | InModule Prelude.String

coq_EvalContext_rect :: a1 -> a1 -> (Prelude.String -> a1) -> EvalContext ->
                        a1
coq_EvalContext_rect f f0 f1 e =
  case e of {
   RegularEvaluation -> f;
   InWithCapability -> f0;
   InModule s -> f1 s}

coq_EvalContext_rec :: a1 -> a1 -> (Prelude.String -> a1) -> EvalContext ->
                       a1
coq_EvalContext_rec =
  coq_EvalContext_rect

coq_EvalContext_eqdec :: EvalContext -> EvalContext -> Classes.Coq_dec_eq
                         EvalContext
coq_EvalContext_eqdec x y =
  coq_EvalContext_rec (\y0 ->
    case y0 of {
     RegularEvaluation -> Prelude.True;
     _ -> Prelude.False}) (\y0 ->
    case y0 of {
     InWithCapability -> Prelude.True;
     _ -> Prelude.False}) (\s y0 ->
    case y0 of {
     InModule s0 ->
      case Classes.eq_dec_point s
             (Classes.coq_EqDec_EqDecPoint Lib.string_EqDec s) s0 of {
       Prelude.True ->  Prelude.True;
       Prelude.False -> Prelude.False};
     _ -> Prelude.False}) x y

coq_EvalContext_EqDec :: Classes.EqDec EvalContext
coq_EvalContext_EqDec =
  coq_EvalContext_eqdec

data PactEnv =
   Build_PactEnv ([] CapabilityType.ACap) ([] EvalContext)

_granted :: PactEnv -> [] CapabilityType.ACap
_granted p =
  case p of {
   Build_PactEnv _granted0 _ -> _granted0}

_context :: PactEnv -> [] EvalContext
_context p =
  case p of {
   Build_PactEnv _ _context0 -> _context0}

granted :: (Functor.Functor a1) -> (([] CapabilityType.ACap) -> a1) ->
           PactEnv -> a1
granted h f env =
  Functor.fmap h (\g -> Build_PactEnv g (_context env)) (f (_granted env))

context :: (Functor.Functor a1) -> (([] EvalContext) -> a1) -> PactEnv -> a1
context h f env =
  Functor.fmap h (\c -> Build_PactEnv (_granted env) c) (f (_context env))

data PactState =
   Build_PactState ([] CapabilityType.ACap) ([] CapabilityType.ACap)

_resources :: PactState -> [] CapabilityType.ACap
_resources p =
  case p of {
   Build_PactState _resources0 _ -> _resources0}

_to_compose :: PactState -> [] CapabilityType.ACap
_to_compose p =
  case p of {
   Build_PactState _ _to_compose0 -> _to_compose0}

resources :: (Functor.Functor a1) -> (([] CapabilityType.ACap) -> a1) ->
             PactState -> a1
resources h f env =
  Functor.fmap h (\r -> Build_PactState r (_to_compose env))
    (f (_resources env))

to_compose :: (Functor.Functor a1) -> (([] CapabilityType.ACap) -> a1) ->
              PactState -> a1
to_compose h f env =
  Functor.fmap h (\tc -> Build_PactState (_resources env) tc)
    (f (_to_compose env))

data PactLog =
   MkLog

type PactM x = RWSE.RWSE PactEnv PactState PactLog Err x

coq_PactM_Functor :: Functor.Functor (PactM Any)
coq_PactM_Functor =
  RWSE.coq_RWSE_Functor

coq_PactM_Applicative :: Applicative.Applicative (PactM Any)
coq_PactM_Applicative =
  RWSE.coq_RWSE_Applicative

coq_PactM_Monad :: Monad.Monad (PactM Any)
coq_PactM_Monad =
  RWSE.coq_RWSE_Monad

