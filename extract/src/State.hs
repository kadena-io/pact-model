{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module State where

import qualified Util.HString as HString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Ratio
import qualified Data.Word
import qualified Prelude
import qualified System.IO.Unsafe

import qualified Applicative
import qualified Functor
import qualified Ltac
import qualified Monad
import qualified Prelude0
import qualified Tuple

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

__ :: any
__ = Prelude.error "Logical or arity value used"

type StateT s m a = s -> m

getT :: () -> (Applicative.Applicative a1) -> () -> StateT a2 a1 a2
getT _ h _ i =
  Applicative.pure __ h __ ((,) i i)

getsT :: () -> (Applicative.Applicative a1) -> () -> () -> (a2 -> a3) ->
         StateT a2 a1 a3
getsT _ h _ _ f s =
  Applicative.pure __ h __ ((,) (f s) s)

modifyT :: () -> (Applicative.Applicative a1) -> () -> (a2 -> a2) -> StateT
           a2 a1 ()
modifyT _ h _ f i =
  Applicative.pure __ h __ ((,) () (f i))

coq_StateT_Functor :: () -> () -> (Functor.Functor a2) -> Functor.Functor
                      (StateT a1 a2 Any)
coq_StateT_Functor _ _ h =
  Functor.Build_Functor (\_ _ f x st ->
    Functor.fmap __ h __ __ (Tuple.first __ __ f __) (x st))

coq_StateT_ap :: () -> (Monad.Monad a1) -> () -> () -> () -> (StateT 
                 a2 a1 (a3 -> a4)) -> (StateT a2 a1 a3) -> StateT a2 
                 a1 a4
coq_StateT_ap _ h _ _ _ f x st =
  Monad.join __ h __
    (Functor.fmap __ (Applicative.is_functor __ (Monad.is_applicative __ h))
      __ __ (\z ->
      case z of {
       (,) f' st' ->
        Functor.fmap __
          (Applicative.is_functor __ (Monad.is_applicative __ h)) __ __
          (Tuple.first __ __ f' __) (x st')}) (f st))

coq_StateT_Applicative :: () -> (Monad.Monad a1) -> () ->
                          Applicative.Applicative (StateT a2 a1 Any)
coq_StateT_Applicative _ h _ =
  Applicative.Build_Applicative
    (coq_StateT_Functor __ __
      (Applicative.is_functor __ (Monad.is_applicative __ h))) (\_ x st ->
    Applicative.pure __ (Monad.is_applicative __ h) __ ((,) x st))
    (coq_StateT_ap __ h __)

coq_StateT_join :: () -> (Monad.Monad a1) -> () -> () -> (StateT a2 a1
                   (StateT a2 a1 a3)) -> StateT a2 a1 a3
coq_StateT_join _ h _ _ x =
  Ltac.comp __ __ __
    (Ltac.comp __ __ __ (Monad.join __ h __)
      (Functor.fmap __
        (Applicative.is_functor __ (Monad.is_applicative __ h)) __ __
        (Tuple.curry __ __ __ (Prelude0.apply __ __)))) x

coq_StateT_Monad :: () -> (Monad.Monad a1) -> () -> Monad.Monad
                    (StateT a2 a1 Any)
coq_StateT_Monad _ h _ =
  Monad.Build_Monad (coq_StateT_Applicative __ h __)
    (coq_StateT_join __ h __)

