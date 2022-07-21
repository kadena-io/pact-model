{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Util.Types where

import Data.Kind

import Ty
import Exp (Err)
import qualified Exp as E

class ReifyPrim (t :: PrimType) where
  reifyPrim :: PrimType

instance ReifyPrim 'PrimUnit where
  reifyPrim = PrimUnit

instance ReifyPrim 'PrimInteger where
  reifyPrim = PrimInteger

instance ReifyPrim 'PrimDecimal where
  reifyPrim = PrimDecimal

instance ReifyPrim 'PrimTime where
  reifyPrim = PrimTime

instance ReifyPrim 'PrimBool where
  reifyPrim = PrimBool

instance ReifyPrim 'PrimString where
  reifyPrim = PrimString

class ReifyTy (t :: Ty) where
  reifyTy :: Ty

instance forall dom cod. (ReifyTy dom, ReifyTy cod)
    => ReifyTy ('TyArrow dom cod) where
  reifyTy = TyArrow (reifyTy @dom) (reifyTy @cod)

instance forall prim. ReifyPrim prim => ReifyTy ('TyPrim prim) where
  reifyTy = TyPrim (reifyPrim @prim)

instance ReifyTy 'TySym where
  reifyTy = TySym

instance forall t. ReifyTy t => ReifyTy ('TyList t) where
  reifyTy = TyList (reifyTy @t)

instance forall t1 t2. (ReifyTy t1, ReifyTy t2)
    => ReifyTy ('TyPair t1 t2) where
  reifyTy = TyPair (reifyTy @t1) (reifyTy @t2)

instance forall p v. (ReifyTy p, ReifyTy v)
    => ReifyTy ('TyCap p v) where
  reifyTy = TyCap (reifyTy @p) (reifyTy @v)

type Env = [Ty]

data Literal :: PrimType -> Type where
  LitString :: Prelude.String -> Literal 'PrimString
  LitInteger :: Prelude.Int -> Literal 'PrimInteger
  LitDecimal :: Prelude.Int -> Prelude.Int -> Literal 'PrimDecimal
  LitUnit :: Literal 'PrimUnit
  LitBool :: Prelude.Bool -> Literal 'PrimBool
  LitTime :: Prelude.Int -> Literal 'PrimTime

data Builtin :: Ty -> Type where
   AddInt :: Builtin ('TyArrow ('TyPrim 'PrimInteger)
                              ('TyArrow ('TyPrim 'PrimInteger)
                                        ('TyPrim 'PrimInteger)))

data Var :: Env -> Ty -> Type where
  ZV :: Var (t : ts) t
  SV :: Var ts t -> Var (t' : ts) t

data Exp :: Env -> Ty -> Type where
  VAR :: Var ts t -> Exp ts t
  LAM :: Exp (dom : ts) cod -> Exp ts ('TyArrow dom cod)
  APP :: Exp ts ('TyArrow dom cod) -> Exp ts dom -> Exp ts cod
  Error :: Err -> Exp ts t
  Lit :: Literal ty -> Exp ts ('TyPrim ty)
  Bltn :: Builtin t -> Exp ts t
  Symbol :: Prelude.String -> Exp ts 'TySym
  If :: Exp ts ('TyPrim 'PrimBool) -> Exp ts t -> Exp ts t -> Exp ts t
  Pair :: Exp ts t1 -> Exp ts t2 -> Exp ts ('TyPair t1 t2)
  Fst :: Exp ts ('TyPair t1 t2) -> Exp ts t1
  Snd :: Exp ts ('TyPair t1 t2) -> Exp ts t2
  Nil :: Exp ts ('TyList t)
  Cons :: Exp ts t -> Exp ts ('TyList t) -> Exp ts ('TyList t)
  Car :: Exp ts ('TyList t) -> Exp ts t
  Cdr :: Exp ts ('TyList t) -> Exp ts ('TyList t)
  IsNil :: Exp ts ('TyList t) -> Exp ts ('TyPrim 'PrimBool)
  Seq :: Exp ts t' -> Exp ts t -> Exp ts t
  Capability :: Exp ts 'TySym -> Exp ts p -> Exp ts v -> Exp ts ('TyCap p v)
  WithCapability
    :: Exp ts 'TySym
    -> Exp ts ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ts ('TyArrow ('TyPair v v) v)
    -> Exp ts ('TyCap p v)
    -> Exp ts t
    -> Exp ts t
  ComposeCapability
    :: Exp ts 'TySym
    -> Exp ts ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ts ('TyArrow ('TyPair v v) v)
    -> Exp ts ('TyCap p v)
    -> Exp ts t
  InstallCapability :: Exp ts ('TyCap p v) -> Exp ts ('TyPrim 'PrimUnit)
  RequireCapability :: Exp ts ('TyCap p v) -> Exp ts ('TyPrim 'PrimUnit)

forgetLiteral :: Literal ty -> E.Literal
forgetLiteral (LitString s) = E.LitString s
forgetLiteral (LitInteger i) = E.LitInteger i
forgetLiteral (LitDecimal d1 d2) = E.LitDecimal d1 d2
forgetLiteral LitUnit = E.LitUnit
forgetLiteral (LitBool b) = E.LitBool b
forgetLiteral (LitTime t) = E.LitTime t

forgetBultin :: Builtin t -> E.Builtin
forgetBultin AddInt = E.AddInt

forgetVar :: Var ts t -> E.Var
forgetVar ZV = E.ZV undefined undefined
forgetVar (SV v) = E.SV undefined undefined undefined (forgetVar v)

forgetExp :: Exp ts t -> E.Exp
forgetExp (VAR v) = E.VAR undefined (forgetVar v)
forgetExp (LAM e) = E.LAM undefined undefined (forgetExp e)
forgetExp (APP e1 e2) = E.APP undefined undefined (forgetExp e1) (forgetExp e2)
forgetExp (Error err) = E.Error undefined err
forgetExp (Lit lit) = E.Lit undefined (forgetLiteral lit)
forgetExp (Bltn bltn) = E.Bltn undefined (forgetBultin bltn)
forgetExp (Symbol sym) = E.Symbol sym
forgetExp (If b t e) = E.If undefined (forgetExp b) (forgetExp t) (forgetExp e)
forgetExp (Pair x y) = E.Pair undefined undefined (forgetExp x) (forgetExp y)
forgetExp (Fst p) = E.Fst undefined undefined (forgetExp p)
forgetExp (Snd p) = E.Snd undefined undefined (forgetExp p)
forgetExp Nil = E.Nil undefined
forgetExp (Cons x xs) = E.Cons undefined (forgetExp x) (forgetExp xs)
forgetExp (Car xs) = E.Car undefined (forgetExp xs)
forgetExp (Cdr xs) = E.Cdr undefined (forgetExp xs)
forgetExp (IsNil xs) = E.IsNil undefined (forgetExp xs)
forgetExp (Seq e1 e2) = E.Seq undefined undefined (forgetExp e1) (forgetExp e2)
forgetExp (Capability n p v) =
  E.Capability undefined undefined
    (forgetExp n) (forgetExp p) (forgetExp v)
forgetExp (WithCapability n prd mng c e) =
  E.WithCapability undefined undefined undefined
    (forgetExp n) (forgetExp prd) (forgetExp mng) (forgetExp c) (forgetExp e)
forgetExp (ComposeCapability n prd mng c) =
  E.ComposeCapability undefined undefined
    (forgetExp n) (forgetExp prd) (forgetExp mng) (forgetExp c)
forgetExp (InstallCapability c) =
  E.InstallCapability undefined undefined (forgetExp c)
forgetExp (RequireCapability c) =
  E.RequireCapability undefined undefined (forgetExp c)
