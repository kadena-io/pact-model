{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
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
   SubInt :: Builtin ('TyArrow ('TyPrim 'PrimInteger)
                              ('TyArrow ('TyPrim 'PrimInteger)
                                        ('TyPrim 'PrimInteger)))

data Var :: Env -> Ty -> Type where
  ZV :: Var (t : ts) t
  SV :: Var ts t -> Var (t' : ts) t

data Exp :: Env -> Ty -> Type where
  VAR :: Var ts t -> Exp ts t
  LAM :: (ReifyTy dom, ReifyTy cod)
    => Exp (dom : ts) cod -> Exp ts ('TyArrow dom cod)
  APP :: (ReifyTy dom, ReifyTy cod)
    => Exp ts ('TyArrow dom cod) -> Exp ts dom -> Exp ts cod
  Error :: ReifyTy t
    => Err -> Exp ts t
  Lit :: ReifyPrim ty
    => Literal ty -> Exp ts ('TyPrim ty)
  Bltn :: ReifyTy t
    => Builtin t -> Exp ts t
  Symbol :: Prelude.String -> Exp ts 'TySym
  If :: ReifyTy t
    => Exp ts ('TyPrim 'PrimBool) -> Exp ts t -> Exp ts t -> Exp ts t
  Pair :: (ReifyTy t1, ReifyTy t2)
    => Exp ts t1 -> Exp ts t2 -> Exp ts ('TyPair t1 t2)
  Fst :: (ReifyTy t1, ReifyTy t2)
    => Exp ts ('TyPair t1 t2) -> Exp ts t1
  Snd :: (ReifyTy t1, ReifyTy t2)
    => Exp ts ('TyPair t1 t2) -> Exp ts t2
  Nil :: ReifyTy t
    => Exp ts ('TyList t)
  Cons :: ReifyTy t
    => Exp ts t -> Exp ts ('TyList t) -> Exp ts ('TyList t)
  Car :: ReifyTy t
    => Exp ts ('TyList t) -> Exp ts t
  Cdr :: ReifyTy t
    => Exp ts ('TyList t) -> Exp ts ('TyList t)
  IsNil :: ReifyTy t
    => Exp ts ('TyList t) -> Exp ts ('TyPrim 'PrimBool)
  Seq :: (ReifyTy t', ReifyTy t)
    => Exp ts t' -> Exp ts t -> Exp ts t
  Capability :: (ReifyTy p, ReifyTy v)
    => Exp ts 'TySym -> Exp ts p -> Exp ts v -> Exp ts ('TyCap p v)
  WithCapability
    :: (ReifyTy p, ReifyTy v)
    => Exp ts 'TySym
    -> Exp ts ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ts ('TyArrow ('TyPair v v) v)
    -> Exp ts ('TyCap p v)
    -> Exp ts t
    -> Exp ts t
  ComposeCapability
    :: (ReifyTy p, ReifyTy v)
    => Exp ts 'TySym
    -> Exp ts ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ts ('TyArrow ('TyPair v v) v)
    -> Exp ts ('TyCap p v)
    -> Exp ts t
  InstallCapability :: (ReifyTy p, ReifyTy v)
    => Exp ts ('TyCap p v) -> Exp ts ('TyPrim 'PrimUnit)
  RequireCapability :: (ReifyTy p, ReifyTy v)
    => Exp ts ('TyCap p v) -> Exp ts ('TyPrim 'PrimUnit)

reifyExpTy :: forall t ts. ReifyTy t => Exp ts t -> Ty
reifyExpTy _ = reifyTy @t

reifyCapPTy :: forall p v ts. ReifyTy p => Exp ts ('TyCap p v) -> Ty
reifyCapPTy _ = reifyTy @p

reifyCapVTy :: forall p v ts. ReifyTy v => Exp ts ('TyCap p v) -> Ty
reifyCapVTy _ = reifyTy @v

forgetLiteral :: Literal ty -> E.Literal
forgetLiteral (LitString s) = E.LitString s
forgetLiteral (LitInteger i) = E.LitInteger i
forgetLiteral (LitDecimal d1 d2) = E.LitDecimal d1 d2
forgetLiteral LitUnit = E.LitUnit
forgetLiteral (LitBool b) = E.LitBool b
forgetLiteral (LitTime t) = E.LitTime t

forgetBultin :: Builtin t -> E.Builtin
forgetBultin AddInt = E.AddInt
forgetBultin SubInt = E.SubInt

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
  E.Capability (reifyExpTy p) (reifyExpTy v)
    (forgetExp n) (forgetExp p) (forgetExp v)
forgetExp (WithCapability n prd mng c e) =
  E.WithCapability (reifyCapPTy c) (reifyCapVTy c) undefined
    (forgetExp n) (forgetExp prd) (forgetExp mng) (forgetExp c) (forgetExp e)
forgetExp (ComposeCapability n prd mng c) =
  E.ComposeCapability (reifyCapVTy c) undefined
    (forgetExp n) (forgetExp prd) (forgetExp mng) (forgetExp c)
forgetExp (InstallCapability c) =
  E.InstallCapability (reifyCapPTy c) (reifyCapVTy c) (forgetExp c)
forgetExp (RequireCapability c) =
  E.RequireCapability (reifyCapPTy c) (reifyCapVTy c) (forgetExp c)
