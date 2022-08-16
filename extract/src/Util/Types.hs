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
import Data.Void

import Ty
import qualified Bltn as B
import qualified Exp as E
import qualified Lang as L

class ReifyPrim (t :: PrimType) where
  reifyPrim :: PrimType

instance ReifyPrim 'PrimVoid where
  reifyPrim = PrimVoid

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

instance ReifyTy 'TyError where
  reifyTy = TyError

instance ReifyTy 'TySym where
  reifyTy = TySym

instance forall prim. ReifyPrim prim => ReifyTy ('TyPrim prim) where
  reifyTy = TyPrim (reifyPrim @prim)

instance forall t. ReifyTy t => ReifyTy ('TyList t) where
  reifyTy = TyList (reifyTy @t)

instance forall t1 t2. (ReifyTy t1, ReifyTy t2)
    => ReifyTy ('TyPair t1 t2) where
  reifyTy = TyPair (reifyTy @t1) (reifyTy @t2)

instance forall t1 t2. (ReifyTy t1, ReifyTy t2)
    => ReifyTy ('TySum t1 t2) where
  reifyTy = TySum (reifyTy @t1) (reifyTy @t2)

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

type family SemPrimTy (t :: PrimType) :: Type where
  SemPrimTy 'PrimVoid    = Void
  SemPrimTy 'PrimUnit    = ()
  SemPrimTy 'PrimInteger = Integer
  SemPrimTy 'PrimDecimal = Integer -- jww (2022-07-23): TODO
  SemPrimTy 'PrimTime    = Integer
  SemPrimTy 'PrimBool    = Bool
  SemPrimTy 'PrimString  = String

type family SemTy (t :: Ty) :: Type where
  SemTy 'TyError       = L.Err
  SemTy 'TySym         = String
  SemTy ('TyPrim ty)   = SemPrimTy ty
  SemTy ('TyList l)    = [SemTy l]
  SemTy ('TyPair x y)  = (SemTy x, SemTy y)
  SemTy ('TySum x y)   = Either (SemTy x) (SemTy y)
  SemTy ('TyArrow d c) = SemTy d -> SemTy c
  SemTy ('TyCap _ _)   = Void

data Exp :: Ty -> Type where
  VAR :: SemTy t -> Exp t
  LAM :: (ReifyTy dom, ReifyTy cod)
    => (SemTy dom -> Exp cod) -> Exp ('TyArrow dom cod)
  APP :: (ReifyTy dom, ReifyTy cod)
    => Exp ('TyArrow dom cod) -> Exp dom -> Exp cod
  Let :: (ReifyTy t', ReifyTy t)
    => Exp t' -> (SemTy t' -> Exp t) -> Exp t
  Error :: ReifyTy t
    => Exp t
  Catch :: ReifyTy t
    => Exp t -> Exp ('TySum 'TyError t)
  Lit :: ReifyPrim ty
    => Literal ty -> Exp ('TyPrim ty)
  Bltn :: ReifyTy t
    => Builtin t -> Exp t
  Symbol :: Prelude.String -> Exp 'TySym
  If :: ReifyTy t
    => Exp ('TyPrim 'PrimBool) -> Exp t -> Exp t -> Exp t
  Pair :: (ReifyTy t1, ReifyTy t2)
    => Exp t1 -> Exp t2 -> Exp ('TyPair t1 t2)
  Fst :: (ReifyTy t1, ReifyTy t2)
    => Exp ('TyPair t1 t2) -> Exp t1
  Snd :: (ReifyTy t1, ReifyTy t2)
    => Exp ('TyPair t1 t2) -> Exp t2
  Inl :: (ReifyTy t1, ReifyTy t2)
    => Exp t1 -> Exp ('TySum t1 t2)
  Inr :: (ReifyTy t1, ReifyTy t2)
    => Exp t2 -> Exp ('TySum t1 t2)
  Case :: (ReifyTy t1, ReifyTy t2)
    => Exp ('TySum t1 t2) ->
      Exp ('TyArrow t1 t) -> Exp ('TyArrow t2 t) ->
      Exp ('TyPair t1 t2)
  Nil :: ReifyTy t
    => Exp ('TyList t)
  Cons :: ReifyTy t
    => Exp t -> Exp ('TyList t) -> Exp ('TyList t)
  Car :: ReifyTy t
    => Exp ('TyList t) -> Exp t
  Cdr :: ReifyTy t
    => Exp ('TyList t) -> Exp ('TyList t)
  IsNil :: ReifyTy t
    => Exp ('TyList t) -> Exp ('TyPrim 'PrimBool)
  Seq :: (ReifyTy t', ReifyTy t)
    => Exp t' -> Exp t -> Exp t
  Capability :: (ReifyTy p, ReifyTy v)
    => Exp 'TySym -> Exp p -> Exp v -> Exp ('TyCap p v)
  WithCapability
    :: (ReifyTy p, ReifyTy v)
    => Exp 'TySym
    -> Exp ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ('TyArrow ('TyPair v v) v)
    -> Exp ('TyCap p v)
    -> Exp t
    -> Exp t
  ComposeCapability
    :: (ReifyTy p, ReifyTy v)
    => Exp 'TySym
    -> Exp ('TyArrow ('TyCap p v) ('TyPrim 'PrimUnit))
    -> Exp ('TyArrow ('TyPair v v) v)
    -> Exp ('TyCap p v)
    -> Exp t
  InstallCapability :: (ReifyTy p, ReifyTy v)
    => Exp ('TyCap p v) -> Exp ('TyPrim 'PrimUnit)
  RequireCapability :: (ReifyTy p, ReifyTy v)
    => Exp ('TyCap p v) -> Exp ('TyPrim 'PrimUnit)

reifyExpTy :: forall t. ReifyTy t => Exp t -> Ty
reifyExpTy _ = reifyTy @t

reifyCapPTy :: forall p v. ReifyTy p => Exp ('TyCap p v) -> Ty
reifyCapPTy _ = reifyTy @p

reifyCapVTy :: forall p v. ReifyTy v => Exp ('TyCap p v) -> Ty
reifyCapVTy _ = reifyTy @v

forgetLiteral :: Literal ty -> E.Literal
forgetLiteral (LitString s) = E.LitString s
forgetLiteral (LitInteger i) = E.LitInteger i
forgetLiteral (LitDecimal d1 d2) = E.LitDecimal d1 d2
forgetLiteral LitUnit = E.LitUnit
forgetLiteral (LitBool b) = E.LitBool b
forgetLiteral (LitTime t) = E.LitTime t

forgetBultin :: Builtin t -> B.Builtin
forgetBultin AddInt = B.AddInt
forgetBultin SubInt = B.SubInt

forgetExp :: Exp t -> E.Exp v
forgetExp (VAR v) = E.VAR undefined (L.unsafeCoerce v)
forgetExp (LAM e) =
  E.LAM undefined undefined (\x -> forgetExp (e (L.unsafeCoerce x)))
forgetExp (APP e1 e2) =
  E.APP undefined undefined (forgetExp e1) (forgetExp e2)
forgetExp (Let x body) =
  E.Let undefined undefined (forgetExp x)
    (\x' -> forgetExp (body (L.unsafeCoerce x')))
forgetExp Error = E.Error undefined
forgetExp (Catch e) = E.Catch undefined (forgetExp e)
forgetExp (Lit lit) = E.Lit undefined (forgetLiteral lit)
forgetExp (Bltn bltn) = E.Bltn undefined (forgetBultin bltn)
forgetExp (Symbol sym) = E.Symbol sym
forgetExp (If b t e) = E.If undefined (forgetExp b) (forgetExp t) (forgetExp e)
forgetExp (Pair x y) = E.Pair undefined undefined (forgetExp x) (forgetExp y)
forgetExp (Fst p) = E.Fst undefined undefined (forgetExp p)
forgetExp (Snd p) = E.Snd undefined undefined (forgetExp p)
forgetExp (Inl p) = E.Inl undefined undefined (forgetExp p)
forgetExp (Inr p) = E.Inr undefined undefined (forgetExp p)
forgetExp (Case e f g) =
  E.Case undefined undefined undefined (forgetExp e) (forgetExp f) (forgetExp g)
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
