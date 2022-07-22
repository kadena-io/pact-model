Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List.

From Equations Require Export Equations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Section ilist.

Context {A : Type}.

Variable B : A → Type.

Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

Equations ilist_ind (P : ∀ (l : list A), ilist l → Prop)
          (Pinil : P [] tt)
          (Picons : ∀ (a : A) (b : B a) (l : list A) (il : ilist l),
              P l il → P (a :: l) (b, il))
          (l : list A) (il : ilist l) : P l il :=
  ilist_ind Pinil Picons (l:=[]) tt := Pinil;
  ilist_ind Pinil Picons (l:=a :: l) (b, il) :=
    Picons a b l il (ilist_ind Pinil Picons il).

Equations ilist_rect (P : ∀ (l : list A), ilist l → Type)
          (Pinil : P [] tt)
          (Picons : ∀ (a : A) (b : B a) (l : list A) (il : ilist l),
              P l il → P (a :: l) (b, il))
          (l : list A) (il : ilist l) : P l il :=
  ilist_rect Pinil Picons (l:=[]) tt := Pinil;
  ilist_rect Pinil Picons (l:=a :: l) (b, il) :=
    Picons a b l il (ilist_rect Pinil Picons il).

End ilist.
