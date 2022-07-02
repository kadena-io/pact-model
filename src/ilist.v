Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List.

Import ListNotations.

Fixpoint ilist {A} (B : A → Type) (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist B xs
  end.
