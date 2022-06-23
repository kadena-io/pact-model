(************************************************************************
 * Type-indexed n-tuples
 *)

Section ilist.

Variable A : Type.
Variable B : A → Type.

Fixpoint ilist (l : list A) : Type :=
  match l with
  | [] => ()
  | x :: xs => (B x * ilist xs)
  end.

Definition icons {t : A} (x : B t) `(l : ilist ts) : ilist (t :: ts) := (x, l).

Equations isnoc {t : A} (x : B t) `(l : ilist ts) : ilist (ts ++ [t]) :=
  @isnoc s x [] () := (x, ());
  @isnoc s x (_ :: _) (y, ys) := icons y (isnoc x ys).

Equations iapp `(l1 : ilist xs) `(l2 : ilist ys) : ilist (xs ++ ys) :=
  @iapp [] () _ l2 := l2;
  @iapp (_ :: _) (x, l1) _ l2 := icons x (iapp l1 l2).

End ilist.

Arguments ilist {A B} _.
Arguments icons {A B t} x {ts} l.
Arguments isnoc {A B t} x {ts} l.
Arguments iapp {A B xs} l1 {ys} l2.
