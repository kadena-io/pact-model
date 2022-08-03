Require Import
  Coq.Lists.List
  Hask.Control.Monad.

Require Export
  Freer
  Member.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.
Set Primitive Projections.

Definition sendF `(t : f a) : Freer f a := Impure t Pure.

Definition Eff (effs : list (Type -> Type)) (a : Type) : Type :=
  Freer (Union effs) a.

Definition Arr effs a b := a -> Eff effs b.
Arguments Arr effs a b /.

Definition send `{Member eff effs} `(t : eff a) : Eff effs a :=
  Impure (inj t) Pure.

#[export]
Instance Functor_Eff {r} : Functor (Eff r) := Freer_Functor _.
#[export]
Instance Applicative_Eff {r} : Applicative (Eff r) := Freer_Applicative _.
#[export]
Instance Monad_Eff {r} : Monad (Eff r) := Freer_Monad _.

Definition run `(f : Eff [] a) : a :=
  match f with
  | Pure x => x
  | Impure u k => False_rect _ ltac:(inversion u)
  end.

Fixpoint runM `{Monad m} `(f : Eff [m] a) : m a :=
  match f with
  | Pure x     => pure x
  | Impure u q => extract u >>= (runM \o q)
  end.

Fixpoint handleRelay
  `(ret : a -> Eff effs b)
  `(bind : forall v, eff v -> Arr effs v b -> Eff effs b)
  (f : Eff (eff :: effs) a) : Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := handleRelay ret bind \o q in
    match decomp u with
    | inl x => bind _ x k
    | inr u => Impure u k
    end
  end.

Fixpoint handleRelayS
  `(st : s)
  `(ret : s -> a -> Eff effs b)
  `(bind : forall v, s -> eff v -> (s -> Arr effs v b) -> Eff effs b)
  (f : Eff (eff :: effs) a) : Eff effs b :=
  match f with
  | Pure x => ret st x
  | Impure u q =>
    let k st' := handleRelayS st' ret bind \o q in
    match decomp u with
    | inl x => bind _ st x k
    | inr u => Impure u (k st)
    end
  end.

Fixpoint replaceRelay
  `(ret : a -> Eff (v :: effs) b)
  `(bind : forall x, t x -> Arr (v :: effs) x b -> Eff (v :: effs) b)
  (f : Eff (t :: effs) a) :
  Eff (v :: effs) b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := replaceRelay ret bind \o q in
    match decomp u with
    | inl x => bind _ x k
    | inr u => Impure (weaken u) k
    end
  end.

Fixpoint replaceRelayN
  `{Weakens gs}
  `(pure' : a -> Eff (gs ++ effs) w)
  `(bind : forall x, t x -> Arr (gs ++ effs) x w -> Eff (gs ++ effs) w)
  (f : Eff (t :: effs) a) :
  Eff (gs ++ effs) w :=
  match f with
  | Pure x => pure' x
  | Impure u q =>
    let k := replaceRelayN pure' bind \o q in
    match decomp u with
    | inl x => bind _ x k
    | inr u => Impure (weakens u) k
    end
  end.

Definition interpretWith
  `(bind : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff (eff :: effs) a -> Eff effs a := handleRelay Pure bind.

Definition interpret `(handler : eff ~> Eff effs) :
  Eff (eff :: effs) ~> Eff effs :=
  fun _ => interpretWith (fun _ e f => handler _ e >>= f).

Fixpoint handleInterpose {eff effs a b}
         `{M : Member eff effs}
         (ret : a -> Eff effs b)
         (bind : forall v, eff v -> Arr effs v b -> Eff effs b)
         (f : Eff effs a) : Eff effs b :=
  match f with
  | Pure x => ret x
  | Impure u q =>
    let k := handleInterpose ret bind \o q in
    match @prj eff effs M _ u with
    | Some x => bind _ x k
    | None   => Impure u k
    end
  end.

Definition interposeWith `{Member eff effs}
  `(bind : forall v, eff v -> Arr effs v a -> Eff effs a) :
  Eff effs a -> Eff effs a := handleInterpose Pure bind.

Definition interpose `{Member eff effs} `(handler : eff ~> Eff effs) :
  Eff effs ~> Eff effs :=
  fun _ => interposeWith (fun _ e f => handler _ e >>= f).

Definition subsume `{Member eff effs} : Eff (eff :: effs) ~> Eff effs :=
  interpret (fun _ => send).

Definition reinterpret `(t : f ~> Eff (g :: effs)) :
  Eff (f :: effs) ~> Eff (g :: effs) :=
  fun _ => replaceRelay Pure (fun _ e f => t _ e >>= f).

Definition reinterpretN `{Weakens gs}
  `(k : f ~> Eff (gs ++ effs)) : Eff (f :: effs) ~> Eff (gs ++ effs) :=
  fun _ => replaceRelayN Pure (fun _ e f => k _ e >>= f).

Definition reinterpret2
  `(k : f ~> Eff (g :: h :: effs)) : Eff (f :: effs) ~> Eff (g :: h :: effs) :=
  reinterpretN (gs:=[g; h]) k.

Definition reinterpret3
  `(k : f ~> Eff (g :: h :: i :: effs)) :
  Eff (f :: effs) ~> Eff (g :: h :: i :: effs) :=
  reinterpretN (gs:=[g; h; i]) k.

Definition translate `(t : f ~> g) {effs} : Eff (f :: effs) ~> Eff (g :: effs) :=
  reinterpret (fun _ => send \o t _).

Definition extrude {f effs} : Eff (f :: effs) ~> Eff (f :: f :: effs) :=
  reinterpret2 (fun _ => send \o id).

Fixpoint raise {e} `(f : Eff effs a) : Eff (e :: effs) a :=
  match f with
  | Pure x => Pure x
  | Impure u k => Impure (weaken u) (fun x => raise (k x))
  end.

Definition composed {f g h : Type -> Type}
  `(y : g ~> h) `(x : f ~> g) : f ~> h := fun _ => y _ \o x _.
