Require Export
  Coq.Lists.List
  Coq.Unicode.Utf8
  Data.Eq
  Data.Ord.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Map.

Import ListNotations.

Context {k v : Type}.

Fixpoint al_lookup `{Eq k} (i : k) (l : list (k * v)) : option v :=
  match l with
  | [] => None
  | (i', v) :: xs =>
      match eq_dec i i' with
      | left  _ => Some v
      | right _ => al_lookup i xs
      end
  end.

Definition null (l : list (k * v)) : bool.
Abort.

Definition size (l : list (k * v)) : nat.
Abort.

Definition member `{Ord k} (i : k) (l : list (k * v)) : bool
Abort.

Definition lookup `{Ord k} (i : k) : list (k * v) → option v :=
  alist_lookup i ∘ toList.

Definition findWithDefault `{Ord k} (d : v) (i : k) (l : list (k * v)) : v

Definition empty : list (k * v)

Definition singleton (i : k) (x : v) : list (k * v)

Definition insert `{Ord k} (i : k) (x : v) (l : list (k * v)) : list (k * v)

Definition insertWith `{Ord k} (f : v -> v -> v) (i : k) (x : v) (l : list (k * v)) : list (k * v)

Definition insertWithKey `{Ord k} (f : k -> v -> v -> v) (i : k) (x : v) (l : list (k * v)) : list (k * v)

Definition insertLookupWithKey `{Ord k} ((k -> v -> v -> v) (i : k) (x : v) (l : list (k * v)) : (option v * list (k * v))

Definition delete `{Ord k} ((i : k) (l : list (k * v)) : list (k * v)

Definition adjust `{Ord k} (f : v -> v) (i : k) (l : list (k * v)) : list (k * v)

Definition alter `{Ord k} (f : option v -> option v) (i : k) (l : list (k * v)) : list (k * v)

Definition map : (f : v -> v') (l : list (k * v)) : list (k * v')

Definition mapWithKey : (f : k -> v -> v') (l : list (k * v)) : list (k * v')

Definition fold : (f : v -> v' -> v') (x' : v') (l : list (k * v)) : v'

Definition foldrWithKey : (f : k -> v -> v' -> v') (x' : v') (l : list (k * v)) v'

Definition foldlWithKey : (f : v' -> k -> v -> v') (x' : v') (l : list (k * v)) v'

Definition elems : (l : list (k * v)) : list v

Definition keys : (l : list (k * v)) : list k

Definition assocs : (l : list (k * v)) : list (k * v)

Definition filter `{Ord k} (f : v -> bool) (l : list (k * v)) : list (k * v)

Definition mapMaybe `{Ord k} (f : v -> option v') (l : list (k * v)) : list (k * v')

(****************************************************************************)

Inductive Map (k v : Type) :=
  | mkMap : list (k * v)%type → Map k v.

Definition toList (m : Map k v) : list (k * v) :=
  match m with mkMap _ _ l => l end.

Definition fromList : list (k * v) → Map k v := mkMap _ _.

Definition null : Map k v -> Bool

Definition size : Map k v -> Int

Definition member : Ord k => k -> Map k v -> Bool

Definition lookup `{Ord k} (i : k) : Map k v → option v :=
  alist_lookup i ∘ toList.

Definition findWithDefault : Ord k => v -> k -> Map k v -> v

Definition empty : Map k v

Definition singleton : k -> v -> Map k v

Definition insert : Ord k => k -> v -> Map k v -> Map k v

Definition insertWith : Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v

Definition insertWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v

Definition insertLookupWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> (Maybe v, Map k v)

Definition delete : Ord k => k -> Map k v -> Map k v

Definition adjust : Ord k => (v -> v) -> k -> Map k v -> Map k v

Definition alter : Ord k => (Maybe v -> Maybe v) -> k -> Map k v -> Map k v

Definition map : (v -> b) -> Map k v -> Map k b

Definition mapWithKey : (k -> v -> b) -> Map k v -> Map k b

Definition fold : (v -> b -> b) -> b -> Map k v -> b

Definition foldrWithKey : (k -> v -> b -> b) -> b -> Map k v -> b

Definition foldlWithKey : (b -> k -> v -> b) -> b -> Map k v -> b

Definition elems : Map k v -> [v]

Definition keys : Map k v -> [k]

Definition assocs : Map k v -> list (k * v)

Definition filter : Ord k => (v -> Bool) -> Map k v -> Map k v

Definition mapMaybe : Ord k => (v -> Maybe b) -> Map k v -> Map k b
