Section Constrained.

(** A partial magma defines a constrained version of its binary operation.
    This operation is typically not associative, since order of operation can
    matter. *)
Class PartialMagma (A : Type) := {
  pappendLim (x y : A) : option A;
}.

Instance nat_PartialMagma (limit : nat) : PartialMagma nat := {
  pappendLim := λ (x y : nat),
    let z := x + y in
    if limit <? z
    then None
    else Some z
}.

End Constrained.
