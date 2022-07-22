
Declare Custom Entry exp.
Notation "<{ e }>" := e (e custom exp at level 99).

Notation "( x )"  := x (in custom exp, x at level 99).
Notation "x"      := x (in custom exp at level 0, x constr at level 0).
Notation "S ⟶ T" := (TyArrow S T)
                      (in custom exp at level 50, right associativity).

Notation "` 1"   := (VAR ZV)
                      (in custom exp at level 0).
Notation "` 2"   := (VAR (SV ZV))
                      (in custom exp at level 0).
Notation "` 3"   := (VAR (SV (SV ZV)))
                      (in custom exp at level 0).
Notation "x y"   := (APP x y)
                      (in custom exp at level 1, left associativity).
Notation "'λ' y" := (LAM y)
                      (in custom exp at level 90,
                          y custom exp at level 99,
                          left associativity).

Notation "'bool'"  := 𝔹 (in custom exp at level 0).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := (Lit (LitBool true))
                        (in custom exp at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := (Lit (LitBool false))
                        (in custom exp at level 0).

Notation "'if' x 'then' y 'else' z" :=
  (If x y z)
    (in custom exp at level 89,
        x custom exp at level 99,
        y custom exp at level 99,
        z custom exp at level 99,
        left associativity).

Notation "'raise' e" := (Error e) (in custom exp at level 1).

Notation "x + y" := (APP (APP (Bltn AddInt) x) y)
                      (in custom exp at level 1).
Notation "x - y" := (APP (APP (Bltn SubInt) x) y)
                      (in custom exp at level 1).

Notation "' n" := (Symbol n%string)
                    (in custom exp at level 1).

Notation "()" := (Lit LitUnit)
                   (in custom exp at level 1).

Notation "( x , y )" := (Pair x y) (in custom exp at level 1).
Notation "'fst' x"   := (fst x) (at level 1).
Notation "'fst' x"   := (Fst x) (in custom exp at level 1).
Notation "'snd' x"   := (snd x) (at level 1).
Notation "'snd' x"   := (Snd x) (in custom exp at level 1).

Notation "x :: y"    := (Cons x y) (in custom exp at level 1).
Notation "'nil'"     := nil (at level 1).
Notation "'nil'"     := Nil (in custom exp at level 1).
Notation "'car' xs"  := (Car xs) (in custom exp at level 1).
Notation "'cdr' xs"  := (Cdr xs) (in custom exp at level 1).
Notation "'nilp' xs" := (IsNil xs) (in custom exp at level 1).

Notation "x ; y" := (Seq x y) (in custom exp at level 90).
Notation "'$' s" := (Lit (LitString s%string))
                      (in custom exp at level 90).

Notation "{cap n 'arg:' p 'val:' v }" :=
  (Capability ltac:(eauto) ltac:(eauto) n p v)
  (in custom exp at level 1,
      n custom exp at level 99,
      p custom exp at level 99,
      v custom exp at level 99,
      only parsing).

Notation "'require-capability' c" := (RequireCapability c)
                                       (in custom exp at level 1).

(*
Definition foo {Γ} : Exp (ℤ :: ℤ :: Γ) ℤ :=
  <{ if true
     then
       `1 ;
       require-capability {cap '"ALLOW_USER" arg: $"john" val: () } ;
       `2
     else `1 + `2 }>.
*)
