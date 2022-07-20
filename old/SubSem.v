(************************************************************************
 * SubSem
 *)

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SubSem NoSub      _  := tt;
  SubSem (Push t σ) se := (SemExp t se, SubSem σ se).

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s () = ().
Proof. now dependent elimination s. Qed.

Lemma SubSem_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SubSem (ScR s r) se = SubSem s (RenSem r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp RenSem.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR.
    + now simp SubSem.
    + simp SubSem.
      f_equal.
      * now rewrite SemExp_RenSem.
      * dependent elimination r; simp RenSem;
        now rewrite IHs1.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v (SubSem s se) = SemExp (SubVar s v) se.
Proof.
  intros.
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e (SubSem s se) = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  (* - now rewrite IHe1, IHe2, IHe3. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.
*)

(*
Inductive SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' → Set :=
  SubSem NoSub      _  := inr tt;
  SubSem (Push t σ) se := t' <- SemExp t se ;
                          ρ' <- SubSem σ se ;
                          pure (t', ρ').

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : Err + SemEnv Γ' :=
  SubSem NoSub      _  := inr tt;
  SubSem (Push t σ) se := t' <- SemExp t se ;
                          ρ' <- SubSem σ se ;
                          pure (t', ρ').

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s () = inr ().
Proof. now dependent elimination s. Qed.

Lemma SubSem_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SubSem (ScR s r) se = SubSem s (RenSem r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp RenSem.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR; simp SubSem; auto.
    repeat f_equal; simpl.
    + extensionality z.
      now repeat f_equal.
    + dependent elimination r; simpl in *; simp RenSem in *;
      now rewrite <- SemExp_RenSem.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = inr se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v <$> SubSem s se = SemExp (SubVar s v) se.
Proof.
  intros.
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - dependent elimination v;
    simp SubVar in *; simp SubSem in *; simpl in *.
    rewrite H0 in *; simpl in *.
(*
    dependent elimination v; simpl; simp RenVar; simp SubVar.
    simpl in *.
    destruct (SemExp e se); simpl; auto.
    destruct (SubSem s se); simpl; auto.
    simpl in *.
    cbv.
Qed.
*)

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e =<< SubSem s se = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  (* - destruct (HostExpSem_valid h) as [? H1]. *)
  (*   rewrite H1; simpl. *)
  -
  (* - now rewrite IHe1, IHe2, IHe3. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.

