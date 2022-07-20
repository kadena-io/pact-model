Set Warnings "-cannot-remove-as-expected".

Require Import
  Lib
  Ty
  Exp
  Value
  Ren
  Sub
  Sem
  Log.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Evaluation contexts *)

Section Step.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

(*

(* A context defines a hole which, after substitution, yields an expression of
   the index type. *)
Inductive Frame Γ : Ty → Ty → Type :=
  (* | C_If1 {τ} : Frame Γ τ' TyBool → Exp Γ τ → Exp Γ τ → Frame Γ τ' TyBool *)
  (* | C_If2 {τ} : Exp Γ TyBool → Frame Γ τ → Exp Γ τ → Frame Γ τ *)
  (* | C_If3 {τ} : Exp Γ TyBool → Exp Γ τ → Frame Γ τ → Frame Γ τ *)

  | F_AppL {dom cod} : Exp Γ dom → Frame Γ (dom ⟶ cod) cod
  | F_AppR {dom cod} : Exp Γ (dom ⟶ cod) → Frame Γ dom cod.

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Frame.

Inductive Ctxt Γ : Ty → Ty → Type :=
  | C_Nil {τ}         : Ctxt Γ τ τ
  | C_Cons {τ τ' τ''} : Frame Γ τ' τ → Ctxt Γ τ'' τ' → Ctxt Γ τ'' τ.

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Ctxt.

(* [Ctxt] forms a category with objects = types and morphisms = contexts. *)

Definition Ctxt_id {Γ τ} : Ctxt Γ τ τ := C_Nil _.
Arguments Ctxt_id {_ _} /.

Program Fixpoint Ctxt_comp {Γ τ τ' τ''}
        (C : Ctxt Γ τ' τ) (C' : Ctxt Γ τ'' τ') : Ctxt Γ τ'' τ :=
  match C with
  | C_Nil _      => C'
  | C_Cons _ f c => C_Cons _ f (Ctxt_comp c C')
  end.

Theorem Ctxt_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp Ctxt_id C = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_id_right {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp C Ctxt_id = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_comp_assoc {Γ τ τ' τ'' τ'''}
        {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'} {C'' : Ctxt Γ τ''' τ''} :
  Ctxt_comp C (Ctxt_comp C' C'') = Ctxt_comp (Ctxt_comp C C') C''.
Proof. induction C; simpl; auto; now f_equal. Qed.

Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | R_Beta {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e).

Derive Signature for Redex.

Unset Elimination Schemes.

Inductive Plug {Γ τ'} (e : Exp Γ τ') : ∀ {τ}, Ctxt Γ τ' τ → Exp Γ τ → Prop :=
  | Plug_Hole : Plug e (C_Nil _) e

  (* | Plug_If1 {Γ τ} (C : Ctxt Γ TyBool) (e e' : Exp Γ TyBool) (e1 e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If1 _ C e1 e2) e (If e' e1 e2) *)
  (* | Plug_If2 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If2 _ e1 C e2) e (If e1 e' e2) *)
  (* | Plug_If3 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If3 _ e1 e2 C) e (If e1 e2 e') *)

  | Plug_AppL {dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e' : Exp Γ (dom ⟶ cod)} {e2 : Exp Γ dom} :
    Plug e C e' →
    Plug e (C_Cons _ (F_AppL _ e2) C) (APP e' e2)

  | Plug_AppR {dom cod} {C : Ctxt Γ τ' dom}
              {e' : Exp Γ dom} {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug e C e' →
    Plug e (C_Cons _ (F_AppR _ e1) C) (APP e1 e').

Derive Signature for Plug.

Set Elimination Schemes.

Scheme Plug_ind := Induction for Plug Sort Prop.

(* [Plug] forms a category with objects = expressions and morphisms = plugs
   over existential contexts. *)

Definition Plug_id {Γ τ} {x : Exp Γ τ} : Plug x (C_Nil Γ) x := Plug_Hole _.
Arguments Plug_id {_ _ _} /.

Fixpoint Plug_comp {Γ τ τ' τ''}
         {x : Exp Γ τ''} {y : Exp Γ τ'} {z : Exp Γ τ}
         {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'}
         (P : Plug x C' y) (P' : Plug y C z) :
  Plug x (Ctxt_comp C C') z :=
  match P' with
  | Plug_Hole _      => P
  | Plug_AppL _ p'   => Plug_AppL _ (Plug_comp P p')
  | Plug_AppR _ V p' => Plug_AppR _ V (Plug_comp P p')
  end.

(* This should be provable, but the dependent types get in the way. *)
Theorem Plug_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
        (P : Plug x C y) :
  Plug_comp Plug_id P ~= P.
Proof.
  dependent induction P; simpl in *; auto.
Abort.
(*
  - rewrite (Plug_comp_equation_3 _ _ _ _ _ _ _ _ _ _ _ Plug_id _ P).
    pose proof (@Ctxt_id_right _ _ _ C).
    simpl in *.
    Fail now rewrite IHP.
*)

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step {Γ τ} : Exp Γ τ → Exp Γ τ → Prop :=
  | StepRule {τ'} {C : Ctxt Γ τ' τ} {e1 e2 : Exp Γ τ'} {e1' e2' : Exp Γ τ} :
    Plug e1 C e1' →
    Plug e2 C e2' →
    Redex e1 e2 →
    e1' ---> e2'

  | StepError {τ' τ''} {F : Frame Γ τ' τ} {C : Ctxt Γ τ'' τ'}
              {m : Err} {e' : Exp Γ τ} :
    Plug (Error m) (C_Cons _ F C) e' →
    e' ---> Error m

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP ErrorP Plug Redex Step : core.

*)

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Prop :=
(*
  | ST_Seq1 Γ τ τ' (e1 e1' : Exp Γ τ') (e2 : Exp Γ τ) :
    e1 ---> e1' →
    Seq e1 e2 ---> Seq e1' e2
  | ST_Seq1Err Γ τ τ' (m : Err) (e2 : Exp Γ τ) :
    Seq (τ':=τ') (Error m) e2 ---> Error m
  | ST_Seq2 Γ τ τ' (e1 : Exp Γ τ') (e2 : Exp Γ τ) :
    ValueP e1 →
    Seq e1 e2 ---> e2

  | ST_Host Γ τ (h : HostExp τ) :
    HostedExp h ---> projT1 (Reduce (Γ:=Γ) h)

  | ST_IfTrue Γ τ (t e : Exp Γ τ) :
    If ETrue t e ---> t
  | ST_IfFalse Γ τ (t e : Exp Γ τ) :
    If EFalse t e ---> e
  | ST_If Γ b b' τ (t e : Exp Γ τ) :
    b ---> b' →
    If b t e ---> If b' t e
  | ST_IfErr Γ τ (m : Err) (t e : Exp Γ τ) :
    If (Error m) t e ---> Error m

  | ST_Pair1 Γ τ1 τ2 (x x' : Exp Γ τ1) (y : Exp Γ τ2) :
    x ---> x' →
    Pair x y ---> Pair x' y
  | ST_Pair2 Γ τ1 τ2 (x : Exp Γ τ1) (y y' : Exp Γ τ2) :
    ValueP x →
    y ---> y' →
    Pair x y ---> Pair x y'
  | ST_Pair1Err Γ τ1 τ2 (m : Err) (y : Exp Γ τ2) :
    Pair (τ1:=τ1) (Error m) y ---> Error m
  | ST_Pair2Err Γ τ1 τ2 (x : Exp Γ τ1) (m : Err) :
    ValueP x →
    Pair (τ2:=τ2) x (Error m) ---> Error m

  | ST_Fst1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Fst p ---> Fst p'
  | ST_Fst1Err Γ τ1 τ2 (m : Err) :
    Fst (Γ:=Γ) (τ1:=τ1) (τ2:=τ2) (Error m) ---> Error m
  | ST_FstPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Fst (Pair v1 v2) ---> v1

  | ST_Snd1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Snd p ---> Snd p'
  | ST_Snd1Err Γ τ1 τ2 (m : Err) :
    Snd (Γ:=Γ) (τ1:=τ1) (τ2:=τ2) (Error m) ---> Error m
  | ST_SndPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Snd (Pair v1 v2) ---> v2

  | ST_Cons1 Γ τ (x : Exp Γ τ) x' (xs : Exp Γ (TyList τ)) :
    x ---> x' →
    Cons x xs ---> Cons x' xs
  | ST_Cons2 Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) xs' :
    ValueP x →
    xs ---> xs' →
    Cons x xs ---> Cons x xs'
  | ST_Cons1Err Γ τ (m : Err) (xs : Exp Γ (TyList τ)) :
    Cons (Error m) xs ---> Error m
  | ST_Cons2Err Γ τ (x : Exp Γ τ) (m : Err) :
    ValueP x →
    Cons x (Error m) ---> Error m

  | ST_Car1 Γ τ (l l' : Exp Γ (TyList τ)) :
    l ---> l' →
    Car l ---> Car l'
  | ST_Car1Err Γ τ (m : Err) :
    Car (Γ:=Γ) (τ:=τ) (Error m) ---> Error m
  | ST_CarNil Γ τ :
    Car (Nil (Γ:=Γ) (τ:=τ)) ---> Error CarOfNil
  | ST_CarCons Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP x →
    ValueP xs →
    Car (Cons x xs) ---> x

  | ST_Cdr1 Γ τ (l l' : Exp Γ (TyList τ)) :
    l ---> l' →
    Cdr l ---> Cdr l'
  | ST_Cdr1Err Γ τ (m : Err) :
    Cdr (Γ:=Γ) (τ:=τ) (Error m) ---> Error m
  | ST_CdrNil Γ τ :
    Cdr (Nil (Γ:=Γ) (τ:=τ)) ---> Nil
  | ST_CdrCons Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP x →
    ValueP xs →
    Cdr (Cons x xs) ---> xs

  | ST_IsNil1 Γ τ (l l' : Exp Γ (TyList τ)) :
    l ---> l' →
    IsNil l ---> IsNil l'
  | ST_IsNil1Err Γ τ (m : Err) :
    IsNil (Γ:=Γ) (τ:=τ) (Error m) ---> Error m
  | ST_IsNilNil Γ τ :
    IsNil (Nil (Γ:=Γ) (τ:=τ)) ---> ETrue
  | ST_IsNilCons Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP x →
    ValueP xs →
    IsNil (Cons x xs) ---> EFalse

  | ST_AppHost Γ dom cod (f : HostExp (dom ⟶ cod)) (v : Exp Γ dom) :
    ∀ H : ValueP v,
    APP (HostedFun f) v ---> CallHost f v H
*)

  | ST_AppAbs Γ dom cod (e : Exp (dom :: Γ) cod) (v : Exp Γ dom) :
    ValueP v →
    APP (LAM e) v ---> SubExp {|| v ||} e

  | ST_AppL Γ dom cod (e1 : Exp Γ (dom ⟶ cod)) e1' (e2 : Exp Γ dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2
  | ST_AppLErr Γ dom cod (m : Err) (e2 : Exp Γ dom) :
    APP (dom:=dom) (cod:=cod) (Error m) e2 ---> Error m

  | ST_AppR Γ dom cod (v1 : Exp Γ (dom ⟶ cod)) (e2 : Exp Γ dom) e2' :
    ValueP v1 →
    e2 ---> e2' →
    APP v1 e2 ---> APP v1 e2'
  | ST_AppRErr Γ dom cod (v1 : Exp Γ (dom ⟶ cod)) (m : Err) :
    ValueP v1 →
    APP v1 (Error m) ---> Error m

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP ErrorP Step : core.

#[local] Hint Extern 1 (¬ ErrorP _) => inversion 1 : core.
#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ErrorP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now right; left; eexists.
  - now left; constructor.
  - now inv v.
  - now left; constructor.
  - right.
    destruct IHe1 as [V1|[E1|[e1' H1']]];
    destruct IHe2 as [V2|[E2|[e2' H2']]].
    + dependent elimination V1;  now eauto 6.
    + dependent elimination V1;
      dependent elimination E2;  now eauto 6.
    + dependent elimination H2'; now eauto 6.
    + dependent elimination V2;
      dependent elimination E1;  now eauto 6.
    + dependent elimination E1;  now eauto 6.
    + dependent elimination E1;  now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1';
      dependent elimination H2'; now eauto 6.
Qed.

(*
Lemma Plug_value {Γ τ} {C : Ctxt Γ τ τ} (e v : Exp Γ τ) :
  ValueP v → Plug e C v → C = C_Nil _ ∧ e = v.
Proof.
  intros.
  dependent elimination H0;
  now inv H1.
Qed.

Lemma Plug_error {Γ τ} {C : Ctxt Γ τ τ} (e v : Exp Γ τ) :
  ErrorP v → Plug e C v → C = C_Nil _ ∧ e = v.
Proof.
  intros.
  dependent elimination H0;
  now inv H1.
Qed.

Lemma Value_not_redex {Γ τ} (e v : Exp Γ τ) :
  ValueP v → ¬ Redex v e.
Proof.
  repeat intro.
  dependent elimination H0;
  now inv H1.
Qed.

Lemma Error_not_redex {Γ τ} (e v : Exp Γ τ) :
  ErrorP v → ¬ Redex v e.
Proof.
  repeat intro.
  dependent elimination H0;
  now inv H1.
Qed.
*)

Lemma Value_irreducible {Γ τ} {e e' : Exp Γ τ} :
  ValueP e → ¬ (e ---> e').
Proof.
  repeat intro.
  dependent elimination H0;
  dependent elimination H1.
  (* - inv p. *)
  (*   now inv r. *)
  (* - now inv p1. *)
  (* - inv p. *)
  (*   now inv r. *)
  (* - now inv p1. *)
Qed.

Lemma Value_cannot_start {Γ τ} {e e' : Exp Γ τ} :
  (e ---> e') → ¬ ValueP e.
Proof.
  repeat intro.
  dependent elimination H0;
  dependent elimination H1.
  (* - inv p. *)
  (*   now inv r. *)
  (* - now inv p. *)
  (* - inv p1. *)
  (* - now inv p1. *)
Qed.

Lemma Error_irreducible {Γ τ} {e e' : Exp Γ τ} :
  ErrorP e → ¬ (e ---> e').
Proof.
  repeat intro.
  dependent elimination H0;
  dependent elimination H1.
  (* - inv p. *)
  (*   now inv r. *)
  (* - now inv p1. *)
Qed.

Lemma Error_cannot_start {Γ τ} {e e' : Exp Γ τ} :
  (e ---> e') → ¬ ErrorP e.
Proof.
  repeat intro.
  dependent elimination H0;
  dependent elimination H1.
  (* - inv p. *)
  (*   now inv r. *)
  (* - now inv p1. *)
Qed.

(*
Lemma Plug_deterministic {Γ τ} e2 :
  ∀ τ' (C : Ctxt Γ τ' τ) e1 e1',
    Redex e1 e1' → Plug e1 C e2 →
  ∀ τ'' (C' : Ctxt Γ τ'' τ) f1 f1',
    Redex f1 f1' → Plug f1 C' e2 →
    τ' = τ'' ∧ C ~= C' ∧ e1 ~= f1.
Proof.
  intros τ' C e1 e1' R1 P1 τ'' C' f1 f1' R2 P2.
  generalize dependent C'.
  induction P1; intros; subst.
  inv P2; auto.
  - exfalso.
    dependent elimination R1.
    dependent elimination R2.
    now inv H3.
  - exfalso.
    dependent elimination R1.
    dependent elimination R2.
    now inv H4.
  - dependent elimination P2.
    + exfalso.
      dependent elimination R1.
      dependent elimination R2.
      now inv P1.
    + intuition.
      now destruct (IHP1 _ p); reduce.
    + exfalso.
      dependent elimination R1.
      dependent elimination R2.
      now inv P1.
  - dependent elimination P2.
    + exfalso.
      dependent elimination R1.
      dependent elimination R2.
      now inv P1.
    + exfalso.
      dependent elimination R1.
      dependent elimination R2.
      now inv p.
    + intuition.
      now destruct (IHP1 _ p0); reduce.
Qed.

Lemma Plug_error_deterministic {Γ τ} {e : Exp Γ τ} :
  ∀ τ' {C : Ctxt Γ τ' τ} x,
    Plug (Error x) C e →
  ∀ τ'' (C' : Ctxt Γ τ'' τ) x',
    Plug (Error x') C' e →
    τ' = τ'' ∧ x = x' ∧ C ~= C'.
Proof.
  intros τ' C x P1 τ'' C' x' P2.
  intros.
  generalize dependent C'.
  generalize dependent x'.
  generalize dependent τ''.
  induction P1; intros; subst.
  - now dependent elimination P2.
  - dependent elimination P2.
    + now destruct (IHP1 _ _ _ p); reduce.
    + exfalso.
      clear -P1 v.
      dependent elimination v.
      now inv P1.
  - dependent elimination P2.
    + exfalso.
      clear -p v.
      dependent elimination v.
      now inv p.
    + now destruct (IHP1 _ _ _ p0); reduce.
Qed.

(*
Lemma Plug_errors_block_redex {Γ τ} e2 :
  ∀ τ' (C : Ctxt Γ τ' τ) n e y,
    Plug (Error y) n C e →
  ∀ τ'' (C' : Ctxt Γ τ'' τ) m f1 f1',
    Redex f1 f1' → Plug f1 m C' e2 →
    τ' = τ'' ∧ n = m ∧ C ~= C' ∧ e1 ~= f1.
*)

Lemma Plug_functional {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e C e1 → ∀ e2, Plug e C e2 → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H1.
  - dependent destruction H1.
    now f_equal; auto.
  - dependent destruction H1.
    now f_equal; auto.
Qed.

Lemma Plug_injective {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e1 C e → ∀ e2, Plug e2 C e → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H1.
  - dependent destruction H1.
    now f_equal; auto.
  - dependent destruction H1.
    now f_equal; auto.
Qed.

Lemma Redex_deterministic {Γ τ} {e : Exp Γ τ} :
  ∀ e', Redex e e' → ∀ e'', Redex e e'' → e' = e''.
Proof.
  intros.
  dependent elimination H0.
  dependent elimination H1.
  reflexivity.
Qed.
*)

(*
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + simp SubVar in H1.
  (*     now induction v; inv H1; intuition. *)
  (*   + simp SubVar in H1. *)
  (*     rewrite SubVar_idSub in H1. *)
  (*     now induction v0; inv H1; intuition. *)
*)

(*
Lemma If_loop_true {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = x).
Proof.
  induction x; intro; inv H.
  now eapply IHx2; eauto.
Qed.

Lemma If_loop_false {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy3; eauto.
Qed.

Lemma Seq_loop {Γ τ ty} {x : Exp Γ ty} {y : Exp Γ τ} :
  ¬ (Seq x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy2; eauto.
Qed.
*)

(*
#[export]
Program Instance RenExp_Step {Γ Γ' τ} (σ : Ren Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (RenExp σ).
Next Obligation.
  intros.
  induction H0; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply RenExp_ValueP ].
  (* - now apply Reduce_preserves_renaming. *)
  (* - now apply CallHost_preserves_renaming. *)
Abort.
*)
(*
  - dependent elimination H2.
    (* epose proof (StepRule (Plug_AppR _ H0) *)
    (*                       (Plug_AppR _ H1) H3). *)
    dependent induction H2.
    + inv H1; simpl.
      rewrite <- SubExp_ScR.
      simp ScR.
      rewrite <- RcS_idSub.
      pose proof (SubExp_RcS (Keep σ) (Push (RenExp σ v) idSub) e) as H1.
      simp RcS in H1.
      rewrite H1.
      repeat econstructor.
      now apply RenExp_ValueP.
    + specialize (IHPlug _ _ _ _ _ eq_refl H1 v0).
      apply IHPlug.
      dependent destruction H1; simpl.

      repeat econstructor.
      epose proof (StepRule (Plug_AppL p)
                            (Plug_AppL H1)).

Qed.
*)

(*
#[export]
Program Instance SubExp_Step {Γ Γ' τ} (σ : Sub Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (SubExp σ).
Next Obligation.
  intros.
Abort.
*)
(*
  induction H; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply SubExp_ValueP ].
  (* - now apply Reduce_preserves_substitution. *)
  (* - now apply CallHost_preserves_substitution. *)
  - rewrite <- SubExp_ScS.
    simpl ScS.
    rewrite ScS_idSub_left.
    pose proof (SubExp_ScS (Keepₛ σ) (Push (SubExp σ v) idSub) e) as H1.
    simpl in H1.
    simp SubVar in H1.
    unfold Dropₛ in H1.
    rewrite ScS_ScR in H1.
    rewrite RcS_skip1 in H1.
    rewrite ScS_idSub_right in H1.
    rewrite H1.
    constructor.
    now apply SubExp_ValueP.
Qed.
*)

(*
Lemma pluggable {Γ τ} {e1 e2 : Exp Γ τ} {τ'}
      {C : Ctxt Γ τ' τ} {f1 f2 : Exp Γ τ'} :
  ¬ ErrorP e1 →
  f1 ---> f2 →
  Plug f1 C e1 →
  Plug f2 C e2 →
  e1 ---> e2.
Proof.
  intros.
  dependent induction H1.
  - exact (StepRule (Plug_comp H1 H4) (Plug_comp H2 H5) H3).
  - exfalso.
    dependent elimination H1.
Abort.
*)

Lemma SubVar_ZV_of_value_never_error {Γ τ} {x : Exp Γ τ} :
  ValueP x → ∀ m, ¬ (SubVar {|| x ||} ZV = Error m).
Proof.
  intros.
  inv H0; simp SubVar;
  now intro.
Qed.

Lemma SubVar_SV_of_value_never_error {Γ τ}
      {x : Exp Γ τ} (v : Var Γ τ) :
  ValueP x → ∀ m, ¬ (SubVar {|| x ||} (SV v) = Error m).
Proof.
  intros.
  induction v; simp SubVar;
  rewrite SubVar_idSub;
  now intro.
Qed.

Lemma SubVar_of_value_never_error {Γ τ ty}
      {x : Exp Γ ty} (v : Var (ty :: Γ) τ) :
  ValueP x → ∀ m, ¬ (SubVar {|| x ||} v = Error m).
Proof.
  intros.
  pose proof (SubVar_ZV_of_value_never_error H0 m).
  dependent elimination v; simp SubVar in *.
  rewrite SubVar_idSub.
  intro.
  apply H1.
  now inv H2.
Qed.

Lemma SubExp_of_value_never_error {Γ τ ty}
      {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ValueP v → ¬ ErrorP e → ∀ m, ¬ (SubExp {||v||} e = Error m).
Proof.
  intros.
  dependent elimination e; simpl.
  - exfalso.
    now apply H1.
  - now intro.
  - now apply SubVar_of_value_never_error.
  - now intro.
  - now intro.
Qed.

Lemma SubExp_error {Γ τ ty}
      {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} {m} :
  ValueP v → SubExp {||v||} e = Error m → e = Error m.
Proof.
  intros.
  dependent elimination e; simpl in *.
  - now inv H1.
  - congruence.
  - pose proof (SubVar_of_value_never_error v0 H0 m).
    contradiction.
  - congruence.
  - congruence.
Qed.

(*
Lemma Step_Error_ind (Γ : Env) (τ : Ty) (e0 : Exp Γ τ) (m0 : Err)
      (P : ∀ τ (e : Exp Γ τ) m, e ---> Error m → Prop)
      (Pbeta : ∀ dom (e : Exp (dom :: Γ) τ) v (V : ValueP v) m
                 (r : Redex (APP (LAM e) v) (Error m)),
          e0 = APP (LAM e) v →
          m = m0 →
          P τ (APP (LAM e) v) m
            (StepRule (C:=C_Nil _) (Plug_Hole _) (Plug_Hole _) r))
      (Preduce : ∀ τ' τ'' (e : Exp Γ τ) (F : Frame Γ τ' τ) (C : Ctxt Γ τ'' τ') m
                   (p : Plug (Error m) (C_Cons _ F C) e),
          e0 = e →
          m = m0 →
          P τ e m (StepError p)):
  ∀ (s : e0 ---> Error m0), P τ e0 m0 s.
Proof.
  intros.
  dependent elimination s.
  - dependent elimination r.
    dependent destruction p0.
    pose proof (SubExp_error v0 x0); subst.
    dependent destruction p.
    simpl.
    now apply Pbeta.
  - now apply Preduce.
Qed.

(** A single expression can be plugged in multiple ways. *)
Lemma Plug_can_diverge {Γ τ} {e : Exp (TyUnit :: Γ) τ}
      {e' : Exp Γ (TyUnit ⟶ TyUnit)} {m : Err} :
  let f := APP (LAM (VAR ZV))
               (APP (LAM (VAR ZV))
                    EUnit) in
  Plug (Γ:=Γ) (LAM (VAR ZV))
       (C_Cons _ (F_AppL _ (APP (LAM (VAR ZV)) EUnit)) (C_Nil _)) f ∧
  Plug (Γ:=Γ) (LAM (VAR ZV))
       (C_Cons _ (F_AppR _ (LAM (VAR ZV)))
               (C_Cons _ (F_AppL _ EUnit) (C_Nil _))) f.
Proof. now simpl; eauto 6. Qed.
*)

(*
Theorem diamond_property {Γ τ} {r s t : Exp Γ τ} {m : Err} :
  r ---> s → r ---> t → s ≠ t → ∃ u, s ---> u ∧ t ---> u.
Proof.
  intros Hrs Hrt snt.
  induction Hrs, Hrt.
  - assert (τ' = τ'0 ∧ C ~= C0 ∧ e1 ~= e0)
        by (eapply Plug_deterministic; eassumption).
    reduce.
    pose proof (Redex_deterministic _ H2 _ H5).
    subst.
    pose proof (Plug_functional _ _ H1 _ H4).
    contradiction.
  - exfalso.
    inv H2.
    ...
  - exfalso.
    ...
  - pose proof (Plug_error_deterministic _ _ H0 _ _ _ H1).
    reduce.
    contradiction.
Abort.
*)

Theorem diamond_property {Γ τ} {r s t : Exp Γ τ} :
  r ---> s → r ---> t → s ≠ t → ∃ u, s ---> u ∧ t ---> u.
Proof.
  intros Hrs Hrt snt.
  dependent induction r; try now inv Hrs.
  intuition auto.
Abort.

(*
Lemma Step_Error_impl {Γ τ} {e' : Exp Γ τ} {m : Err} :
  e' ---> Error m →
      (∃ dom (v : Exp Γ dom) (e : Exp (dom :: Γ) τ),
         (∀ τ' τ'' (F : Frame Γ τ' τ) (C : Ctxt Γ τ'' τ'),
            ¬ Plug (Error m) (C_Cons _ F C) e') ∧
         ValueP v ∧ e' = APP (LAM e) v ∧ Redex e' (Error m))
    ∨ (∃ τ' τ'' (F : Frame Γ τ' τ) (C : Ctxt Γ τ'' τ'),
         (∀ τ' (e : Exp Γ τ') C',
            ¬ (e ≠ Error m ∧ Plug e C' e')) ∧
         Plug (Error m) (C_Cons _ F C) e').
Proof.
  intros.
  dependent elimination H0.
  - dependent elimination r.
    dependent destruction p0.
    pose proof (SubExp_error v0 x); subst.
    dependent destruction p.
    left.
    repeat eexists; eauto.
    repeat intro.
    inv H0.
    inv H3.
    inv H9;
    inv v0.
  - right.
    repeat eexists.
    + repeat intro; reduce.
      apply H0; clear H0.
      generalize dependent τ'.
      induction p1; intros.
      * inv H1; auto.
      * ...
      * ...
    + now apply p1.
Qed.
*)

Lemma AppL_LAM {Γ dom cod} {e e' : Exp Γ (dom ⟶ cod)} {x : Exp Γ dom} :
  ¬ ErrorP e' →
  e ---> e' →
  APP e x ---> APP e' x.
Proof.
  intros.
  dependent induction H1; now eauto 6.
Qed.

Corollary AppL_LAM_error {Γ dom cod} {x : Exp Γ dom} m :
  APP (Error (τ:=dom ⟶ cod) m) x ---> Error m.
Proof. now eauto 6. Qed.

Lemma AppR_LAM {Γ dom cod} {e : Exp (dom :: Γ) cod} {x x' : Exp Γ dom} :
  ¬ ErrorP x' →
  x ---> x' →
  APP (LAM e) x ---> APP (LAM e) x'.
Proof.
  intros.
  dependent induction H1; now eauto 6.
Qed.

Corollary AppR_LAM_error {Γ dom cod} {v : Exp Γ (dom ⟶ cod)} m :
  ValueP v →
  APP v (Error (τ:=dom) m) ---> Error m.
Proof. now eauto 6. Qed.

(* Definition normal_form `(R : relation X) (t : X) : Prop := *)
(*   ¬ ∃ t', R t t'. *)
Definition normal_form `(R : relation X) (t : X) : Prop :=
  ∀ t', ¬ R t t'.

Definition deterministic `(R : relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
Proof.
  repeat intro.
  dependent elimination H0.
  dependent induction H1.
  now inv H1.
Qed.

Lemma error_is_nf {Γ τ} (v : Exp Γ τ) :
  ErrorP v → normal_form Step v.
Proof.
  repeat intro.
  dependent elimination H0.
  dependent induction H1.
Qed.

Lemma nf_is_value_or_error {τ} (v : Exp [] τ) :
  normal_form Step v → ValueP v ∨ ErrorP v.
Proof.
  intros.
  destruct (strong_progress v); intuition eauto; reduce.
  now edestruct H0; eauto.
Qed.

Theorem nf_same_as_value_or_error {τ} (v : Exp [] τ) :
  normal_form Step v ↔ ValueP v ∨ ErrorP v.
Proof.
  split.
  - now apply nf_is_value_or_error.
  - intros [?|?].
    + now apply value_is_nf.
    + now apply error_is_nf.
Qed.

(*
Definition aborts {Γ} (m : Err) := λ τ (x : Exp Γ τ), x ---> Error m.
Arguments aborts {Γ} m /.

Definition HasError {Γ τ} (m : Err) := ExpP (Γ:=Γ) (τ:=τ) (aborts m).

Definition has_error_impl {Γ τ} {x : Exp Γ τ} {m} :
  HasError m x → x ---> Error m := ExpP_P _.

Lemma has_error_propagates {Γ τ} {x : Exp Γ τ} {m} :
  HasError m x → ∀ y, x ---> y → HasError m y.
Proof.
  unfold HasError.
  intros H0 y S1.
  generalize dependent x.
  generalize dependent y.
  generalize dependent m.
  induction τ; simpl; simp ExpP; intros; simp ExpP in *.
  - dependent elimination H0;
    dependent elimination S1.
Abort.

Lemma have_error {Γ τ} {x : Exp Γ τ} {m} :
  x ---> Error m → HasError m x.
Proof.
  unfold HasError.
  intros.
  generalize dependent x.
  generalize dependent m.
  induction τ; simpl; simp ExpP;
  intros; simp ExpP in *.
  intuition.
  eapply IHτ2.
  apply has_error_impl in H1.
  eapply Step_Error_ind; intuition eauto; subst.
  rewrite H2.
  dependent elimination H1;
  now apply AppL_LAM_error.
Qed.
*)

Lemma errors_deterministic {Γ τ} {x : Exp Γ τ} {m} :
  x ---> Error m → ∀ y, x ---> y → y = Error m.
Proof.
  intros.
  inv H0;
  inv H1; auto.
  inv H4.
Abort.

Theorem Step_deterministic Γ τ :
  deterministic (Step (Γ:=Γ) (τ:=τ)).
Proof.
  repeat intro.
  induction H0.
  - inv H1; auto.
    + now inv H5.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + now inv H0.
  - inv H1.
    + now inv H0.
    + now f_equal; intuition.
    + now inv H0.
    + eapply Value_cannot_start in H6; eauto; tauto.
    + eapply Value_cannot_start in H5; eauto; tauto.
  - inv H1; auto.
    + now inv H4.
    + now inv H5.
    + now inv H4.
  - inv H1.
    + eapply Value_cannot_start in H6; eauto; tauto.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + now inv H0.
    + now f_equal; intuition.
    + now inv H2.
  - inv H1; auto.
    + now inv H5.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + now inv H0.
    + now inv H9.
Qed.

End Step.

Notation " t '--->' t' " := (Step t t') (at level 40).

Section Irr.

Import ListNotations.

Lemma App_Lam_loop_var `{HostExprs A}
      {Γ τ ty} {v : Exp Γ ty} {v0 : Var (ty :: Γ) τ} :
  ¬ (SubVar {||v||} v0 = APP (LAM (VAR v0)) v).
Proof.
  intro.
  dependent induction v0;
  simp SubVar in H0.
  - induction v; inv H0.
    now eapply IHv2; eauto.
  - rewrite SubVar_idSub in H0.
    now inv H0.
Qed.

Lemma App_Lam_loop `{HostExprs A}
      {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (SubExp {||v||} e = APP (LAM e) v).
Proof.
  intro H0.
  generalize dependent v.
  dependent induction e; simpl; intros;
  try congruence.
  - now eapply App_Lam_loop_var; eauto.
  - inv H0.
    (* impossible *)
Abort.

(* A term never reduces to itself. *)
#[export]
Program Instance Step_Irreflexive `{HostExprs A} {Γ τ} :
  Irreflexive (Step (Γ:=Γ) (τ:=τ)).
Next Obligation.
  dependent induction H0; try tauto.
  now eapply App_Lam_loop; eauto.
Qed.

Corollary Step_productive `{HostExprs A} {Γ τ} {x x' : Exp Γ τ} :
  x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  eapply Step_Irreflexive.
  exact H0.
Qed.

End Irr.
