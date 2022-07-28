Require Import
  Coq.Unicode.Utf8
  Coq.Program.Equality
  Coq.Logic.Eqdep.

Ltac reduce_jmeq :=
  repeat match goal with
  | [ H : ∀ _: _, _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl JMeq_refl)

  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl)
  end.

Ltac reduce :=
  reduce_jmeq;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

Ltac branch :=
  repeat match goal with
  | [ H : _ ∨ _ |- _ ] => destruct H
  end.

Ltac matches :=
  lazymatch goal with
  | [ |- context[if ?X _ then _ else _] ] =>
      let Heqe := fresh "Heqe" in
      destruct X eqn:Heqe
  | [ |- context[match ?X with | _ => _ end] ] =>
      let Heqe := fresh "Heqe" in
      destruct X eqn:Heqe
  end; simpl; auto.

Ltac inv H := inversion H; subst; clear H; reduce.

Ltac equality := intuition congruence.
