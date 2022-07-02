Inductive sample : Type :=
  | nothing : sample
  | everything : list sample -> sample.

Section Sample.

Variable P : sample → Type.
Variable Pnothing : P nothing.
Variable Psomething : ∀ (l : list sample), ilist P l -> P (everything l).

Equations sample_rect' (s : sample) : P s :=
  sample_rect' nothing := Pnothing;
  sample_rect' (everything l) := Psomething l (sample_sub_rect' l)
where sample_sub_rect' (l : list sample) : ilist P l :=
  sample_sub_rect' [] := tt;
  sample_sub_rect' (x :: xs) := (sample_rect' x, sample_sub_rect' xs).

End Sample.

Example foo : sample → nat.
Proof.
  intros.
  induction H using sample_rect'.
  admit.

