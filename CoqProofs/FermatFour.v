(*
  Coq port of the wrapper surface from LeanProofs/FermatFour.lean.

  The Lean file imports mathlib's full descent proof of Fermat's Last Theorem
  for exponent 4 (`not_fermat_42` / `fermatLastTheoremFour`) and exposes two
  small project-local theorem names.  Coq's installed standard/contrib
  libraries do not ship an equivalent theorem.  There is a historical
  self-contained Coq formalization in rocq-archive/coq-contribs `fermat4`,
  but it targets Coq 8.0 and is not a drop-in dependency for Rocq 9.0.

  This module therefore proves the local wrapper layer under an explicit
  descent-step parameter.  No global axiom is introduced: downstream users can
  instantiate the section with the classical construction of a smaller
  counterexample from any counterexample.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Lia Ring.

Open Scope Z_scope.

Module LeanProofs.
Module FermatFour.

Definition Fermat42 (a b c : Z) : Prop :=
  a <> 0 /\ b <> 0 /\ (a ^ 4 + b ^ 4 = c ^ 2)%Z.

Definition PythagoreanTriple (x y z : Z) : Prop :=
  (x ^ 2 + y ^ 2 = z ^ 2)%Z.

Definition cMeasure (c : Z) : nat :=
  Z.to_nat (Z.abs c).

Definition Fermat42_descent_step : Prop :=
  forall a b c : Z,
    Fermat42 a b c ->
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.

Definition Fermat42_descent_statement : Prop :=
  forall a b c : Z, a <> 0 -> b <> 0 -> ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).

Theorem Fermat42_comm {a b c : Z} :
    Fermat42 a b c <-> Fermat42 b a c.
Proof.
  unfold Fermat42.
  split.
  - intros (ha & hb & h).
    repeat split; try assumption.
    rewrite Z.add_comm.
    exact h.
  - intros (hb & ha & h).
    repeat split; try assumption.
    rewrite Z.add_comm.
    exact h.
Qed.

Theorem Fermat42_scale {a b c k : Z} (hk : k <> 0) :
    Fermat42 a b c <-> Fermat42 (k * a) (k * b) (k ^ 2 * c).
Proof.
  unfold Fermat42.
  split.
  - intros (ha & hb & h).
    repeat split.
    + intros hka. apply Z.mul_eq_0 in hka as [hk0 | ha0]; tauto.
    + intros hkb. apply Z.mul_eq_0 in hkb as [hk0 | hb0]; tauto.
    + replace ((k * a) ^ 4 + (k * b) ^ 4) with
        (k ^ 4 * (a ^ 4 + b ^ 4)) by ring.
      replace ((k ^ 2 * c) ^ 2) with (k ^ 4 * c ^ 2) by ring.
      now rewrite h.
  - intros (hka & hkb & h).
    repeat split.
    + intros ha. subst a. rewrite Z.mul_0_r in hka. contradiction.
    + intros hb. subst b. rewrite Z.mul_0_r in hkb. contradiction.
    + apply (Z.mul_cancel_l _ _ (k ^ 4)).
      { apply Z.pow_nonzero; lia. }
      replace (k ^ 4 * (a ^ 4 + b ^ 4)) with
        ((k * a) ^ 4 + (k * b) ^ 4) by ring.
      replace (k ^ 4 * c ^ 2) with ((k ^ 2 * c) ^ 2) by ring.
      exact h.
Qed.

Theorem Fermat42_pythagorean_squares {a b c : Z} (h : Fermat42 a b c) :
    PythagoreanTriple (a ^ 2) (b ^ 2) c.
Proof.
  destruct h as (_ & _ & h).
  unfold PythagoreanTriple.
  rewrite <- h.
  ring.
Qed.

Lemma pow4_pos (a : Z) (ha : a <> 0) : 0 < a ^ 4.
Proof.
  assert (hnonneg : 0 <= a ^ 4).
  { apply Z.pow_even_nonneg. exists 2. reflexivity. }
  assert (hnz : a ^ 4 <> 0).
  { apply Z.pow_nonzero; lia. }
  lia.
Qed.

Theorem Fermat42_c_ne_zero {a b c : Z} (h : Fermat42 a b c) :
    c <> 0.
Proof.
  intros hc.
  destruct h as (ha & hb & heq).
  subst c.
  assert (ha4 : 0 < a ^ 4) by now apply pow4_pos.
  assert (hb4 : 0 < b ^ 4) by now apply pow4_pos.
  nia.
Qed.

Theorem no_Fermat42_of_descent (descent : Fermat42_descent_step) :
    forall a b c : Z, ~ Fermat42 a b c.
Proof.
  pose (P := fun n : nat => forall a b c : Z,
    cMeasure c = n -> ~ Fermat42 a b c).
  enough (H : forall n : nat, P n).
  { intros a b c h. exact (H (cMeasure c) a b c eq_refl h). }
  apply (well_founded_induction lt_wf P).
  unfold P.
  intros n ih a b c hc h.
  destruct (descent a b c h) as (a' & b' & c' & h' & hlt).
  assert (hlt_n : (cMeasure c' < n)%nat) by lia.
  exact (ih (cMeasure c') hlt_n a' b' c' eq_refl h').
Qed.

Theorem Fermat42_descent_statement_of_step
    (descent : Fermat42_descent_step) :
    Fermat42_descent_statement.
Proof.
  intros a b c ha hb heq.
  exact (no_Fermat42_of_descent descent a b c (conj ha (conj hb heq))).
Qed.

Section WithDescent.

Variable descent_step : Fermat42_descent_step.

Theorem no_square_right_int_solutions : Fermat42_descent_statement.
Proof.
  exact (Fermat42_descent_statement_of_step descent_step).
Qed.

Theorem fermat_four_no_square_right_int_solutions
    {a b c : Z} (ha : a <> 0) (hb : b <> 0) :
    ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).
Proof.
  exact (no_square_right_int_solutions a b c ha hb).
Qed.

Theorem fermat_four_no_positive_nat_solutions
    {a b c : nat}
    (ha : (0 < a)%nat) (hb : (0 < b)%nat) (_hc : (0 < c)%nat) :
    (a ^ 4 + b ^ 4 <> c ^ 4)%nat.
Proof.
  intro hnat.
  pose proof (f_equal Z.of_nat hnat) as hz.
  rewrite Nat2Z.inj_add in hz.
  repeat rewrite Nat2Z.inj_pow in hz.
  change (Z.of_nat 4) with 4 in hz.
  apply (no_square_right_int_solutions
    (Z.of_nat a) (Z.of_nat b) ((Z.of_nat c) ^ 2)).
  - lia.
  - lia.
  - rewrite hz.
    ring.
Qed.

End WithDescent.

End FermatFour.
End LeanProofs.
