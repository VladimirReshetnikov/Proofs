(*
  Coq port of the rational core of LeanProofs/FloorSqrtSum.lean.

  The Lean file proves the identity first over Rat and then casts back to Nat.
  This Coq port records the rational theorem directly; it is the algebraic
  heart of the argument and avoids a separate natural-division normalization
  layer for now.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith.

Open Scope Q_scope.

Module LeanProofs.
Module FloorSqrtSum.

Definition Qnat (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Fixpoint sumFloorSqrt (n : nat) : nat :=
  match n with
  | O => O
  | S n' => sumFloorSqrt n' + Nat.sqrt (S n')
  end.

Definition floorSqrtSumClosedFormQ (n : nat) : Q :=
  let s := Qnat (Nat.sqrt n) in
  s * Qnat (S n) - s * (s + 1) * (2 * s + 1) / 6.

Lemma Qnat_succ (n : nat) :
    Qnat (S n) == Qnat n + 1.
Proof.
  unfold Qnat. rewrite Nat2Z.inj_succ. unfold Qeq. simpl. lia.
Qed.

Lemma Qnat_add (m n : nat) :
    Qnat (m + n) == Qnat m + Qnat n.
Proof.
  unfold Qnat. rewrite Nat2Z.inj_add. unfold Qeq. simpl. lia.
Qed.

Lemma Qnat_mul (m n : nat) :
    Qnat (m * n)%nat == Qnat m * Qnat n.
Proof.
  unfold Qnat. rewrite Nat2Z.inj_mul. unfold Qeq. simpl. lia.
Qed.

Lemma floorSqrtSumClosedFormQ_step_same
    (n q : nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (S n) = q) :
    floorSqrtSumClosedFormQ (S n) ==
      floorSqrtSumClosedFormQ n + Qnat q.
Proof.
  unfold floorSqrtSumClosedFormQ.
  rewrite hq, hs.
  rewrite Qnat_succ.
  ring.
Qed.

Lemma floorSqrtSumClosedFormQ_step_jump
    (n q : nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (S n) = S q)
    (hn : S n = (S q * S q)%nat) :
    floorSqrtSumClosedFormQ (S n) ==
      floorSqrtSumClosedFormQ n + Qnat (S q).
Proof.
  unfold floorSqrtSumClosedFormQ.
  rewrite hq, hs, hn.
  repeat rewrite Qnat_succ.
  rewrite Qnat_mul.
  repeat rewrite Qnat_succ.
  field.
Qed.

Lemma sqrt_succ_eq_self_or_succ (n : nat) :
    Nat.sqrt (S n) = Nat.sqrt n \/ Nat.sqrt (S n) = S (Nat.sqrt n).
Proof.
  destruct (Nat.sqrt_succ_or n) as [h | h].
  - right. exact h.
  - left. exact h.
Qed.

Lemma sqrt_jump_square
    (n q : nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (S n) = S q) :
    S n = (S q * S q)%nat.
Proof.
  pose proof (Nat.sqrt_spec' n) as hn.
  pose proof (Nat.sqrt_spec' (S n)) as hsn.
  rewrite hq in hn.
  rewrite hs in hsn.
  lia.
Qed.

Theorem sum_floor_sqrt_eq_closedForm_Q (n : nat) :
    Qnat (sumFloorSqrt n) == floorSqrtSumClosedFormQ n.
Proof.
  induction n as [|n ih].
  - unfold sumFloorSqrt, floorSqrtSumClosedFormQ, Qnat.
    rewrite Nat.sqrt_0. field.
  - simpl sumFloorSqrt.
    rewrite Qnat_add.
    rewrite ih.
    destruct (sqrt_succ_eq_self_or_succ n) as [hs | hs].
    + rewrite (floorSqrtSumClosedFormQ_step_same n (Nat.sqrt n) eq_refl hs).
      rewrite hs. reflexivity.
    + pose proof (sqrt_jump_square n (Nat.sqrt n) eq_refl hs) as hn.
      rewrite (floorSqrtSumClosedFormQ_step_jump n (Nat.sqrt n) eq_refl hs hn).
      rewrite hs. reflexivity.
Qed.

End FloorSqrtSum.
End LeanProofs.
