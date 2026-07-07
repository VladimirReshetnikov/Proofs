(*
  Coq port of the Calkin-Wilf pair core from
  LeanProofs/RationalFloorOrbit.lean.

  The Lean module goes on to prove the inverse index map and the rational
  floor-orbit enumeration theorem.  This Coq module establishes the executable
  pair generator and its two structural invariants: every generated pair is
  positive and coprime.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.

Import ListNotations.

Module LeanProofs.
Module RationalFloorOrbit.

Definition Coprime (a b : nat) : Prop :=
  Nat.gcd a b = 1.

Fixpoint cwPairFuel (fuel n : nat) : nat * nat :=
  match fuel with
  | 0 => (1, 1)
  | S fuel' =>
      match n with
      | 0 => (1, 1)
      | S m =>
          let p := cwPairFuel fuel' (m / 2) in
          if Nat.even m
          then (fst p, fst p + snd p)
          else (fst p + snd p, snd p)
      end
  end.

Definition cwPair (n : nat) : nat * nat :=
  cwPairFuel n n.

Theorem cwPair_zero : cwPair 0 = (1, 1).
Proof. reflexivity. Qed.

Lemma div2_lt_succ (m : nat) : m / 2 < S m.
Proof.
  destruct m as [|m].
  - simpl. lia.
  - eapply Nat.lt_trans.
    + apply Nat.div_lt; lia.
    + lia.
Qed.

Theorem cwPairFuel_ge (n fuel : nat) :
    n <= fuel -> cwPairFuel fuel n = cwPair n.
Proof.
  revert fuel.
  induction n as [n ih] using lt_wf_ind.
  intros fuel hle.
  unfold cwPair.
  destruct n as [|m].
  - destruct fuel; reflexivity.
  - destruct fuel as [|fuel']; [lia|].
    cbn [cwPairFuel fst snd].
    assert (hidx : m / 2 < S m) by apply div2_lt_succ.
    rewrite (ih (m / 2) hidx fuel') by lia.
    rewrite (ih (m / 2) hidx m) by lia.
    reflexivity.
Qed.

Theorem cwPair_unfold_succ (m : nat) :
    cwPair (S m) =
      let p := cwPair (m / 2) in
      if Nat.even m
      then (fst p, fst p + snd p)
      else (fst p + snd p, snd p).
Proof.
  unfold cwPair at 1.
  cbn [cwPairFuel fst snd].
  rewrite cwPairFuel_ge.
  - reflexivity.
  - pose proof (div2_lt_succ m). lia.
Qed.

Theorem cwPair_left (n : nat) :
    cwPair (2 * n + 1) =
      let p := cwPair n in (fst p, fst p + snd p).
Proof.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  rewrite cwPair_unfold_succ.
  replace ((2 * n) / 2) with n by
    (symmetry; rewrite Nat.mul_comm; apply Nat.div_mul; lia).
  rewrite Nat.even_even.
  reflexivity.
Qed.

Theorem cwPair_right (n : nat) :
    cwPair (2 * n + 2) =
      let p := cwPair n in (fst p + snd p, snd p).
Proof.
  replace (2 * n + 2) with (S (2 * n + 1)) by lia.
  rewrite cwPair_unfold_succ.
  replace ((2 * n + 1) / 2) with n.
  - rewrite Nat.even_odd.
    reflexivity.
  - replace (2 * n + 1) with (Nat.b2n true + 2 * n) by (simpl; lia).
    rewrite Nat.add_b2n_double_div2.
    reflexivity.
Qed.

Lemma coprime_add_right {a b : nat} :
    Coprime a b -> Coprime a (a + b).
Proof.
  intro h.
  unfold Coprime in *.
  rewrite Nat.add_comm.
  now rewrite Nat.gcd_add_diag_r.
Qed.

Lemma coprime_add_left {a b : nat} :
    Coprime a b -> Coprime (a + b) b.
Proof.
  intro h.
  unfold Coprime in *.
  rewrite Nat.gcd_comm.
  rewrite Nat.gcd_add_diag_r.
  now rewrite Nat.gcd_comm.
Qed.

Theorem cwPairFuel_pos (fuel n : nat) :
    0 < fst (cwPairFuel fuel n) /\ 0 < snd (cwPairFuel fuel n).
Proof.
  revert n.
  induction fuel as [|fuel ih]; intro n.
  - simpl. lia.
  - destruct n as [|m].
    + simpl. lia.
    + cbn [cwPairFuel fst snd].
      pose proof (ih (m / 2)) as hp.
      destruct (cwPairFuel fuel (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      cbn [fst snd].
      destruct hp as [ha hb].
      destruct (Nat.even m); cbn [fst snd]; lia.
Qed.

Theorem cwPair_pos (n : nat) :
    0 < fst (cwPair n) /\ 0 < snd (cwPair n).
Proof.
  apply cwPairFuel_pos.
Qed.

Theorem cwPairFuel_coprime (fuel n : nat) :
    Coprime (fst (cwPairFuel fuel n)) (snd (cwPairFuel fuel n)).
Proof.
  revert n.
  induction fuel as [|fuel ih]; intro n.
  - reflexivity.
  - destruct n as [|m].
    + reflexivity.
    + cbn [cwPairFuel fst snd].
      pose proof (ih (m / 2)) as hc.
      destruct (cwPairFuel fuel (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hc |- *.
      cbn [fst snd].
      destruct (Nat.even m).
      * cbn [fst snd]. now apply coprime_add_right.
      * cbn [fst snd]. now apply coprime_add_left.
Qed.

Theorem cwPair_coprime (n : nat) :
    Coprime (fst (cwPair n)) (snd (cwPair n)).
Proof.
  apply cwPairFuel_coprime.
Qed.

Definition pairNext (p : nat * nat) : nat * nat :=
  let a := fst p in
  let b := snd p in
  (b, (2 * (a / b) + 1) * b - a).

Theorem cwPair_first_values :
    map cwPair [0; 1; 2; 3; 4; 5; 6; 7] =
      [(1, 1); (1, 2); (2, 1); (1, 3);
       (3, 2); (2, 3); (3, 1); (1, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

End RationalFloorOrbit.
End LeanProofs.
