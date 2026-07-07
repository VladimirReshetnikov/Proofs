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

Theorem div_lt_mul_add (a b : nat) (hb : 0 < b) :
    a < (a / b) * b + b.
Proof.
  pose proof (Nat.div_mod a b ltac:(lia)) as h.
  pose proof (Nat.mod_upper_bound a b ltac:(lia)) as hm.
  rewrite h at 1.
  rewrite Nat.mul_comm.
  lia.
Qed.

Theorem pairNext_left_child (a b : nat) (hb : 0 < b) :
    pairNext (a, a + b) = (a + b, b).
Proof.
  unfold pairNext.
  cbn [fst snd].
  rewrite Nat.div_small by lia.
  f_equal.
  assert (hle : a <= (2 * 0 + 1) * (a + b)) by lia.
  lia.
Qed.

Theorem pairNext_right_child_arith {a b : nat} (hb : 0 < b) :
    b + ((2 * (a / b) + 1) * b - a) =
      (2 * (a / b + 1) + 1) * b - (a + b).
Proof.
  pose proof (div_lt_mul_add a b hb) as hlt.
  assert (hle1 : a <= (2 * (a / b) + 1) * b) by lia.
  assert (hle2 : a + b <= (2 * (a / b + 1) + 1) * b) by lia.
  lia.
Qed.

Theorem cwPair_succ (n : nat) : cwPair (n + 1) = pairNext (cwPair n).
Proof.
  induction n as [n ih] using lt_wf_ind.
  destruct n as [|m].
  - reflexivity.
  - destruct (Nat.even m) eqn:heven.
    + assert (hm : m = 2 * (m / 2)).
      { assert (hodd : Nat.odd m = false).
        { destruct (Nat.odd m) eqn:hodd; [|reflexivity].
          rewrite <- Nat.negb_odd in heven.
          rewrite hodd in heven.
          discriminate.
        }
        pose proof (Nat.div2_odd m) as hsplit.
        rewrite hodd in hsplit.
        simpl in hsplit.
        rewrite <- Nat.div2_div.
        lia.
      }
      replace (S m + 1) with (2 * (m / 2) + 2) by lia.
      replace (S m) with (2 * (m / 2) + 1) by lia.
      rewrite cwPair_right.
      rewrite cwPair_left.
      pose proof (cwPair_pos (m / 2)) as hp.
      destruct (cwPair (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      rewrite pairNext_left_child by lia.
      reflexivity.
    + assert (hm : m = 2 * (m / 2) + 1).
      { assert (hodd : Nat.odd m = true).
        { destruct (Nat.odd m) eqn:hodd; [reflexivity|].
          rewrite <- Nat.negb_odd in heven.
          rewrite hodd in heven.
          discriminate.
        }
        pose proof (Nat.div2_odd m) as hsplit.
        rewrite hodd in hsplit.
        simpl in hsplit.
        rewrite <- Nat.div2_div.
        lia.
      }
      replace (S m + 1) with (2 * (m / 2 + 1) + 1) by lia.
      replace (S m) with (2 * (m / 2) + 2) by lia.
      rewrite cwPair_left.
      rewrite cwPair_right.
      rewrite (ih (m / 2)) by apply div2_lt_succ.
      pose proof (cwPair_pos (m / 2)) as hp.
      destruct (cwPair (m / 2)) as [a b] eqn:Hp.
      cbn [fst snd] in hp |- *.
      unfold pairNext.
      cbn [fst snd].
      destruct hp as [_ hb].
      assert (hdiv : (a + b) / b = a / b + 1).
      { replace (a + b) with (1 * b + a) by lia.
        rewrite Nat.div_add_l by lia.
        lia.
      }
      rewrite hdiv.
      f_equal.
      exact (pairNext_right_child_arith hb).
Qed.

Theorem cwPair_first_values :
    map cwPair [0; 1; 2; 3; 4; 5; 6; 7] =
      [(1, 1); (1, 2); (2, 1); (1, 3);
       (3, 2); (2, 3); (3, 1); (1, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

End RationalFloorOrbit.
End LeanProofs.
