(*
  Coq port of the Calkin-Wilf pair core from
  LeanProofs/RationalFloorOrbit.lean.

  The Lean module goes on to prove the rational floor-orbit enumeration
  theorem.  This Coq module establishes the executable pair generator, inverse
  index map, and the rational-number bridge for the orbit successor step.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith.

Import ListNotations.

Local Open Scope nat_scope.

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

Fixpoint cwIndexFuel (fuel a b : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if ((a =? 0) || (b =? 0))%bool then 0
      else if a =? b then 0
      else if a <? b
           then 2 * cwIndexFuel fuel' a (b - a) + 1
           else 2 * cwIndexFuel fuel' (a - b) b + 2
  end.

Definition cwIndex (a b : nat) : nat :=
  cwIndexFuel (a + b + 1) a b.

Theorem cwIndexFuel_ge (a b fuel : nat) :
    a + b + 1 <= fuel -> cwIndexFuel fuel a b = cwIndex a b.
Proof.
  revert a b.
  induction fuel as [fuel ih] using lt_wf_ind.
  intros a b hle.
  destruct fuel as [|fuel']; [lia|].
  unfold cwIndex.
  replace (a + b + 1) with (S (a + b)) by lia.
  cbn [cwIndexFuel].
  destruct (((a =? 0) || (b =? 0))%bool) eqn:hz.
  - reflexivity.
  - apply Bool.orb_false_iff in hz as [ha0 hb0].
    apply Nat.eqb_neq in ha0.
    apply Nat.eqb_neq in hb0.
    destruct (a =? b) eqn:heq.
    + reflexivity.
    + apply Nat.eqb_neq in heq.
      destruct (a <? b) eqn:hlt.
      * apply Nat.ltb_lt in hlt.
        rewrite (ih fuel') by lia.
        rewrite (ih (a + b)) by lia.
        reflexivity.
      * apply Nat.ltb_ge in hlt.
        rewrite (ih fuel') by lia.
        rewrite (ih (a + b)) by lia.
        reflexivity.
Qed.

Theorem cwIndex_eq_of_eq {a b : nat} (ha : 0 < a) (hb : 0 < b) (h : a = b) :
    cwIndex a b = 0.
Proof.
  subst a.
  unfold cwIndex.
  replace (b + b + 1) with (S (b + b)) by lia.
  cbn [cwIndexFuel].
  replace (b =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (b =? b) with true by (symmetry; apply Nat.eqb_refl).
  reflexivity.
Qed.

Theorem cwIndex_left {a b : nat} (ha : 0 < a) (h : a < b) :
    cwIndex a b = 2 * cwIndex a (b - a) + 1.
Proof.
  unfold cwIndex at 1.
  replace (a + b + 1) with (S (a + b)) by lia.
  cbn [cwIndexFuel].
  replace (a =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (b =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (a =? b) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (a <? b) with true by (symmetry; apply Nat.ltb_lt; lia).
  cbn.
  rewrite cwIndexFuel_ge by lia.
  reflexivity.
Qed.

Theorem cwIndex_right {a b : nat} (hb : 0 < b) (h : b < a) :
    cwIndex a b = 2 * cwIndex (a - b) b + 2.
Proof.
  unfold cwIndex at 1.
  replace (a + b + 1) with (S (a + b)) by lia.
  cbn [cwIndexFuel].
  replace (a =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (b =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (a =? b) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (a <? b) with false by (symmetry; apply Nat.ltb_ge; lia).
  cbn.
  rewrite cwIndexFuel_ge by lia.
  reflexivity.
Qed.

Theorem coprime_sub_right {a b : nat} (h : a < b) (hc : Coprime a b) :
    Coprime a (b - a).
Proof.
  unfold Coprime in *.
  now rewrite Nat.gcd_sub_diag_r by lia.
Qed.

Theorem coprime_sub_left {a b : nat} (h : b < a) (hc : Coprime a b) :
    Coprime (a - b) b.
Proof.
  unfold Coprime in *.
  rewrite Nat.gcd_comm.
  rewrite Nat.gcd_sub_diag_r by lia.
  now rewrite Nat.gcd_comm.
Qed.

Theorem cwPair_cwIndex (a b : nat) (ha : 0 < a) (hb : 0 < b)
    (hc : Coprime a b) :
    cwPair (cwIndex a b) = (a, b).
Proof.
  remember (a + b) as s eqn:hs.
  revert a b hs ha hb hc.
  induction s as [s ih] using lt_wf_ind.
  intros a b hs ha hb hc.
  destruct (Nat.lt_trichotomy a b) as [hlt | [heq | hgt]].
  - assert (hbsub : 0 < b - a) by lia.
    pose proof (ih (a + (b - a)) ltac:(lia)
      a (b - a) eq_refl ha hbsub (coprime_sub_right hlt hc)) as hp.
    rewrite (cwIndex_left ha hlt).
    rewrite cwPair_left.
    rewrite hp.
    cbn [fst snd].
    f_equal; lia.
  - subst a.
    unfold Coprime in hc.
    rewrite Nat.gcd_diag in hc.
    assert (hb1 : b = 1) by lia.
    subst b.
    rewrite cwIndex_eq_of_eq by lia.
    reflexivity.
  - assert (hasub : 0 < a - b) by lia.
    pose proof (ih ((a - b) + b) ltac:(lia)
      (a - b) b eq_refl hasub hb (coprime_sub_left hgt hc)) as hp.
    rewrite (cwIndex_right hb hgt).
    rewrite cwPair_right.
    rewrite hp.
    cbn [fst snd].
    f_equal; lia.
Qed.

Theorem cwIndex_cwPair (n : nat) :
    cwIndex (fst (cwPair n)) (snd (cwPair n)) = n.
Proof.
  induction n as [n ih] using lt_wf_ind.
  destruct n as [|m].
  - rewrite cwPair_zero.
    cbn [fst snd].
    now rewrite cwIndex_eq_of_eq by lia.
  - rewrite cwPair_unfold_succ.
    pose proof (cwPair_pos (m / 2)) as hp.
    pose proof (ih (m / 2) (div2_lt_succ m)) as ihp.
    destruct (cwPair (m / 2)) as [a b] eqn:Hp.
    cbn [fst snd] in hp, ihp |- *.
    destruct hp as [ha hb].
    destruct (Nat.even m) eqn:heven.
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
      cbn [fst snd].
      assert (hidx : cwIndex a (a + b) = 2 * cwIndex a (a + b - a) + 1).
      { apply cwIndex_left; lia. }
      rewrite hidx.
      replace (a + b - a) with b by lia.
      rewrite ihp.
      lia.
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
      cbn [fst snd].
      assert (hidx : cwIndex (a + b) b = 2 * cwIndex (a + b - b) b + 2).
      { apply cwIndex_right; lia. }
      rewrite hidx.
      replace (a + b - b) with a by lia.
      rewrite ihp.
      lia.
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

Definition positiveDenOfNat (b : nat) : positive :=
  Pos.of_succ_nat (Nat.pred b).

Lemma Zpos_positiveDenOfNat (b : nat) (hb : 0 < b) :
    Z.pos (positiveDenOfNat b) = Z.of_nat b.
Proof.
  unfold positiveDenOfNat.
  rewrite Zpos_P_of_succ_nat.
  destruct b as [|b]; [lia|].
  simpl.
  lia.
Qed.

Definition pairRat (p : nat * nat) : Q :=
  Qmake (Z.of_nat (fst p)) (positiveDenOfNat (snd p)).

Definition qOfNat (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Definition qfloorNat (q : Q) : nat :=
  Z.to_nat ((Qnum q / Z.pos (Qden q))%Z).

Theorem qfloorNat_pairRat (a b : nat) (hb : 0 < b) :
    qfloorNat (pairRat (a, b)) = a / b.
Proof.
  unfold qfloorNat, pairRat.
  cbn [fst snd Qnum Qden].
  rewrite Zpos_positiveDenOfNat by lia.
  rewrite Z2Nat.inj_div by lia.
  rewrite Nat2Z.id.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Theorem pairRat_eq_div (a b : nat) (hb : 0 < b) :
    Qeq (pairRat (a, b)) (Qdiv (qOfNat a) (qOfNat b)).
Proof.
  unfold pairRat, qOfNat.
  cbn [fst snd].
  rewrite <- (Zpos_positiveDenOfNat b hb).
  apply Qmake_Qdiv.
Qed.

Theorem qOfNat_nonzero (n : nat) (hn : 0 < n) :
    ~ Qeq (qOfNat n) (inject_Z 0%Z).
Proof.
  unfold qOfNat, inject_Z, Qeq.
  cbn.
  lia.
Qed.

Definition rationalNext (q : Q) : Q :=
  Qinv (Qplus (Qminus (inject_Z 1%Z) q)
    (Qmult (inject_Z 2%Z) (qOfNat (qfloorNat q)))).

Theorem pairNext_den_pos (a b : nat) (hb : 0 < b) :
    0 < snd (pairNext (a, b)).
Proof.
  unfold pairNext.
  cbn [fst snd].
  pose proof (div_lt_mul_add a b hb).
  lia.
Qed.

Local Open Scope Q_scope.

Theorem qOfNat_den_expr (a b k : nat)
    (hle : (a <= (2 * k + 1) * b)%nat) :
    qOfNat ((2 * k + 1) * b - a) ==
      (2 * qOfNat k + 1) * qOfNat b - qOfNat a.
Proof.
  unfold qOfNat, Qeq, Qplus, Qminus, Qopp, Qmult, inject_Z.
  cbn.
  rewrite Nat2Z.inj_sub by lia.
  rewrite Nat2Z.inj_mul.
  repeat rewrite Nat2Z.inj_add.
  replace
    (match Z.of_nat k with
     | 0%Z => 0%Z
     | Z.pos y' => Z.pos y'~0
     | Z.neg y' => Z.neg y'~0
     end) with (2 * Z.of_nat k)%Z.
  - ring.
  - destruct k; reflexivity.
Qed.

Theorem rationalNext_pairRat (a b : nat) (hb : (0 < b)%nat) :
    rationalNext (pairRat (a, b)) == pairRat (pairNext (a, b)).
Proof.
  unfold rationalNext.
  rewrite qfloorNat_pairRat by lia.
  setoid_rewrite (pairRat_eq_div a b hb).
  unfold pairNext.
  cbn [fst snd].
  rewrite (pairRat_eq_div b ((2 * (a / b) + 1) * b - a))
    by (apply pairNext_den_pos; lia).
  change (/ (1 - qOfNat a / qOfNat b + 2 * qOfNat (a / b)) ==
    qOfNat b / qOfNat ((2 * (a / b) + 1) * b - a)).
  pose proof (div_lt_mul_add a b hb) as hlt.
  assert (hle : (a <= (2 * (a / b) + 1) * b)%nat) by lia.
  assert (hdpos : (0 < (2 * (a / b) + 1) * b - a)%nat) by lia.
  pose proof (qOfNat_den_expr a b (a / b) hle) as hden.
  rewrite hden.
  field.
  split.
  - intro hzero.
    apply (qOfNat_nonzero ((2 * (a / b) + 1) * b - a) hdpos).
    eapply Qeq_trans; [exact hden | exact hzero].
  - apply qOfNat_nonzero; lia.
Qed.

Definition cwRat (n : nat) : Q :=
  pairRat (cwPair n).

Theorem rationalNext_cwRat (n : nat) :
    rationalNext (cwRat n) == cwRat (n + 1).
Proof.
  unfold cwRat.
  rewrite cwPair_succ.
  destruct (cwPair n) as [a b] eqn:Hp.
  pose proof (cwPair_pos n) as hpos.
  rewrite Hp in hpos.
  apply rationalNext_pairRat.
  cbn [snd] in hpos.
  lia.
Qed.

Local Open Scope nat_scope.

Theorem pairRat_first_values :
    map pairRat [(1, 1); (1, 2); (2, 1); (1, 3)] =
      [Qmake 1 1; Qmake 1 2; Qmake 2 1; Qmake 1 3].
Proof.
  reflexivity.
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
