(*
  Coq port of the initial exact-logarithm layer of
  LeanProofs/A002845.lean.

  This Coq port keeps the proved exact-logarithm reduction, connects it to the
  Coq SparseBinary port, and uses Coq's binary natural numbers as the
  executable logarithm representation.  That is enough to replay the first six
  OEIS values without constructing enormous unary naturals.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import NArith.Nnat.
From LeanProofsCoq Require Import PowTower SparseBinary.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A002845.

Module PowExpr.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.
Module SB := LeanProofsCoq.SparseBinary.LeanProofs.A002845.Sparse.

Definition PowExpr := PT.Expr.

Definition Sparse : Type :=
  LeanProofsCoq.SparseBinary.LeanProofs.A002845.Sparse.

Definition two : PowExpr := PT.atom.

Definition pow : PowExpr -> PowExpr -> PowExpr := PT.pow.

Definition evalNat : PowExpr -> nat :=
  PT.eval 2 Nat.pow.

Definition logCombineNat (a b : nat) : nat :=
  a * Nat.pow 2 b.

Fixpoint logEvalNat (e : PowExpr) : nat :=
  match e with
  | PT.atom => 1
  | PT.pow a b => logCombineNat (logEvalNat a) (logEvalNat b)
  end.

Definition logCombineN (a b : N) : N :=
  (a * N.pow 2 b)%N.

Fixpoint logEvalN (e : PowExpr) : N :=
  match e with
  | PT.atom => 1%N
  | PT.pow a b => logCombineN (logEvalN a) (logEvalN b)
  end.

Theorem logEvalNat_eq_sharedEval (e : PowExpr) :
    logEvalNat e = PT.eval 1 logCombineNat e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Theorem logEvalN_eq_sharedEval (e : PowExpr) :
    logEvalN e = PT.eval 1%N logCombineN e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Theorem logEvalN_of_nat (e : PowExpr) :
    logEvalN e = N.of_nat (logEvalNat e).
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl.
    unfold logCombineN, logCombineNat.
    rewrite Nat2N.inj_mul, Nat2N.inj_pow.
    now rewrite <- iha, <- ihb.
Qed.

Theorem evalNat_eq_two_pow_logEvalNat (e : PowExpr) :
    evalNat e = Nat.pow 2 (logEvalNat e).
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - unfold evalNat at 1. simpl.
    fold (evalNat a). fold (evalNat b).
    rewrite iha, ihb.
    unfold logCombineNat.
    now rewrite Nat.pow_mul_r.
Qed.

Lemma N_eqb_of_nat (x y : nat) :
    N.eqb (N.of_nat x) (N.of_nat y) = Nat.eqb x y.
Proof.
  destruct (N.eqb_spec (N.of_nat x) (N.of_nat y)) as [hn | hn];
    destruct (Nat.eqb_spec x y) as [h | h]; try reflexivity.
  - exfalso. apply h. now apply Nat2N.inj_iff.
  - exfalso. apply hn. now subst.
Qed.

Lemma memberBy_map_N_of_nat (x : nat) (xs : list nat) :
    PT.memberBy N.eqb (N.of_nat x) (map N.of_nat xs) =
      PT.memberBy Nat.eqb x xs.
Proof.
  induction xs as [|y ys ih].
  - reflexivity.
  - simpl. rewrite N_eqb_of_nat, ih. reflexivity.
Qed.

Lemma dedupBy_map_N_of_nat (xs : list nat) :
    PT.dedupBy N.eqb (map N.of_nat xs) =
      map N.of_nat (PT.dedupBy Nat.eqb xs).
Proof.
  induction xs as [|x xs ih].
  - reflexivity.
  - simpl.
    rewrite ih.
    unfold PT.insertBy.
    rewrite memberBy_map_N_of_nat.
    destruct (PT.memberBy Nat.eqb x (PT.dedupBy Nat.eqb xs));
      reflexivity.
Qed.

Lemma evalList_logEvalN_of_nat (n : nat) :
    PT.evalList logEvalN n =
      map N.of_nat (PT.evalList logEvalNat n).
Proof.
  unfold PT.evalList.
  rewrite map_map.
  apply map_ext.
  exact logEvalN_of_nat.
Qed.

Definition directLogCardNat (n : nat) : nat :=
  PT.valueCount Nat.eqb logEvalNat n.

Definition directLogCardN (n : nat) : nat :=
  PT.valueCount N.eqb logEvalN n.

Theorem directLogCardN_eq_directLogCardNat (n : nat) :
    directLogCardN n = directLogCardNat n.
Proof.
  unfold directLogCardN, directLogCardNat.
  unfold PT.valueCount, PT.valueList.
  rewrite evalList_logEvalN_of_nat.
  rewrite dedupBy_map_N_of_nat.
  now rewrite length_map.
Qed.

Definition a002845 : nat -> nat := directLogCardN.

Theorem a002845_eq_directLogCardNat (n : nat) :
    a002845 n = directLogCardNat n.
Proof.
  exact (directLogCardN_eq_directLogCardNat n).
Qed.

Definition certifiedCombineLog (a b : Sparse) : Sparse :=
  SB.shift a b.

Fixpoint sparseLogEval (e : PowExpr) : Sparse :=
  match e with
  | PT.atom => SB.ofN 1
  | PT.pow a b => certifiedCombineLog (sparseLogEval a) (sparseLogEval b)
  end.

Theorem canonical_sparseLogEval (e : PowExpr) :
    SB.Canonical (sparseLogEval e).
Proof.
  induction e as [|a iha b ihb].
  - apply SB.canonical_ofN.
  - unfold sparseLogEval; fold (sparseLogEval a); fold (sparseLogEval b).
    unfold certifiedCombineLog.
    exact (proj1 (SB.shift_spec iha ihb)).
Qed.

Theorem sparseLogEval_eq_logEvalN (e : PowExpr) :
    sparseLogEval e = logEvalN e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl.
    unfold certifiedCombineLog, SB.shift, logCombineN.
    now rewrite iha, ihb.
Qed.

Theorem eval_sparseLogEval (e : PowExpr) :
    SB.eval (sparseLogEval e) = logEvalN e.
Proof.
  now rewrite sparseLogEval_eq_logEvalN.
Qed.

Definition certifiedSparseCard (n : nat) : nat :=
  PT.valueCount SB.beq sparseLogEval n.

Theorem certifiedSparseCard_eq_directLogCardN (n : nat) :
    certifiedSparseCard n = directLogCardN n.
Proof.
  reflexivity.
Qed.

Theorem a002845_eq_certifiedSparseCard (n : nat) :
    a002845 n = certifiedSparseCard n.
Proof.
  unfold a002845.
  symmetry.
  apply certifiedSparseCard_eq_directLogCardN.
Qed.

Theorem a002845_one : a002845 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_two : a002845 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_three : a002845 3 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_four : a002845 4 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_five : a002845 5 = 4.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_six : a002845 6 = 8.
Proof. vm_compute. reflexivity. Qed.

End PowExpr.

Export PowExpr.

End A002845.
End LeanProofs.
