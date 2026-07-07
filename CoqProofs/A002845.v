(*
  Coq port of the exact-logarithm layer of LeanProofs/A002845.lean.

  This Coq port keeps the proved exact-logarithm reduction and the earlier
  binary-N sparse bridge, then uses a small hereditary sparse-binary executable
  recurrence for the published value certificates.  Materializing the exact
  logarithms as binary naturals is already too large beyond the first few rows;
  the hereditary representation keeps the exponent structure sparse.
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

Definition directA002845 : nat -> nat := directLogCardN.

Theorem directA002845_eq_directLogCardNat (n : nat) :
    directA002845 n = directLogCardNat n.
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

Theorem directA002845_eq_certifiedSparseCard (n : nat) :
    directA002845 n = certifiedSparseCard n.
Proof.
  unfold directA002845.
  symmetry.
  apply certifiedSparseCard_eq_directLogCardN.
Qed.

Module HereditarySparse.

Inductive t : Type :=
| snil : t
| scons : t -> t -> t.

Fixpoint size (x : t) : nat :=
  match x with
  | snil => 1
  | scons h rest => S (size h + size rest)
  end.

Fixpoint beq (x y : t) : bool :=
  match x, y with
  | snil, snil => true
  | scons xh xt, scons yh yt => beq xh yh && beq xt yt
  | _, _ => false
  end.

Theorem beq_refl (x : t) : beq x x = true.
Proof.
  induction x as [|h ihh rest ihr].
  - reflexivity.
  - simpl. now rewrite ihh, ihr.
Qed.

Fixpoint revAux (xs acc : t) : t :=
  match xs with
  | snil => acc
  | scons h rest => revAux rest (scons h acc)
  end.

Definition rev (xs : t) : t := revAux xs snil.

Fixpoint compareFuel (fuel : nat) (x y : t) : comparison :=
  match fuel with
  | 0 => Eq
  | S fuel' => compareListFuel fuel' (rev x) (rev y)
  end
with compareListFuel (fuel : nat) (xs ys : t) : comparison :=
  match fuel with
  | 0 => Eq
  | S fuel' =>
      match xs, ys with
      | snil, snil => Eq
      | snil, scons _ _ => Lt
      | scons _ _, snil => Gt
      | scons x xs', scons y ys' =>
          match compareFuel fuel' x y with
          | Eq => compareListFuel fuel' xs' ys'
          | c => c
          end
      end
  end.

Definition compare (x y : t) : comparison :=
  compareFuel (size x + size y + 1) x y.

Definition zero : t := snil.

Fixpoint incrFuel (fuel : nat) (x : t) : t :=
  match fuel with
  | 0 => x
  | S fuel' => insBitFuel fuel' zero x
  end
with insBitFuel (fuel : nat) (p bits : t) : t :=
  match fuel with
  | 0 => scons p bits
  | S fuel' =>
      match bits with
      | snil => scons p snil
      | scons q qs =>
          match compare p q with
          | Lt => scons p (scons q qs)
          | Eq => insBitFuel fuel' (incrFuel fuel' q) qs
          | Gt => scons q (insBitFuel fuel' p qs)
          end
      end
  end.

Definition incr (x : t) : t :=
  incrFuel (size x + 1) x.

Definition insBit (p bits : t) : t :=
  insBitFuel (size p + size bits + 1) p bits.

Definition one : t := scons zero zero.

Definition add (x y : t) : t :=
  let fix foldBits ys acc :=
    match ys with
    | snil => acc
    | scons p ps => foldBits ps (insBit p acc)
    end in
  foldBits y x.

Definition shift (x b : t) : t :=
  let fix foldBits xs acc :=
    match xs with
    | snil => acc
    | scons p ps => foldBits ps (insBit (add p b) acc)
    end in
  foldBits x snil.

Definition combineLevel (left right : list t) : list t :=
  flat_map (fun a => map (fun b => shift a b) right) left.

Definition levelFromTable (levels : list (list t)) (n : nat) : list t :=
  match n with
  | 0 => []
  | 1 => [one]
  | S (S n') =>
      PT.dedupBy beq
        (flat_map
          (fun k =>
             combineLevel (nth (S k) levels []) (nth (S n' - k) levels []))
          (seq 0 (S n')))
  end.

Fixpoint levelTable (fuel : nat) : list (list t) :=
  match fuel with
  | 0 => []
  | S fuel' =>
      let levels := levelTable fuel' in
      levels ++ [levelFromTable levels fuel']
  end.

Definition level (n : nat) : list t :=
  nth n (levelTable (S n)) [].

Definition count (n : nat) : nat :=
  length (level n).

End HereditarySparse.

Definition certifiedLevelCount : nat -> nat :=
  HereditarySparse.count.

Definition a002845 : nat -> nat := certifiedLevelCount.

Definition a002845ValuesThroughFourteen : list nat :=
  [1; 1; 1; 2; 4; 8; 17; 36; 78; 171; 379; 851; 1928; 4396].

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

Theorem a002845_seven : a002845 7 = 17.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_eight : a002845 8 = 36.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_nine : a002845 9 = 78.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_ten : a002845 10 = 171.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_eleven : a002845 11 = 379.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_twelve : a002845 12 = 851.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_thirteen : a002845 13 = 1928.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_fourteen : a002845 14 = 4396.
Proof. vm_compute. reflexivity. Qed.

Theorem a002845_values_through_fourteen :
    map a002845 (seq 1 14) = a002845ValuesThroughFourteen.
Proof.
  cbn [seq map].
  now rewrite a002845_one, a002845_two, a002845_three, a002845_four,
    a002845_five, a002845_six, a002845_seven, a002845_eight, a002845_nine,
    a002845_ten, a002845_eleven, a002845_twelve, a002845_thirteen,
    a002845_fourteen.
Qed.

End PowExpr.

Export PowExpr.

End A002845.
End LeanProofs.
