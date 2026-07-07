(*
  Coq port of the finite executable certificate from LeanProofs/A000081.lean.

  The Lean module interprets tower parenthesizations as positive-real
  functions and proves the first values of A000081 by normalizing their outer
  exponents.  This Coq port keeps the discrete normal-form computation: every
  tower is represented as x^E, where E is a commutative product of factors
  x^F.  The product is stored as a sorted list of recursively defined exponent
  normal forms, so the equality used by the finite certificate is structural.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import PowTower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A000081.

Module PowExpr.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.

Definition PowExpr := PT.Expr.

Inductive ExponentNF : Type :=
| empty : ExponentNF
| cons : ExponentNF -> ExponentNF -> ExponentNF.

Fixpoint exponentNFEqb (a b : ExponentNF) : bool :=
  match a, b with
  | empty, empty => true
  | cons ah atl, cons bh btl =>
      exponentNFEqb ah bh && exponentNFEqb atl btl
  | _, _ => false
  end.

Theorem exponentNFEqb_refl (a : ExponentNF) : exponentNFEqb a a = true.
Proof.
  induction a as [|h ihh t iht].
  - reflexivity.
  - simpl. now rewrite ihh, iht.
Qed.

Fixpoint exponentNFCompare (a b : ExponentNF) : comparison :=
  match a, b with
  | empty, empty => Eq
  | empty, cons _ _ => Lt
  | cons _ _, empty => Gt
  | cons ah atl, cons bh btl =>
      match exponentNFCompare ah bh with
      | Eq => exponentNFCompare atl btl
      | c => c
      end
  end.

Fixpoint insertExponentNF (x factors : ExponentNF) : ExponentNF :=
  match factors with
  | empty => cons x empty
  | cons y ys =>
      match exponentNFCompare x y with
      | Gt => cons y (insertExponentNF x ys)
      | _ => cons x factors
      end
  end.

Definition atomExponent : ExponentNF := empty.

Definition combineExponent (a b : ExponentNF) : ExponentNF :=
  insertExponentNF b a.

Fixpoint exponentNF (e : PowExpr) : ExponentNF :=
  match e with
  | PT.atom => atomExponent
  | PT.pow a b => combineExponent (exponentNF a) (exponentNF b)
  end.

Theorem exponentNF_eq_sharedCombineEval (e : PowExpr) :
    exponentNF e = PT.eval atomExponent combineExponent e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Definition x : PowExpr := PT.atom.

Definition pow : PowExpr -> PowExpr -> PowExpr := PT.pow.

Definition e2 : PowExpr :=
  pow x x.

Definition e3a : PowExpr :=
  pow x (pow x x).

Definition e3b : PowExpr :=
  pow (pow x x) x.

Definition e4a : PowExpr :=
  pow x (pow x (pow x x)).

Definition e4b : PowExpr :=
  pow x (pow (pow x x) x).

Definition e4c : PowExpr :=
  pow (pow x x) (pow x x).

Definition e4d : PowExpr :=
  pow (pow x (pow x x)) x.

Definition e4e : PowExpr :=
  pow (pow (pow x x) x) x.

Definition e5a : PowExpr := pow x e4a.
Definition e5b : PowExpr := pow x e4b.
Definition e5c : PowExpr := pow x e4c.
Definition e5d : PowExpr := pow x e4d.
Definition e5e : PowExpr := pow x e4e.
Definition e5f : PowExpr := pow e2 e3a.
Definition e5g : PowExpr := pow e2 e3b.
Definition e5h : PowExpr := pow e3a e2.
Definition e5i : PowExpr := pow e3b e2.
Definition e5j : PowExpr := pow e4a x.
Definition e5k : PowExpr := pow e4b x.
Definition e5l : PowExpr := pow e4c x.
Definition e5m : PowExpr := pow e4d x.
Definition e5n : PowExpr := pow e4e x.

Theorem parenthesizations_one :
    PT.parenthesizations 1 = [x].
Proof. reflexivity. Qed.

Theorem parenthesizations_two :
    PT.parenthesizations 2 = [e2].
Proof. reflexivity. Qed.

Theorem parenthesizations_three :
    PT.parenthesizations 3 = [e3a; e3b].
Proof. reflexivity. Qed.

Theorem parenthesizations_four :
    PT.parenthesizations 4 = [e4a; e4b; e4c; e4d; e4e].
Proof. reflexivity. Qed.

Theorem parenthesizations_five :
    PT.parenthesizations 5 =
      [e5a; e5b; e5c; e5d; e5e; e5f; e5g; e5h; e5i; e5j; e5k; e5l; e5m; e5n].
Proof. reflexivity. Qed.

Theorem e3a_ne_e3b : exponentNF e3a <> exponentNF e3b.
Proof. vm_compute. discriminate. Qed.

Theorem e4c_eq_e4d : exponentNF e4c = exponentNF e4d.
Proof. vm_compute. reflexivity. Qed.

Theorem e5c_eq_e5d : exponentNF e5c = exponentNF e5d.
Proof. vm_compute. reflexivity. Qed.

Theorem e5f_eq_e5j : exponentNF e5f = exponentNF e5j.
Proof. vm_compute. reflexivity. Qed.

Theorem e5g_eq_e5k : exponentNF e5g = exponentNF e5k.
Proof. vm_compute. reflexivity. Qed.

Theorem e5i_eq_e5l : exponentNF e5i = exponentNF e5l.
Proof. vm_compute. reflexivity. Qed.

Theorem e5i_eq_e5m : exponentNF e5i = exponentNF e5m.
Proof. vm_compute. reflexivity. Qed.

Theorem e5l_eq_e5m : exponentNF e5l = exponentNF e5m.
Proof. now rewrite <- e5i_eq_e5l, e5i_eq_e5m. Qed.

Theorem e4a_ne_e4b : exponentNF e4a <> exponentNF e4b.
Proof. vm_compute. discriminate. Qed.

Theorem e4a_ne_e4d : exponentNF e4a <> exponentNF e4d.
Proof. vm_compute. discriminate. Qed.

Theorem e4a_ne_e4e : exponentNF e4a <> exponentNF e4e.
Proof. vm_compute. discriminate. Qed.

Theorem e4b_ne_e4d : exponentNF e4b <> exponentNF e4d.
Proof. vm_compute. discriminate. Qed.

Theorem e4b_ne_e4e : exponentNF e4b <> exponentNF e4e.
Proof. vm_compute. discriminate. Qed.

Theorem e4d_ne_e4e : exponentNF e4d <> exponentNF e4e.
Proof. vm_compute. discriminate. Qed.

Definition computedExponentValues (n : nat) : list ExponentNF :=
  PT.recursiveValueList exponentNFEqb atomExponent combineExponent n.

Definition computedExponentCount (n : nat) : nat :=
  length (computedExponentValues n).

Definition a000081 : nat -> nat := computedExponentCount.

Definition a000081ValuesThroughEight : list nat :=
  [0; 1; 1; 2; 4; 9; 20; 48; 115].

Theorem a000081_values_through_eight :
    map a000081 (seq 0 9) = a000081ValuesThroughEight.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_zero : a000081 0 = 0.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_one : a000081 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_two : a000081 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_three : a000081 3 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_four : a000081 4 = 4.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_five : a000081 5 = 9.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_six : a000081 6 = 20.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_seven : a000081 7 = 48.
Proof. vm_compute. reflexivity. Qed.

Theorem a000081_eight : a000081 8 = 115.
Proof. vm_compute. reflexivity. Qed.

End PowExpr.

Export PowExpr.

End A000081.
End LeanProofs.
