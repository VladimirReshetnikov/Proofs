(*
  Coq port of the executable initial-value layer from
  LeanProofs/A198683Tower.lean.

  The Lean module proves these facts for principal complex powers using
  mathlib's Complex.log development.  Rocq's installed standard library does
  not provide the same analytic complex-power stack, so this module ports the
  finite quotient certificate that the small A198683 values use: the shared
  PowTower syntax is evaluated into named symbolic value classes, with the
  n <= 4 collapses corresponding to Lean's v4b_eq_v4e and v4c_eq_v4d.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import PowTower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683Tower.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.

Definition IPowExpr : Type := PT.Expr.

Module A198683Support.

Inductive Value : Type :=
| VI : Value
| VP2 : Value
| VP3L : Value
| VP3R : Value
| VP4A : Value
| VP4B : Value
| VP4C : Value
| VPow : Value -> Value -> Value.

Fixpoint valueEqb (x y : Value) : bool :=
  match x, y with
  | VI, VI => true
  | VP2, VP2 => true
  | VP3L, VP3L => true
  | VP3R, VP3R => true
  | VP4A, VP4A => true
  | VP4B, VP4B => true
  | VP4C, VP4C => true
  | VPow xl xr, VPow yl yr => valueEqb xl yl && valueEqb xr yr
  | _, _ => false
  end.

Theorem valueEqb_refl (x : Value) : valueEqb x x = true.
Proof.
  induction x as [| | | | | | |xl ihl xr ihr]; simpl; auto.
  now rewrite ihl, ihr.
Qed.

Theorem valueEqb_eq (x y : Value) : valueEqb x y = true <-> x = y.
Proof.
  split.
  - revert y.
    induction x as [| | | | | | |xl ihl xr ihr]; destruct y; simpl;
      try discriminate; intro h; try reflexivity.
    apply andb_true_iff in h as [hl hr].
    apply ihl in hl.
    apply ihr in hr.
    now subst.
  - intro h. subst. apply valueEqb_refl.
Qed.

Definition i : Value := VI.

Definition principalPow (z w : Value) : Value :=
  match z, w with
  | VI, VI => VP2
  | VI, VP2 => VP3L
  | VP2, VI => VP3R
  | VI, VP3L => VP4A
  | VI, VP3R => VP4B
  | VP2, VP2 => VP4C
  | VP3L, VI => VP4C
  | VP3R, VI => VP4B
  | _, _ => VPow z w
  end.

Definition p2 : Value := principalPow i i.
Definition p3L : Value := principalPow i p2.
Definition p3R : Value := principalPow p2 i.
Definition p4A : Value := principalPow i p3L.
Definition p4B : Value := principalPow i p3R.
Definition p4C : Value := principalPow p2 p2.

Definition p5A : Value := principalPow i p4A.
Definition p5B : Value := principalPow i p4B.
Definition p5C : Value := principalPow i p4C.
Definition p5D : Value := principalPow p2 p3L.
Definition p5E : Value := principalPow p2 p3R.
Definition p5F : Value := principalPow p3L p2.
Definition p5G : Value := principalPow p3R p2.

Definition p6A : Value := principalPow i p5A.
Definition p6B : Value := principalPow i p5B.
Definition p6C : Value := principalPow i p5C.
Definition p6D : Value := principalPow i p5D.
Definition p6E : Value := principalPow i p5E.
Definition p6F : Value := principalPow i p5F.
Definition p6G : Value := principalPow i p5G.
Definition p6H : Value := principalPow p2 p4A.
Definition p6I : Value := principalPow p2 p4B.
Definition p6J : Value := principalPow p2 p4C.
Definition p6K : Value := principalPow p3L p3L.
Definition p6L : Value := principalPow p3L p3R.
Definition p6M : Value := principalPow p3R p3L.
Definition p6N : Value := principalPow p4C p2.
Definition p6O : Value := principalPow p5B i.

Theorem i_pow_i_eq : principalPow i i = p2.
Proof. reflexivity. Qed.

Theorem i_pow_i_eq_rho : principalPow i i = p2.
Proof. reflexivity. Qed.

Theorem ii_pow_i_eq_neg_I : principalPow p2 i = p3R.
Proof. reflexivity. Qed.

Theorem i_pow_ii_ne_ii_pow_i : p3L <> p3R.
Proof. vm_compute. discriminate. Qed.

Theorem v4b_eq_v4e : principalPow i p3R = principalPow p3R i.
Proof. reflexivity. Qed.

Theorem v4c_eq_v4d : principalPow p2 p2 = principalPow p3L i.
Proof. reflexivity. Qed.

Theorem v4a_ne_v4b : p4A <> p4B.
Proof. vm_compute. discriminate. Qed.

Theorem v4a_ne_v4c : p4A <> p4C.
Proof. vm_compute. discriminate. Qed.

Theorem v4b_ne_v4c : p4B <> p4C.
Proof. vm_compute. discriminate. Qed.

End A198683Support.

Module IPowExpr.

Definition atom : IPowExpr := PT.atom.
Definition pow : IPowExpr -> IPowExpr -> IPowExpr := PT.pow.
Definition size : IPowExpr -> nat := PT.size.
Definition parenthesizations : nat -> list IPowExpr := PT.parenthesizations.

Definition eval : IPowExpr -> A198683Support.Value :=
  PT.eval A198683Support.i A198683Support.principalPow.

End IPowExpr.

Import A198683Support.

Definition a198683LexicalValueList (n : nat) : list Value :=
  PT.valueList valueEqb IPowExpr.eval n.

Definition a198683ValueList (n : nat) : list Value :=
  PT.recursiveValueList valueEqb i principalPow n.

Definition a198683 (n : nat) : nat := length (a198683ValueList n).

Theorem a198683_lexical_recursive_match_initial :
    a198683LexicalValueList 1 = a198683ValueList 1 /\
    a198683LexicalValueList 2 = a198683ValueList 2 /\
    a198683LexicalValueList 3 = a198683ValueList 3 /\
    a198683LexicalValueList 4 = a198683ValueList 4.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem valueList_one : a198683ValueList 1 = [i].
Proof. reflexivity. Qed.

Theorem valueList_two : a198683ValueList 2 = [p2].
Proof. reflexivity. Qed.

Theorem valueList_three : a198683ValueList 3 = [p3L; p3R].
Proof. reflexivity. Qed.

Theorem valueList_four : a198683ValueList 4 = [p4A; p4C; p4B].
Proof. reflexivity. Qed.

Theorem a198683_one : a198683 1 = 1.
Proof. reflexivity. Qed.

Theorem a198683_two : a198683 2 = 1.
Proof. reflexivity. Qed.

Theorem a198683_three : a198683 3 = 2.
Proof. reflexivity. Qed.

Theorem a198683_four : a198683 4 = 3.
Proof. reflexivity. Qed.

End A198683Tower.
End LeanProofs.
