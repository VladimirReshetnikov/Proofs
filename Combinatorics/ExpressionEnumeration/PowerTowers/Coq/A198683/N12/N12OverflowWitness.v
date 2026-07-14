(*
  Coq port of the syntactic witness layer from
  PowerTowers/A198683/N12/N12OverflowWitness.lean.

  The Lean module interprets these expressions as complex principal powers and
  proves semantic membership plus log-modulus separation lemmas.  This Coq
  module ports the traced expression itself over the shared PowTower syntax and
  checks that the n = 11 base and n = 12 overflow candidate are genuine
  parenthesizations of the requested sizes.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From PowerTowers Require Import Core.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683N12OverflowWitness.

Module PT := PowerTowers.Core.LeanProofs.PowTower.

Definition IPowExpr := PT.Expr.

Definition atom : IPowExpr := PT.atom.

Definition pow : IPowExpr -> IPowExpr -> IPowExpr := PT.pow.

Definition w2 : IPowExpr :=
  pow atom atom.

Definition w3R : IPowExpr :=
  pow w2 atom.

Definition w4C : IPowExpr :=
  pow w2 w2.

Definition w5C : IPowExpr :=
  pow atom w4C.

Definition w8 : IPowExpr :=
  pow w3R w5C.

Definition w9 : IPowExpr :=
  pow atom w8.

Definition w10 : IPowExpr :=
  pow atom w9.

Definition overflowBase11 : IPowExpr :=
  pow atom w10.

Definition overflowCandidate12 : IPowExpr :=
  pow atom overflowBase11.

Theorem w2_size : PT.size w2 = 2.
Proof. reflexivity. Qed.

Theorem w3R_size : PT.size w3R = 3.
Proof. reflexivity. Qed.

Theorem w4C_size : PT.size w4C = 4.
Proof. reflexivity. Qed.

Theorem w5C_size : PT.size w5C = 5.
Proof. reflexivity. Qed.

Theorem w8_size : PT.size w8 = 8.
Proof. reflexivity. Qed.

Theorem w9_size : PT.size w9 = 9.
Proof. reflexivity. Qed.

Theorem w10_size : PT.size w10 = 10.
Proof. reflexivity. Qed.

Theorem overflowBase11_size : PT.size overflowBase11 = 11.
Proof. reflexivity. Qed.

Theorem overflowCandidate12_size : PT.size overflowCandidate12 = 12.
Proof. reflexivity. Qed.

Theorem overflowBase11_parenthesization :
    PT.memberBy PT.exprEqb overflowBase11 (PT.parenthesizations 11) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem overflowCandidate12_parenthesization :
    PT.memberBy PT.exprEqb overflowCandidate12 (PT.parenthesizations 12) = true.
Proof. vm_compute. reflexivity. Qed.

End A198683N12OverflowWitness.
End LeanProofs.
