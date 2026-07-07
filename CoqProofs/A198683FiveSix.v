(*
  Coq port of the executable finite-count surface from
  LeanProofs/A198683FiveSix.lean.

  The Lean file proves that the complex value sets for n = 5 and n = 6 are
  exactly the named p5*/p6* candidate sets.  This Coq port reuses the symbolic
  quotient from A198683Tower.v: the quotient records the same finite collapse
  table, and Coq checks the resulting value lists and cardinalities by
  computation.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import A198683Tower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683FiveSix.

Module AT := LeanProofsCoq.A198683Tower.LeanProofs.A198683Tower.
Module AS := AT.A198683Support.

Definition valueListFiveCandidates : list AS.Value :=
  [AS.p5A; AS.p5C; AS.p5B; AS.p5F; AS.p5D; AS.p5G; AS.p5E].

Definition valueListSixCandidates : list AS.Value :=
  [AS.p6A; AS.p6C; AS.p6B; AS.p6F; AS.p6D; AS.p6G; AS.p6I; AS.p6K;
    AS.p6H; AS.p6J; AS.p6O; AS.p6N; AS.p6M; AS.p6L; AS.p6E].

Theorem valueSet_five_eq_candidates :
    AT.a198683ValueList 5 = valueListFiveCandidates.
Proof. vm_compute. reflexivity. Qed.

Theorem mem_valueSet_five_named :
    AT.PT.memberBy AS.valueEqb AS.p5A (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5B (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5C (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5D (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5E (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5F (AT.a198683ValueList 5) = true /\
    AT.PT.memberBy AS.valueEqb AS.p5G (AT.a198683ValueList 5) = true.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem valueSet_six_eq_candidates :
    AT.a198683ValueList 6 = valueListSixCandidates.
Proof. vm_compute. reflexivity. Qed.

Theorem mem_valueSet_six_named :
    AT.PT.memberBy AS.valueEqb AS.p6A (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6B (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6C (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6D (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6E (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6F (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6G (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6H (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6I (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6J (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6K (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6L (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6M (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6N (AT.a198683ValueList 6) = true /\
    AT.PT.memberBy AS.valueEqb AS.p6O (AT.a198683ValueList 6) = true.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem a198683_five : AT.a198683 5 = 7.
Proof. vm_compute. reflexivity. Qed.

Theorem a198683_five_le_seven : AT.a198683 5 <= 7.
Proof. rewrite a198683_five. apply Nat.le_refl. Qed.

Theorem a198683_six : AT.a198683 6 = 15.
Proof. vm_compute. reflexivity. Qed.

Theorem a198683_six_le_fifteen : AT.a198683 6 <= 15.
Proof. rewrite a198683_six. apply Nat.le_refl. Qed.

End A198683FiveSix.
End LeanProofs.
