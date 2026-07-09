(*
  Coq counterpart for the public level-8 bound surface of
  LeanProofs/A198683EightBounds.lean.

  The Lean file proves semantic complex-power bounds
  `16 <= a198683 8 <= 127`.  The current Coq A198683 tower quotient still
  keeps the 135 raw level-8 candidates, while the imported Schoenfield
  certificate already normalizes the generated level-8 class table to 77
  classes.  This file records the Coq-side finite certificate surface that
  corresponds to those level-8 bounds without claiming the missing analytic
  semantic bridge.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import A198683Tower A198683Schoenfield.

Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683EightBounds.

Module AT := LeanProofsCoq.A198683Tower.LeanProofs.A198683Tower.
Module Sch := LeanProofsCoq.A198683Schoenfield.LeanProofs.A198683Schoenfield.

Definition rawA198683EightCandidateCount : nat := AT.a198683 8.

Definition schoenfieldA198683EightClassCount : nat :=
  Sch.normalizedClassCount Sch.labelsEight.

Theorem rawA198683EightCandidateCount_eq :
  rawA198683EightCandidateCount = 135.
Proof. vm_compute. reflexivity. Qed.

Theorem a198683EightCandidates_length :
  List.length Sch.labelsEight = 429.
Proof.
  exact (Sch.certificateOk_length_of Sch.schoenfield_a198683_eight).
Qed.

Theorem schoenfieldA198683EightClassCount_eq :
  schoenfieldA198683EightClassCount = 77.
Proof.
  exact Sch.schoenfield_a198683_eight_class_count.
Qed.

Theorem schoenfield_a198683_eight_ge :
  16 <= schoenfieldA198683EightClassCount.
Proof. rewrite schoenfieldA198683EightClassCount_eq; lia. Qed.

Theorem schoenfield_a198683_eight_le :
  schoenfieldA198683EightClassCount <= 127.
Proof. rewrite schoenfieldA198683EightClassCount_eq; lia. Qed.

Theorem schoenfield_a198683_eight_pos :
  1 <= schoenfieldA198683EightClassCount.
Proof. rewrite schoenfieldA198683EightClassCount_eq; lia. Qed.

End A198683EightBounds.
End LeanProofs.
