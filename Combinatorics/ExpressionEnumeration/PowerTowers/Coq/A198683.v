(*
  Coq port of the final executable assembly from PowerTowers/A198683.lean.

  The Lean module proves the n = 7 lower bound semantically for principal
  complex powers and combines it with A198683SevenUpper.  This Coq counterpart
  assembles the same public arithmetic surface over the finite symbolic
  quotient from A198683Tower.v, whose n = 7 collapse table is generated from
  the retained Schoenfield certificate.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From PowerTowers.A198683.SmallValues Require Import FiveSix SevenUpper.

Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683.

Module AT := PowerTowers.A198683.Tower.LeanProofs.A198683Tower.
Module FS := PowerTowers.A198683.SmallValues.FiveSix.LeanProofs.A198683FiveSix.
Module SU := PowerTowers.A198683.SmallValues.SevenUpper.LeanProofs.A198683SevenUpper.

Definition a198683 : nat -> nat := AT.a198683.

Theorem a198683_one : a198683 1 = 1.
Proof. exact AT.a198683_one. Qed.

Theorem a198683_two : a198683 2 = 1.
Proof. exact AT.a198683_two. Qed.

Theorem a198683_three : a198683 3 = 2.
Proof. exact AT.a198683_three. Qed.

Theorem a198683_four : a198683 4 = 3.
Proof. exact AT.a198683_four. Qed.

Theorem a198683_five : a198683 5 = 7.
Proof. exact FS.a198683_five. Qed.

Theorem a198683_six : a198683 6 = 15.
Proof. exact FS.a198683_six. Qed.

Theorem a198683_five_le_seven : a198683 5 <= 7.
Proof. exact FS.a198683_five_le_seven. Qed.

Theorem a198683_six_le_fifteen : a198683 6 <= 15.
Proof. exact FS.a198683_six_le_fifteen. Qed.

Theorem a198683_seven_le_thirty_four : a198683 7 <= 34.
Proof. exact SU.a198683_seven_le_thirty_four. Qed.

Theorem thirty_four_le_a198683_seven : 34 <= a198683 7.
Proof. unfold a198683. rewrite SU.a198683_seven. apply Nat.le_refl. Qed.

Theorem a198683_seven : a198683 7 = 34.
Proof. exact SU.a198683_seven. Qed.

Theorem thirty_three_le_a198683_seven : 33 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem thirty_two_le_a198683_seven : 32 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem thirty_one_le_a198683_seven : 31 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem thirty_le_a198683_seven : 30 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_nine_le_a198683_seven : 29 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_eight_le_a198683_seven : 28 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_seven_le_a198683_seven : 27 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_six_le_a198683_seven : 26 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_five_le_a198683_seven : 25 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_four_le_a198683_seven : 24 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_three_le_a198683_seven : 23 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_two_le_a198683_seven : 22 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_one_le_a198683_seven : 21 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem twenty_le_a198683_seven : 20 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem fifteen_le_a198683_seven : 15 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem fourteen_le_a198683_seven : 14 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem eleven_le_a198683_seven : 11 <= a198683 7.
Proof. rewrite a198683_seven. lia. Qed.

Theorem a198683_seven_le_thirty_eight : a198683 7 <= 38.
Proof. rewrite a198683_seven. lia. Qed.

Theorem a198683_seven_le_forty_four : a198683 7 <= 44.
Proof. rewrite a198683_seven. lia. Qed.

Theorem a198683_seven_le_forty_five : a198683 7 <= 45.
Proof. rewrite a198683_seven. lia. Qed.

Theorem a198683_seven_le_fifty_one : a198683 7 <= 51.
Proof. rewrite a198683_seven. lia. Qed.

Theorem a198683_seven_le_fifty_six : a198683 7 <= 56.
Proof. rewrite a198683_seven. lia. Qed.

End A198683.
End LeanProofs.
