(*
  Coq port of the finite upper-bound surface from
  PowerTowers/A198683/SmallValues/SevenUpper.lean.

  Lean proves the n = 7 upper bound for principal complex powers by showing
  that the semantic value set is covered by 34 collapsed representatives.  The
  Coq port uses the finite symbolic quotient from A198683Tower.v; its n = 7
  root-combination table is generated from the retained Schoenfield labels and
  checked here by computation.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From PowerTowers.A198683 Require Import Tower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683SevenUpper.

Module AT := PowerTowers.A198683.Tower.LeanProofs.A198683Tower.
Module AS := AT.A198683Support.

Definition valueListSevenCollapsedReps : list AS.Value :=
  [AS.VClass 30; AS.VClass 32; AS.VClass 31; AS.VClass 35; AS.VClass 33;
    AS.VClass 36; AS.VClass 38; AS.VClass 40; AS.VClass 37; AS.VClass 39;
    AS.VClass 44; AS.VClass 43; AS.VClass 42; AS.VClass 41; AS.VClass 53;
    AS.VClass 58; AS.VClass 52; AS.VClass 54; AS.VClass 61; AS.VClass 62;
    AS.VClass 45; AS.VClass 47; AS.VClass 46; AS.VClass 50; AS.VClass 48;
    AS.VClass 51; AS.VClass 60; AS.VClass 55; AS.VClass 57; AS.VClass 56;
    AS.VClass 63; AS.VClass 59; AS.VClass 34; AS.VClass 49].

Theorem valueSet_seven_eq_collapsedReps :
    AT.a198683ValueList 7 = valueListSevenCollapsedReps.
Proof. vm_compute. reflexivity. Qed.

Theorem a198683_seven : AT.a198683 7 = 34.
Proof. vm_compute. reflexivity. Qed.

Theorem a198683_seven_le_thirty_four : AT.a198683 7 <= 34.
Proof. rewrite a198683_seven. apply Nat.le_refl. Qed.

End A198683SevenUpper.
End LeanProofs.
