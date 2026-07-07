(*
  Coq port of the executable ordinal-note layer from
  LeanProofs/A199812.lean.

  The Lean module connects this normal-form computation to mathlib's ordinal
  semantics.  This Coq module ports the discrete Cantor-normal-form recurrence
  used for computation: inner exponents below epsilon_0 are represented by
  ordinal notes, and the tower split recurrence combines notes by
  a, b |-> a + omega^b.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import PowTower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A199812.

Module TowerExpr.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.

Definition PowExpr := PT.Expr.

Inductive ONote : Type :=
| ozero : ONote
| oadd : ONote -> nat -> ONote -> ONote.

Fixpoint onoteEqb (a b : ONote) : bool :=
  match a, b with
  | ozero, ozero => true
  | oadd ae an ar, oadd be bn br =>
      onoteEqb ae be && Nat.eqb an bn && onoteEqb ar br
  | _, _ => false
  end.

Theorem onoteEqb_refl (a : ONote) : onoteEqb a a = true.
Proof.
  induction a as [|e ihe n r ihr].
  - reflexivity.
  - simpl. now rewrite ihe, Nat.eqb_refl, ihr.
Qed.

Fixpoint onoteCompare (a b : ONote) : comparison :=
  match a, b with
  | ozero, ozero => Eq
  | ozero, oadd _ _ _ => Lt
  | oadd _ _ _, ozero => Gt
  | oadd ae an ar, oadd be bn br =>
      match onoteCompare ae be with
      | Eq =>
          match Nat.compare an bn with
          | Eq => onoteCompare ar br
          | c => c
          end
      | c => c
      end
  end.

Definition principalPower (e : ONote) : ONote :=
  oadd e 1 ozero.

Fixpoint addPrincipalPower (a b : ONote) : ONote :=
  match a with
  | ozero => principalPower b
  | oadd e n rest =>
      match onoteCompare e b with
      | Lt => principalPower b
      | Eq => oadd e (S n) ozero
      | Gt => oadd e n (addPrincipalPower rest b)
      end
  end.

Definition combineDegree (a b : ONote) : ONote :=
  addPrincipalPower a b.

Fixpoint degreeNote (e : PowExpr) : ONote :=
  match e with
  | PT.atom => ozero
  | PT.pow a b => combineDegree (degreeNote a) (degreeNote b)
  end.

Theorem degreeNote_eq_sharedCombineEval (e : PowExpr) :
    degreeNote e = PT.eval ozero combineDegree e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Definition computedDegreeValues (n : nat) : list ONote :=
  PT.recursiveValueList onoteEqb ozero combineDegree n.

Definition computedDegreeCount (n : nat) : nat :=
  length (computedDegreeValues n).

Definition a199812 : nat -> nat := computedDegreeCount.

Definition a199812ValuesThroughEleven : list nat :=
  [1; 1; 2; 5; 13; 32; 79; 193; 478; 1196; 3037].

Theorem a199812_values_through_eleven :
    map a199812 (seq 1 11) = a199812ValuesThroughEleven.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_one : a199812 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_two : a199812 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_three : a199812 3 = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_four : a199812 4 = 5.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_five : a199812 5 = 13.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_six : a199812 6 = 32.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_seven : a199812 7 = 79.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_eight : a199812 8 = 193.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_nine : a199812 9 = 478.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_ten : a199812 10 = 1196.
Proof. vm_compute. reflexivity. Qed.

Theorem a199812_eleven : a199812 11 = 3037.
Proof. vm_compute. reflexivity. Qed.

End TowerExpr.

Export TowerExpr.

End A199812.
End LeanProofs.
