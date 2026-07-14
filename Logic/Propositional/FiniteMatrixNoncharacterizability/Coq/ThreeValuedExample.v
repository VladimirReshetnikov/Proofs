(*
  The familiar three-element Heyting chain H3.

  Its values are 0 < u < 1, conjunction and disjunction are min and max,
  implication is 1 when x <= y and y otherwise, and only 1 is designated.
  This file proves the illustrative separating fact: H3 validates

                         (p -> q) \/ (q -> p),

  whereas intuitionistic propositional logic does not derive that formula.
  We deliberately make no claim here that the local matrix semantics is a
  complete semantics, or that every IPC rule is preserved by a single H3
  valuation.
*)

From Stdlib Require Import List Lia.
From NaturalDeduction Require Import Calculus.
From FiniteMatrixNoncharacterizability Require Import
  FiniteMatrixNoncharacterizability.

Import ListNotations.
Import NaturalDeduction.
Import FiniteMatrixTheorem.

Set Implicit Arguments.

Module ThreeValuedExample.

(** Truth tables for the chain [false_value_3 < undecided_value < true_value]. *)
Definition h3_and (x y : three) : three :=
  match x, y with
  | false_value_3, _ => false_value_3
  | _, false_value_3 => false_value_3
  | true_value, z => z
  | z, true_value => z
  | undecided_value, undecided_value => undecided_value
  end.

Definition h3_or (x y : three) : three :=
  match x, y with
  | true_value, _ => true_value
  | _, true_value => true_value
  | false_value_3, z => z
  | z, false_value_3 => z
  | undecided_value, undecided_value => undecided_value
  end.

Definition h3_imp (x y : three) : three :=
  match x with
  | false_value_3 => true_value
  | undecided_value =>
      match y with
      | false_value_3 => false_value_3
      | _ => true_value
      end
  | true_value => y
  end.

Definition h3_designated (x : three) : Prop := x = true_value.

Definition h3_matrix : finite_matrix :=
  make_three_valued_matrix
    false_value_3 h3_and h3_or h3_imp h3_designated.

Definition prelinearity (p q : formula nat) : formula nat :=
  Disj (Impl p q) (Impl q p).

Lemma h3_values_validate_prelinearity : forall x y,
    h3_designated (h3_or (h3_imp x y) (h3_imp y x)).
Proof.
  intros x y. destruct x; destruct y; reflexivity.
Qed.

(** Every H3 valuation designates every instance of prelinearity. *)
Theorem h3_validates_prelinearity : forall p q,
    matrix_valid h3_matrix (prelinearity p q).
Proof.
  intros p q rho.
  change (h3_designated
    (h3_or
      (h3_imp (matrix_eval h3_matrix rho p) (matrix_eval h3_matrix rho q))
      (h3_imp (matrix_eval h3_matrix rho q) (matrix_eval h3_matrix rho p)))).
  apply h3_values_validate_prelinearity.
Qed.

Definition prelinearity_01 : formula nat :=
  prelinearity (atom 0) (atom 1).

(** At the branching root, leaf [i] refutes [atom i -> atom j], and leaf [j]
    refutes the converse. *)
Lemma root_refutes_distinct_prelinearity : forall i j,
    i <> j ->
    ~ forces branching_model root (prelinearity (atom i) (atom j)).
Proof.
  intros i j Hneq Hforce.
  destruct Hforce as [Hij | Hji].
  - specialize (Hij (leaf i) I eq_refl).
    unfold branch_atom_forced in Hij.
    injection Hij as Heq. contradiction.
  - specialize (Hji (leaf j) I eq_refl).
    unfold branch_atom_forced in Hji.
    injection Hji as Heq. apply Hneq. symmetry. exact Heq.
Qed.

Theorem root_refutes_prelinearity_01 :
    ~ forces branching_model root prelinearity_01.
Proof.
  apply root_refutes_distinct_prelinearity. lia.
Qed.

(** Hence the H3-valid formula is not an IPC theorem. *)
Theorem prelinearity_01_not_intuitionistically_derivable :
    ~ intuitionistically_derives [] prelinearity_01.
Proof.
  intros Hderives.
  apply root_refutes_prelinearity_01.
  eapply intuitionistic_kripke_soundness.
  - exact Hderives.
  - intros p Hin. contradiction.
Qed.

Theorem h3_validates_non_IPC_theorem :
    matrix_valid h3_matrix prelinearity_01 /\
    ~ intuitionistically_derives [] prelinearity_01.
Proof.
  split.
  - apply h3_validates_prelinearity.
  - apply prelinearity_01_not_intuitionistically_derivable.
Qed.

End ThreeValuedExample.
