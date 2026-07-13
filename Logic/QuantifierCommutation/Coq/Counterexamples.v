(*
  Finite constructive counterexamples to commutation of nested [no_exists]
  and nested [exists!].  No excluded middle, choice, or extensionality is
  used.
*)

From QuantifierCommutation Require Import Commutation.

Import QuantifierLaws.

Set Implicit Arguments.

Module QuantifierCounterexamples.

(** * Nested [no_exists] does not commute *)

Inductive two : Type :=
| two_zero
| two_one.

(** Every row contains [two_zero], while column [two_one] is empty. *)
Definition no_exists_relation (_x y : two) : Prop := y = two_zero.

Theorem nested_no_exists_xy_holds :
    nested_no_exists_xy no_exists_relation.
Proof.
  unfold nested_no_exists_xy, no_exists, no_exists_relation.
  intros [x Hempty].
  apply Hempty. exists two_zero. reflexivity.
Qed.

Theorem nested_no_exists_yx_fails :
    ~ nested_no_exists_yx no_exists_relation.
Proof.
  unfold nested_no_exists_yx, no_exists, no_exists_relation.
  intros Houter.
  apply Houter. exists two_one.
  intros [x Himpossible]. discriminate Himpossible.
Qed.

(** Thus even the forward implication needed to swap the quantifiers fails. *)
Theorem nested_no_exists_swap_implication_fails :
    ~ (nested_no_exists_xy no_exists_relation ->
       nested_no_exists_yx no_exists_relation).
Proof.
  intros Hswap.
  apply nested_no_exists_yx_fails.
  apply Hswap.
  exact nested_no_exists_xy_holds.
Qed.

Theorem nested_no_exists_not_equivalent :
    ~ (nested_no_exists_xy no_exists_relation <->
       nested_no_exists_yx no_exists_relation).
Proof.
  intros Hequiv.
  apply nested_no_exists_yx_fails.
  apply (proj1 Hequiv).
  exact nested_no_exists_xy_holds.
Qed.

(** * Nested unique existence does not commute *)

Inductive three : Type :=
| point_a
| point_b
| point_c.

(**
  The relation is exactly [(a,a), (b,b), (b,c)].  Its rows contain
  respectively

    {a}, {b,c}, {},

  whereas the columns contain respectively

    {a}, {b}, {b}.

  Consequently exactly one row is a singleton, but all three columns are
  singletons.
*)
Definition exists_unique_relation (x y : three) : Prop :=
  match x, y with
  | point_a, point_a => True
  | point_b, point_b => True
  | point_b, point_c => True
  | _, _ => False
  end.

Lemma row_a_is_unique :
    exists! y, exists_unique_relation point_a y.
Proof.
  exists point_a. split.
  - exact I.
  - intros y Hy. destruct y; simpl in Hy.
    + reflexivity.
    + contradiction.
    + contradiction.
Qed.

Lemma row_b_is_not_unique :
    ~ (exists! y, exists_unique_relation point_b y).
Proof.
  intros [y [_ Hunique]].
  pose proof (Hunique point_b I) as Hyb.
  pose proof (Hunique point_c I) as Hyc.
  assert (point_b = point_c) as Hbc.
  { rewrite <- Hyb. exact Hyc. }
  discriminate Hbc.
Qed.

Lemma row_c_is_not_unique :
    ~ (exists! y, exists_unique_relation point_c y).
Proof.
  intros [y [Hy _]].
  destruct y; simpl in Hy; contradiction.
Qed.

Lemma column_a_is_unique :
    exists! x, exists_unique_relation x point_a.
Proof.
  exists point_a. split.
  - exact I.
  - intros x Hx. destruct x; simpl in Hx.
    + reflexivity.
    + contradiction.
    + contradiction.
Qed.

Lemma column_b_is_unique :
    exists! x, exists_unique_relation x point_b.
Proof.
  exists point_b. split.
  - exact I.
  - intros x Hx. destruct x; simpl in Hx.
    + contradiction.
    + reflexivity.
    + contradiction.
Qed.

Lemma column_c_is_unique :
    exists! x, exists_unique_relation x point_c.
Proof.
  exists point_b. split.
  - exact I.
  - intros x Hx. destruct x; simpl in Hx.
    + contradiction.
    + reflexivity.
    + contradiction.
Qed.

Theorem nested_exists_unique_xy_holds :
    nested_exists_unique_xy exists_unique_relation.
Proof.
  unfold nested_exists_unique_xy.
  exists point_a. split.
  - exact row_a_is_unique.
  - intros x Hunique. destruct x.
    + reflexivity.
    + exfalso. exact (row_b_is_not_unique Hunique).
    + exfalso. exact (row_c_is_not_unique Hunique).
Qed.

Theorem nested_exists_unique_yx_fails :
    ~ nested_exists_unique_yx exists_unique_relation.
Proof.
  unfold nested_exists_unique_yx.
  intros [y [_ Hunique]].
  pose proof (Hunique point_a column_a_is_unique) as Hya.
  pose proof (Hunique point_b column_b_is_unique) as Hyb.
  assert (point_a = point_b) as Hab.
  { rewrite <- Hya. exact Hyb. }
  discriminate Hab.
Qed.

(** Again, the forward implication—and therefore equivalence—fails. *)
Theorem nested_exists_unique_swap_implication_fails :
    ~ (nested_exists_unique_xy exists_unique_relation ->
       nested_exists_unique_yx exists_unique_relation).
Proof.
  intros Hswap.
  apply nested_exists_unique_yx_fails.
  apply Hswap.
  exact nested_exists_unique_xy_holds.
Qed.

Theorem nested_exists_unique_not_equivalent :
    ~ (nested_exists_unique_xy exists_unique_relation <->
       nested_exists_unique_yx exists_unique_relation).
Proof.
  intros Hequiv.
  apply nested_exists_unique_yx_fails.
  apply (proj1 Hequiv).
  exact nested_exists_unique_xy_holds.
Qed.

End QuantifierCounterexamples.
