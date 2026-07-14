(* ===================================================================== *)
(*  SKI.v                                                               *)
(*                                                                       *)
(*  The ordinary SKI combinator calculus with full contextual reduction. *)
(*  It is the universal reference calculus for the checked Iota compiler. *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction.

Set Implicit Arguments.

Module SKI.

Inductive term : Type :=
| ident : term
| konst : term
| scomb : term
| app : term -> term -> term.

Inductive step : term -> term -> Prop :=
| step_ident : forall x,
    step (app ident x) x
| step_konst : forall x y,
    step (app (app konst x) y) x
| step_scomb : forall x y z,
    step (app (app (app scomb x) y) z)
      (app (app x z) (app y z))
| step_app_left : forall x x' y,
    step x x' -> step (app x y) (app x' y)
| step_app_right : forall x y y',
    step y y' -> step (app x y) (app x y').

Definition reaches : term -> term -> Prop := Reduction.star step.
Definition progresses : term -> term -> Prop := Reduction.plus step.

Lemma reaches_refl : forall x, reaches x x.
Proof. intro x; apply Reduction.star_refl. Qed.

Lemma reaches_one : forall x y, step x y -> reaches x y.
Proof. intros x y h; exact (@Reduction.star_one term step x y h). Qed.

Lemma reaches_trans : forall x y z,
  reaches x y -> reaches y z -> reaches x z.
Proof. intros x y z; apply Reduction.star_trans. Qed.

Lemma reaches_app_left : forall x x' y,
  reaches x x' -> reaches (app x y) (app x' y).
Proof.
  intros x x' y h.
  eapply Reduction.star_map with (f := fun t => app t y) in h.
  - exact h.
  - intros a b hab. now apply step_app_left.
Qed.

Lemma reaches_app_right : forall x y y',
  reaches y y' -> reaches (app x y) (app x y').
Proof.
  intros x y y' h.
  eapply Reduction.star_map with (f := fun t => app x t) in h.
  - exact h.
  - intros a b hab. now apply step_app_right.
Qed.

Lemma progresses_app_left : forall x x' y,
  progresses x x' -> progresses (app x y) (app x' y).
Proof.
  intros x x' y h.
  eapply Reduction.plus_map with (f := fun t => app t y) in h.
  - exact h.
  - intros a b hab. now apply step_app_left.
Qed.

Lemma progresses_app_right : forall x y y',
  progresses y y' -> progresses (app x y) (app x y').
Proof.
  intros x y y' h.
  eapply Reduction.plus_map with (f := fun t => app x t) in h.
  - exact h.
  - intros a b hab. now apply step_app_right.
Qed.

Fixpoint size (t : term) : nat :=
  match t with
  | ident | konst | scomb => 1
  | app lhs rhs => 1 + size lhs + size rhs
  end.

(* The standard self-application loop.  [delta x] reduces to [x x], so *)
(* [omega = delta delta] admits a nonempty cycle.                         *)
Definition delta : term := app (app scomb ident) ident.
Definition omega : term := app delta delta.

Theorem omega_positive_cycle : progresses omega omega.
Proof.
  unfold progresses, omega, delta.
  eapply Reduction.plus_step.
  - apply step_scomb.
  - eapply Reduction.star_step.
    + apply step_app_left.
      apply step_ident.
    + eapply Reduction.star_step.
      * apply step_app_right.
        apply step_ident.
      * apply Reduction.star_refl.
Qed.

End SKI.
