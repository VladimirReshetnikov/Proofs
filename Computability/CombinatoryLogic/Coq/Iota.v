(* ===================================================================== *)
(*  Iota.v                                                              *)
(*                                                                       *)
(*  Pure Iota programs have exactly one leaf constructor and application. *)
(*  Reduction is presented in a separate runtime language containing the *)
(*  auxiliary S and K combinators used by the standard rules             *)
(*                                                                       *)
(*      iota x  -->  x S K                                               *)
(*      K x y   -->  x                                                   *)
(*      S x y z -->  x z (y z).                                         *)
(*                                                                       *)
(*  Thus S and K may occur in checked intermediate configurations, but   *)
(*  never in a source program or in the output of the SKI compiler.       *)
(* ===================================================================== *)

From CombinatoryLogic Require Import Reduction.

Set Implicit Arguments.

Module IotaRuntime.

Inductive term : Type :=
| iota : term
| konst : term
| scomb : term
| app : term -> term -> term.

(* Runtime terms in the image of the pure source language. *)
Inductive pure : term -> Prop :=
| pure_iota : pure iota
| pure_app : forall x y, pure x -> pure y -> pure (app x y).

Inductive step : term -> term -> Prop :=
| step_iota : forall x,
    step (app iota x) (app (app x scomb) konst)
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

End IotaRuntime.

Module Iota.

(* This is the complete source grammar: no auxiliary runtime symbol can be *)
(* constructed at this type.                                               *)
Inductive term : Type :=
| iota : term
| app : term -> term -> term.

Fixpoint embed (t : term) : IotaRuntime.term :=
  match t with
  | iota => IotaRuntime.iota
  | app lhs rhs => IotaRuntime.app (embed lhs) (embed rhs)
  end.

Lemma embed_pure : forall t, IotaRuntime.pure (embed t).
Proof.
  induction t as [|lhs IHlhs rhs IHrhs]; simpl.
  - apply IotaRuntime.pure_iota.
  - now apply IotaRuntime.pure_app.
Qed.

Lemma pure_has_preimage : forall runtime,
  IotaRuntime.pure runtime -> exists source, embed source = runtime.
Proof.
  intros runtime hpure.
  induction hpure as [|lhs rhs _ IHlhs _ IHrhs].
  - exists iota. reflexivity.
  - destruct IHlhs as [sourceL hsourceL].
    destruct IHrhs as [sourceR hsourceR].
    exists (app sourceL sourceR).
    simpl. now rewrite hsourceL, hsourceR.
Qed.

Theorem pure_iff_embedded : forall runtime,
  IotaRuntime.pure runtime <-> exists source, embed source = runtime.
Proof.
  intro runtime. split.
  - apply pure_has_preimage.
  - intros [source hsource].
    rewrite <- hsource.
    apply embed_pure.
Qed.

Lemma embed_injective : forall x y, embed x = embed y -> x = y.
Proof.
  induction x as [|xl IHxl xr IHxr]; intros y heq;
    destruct y as [|yl yr]; simpl in heq; try discriminate.
  - reflexivity.
  - inversion heq; subst.
    f_equal; [now apply IHxl | now apply IHxr].
Qed.

Definition reaches (x y : term) : Prop :=
  IotaRuntime.reaches (embed x) (embed y).

Definition progresses (x y : term) : Prop :=
  IotaRuntime.progresses (embed x) (embed y).

Lemma reaches_refl : forall x, reaches x x.
Proof. intro x; apply IotaRuntime.reaches_refl. Qed.

Lemma reaches_trans : forall x y z,
  reaches x y -> reaches y z -> reaches x z.
Proof. intros x y z; apply IotaRuntime.reaches_trans. Qed.

(* Barker's pure-Iota representatives of the ordinary I, K, and S         *)
(* combinators. Application is left-associative in the accompanying prose. *)
Definition identCode : term := app iota iota.
Definition konstCode : term := app iota (app iota identCode).
Definition scombCode : term := app iota (app iota (app iota identCode)).

Fixpoint size (t : term) : nat :=
  match t with
  | iota => 1
  | app lhs rhs => 1 + size lhs + size rhs
  end.

(* Follow the leftmost outermost standard reduction.  This tactic merely   *)
(* assembles constructors of [IotaRuntime.step] and [Reduction.star]; the   *)
(* resulting derivations are ordinary kernel-checked proof terms.          *)
Ltac runtime_one_step :=
  repeat first
    [ apply IotaRuntime.step_iota
    | apply IotaRuntime.step_konst
    | apply IotaRuntime.step_scomb
    | apply IotaRuntime.step_app_left
    | apply IotaRuntime.step_app_right ].

Ltac runtime_head_step :=
  eapply Reduction.star_step;
  [ runtime_one_step
  | cbn [embed identCode konstCode scombCode] ].

Theorem identCode_correct : forall x,
  IotaRuntime.reaches
    (IotaRuntime.app (embed identCode) x) x.
Proof.
  intro x.
  cbn [embed identCode].
  do 5 runtime_head_step.
  apply Reduction.star_refl.
Qed.

Theorem identCode_correct_positive : forall x,
  IotaRuntime.progresses
    (IotaRuntime.app (embed identCode) x) x.
Proof.
  intro x.
  cbn [embed identCode].
  eapply Reduction.plus_step.
  - runtime_one_step.
  - cbn [embed identCode konstCode scombCode].
    do 4 runtime_head_step.
    apply Reduction.star_refl.
Qed.

Theorem konstCode_unfolds :
  IotaRuntime.reaches (embed konstCode) IotaRuntime.konst.
Proof.
  cbn [embed identCode konstCode].
  do 9 runtime_head_step.
  apply Reduction.star_refl.
Qed.

Theorem konstCode_correct : forall x y,
  IotaRuntime.reaches
    (IotaRuntime.app (IotaRuntime.app (embed konstCode) x) y) x.
Proof.
  intros x y.
  eapply IotaRuntime.reaches_trans.
  - apply IotaRuntime.reaches_app_left.
    apply IotaRuntime.reaches_app_left.
    exact konstCode_unfolds.
  - apply IotaRuntime.reaches_one.
    apply IotaRuntime.step_konst.
Qed.

Theorem konstCode_correct_positive : forall x y,
  IotaRuntime.progresses
    (IotaRuntime.app (IotaRuntime.app (embed konstCode) x) y) x.
Proof.
  intros x y.
  cbn [embed identCode konstCode].
  eapply Reduction.plus_step.
  - runtime_one_step.
  - cbn [embed identCode konstCode scombCode].
    do 9 runtime_head_step.
    apply Reduction.star_refl.
Qed.

Theorem scombCode_unfolds :
  IotaRuntime.reaches (embed scombCode) IotaRuntime.scomb.
Proof.
  cbn [embed identCode scombCode].
  do 11 runtime_head_step.
  apply Reduction.star_refl.
Qed.

Theorem scombCode_correct : forall x y z,
  IotaRuntime.reaches
    (IotaRuntime.app
      (IotaRuntime.app (IotaRuntime.app (embed scombCode) x) y) z)
    (IotaRuntime.app (IotaRuntime.app x z) (IotaRuntime.app y z)).
Proof.
  intros x y z.
  eapply IotaRuntime.reaches_trans.
  - apply IotaRuntime.reaches_app_left.
    apply IotaRuntime.reaches_app_left.
    apply IotaRuntime.reaches_app_left.
    exact scombCode_unfolds.
  - apply IotaRuntime.reaches_one.
    apply IotaRuntime.step_scomb.
Qed.

Theorem scombCode_correct_positive : forall x y z,
  IotaRuntime.progresses
    (IotaRuntime.app
      (IotaRuntime.app (IotaRuntime.app (embed scombCode) x) y) z)
    (IotaRuntime.app (IotaRuntime.app x z) (IotaRuntime.app y z)).
Proof.
  intros x y z.
  cbn [embed identCode scombCode].
  eapply Reduction.plus_step.
  - runtime_one_step.
  - cbn [embed identCode konstCode scombCode].
    do 11 runtime_head_step.
    apply Reduction.star_refl.
Qed.

End Iota.
