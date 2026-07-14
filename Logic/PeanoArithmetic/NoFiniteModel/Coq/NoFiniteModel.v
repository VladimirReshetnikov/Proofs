(*
  Peano arithmetic has no finite model.

  Finiteness is presented conventionally by mutually inverse maps between a
  carrier and [Fin.t n].  On a finite carrier every injective endomap is
  surjective.  A PA model's successor is injective, but zero is outside its
  image, yielding the contradiction.

  The argument is constructive.  Although the reused PAHF module imports
  broader classical infrastructure for its other developments, no classical
  principle is used by any theorem in this file.
*)

#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Import Lists.List Vectors.Fin Vectors.FinFun.
From PAHF Require Import PAHF.

Set Implicit Arguments.

Module NoFiniteModelTheorem.

(** A specified equivalence with the standard finite type [Fin.t n]. *)
Record FinitePresentation (A : Type) : Type := {
  finite_size : nat;
  finite_encode : A -> Fin.t finite_size;
  finite_decode : Fin.t finite_size -> A;
  finite_decode_encode : forall x,
    finite_decode (finite_encode x) = x;
  finite_encode_decode : forall i,
    finite_encode (finite_decode i) = i
}.

Arguments finite_size {A} _.
Arguments finite_encode {A} _ _.
Arguments finite_decode {A} _ _.

(** Propositional packaging of the existence of such presentation data. *)
Definition HasFinitePresentation (A : Type) : Prop :=
  inhabited (FinitePresentation A).

Lemma finite_encode_injective : forall (A : Type)
    (P : FinitePresentation A),
    Injective (finite_encode P).
Proof.
  intros A P x y Heq.
  rewrite <- (finite_decode_encode P x).
  rewrite <- (finite_decode_encode P y).
  now rewrite Heq.
Qed.

(** A [FinitePresentation] supplies the standard exhaustive-list notion of
    finiteness used by Rocq's constructive finite-function library. *)
Lemma finite_presentation_is_finite : forall (A : Type),
    FinitePresentation A -> Finite A.
Proof.
  intros A P.
  destruct (Fin_Finite (finite_size P)) as [indices Hindices].
  exists (map (finite_decode P) indices).
  intros a.
  apply in_map_iff.
  exists (finite_encode P a). split.
  - apply finite_decode_encode.
  - apply Hindices.
Qed.

(** Equality is decidable by transporting [Fin.eq_dec] across the
    presentation. *)
Definition finite_presentation_eq_dec : forall (A : Type)
    (P : FinitePresentation A) (x y : A), {x = y} + {x <> y}.
Proof.
  intros A P x y.
  destruct (Fin.eq_dec (finite_encode P x) (finite_encode P y))
    as [Heq | Hneq].
  - left. exact (@finite_encode_injective A P x y Heq).
  - right. intro Hxy. apply Hneq. now rewrite Hxy.
Defined.

(** The proposition-level decision procedure expected by [FinFun]. *)
Definition finite_presentation_decidable_eq : forall (A : Type),
    FinitePresentation A -> ListDec.decidable_eq A.
Proof.
  intros A P x y.
  destruct (finite_presentation_eq_dec P x y) as [Heq | Hneq].
  - left. exact Heq.
  - right. exact Hneq.
Defined.

(** The finite pigeonhole principle in the exact form needed below. *)
Theorem injective_endomap_of_finite_carrier_is_surjective :
    forall (A : Type) (P : FinitePresentation A) (f : A -> A),
      Injective f -> Surjective f.
Proof.
  intros A P f Hinjective.
  pose proof (@Endo_Injective_Surjective A
    (finite_presentation_is_finite P)
    (finite_presentation_decidable_eq P) f) as Hfinite.
  exact (proj1 Hfinite Hinjective).
Qed.

(** The generic successor obstruction shared by both PA-model records in
    [PAHF.v]. *)
Theorem finite_carrier_cannot_have_injective_successor_missing_zero :
    forall (A : Type) (P : FinitePresentation A)
      (zero : A) (succ : A -> A),
      Injective succ ->
      (forall a, succ a <> zero) ->
      False.
Proof.
  intros A P zero succ Hinjective Hzero.
  pose proof (@injective_endomap_of_finite_carrier_is_surjective
    A P succ Hinjective) as Hsurjective.
  destruct (Hsurjective zero) as [a Ha].
  exact (Hzero a Ha).
Qed.

(** Every particular model packaged by the repository's existing [PAModel]
    record has no finite presentation. *)
Theorem every_PA_model_has_no_finite_presentation :
    forall M : PAModel, ~ HasFinitePresentation M.
Proof.
  intros M [P].
  exact (@finite_carrier_cannot_have_injective_successor_missing_zero
    M P (pa_zero M) (pa_succ M)
    (pa_succ_injective M) (pa_zero_not_succ M)).
Qed.

(** Headline theorem: there exists no finite model of Peano arithmetic. *)
Theorem no_finite_PA_model_exists :
    ~ exists M : PAModel, HasFinitePresentation M.
Proof.
  intros [M Hfinite].
  exact (every_PA_model_has_no_finite_presentation M Hfinite).
Qed.

Corollary peano_arithmetic_has_no_finite_model :
    ~ exists M : PAModel, HasFinitePresentation M.
Proof.
  exact no_finite_PA_model_exists.
Qed.

(** [PAHF.v] also exposes the distinct nested [PA.Model] interface used by
    its syntactic development.  It has the same finite-successor
    obstruction. *)
Theorem every_PA_Model_has_no_finite_presentation :
    forall M : PA.Model, ~ HasFinitePresentation (PA.carrier M).
Proof.
  intros M [P].
  exact (@finite_carrier_cannot_have_injective_successor_missing_zero
    (PA.carrier M) P (PA.zero M) (PA.succ M)
    (PA.succ_injective M) (PA.zero_not_succ M)).
Qed.

(** Headline theorem for the nested [PA.Model] interface. *)
Theorem no_finite_PA_Model_exists :
    ~ exists M : PA.Model, HasFinitePresentation (PA.carrier M).
Proof.
  intros [M Hfinite].
  exact (every_PA_Model_has_no_finite_presentation M Hfinite).
Qed.

Corollary PA_Model_has_no_finite_model :
    ~ exists M : PA.Model, HasFinitePresentation (PA.carrier M).
Proof.
  exact no_finite_PA_Model_exists.
Qed.

End NoFiniteModelTheorem.
