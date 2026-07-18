(**
  Every beta-coded assignment is defined at every model-internal index.

  A beta slot is a remainder modulo

      S ((S index) * step),

  hence its modulus is always positive.  The existing assignment API often
  carries a finite [DefinedThrough] premise because that is the convenient
  represented interface for local constructions.  In a full PA model the
  stronger totality fact follows by a genuine PA induction on the code being
  divided.  This matters at quantified truth clauses: their hidden binder
  assignment is only constrained through the quantified formula code, while
  a recursive proof branch may use a larger proof-wide formula bound.

  The proof below never performs metatheoretic division on a carrier element.
  Its induction predicate is the first-order formula saying that the current
  code has a beta remainder at the fixed step and index.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedTermEvaluationRealization PolynomialPairInjectivity.

Module PABoundedRawCodedAssignmentUniversalDefinedness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedPolynomialPairInjectivity.

(** The library exposes the prefix form of this equivalence.  This one-slot
    form is useful as the induction invariant below. *)
Lemma raw_sat_betaEntryExistsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code step index,
  raw_formula_sat M e (betaEntryExistsTermAt code step index) <->
  exists output : M,
    RawBetaEntry M output
      (raw_term_eval M e code)
      (raw_term_eval M e step)
      (raw_term_eval M e index).
Proof.
  intros M e code step index.
  unfold betaEntryExistsTermAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_betaTermTermAt_iff.
  repeat setoid_rewrite raw_term_eval_rename_succ.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** One successor step of Euclidean remainder.  If the old remainder is
    still below the predecessor of the (successor) modulus, increment it.  If
    it is exactly that predecessor, reset it to zero and increment the
    quotient. *)
Lemma raw_betaEntry_code_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall code step index,
  (exists output : M, RawBetaEntry M output code step index) ->
  exists output : M,
    RawBetaEntry M output (raw_succ M code) step index.
Proof.
  intros M hPA code step index
    (output & modulus & hmodulus & quotient & houtput & hcode).
  subst modulus.
  set (base := raw_mul M (raw_succ M index) step).
  change (rawLt M output (raw_succ M base)) in houtput.
  destruct (raw_lt_succ_cases M hPA output base houtput)
    as [hstrict | ->].
  - exists (raw_succ M output), (raw_succ M base).
    split; [reflexivity |]. exists quotient. split.
    + apply (raw_lt_succ_of_le M hPA).
      exact (raw_succ_le_of_lt_pair M hPA output base hstrict).
    + rewrite raw_add_succ by exact hPA.
      now rewrite hcode.
  - exists (raw_zero M), (raw_succ M base).
    split; [reflexivity |]. exists (raw_succ M quotient). split.
    + change (rawLt M (raw_zero M)
        (rawBetaModulus M step index)).
      exact (raw_zero_lt_betaModulus M hPA step index).
    + rewrite raw_assignmentTotality_add_zero_right by exact hPA.
      rewrite raw_succ_mul by exact hPA.
      rewrite raw_add_succ by exact hPA.
      now rewrite hcode.
Qed.

(** PA-definable induction on the dividend proves a remainder exists for an
    arbitrary, possibly nonstandard, code. *)
Theorem raw_betaEntry_exists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall code step index,
  exists output : M, RawBetaEntry M output code step index.
Proof.
  intros M hPA code step index.
  set (phi := betaEntryExistsTermAt (tVar 0) (tVar 1) (tVar 2)).
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => step
    | 1 => index
    | _ => raw_zero M
    end).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_betaEntryExistsTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 0) (tVar 1) (tVar 2))).
      cbn [raw_term_eval scons].
      exists (raw_zero M),
        (raw_succ M (raw_mul M (raw_succ M index) step)).
      split; [reflexivity |]. exists (raw_zero M). split.
      + exact (raw_zero_lt_betaModulus M hPA step index).
      + rewrite (raw_mul_comm M hPA (raw_zero M)).
        rewrite raw_assignmentTotality_mul_zero_right by exact hPA.
        rewrite raw_assignmentTotality_add_zero_right by exact hPA.
        reflexivity.
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      apply (proj2 (raw_sat_betaEntryExistsTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 0) (tVar 1) (tVar 2))).
      cbn [raw_term_eval scons].
      apply (raw_betaEntry_code_successor M hPA current step index).
      apply (proj1 (raw_sat_betaEntryExistsTermAt_iff M
        (scons M current parameterEnv)
        (tVar 0) (tVar 1) (tVar 2))) in hcurrent.
      cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
  }
  unfold phi in hall.
  pose proof (proj1 (raw_sat_betaEntryExistsTermAt_iff M
    (scons M code parameterEnv)
    (tVar 0) (tVar 1) (tVar 2)) (hall code)) as hcode.
  unfold parameterEnv in hcode.
  cbn [raw_term_eval scons] in hcode.
  exact hcode.
Qed.

(** The represented assignment lookup relation is exactly beta-entry with
    the arguments reordered to present an assignment-like API. *)
Theorem raw_codedAssignmentLookup_exists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall code step index,
  exists value : M,
    RawCodedAssignmentLookup M code step index value.
Proof.
  intros M hPA code step index.
  exact (raw_betaEntry_exists_all M hPA code step index).
Qed.

(** Consequently every beta-coded assignment is defined through every
    model-internal bound, including nonstandard bounds. *)
Theorem raw_codedAssignment_definedThrough_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall code step bound,
  RawCodedAssignmentDefinedThrough M code step bound.
Proof.
  intros M hPA code step bound index _.
  exact (raw_codedAssignmentLookup_exists_all M hPA code step index).
Qed.

End PABoundedRawCodedAssignmentUniversalDefinedness.
