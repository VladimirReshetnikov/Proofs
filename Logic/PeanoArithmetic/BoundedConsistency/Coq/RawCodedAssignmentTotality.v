(**
  Unconditional coded assignments through arbitrary model bounds.

  A fixed-level truth argument needs one assignment table defined beyond all
  free-variable lookups made by a possibly nonstandard formula code.  Finite
  meta-level beta realization is insufficient for such a carrier bound.  We
  therefore iterate the already proved arbitrary-value append theorem by an
  actual instance of PA's definable induction schema.

  The values chosen here are all zero; only totality matters.  The theorem is
  also closed into an object-level PA derivation, making explicit that later
  soundness modules do not assume an externally decoded environment.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedAssignment RawCodedFixedLevelTruthTotality.

Import ListNotations.

Module PABoundedRawCodedAssignmentTotality.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.

Definition RawCodedAssignmentExistsThrough (M : RawPAModel)
    (bound : M) : Prop :=
  exists code step : M,
    RawCodedAssignmentDefinedThrough M code step bound.

Arguments RawCodedAssignmentExistsThrough M bound : clear implicits.

Definition codedAssignmentExistsThroughTermAt (bound : term) : formula :=
  pEx (pEx
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (liftTerm 2 bound))).

Lemma raw_assignmentTotality_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_codedAssignmentExistsThroughTermAt_iff : forall
    (M : RawPAModel) e bound,
  raw_formula_sat M e (codedAssignmentExistsThroughTermAt bound) <->
  RawCodedAssignmentExistsThrough M (raw_term_eval M e bound).
Proof.
  intros M e bound.
  unfold codedAssignmentExistsThroughTermAt,
    RawCodedAssignmentExistsThrough.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_assignmentTotality_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedAssignmentExistsThrough_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedAssignmentExistsThrough M (raw_zero M).
Proof.
  intros M hPA.
  exists (raw_zero M), (raw_zero M).
  exact (raw_codedAssignment_empty_defined M hPA).
Qed.

Lemma raw_codedAssignmentExistsThrough_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound,
  RawCodedAssignmentExistsThrough M bound ->
  RawCodedAssignmentExistsThrough M (raw_succ M bound).
Proof.
  intros M hPA bound (code & step & hdefined).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    code step bound (raw_zero M) hdefined)
    as (newCode & newStep & hnewDefined & _).
  exists newCode, newStep. exact hnewDefined.
Qed.

(** This is genuine first-order induction inside [M].  Its induction formula
    is the displayed existential graph, so the argument remains valid when
    [bound] is nonstandard. *)
Theorem raw_codedAssignmentExistsThrough_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound,
  RawCodedAssignmentExistsThrough M bound.
Proof.
  intros M hPA.
  set (phi := codedAssignmentExistsThroughTermAt (tVar 0)).
  set (parameterEnv := fun _ : nat => raw_zero M).
  assert (hall : forall bound,
      raw_formula_sat M (scons M bound parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedAssignmentExistsThroughTermAt_iff M
        (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedAssignmentExistsThrough_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedAssignmentExistsThroughTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_codedAssignmentExistsThroughTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedAssignmentExistsThrough_succ M hPA
        current hcurrent).
  }
  intro bound. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedAssignmentExistsThroughTermAt_iff M
      (scons M bound parameterEnv) (tVar 0))
    (hall bound)) as hbound.
  cbn [raw_term_eval scons] in hbound. exact hbound.
Qed.

Definition codedAssignmentTotalityFormula : formula :=
  pAll (codedAssignmentExistsThroughTermAt (tVar 0)).

Lemma raw_sat_codedAssignmentTotalityFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e codedAssignmentTotalityFormula <->
  forall bound : M, RawCodedAssignmentExistsThrough M bound.
Proof.
  intros M e. unfold codedAssignmentTotalityFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentExistsThroughTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedAssignmentTotalityFormula_sentence :
  Formula.Sentence codedAssignmentTotalityFormula.
Proof.
  intros k hfree.
  unfold codedAssignmentTotalityFormula,
    codedAssignmentExistsThroughTermAt,
    codedAssignmentDefinedThroughTermAt,
    codedAssignmentLookupTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedAssignmentTotalityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedAssignmentTotalityFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_codedAssignmentTotalityFormula_iff M e)).
  exact (raw_codedAssignmentExistsThrough_all M hPA).
Qed.

Theorem PA_proves_codedAssignmentTotalityFormula :
  Formula.BProv Formula.Ax_s [] codedAssignmentTotalityFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedAssignmentTotalityFormula_sentence.
  - exact codedAssignmentTotalityFormula_raw_valid.
Qed.

End PABoundedRawCodedAssignmentTotality.
