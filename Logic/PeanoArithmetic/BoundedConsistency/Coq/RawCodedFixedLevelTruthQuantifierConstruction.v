(**
  Quantifier constructor laws for positive fixed-level truth certificates.

  A preferred-polarity witness (Sigma existential or Pi universal) appends a
  parent row to the child's same-level traversal under a prepended assignment.
  The opposite polarity is a one-row certificate asserting the absence of a
  lower-level counterexample.  The final decision lemmas isolate precisely
  the only cross-level premise: raising an actual lower counterexample to the
  current successor level.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthConstruction
  RawCodedFixedLevelTruthBooleanConstruction.

Module PABoundedRawCodedFixedLevelTruthQuantifierConstruction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthConstruction.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.

(** A Sigma universal is certified directly by the absence of a lower-level
    Pi counterexample under every represented binder extension. *)
Lemma raw_fixedLevelAll_sigma_of_no_lower_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower) (rawFormulaAllCode M child) ->
  RawFixedLevelNoBinderCounterexample M
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child binderAssignmentCode binderAssignmentStep)
    assignmentCode assignmentStep (rawFormulaAllCode M child) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaAllCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep hdomain hnone.
  assert (hrow : RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFixedLevelSigmaMode M)
      (rawFormulaAllCode M child) assignmentCode assignmentStep).
  {
    left. split; [reflexivity |].
    exists (raw_zero M), child, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. right. right.
    split; [reflexivity | exact hnone].
  }
  destruct (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (rawFixedLevelSigmaMode M) (rawFormulaAllCode M child)
    assignmentCode assignmentStep hrow)
    as (modeCode & modeStep & formulaCode & formulaStep &
        assignmentCodeCode & assignmentCodeStep &
        assignmentStepCode & assignmentStepStep & htraversal).
  cbn [RawFixedLevelSigmaTruthCertificate].
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  exact htraversal.
Qed.

(** A Pi existential is the dual no-counterexample row. *)
Lemma raw_fixedLevelEx_pi_of_no_lower_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower) (rawFormulaExCode M child) ->
  RawFixedLevelNoBinderCounterexample M
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child binderAssignmentCode binderAssignmentStep)
    assignmentCode assignmentStep (rawFormulaExCode M child) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaExCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep hdomain hnone.
  assert (hrow : RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFixedLevelPiMode M)
      (rawFormulaExCode M child) assignmentCode assignmentStep).
  {
    right. split; [reflexivity |].
    exists (raw_zero M), child, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. right.
    split; [reflexivity | exact hnone].
  }
  destruct (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (rawFixedLevelPiMode M) (rawFormulaExCode M child)
    assignmentCode assignmentStep hrow)
    as (modeCode & modeStep & formulaCode & formulaStep &
        assignmentCodeCode & assignmentCodeStep &
        assignmentStepCode & assignmentStepStep & htraversal).
  cbn [RawFixedLevelPiFalsityCertificate].
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  exact htraversal.
Qed.

(** Preferred Sigma existential witness. *)
Lemma raw_fixedLevelEx_sigma_of_witness : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep,
  RawFixedLevelSigmaDomain M (S lower) (rawFormulaExCode M child) ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaExCode M child) newAssignmentCode newAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    child newAssignmentCode newAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaExCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hdomain hprepend hchild.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with M hPA
    lower (rawFixedLevelSigmaMode M) child
    newAssignmentCode newAssignmentStep
    (rawFormulaExCode M child) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower child newAssignmentCode newAssignmentStep)). exact hchild.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    left. split; [reflexivity |].
    exists rootIndex, child, (raw_zero M), (raw_zero M), witness,
      newAssignmentCode, newAssignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. right. left.
    split; [reflexivity |]. split; [exact hprepend |].
    split; [exact hrootBelow | exact hrootLookup].
Qed.

(** Preferred Pi universal counterexample. *)
Lemma raw_fixedLevelAll_pi_of_witness : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep,
  RawFixedLevelPiDomain M (S lower) (rawFormulaAllCode M child) ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    child newAssignmentCode newAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaAllCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hdomain hprepend hchild.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_pi_with M hPA
    lower (rawFixedLevelPiMode M) child
    newAssignmentCode newAssignmentStep
    (rawFormulaAllCode M child) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower child newAssignmentCode newAssignmentStep)). exact hchild.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    right. split; [reflexivity |].
    exists rootIndex, child, (raw_zero M), (raw_zero M), witness,
      newAssignmentCode, newAssignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. left.
    split; [reflexivity |]. split; [exact hprepend |].
    split; [exact hrootBelow | exact hrootLookup].
Qed.

(** Decide a universal once lower Pi counterexamples can be raised to the
    current level.  Classical case analysis here is mirrored by an ordinary
    first-order excluded-middle proof when this semantic theorem is reflected
    through raw model completeness. *)
Theorem raw_fixedLevelAll_decides_from_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower) (rawFormulaAllCode M child) ->
  RawFixedLevelPiDomain M (S lower) (rawFormulaAllCode M child) ->
  (forall witness newAssignmentCode newAssignmentStep,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep ->
    RawFixedLevelPiFalsityCertificate M lower
      child newAssignmentCode newAssignmentStep ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      child newAssignmentCode newAssignmentStep) ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaAllCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep
    hsigmaDomain hpiDomain hraise.
  destruct (classic (exists witness newAssignmentCode newAssignmentStep,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep /\
    RawFixedLevelPiFalsityCertificate M lower
      child newAssignmentCode newAssignmentStep)) as
    [(witness & newAssignmentCode & newAssignmentStep & hprepend & hlower)
    | hnone].
  - right. exact (raw_fixedLevelAll_pi_of_witness M hPA lower child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep hpiDomain hprepend
      (hraise witness newAssignmentCode newAssignmentStep hprepend hlower)).
  - left. apply (raw_fixedLevelAll_sigma_of_no_lower_pi M hPA lower child
      assignmentCode assignmentStep hsigmaDomain).
    exact hnone.
Qed.

Theorem raw_fixedLevelEx_decides_from_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower child
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower) (rawFormulaExCode M child) ->
  RawFixedLevelPiDomain M (S lower) (rawFormulaExCode M child) ->
  (forall witness newAssignmentCode newAssignmentStep,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaExCode M child) newAssignmentCode newAssignmentStep ->
    RawFixedLevelSigmaTruthCertificate M lower
      child newAssignmentCode newAssignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      child newAssignmentCode newAssignmentStep) ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaExCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA lower child assignmentCode assignmentStep
    hsigmaDomain hpiDomain hraise.
  destruct (classic (exists witness newAssignmentCode newAssignmentStep,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaExCode M child) newAssignmentCode newAssignmentStep /\
    RawFixedLevelSigmaTruthCertificate M lower
      child newAssignmentCode newAssignmentStep)) as
    [(witness & newAssignmentCode & newAssignmentStep & hprepend & hlower)
    | hnone].
  - left. exact (raw_fixedLevelEx_sigma_of_witness M hPA lower child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep hsigmaDomain hprepend
      (hraise witness newAssignmentCode newAssignmentStep hprepend hlower)).
  - right. apply (raw_fixedLevelEx_pi_of_no_lower_sigma M hPA lower child
      assignmentCode assignmentStep hpiDomain).
    exact hnone.
Qed.

End PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
