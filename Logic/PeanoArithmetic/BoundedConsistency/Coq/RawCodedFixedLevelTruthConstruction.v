(**
  Small construction principles for positive fixed-level truth certificates.

  The local successor-row checker is useful only after its same-level child
  references have been placed in a globally closed traversal.  This module
  packages the two boundary operations used repeatedly by the totality
  proof: creating a one-row traversal for an atomic row, and appending a
  closed parent row to an existing traversal.  Both operations allocate the
  four synchronized Goedel-beta tables internally, so they remain valid for
  arbitrary elements of an arbitrary model of PA.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedRankZeroTruthTraversal RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthConcatenation.

Module PABoundedRawCodedFixedLevelTruthConstruction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthConcatenation.

(** An atomic successor row has no earlier-state dependencies.  Starting
    from four empty beta tables and applying the already proved arbitrary-
    value append operation therefore yields a genuine one-row traversal. *)
Theorem raw_fixedLevelClosedSuccessorRow_singleton_traversal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower lowerSigmaEvidence lowerPiEvidence
    mode code assignmentCode assignmentStep,
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) mode code assignmentCode assignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (raw_succ M (raw_zero M)) (raw_zero M)
      mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    mode code assignmentCode assignmentStep hrow.
  pose proof (raw_codedAssignment_empty_defined M hPA) as hempty.
  apply (raw_fixedLevelClosedSuccessorRow_append_traversal M hPA
    lower lowerSigmaEvidence lowerPiEvidence
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) mode code assignmentCode assignmentStep);
    try exact hempty.
  - intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hindex _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - exact hrow.
Qed.

(** A rank-zero truth bit can be replayed as the atomic alternative of a
    successor row at any external level.  The advertised successor domain is
    explicit: rank-zero evaluation alone intentionally says nothing about
    the hierarchy bound attached to a malformed code. *)
Theorem raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower root assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower) root ->
  RawRankZeroTruthCertificate M root (rawNumeralValue M 1)
    assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    root assignmentCode assignmentStep.
Proof.
  intros M hPA lower root assignmentCode assignmentStep hdomain htruth.
  assert (hrow : RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep).
  {
    left. split; [reflexivity |].
    exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |]. left. exact htruth.
  }
  destruct (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep hrow)
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

Theorem raw_fixedLevelPiFalsityCertificate_successor_of_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower root assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower) root ->
  RawRankZeroTruthCertificate M root (raw_zero M)
    assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    root assignmentCode assignmentStep.
Proof.
  intros M hPA lower root assignmentCode assignmentStep hdomain hfalse.
  assert (hrow : RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep).
  {
    right. split; [reflexivity |].
    exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |]. left. exact hfalse.
  }
  destruct (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep hrow)
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

(** Append a Sigma parent to any already closed positive traversal.  The
    supplied row may refer to any states in the old prefix; after the append,
    the old bound itself is the distinguished parent index. *)
Theorem raw_fixedLevelSuccessorTruthTraversal_append_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound (rawFixedLevelSigmaMode M) parent
    parentAssignmentCode parentAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal hrow.
  destruct htraversal as
    [hmode [hformula [hassignmentCode
      [hassignmentStep [_ [_ hrows]]]]]].
  destruct (raw_fixedLevelClosedSuccessorRow_append_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound (rawFixedLevelSigmaMode M) parent
    parentAssignmentCode parentAssignmentStep
    hmode hformula hassignmentCode hassignmentStep hrows hrow)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep & hnewTraversal).
  cbn [RawFixedLevelSigmaTruthCertificate].
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep,
    (raw_succ M bound), bound.
  exact hnewTraversal.
Qed.

Theorem raw_fixedLevelSuccessorTruthTraversal_append_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound (rawFixedLevelPiMode M) parent
    parentAssignmentCode parentAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal hrow.
  destruct htraversal as
    [hmode [hformula [hassignmentCode
      [hassignmentStep [_ [_ hrows]]]]]].
  destruct (raw_fixedLevelClosedSuccessorRow_append_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound (rawFixedLevelPiMode M) parent
    parentAssignmentCode parentAssignmentStep
    hmode hformula hassignmentCode hassignmentStep hrows hrow)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep & hnewTraversal).
  cbn [RawFixedLevelPiFalsityCertificate].
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep,
    (raw_succ M bound), bound.
  exact hnewTraversal.
Qed.

End PABoundedRawCodedFixedLevelTruthConstruction.
