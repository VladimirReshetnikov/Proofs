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
  PolynomialPairInjectivity RawCodedAssignment RawCodedProofDescent
  RawCodedRankZeroTruthTraversal RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthConcatenation.

Module PABoundedRawCodedFixedLevelTruthConstruction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthConcatenation.

(** The common existential payload underlying positive Sigma and Pi
    certificates.  Keeping the root mode explicit lets Boolean constructors
    combine arbitrary pairs of already decided children uniformly. *)
Definition RawFixedLevelSuccessorCertificateTraversal (M : RawPAModel)
    (lower : nat) (mode root assignmentCode assignmentStep : M) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex mode root assignmentCode assignmentStep.

Arguments RawFixedLevelSuccessorCertificateTraversal
  M lower mode root assignmentCode assignmentStep : clear implicits.

Lemma raw_fixedLevelSuccessorCertificateTraversal_sigma_iff : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep <->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    root assignmentCode assignmentStep.
Proof.
  intros. cbn [RawFixedLevelSuccessorCertificateTraversal
    RawFixedLevelSigmaTruthCertificate]. reflexivity.
Qed.

Lemma raw_fixedLevelSuccessorCertificateTraversal_pi_iff : forall
    (M : RawPAModel) lower root assignmentCode assignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep <->
  RawFixedLevelPiFalsityCertificate M (S lower)
    root assignmentCode assignmentStep.
Proof.
  intros. cbn [RawFixedLevelSuccessorCertificateTraversal
    RawFixedLevelPiFalsityCertificate]. reflexivity.
Qed.

(** Join two independent certificates and expose both roots as earlier states
    of the next append index.  The first root keeps its old index; the second
    root receives the first traversal's bound as an offset. *)
Theorem raw_fixedLevelSuccessorCertificateTraversals_join : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    secondMode secondRoot secondAssignmentCode secondAssignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep /\
    exists firstIndex : M,
      RawFixedLevelEarlierState M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound firstIndex firstMode firstRoot
        firstAssignmentCode firstAssignmentStep.
Proof.
  intros M hPA lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    (firstModeCode & firstModeStep & firstFormulaCode & firstFormulaStep &
     firstAssignmentCodeCode & firstAssignmentCodeStep &
     firstAssignmentStepCode & firstAssignmentStepStep &
     firstBound & firstRootIndex & hfirst)
    (secondModeCode & secondModeStep & secondFormulaCode & secondFormulaStep &
     secondAssignmentCodeCode & secondAssignmentCodeStep &
     secondAssignmentStepCode & secondAssignmentStepStep &
     secondBound & secondRootIndex & hsecond).
  pose proof hfirst as hfirstParts.
  destruct hfirstParts as
    [_ [_ [_ [_ [hfirstRootBelow [hfirstRootLookup _]]]]]].
  destruct (raw_fixedLevelSuccessorTruthTraversals_concatenate M hPA lower
    firstModeCode firstModeStep firstFormulaCode firstFormulaStep
    firstAssignmentCodeCode firstAssignmentCodeStep
    firstAssignmentStepCode firstAssignmentStepStep
    firstBound firstRootIndex firstMode firstRoot
    firstAssignmentCode firstAssignmentStep
    secondModeCode secondModeStep secondFormulaCode secondFormulaStep
    secondAssignmentCodeCode secondAssignmentCodeStep
    secondAssignmentStepCode secondAssignmentStepStep
    secondBound secondRootIndex secondMode secondRoot
    secondAssignmentCode secondAssignmentStep hfirst hsecond)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hjoined & hfirstLookup).
  pose proof hjoined as hjoinedParts.
  destruct hjoinedParts as
    [_ [_ [_ [_ [hsecondRootBelow [hsecondRootLookup _]]]]]].
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep,
    (raw_add M firstBound secondBound),
    (raw_add M firstBound secondRootIndex).
  split; [exact hjoined |]. split.
  - split; assumption.
  - exists firstRootIndex. split.
    + exact (raw_lt_le_trans_pair M hPA firstRootIndex firstBound
        (raw_add M firstBound secondBound)
        hfirstRootBelow (raw_proof_left_le_sum M firstBound secondBound)).
    + exact hfirstLookup.
Qed.

(** Append one represented row while leaving its root mode abstract.  The two
    public Sigma/Pi wrappers below are just the corresponding projections of
    this common construction. *)
Lemma raw_fixedLevelSuccessorTruthTraversal_append_mode_internal : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parentMode parent parentAssignmentCode parentAssignmentStep,
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
    bound parentMode parent parentAssignmentCode parentAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    parentMode parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    parentMode parent parentAssignmentCode parentAssignmentStep
    htraversal hrow.
  destruct htraversal as
    [hmode [hformula [hassignmentCode
      [hassignmentStep [_ [_ hrows]]]]]].
  destruct (raw_fixedLevelClosedSuccessorRow_append_traversal M hPA
    lower (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound parentMode parent parentAssignmentCode parentAssignmentStep
    hmode hformula hassignmentCode hassignmentStep hrows hrow)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep & hnewTraversal).
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep,
    (raw_succ M bound), bound.
  exact hnewTraversal.
Qed.

(** Higher-order wrappers used only at the Rocq proof level.  The row builder
    receives the concrete beta tables extracted from a child certificate;
    its conclusion is still the ordinary represented closed-row predicate. *)
Theorem raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    childMode child childAssignmentCode childAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex childMode child
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelSigmaMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal) hbuilder.
  apply (proj1 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
    M lower parent parentAssignmentCode parentAssignmentStep)).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_mode_internal M hPA lower
    modeCode modeStep formulaCode formulaStep assignmentCodeCode
    assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex childMode child childAssignmentCode childAssignmentStep
    (rawFixedLevelSigmaMode M) parent parentAssignmentCode parentAssignmentStep
    htraversal (hbuilder _ _ _ _ _ _ _ _ _ _ htraversal)).
Qed.

Theorem raw_fixedLevelSuccessorCertificateTraversal_append_pi_with : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    childMode child childAssignmentCode childAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex childMode child
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelPiMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal) hbuilder.
  apply (proj1 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
    M lower parent parentAssignmentCode parentAssignmentStep)).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_mode_internal M hPA lower
    modeCode modeStep formulaCode formulaStep assignmentCodeCode
    assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex childMode child childAssignmentCode childAssignmentStep
    (rawFixedLevelPiMode M) parent parentAssignmentCode parentAssignmentStep
    htraversal (hbuilder _ _ _ _ _ _ _ _ _ _ htraversal)).
Qed.

Theorem raw_fixedLevelSuccessorCertificateTraversals_append_sigma_with :
  forall (M : RawPAModel), RawPASatisfies M -> forall lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    secondMode secondRoot secondAssignmentCode secondAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep ->
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep ->
    (exists firstIndex,
      RawFixedLevelEarlierState M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound firstIndex firstMode firstRoot
        firstAssignmentCode firstAssignmentStep) ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelSigmaMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep hfirst hsecond hbuilder.
  destruct (raw_fixedLevelSuccessorCertificateTraversals_join M hPA lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    hfirst hsecond)
    as (modeCode & modeStep & formulaCode & formulaStep &
        assignmentCodeCode & assignmentCodeStep &
        assignmentStepCode & assignmentStepStep & bound & secondIndex &
        htraversal & hsecondEarlier & hfirstEarlier).
  apply (proj1 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
    M lower parent parentAssignmentCode parentAssignmentStep)).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_mode_internal M hPA lower
    modeCode modeStep formulaCode formulaStep assignmentCodeCode
    assignmentCodeStep assignmentStepCode assignmentStepStep
    bound secondIndex secondMode secondRoot
    secondAssignmentCode secondAssignmentStep
    (rawFixedLevelSigmaMode M) parent parentAssignmentCode parentAssignmentStep
    htraversal (hbuilder _ _ _ _ _ _ _ _ _ _ htraversal
      hsecondEarlier hfirstEarlier)).
Qed.

Theorem raw_fixedLevelSuccessorCertificateTraversals_append_pi_with :
  forall (M : RawPAModel), RawPASatisfies M -> forall lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    secondMode secondRoot secondAssignmentCode secondAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep ->
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondRoot
      secondAssignmentCode secondAssignmentStep ->
    (exists firstIndex,
      RawFixedLevelEarlierState M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound firstIndex firstMode firstRoot
        firstAssignmentCode firstAssignmentStep) ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelPiMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep hfirst hsecond hbuilder.
  destruct (raw_fixedLevelSuccessorCertificateTraversals_join M hPA lower
    firstMode firstRoot firstAssignmentCode firstAssignmentStep
    secondMode secondRoot secondAssignmentCode secondAssignmentStep
    hfirst hsecond)
    as (modeCode & modeStep & formulaCode & formulaStep &
        assignmentCodeCode & assignmentCodeStep &
        assignmentStepCode & assignmentStepStep & bound & secondIndex &
        htraversal & hsecondEarlier & hfirstEarlier).
  apply (proj1 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
    M lower parent parentAssignmentCode parentAssignmentStep)).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_mode_internal M hPA lower
    modeCode modeStep formulaCode formulaStep assignmentCodeCode
    assignmentCodeStep assignmentStepCode assignmentStepStep
    bound secondIndex secondMode secondRoot
    secondAssignmentCode secondAssignmentStep
    (rawFixedLevelPiMode M) parent parentAssignmentCode parentAssignmentStep
    htraversal (hbuilder _ _ _ _ _ _ _ _ _ _ htraversal
      hsecondEarlier hfirstEarlier)).
Qed.

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
