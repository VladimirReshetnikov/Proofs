(**
  Coverage-wide truth transport for shifted eigenvariable contexts.

  Universal introduction and existential elimination evaluate a premise
  under an assignment with one fresh head.  Their premise context is the
  pointwise unit shift of the ambient context.  A proof-wide numeric bound
  lets the same prepend certificate serve every (possibly nonstandard)
  context entry.  This file keeps the synchronized context tables visible,
  so membership, coverage, and the formula-shift row all refer to the same
  occurrence rather than to an externally decoded list.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedContextLists
  RawCodedContextFunctionality RawCodedContextBounds RawCodedContextShift
  RawCodedFormulaOperations RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage RawCodedPAAxiomTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelContextTruth RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFormulaOperationRankPreservation
  RawCodedFormulaShiftAtomicAdequacy.

Module PABoundedRawCodedRestrictedProofEigenContextTruth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.

(** Public membership for the proof-coverage context predicate.  Its hidden
    traversal may differ from the membership witness, so functionality of
    context traversals is used to move the occurrence to the coverage table. *)
Lemma raw_contextAllCodesBelow_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall context coverageBound code,
  RawContextAllCodesBelow M context coverageBound ->
  RawContextListMember M context code ->
  rawLt M code coverageBound.
Proof.
  intros M hPA context coverageBound code
    (bound & tailCode & tailStep & headCode & headStep &
     htraversal & hall) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    context code bound tailCode tailStep headCode headStep htraversal)
    hmember) as [index [hindex hlookup]].
  exact (hall index hindex code hlookup).
Qed.

(** Definedness restricts along the strict proof-wide code bound. *)
Lemma raw_eigenContext_assignment_defined_of_below : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    assignmentCode assignmentStep code coverageBound,
  rawLt M code coverageBound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep code.
Proof.
  intros M hPA assignmentCode assignmentStep code coverageBound
    hcode hdefined index hindex.
  apply hdefined.
  exact (raw_assignment_lt_trans M hPA
    index code coverageBound hindex hcode).
Qed.

(** The coverage-wide eigenvariable transport.  The source context carries
    the atomic and hierarchy-domain resources.  Target atomic adequacy is
    obtained unconditionally from each formula-shift trace, while the target
    assignment and both formula-local assignment graphs are restrictions of
    the one coverage-wide prepend. *)
Theorem raw_eigenContextShift_sigma_true : forall
    (M : RawPAModel), RawPASatisfies M -> forall level
    sourceContext targetContext coverageBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep head,
  RawContextShift M sourceContext targetContext ->
  RawContextAllCodesBelow M sourceContext coverageBound ->
  RawContextAllCodesBelow M targetContext coverageBound ->
  RawContextAllAtomicallyAdequate M sourceContext ->
  RawContextAllBounded M level sourceContext ->
  RawCodedAssignmentDefinedThrough M
    sourceAssignmentCode sourceAssignmentStep coverageBound ->
  RawCodedAssignmentPrepend M
    sourceAssignmentCode sourceAssignmentStep head coverageBound
    targetAssignmentCode targetAssignmentStep ->
  RawContextAllSigmaTrue M (S level) sourceContext
    sourceAssignmentCode sourceAssignmentStep ->
  RawContextAllSigmaTrue M (S level) targetContext
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA level sourceContext targetContext coverageBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep head
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
     sourceHeadStep & targetTailCode & targetTailStep &
     targetHeadCode & targetHeadStep &
     hsourceTraversal & htargetTraversal & hshiftRows)
    hsourceCoverage htargetCoverage hsourceAtomic hsourceBounded
    hsourceDefined hprepend hsourceTruth.
  assert (htargetDefined : RawCodedAssignmentDefinedThrough M
      targetAssignmentCode targetAssignmentStep coverageBound).
  {
    exact (raw_codedAssignmentPrepend_target_definedThrough_bound M hPA
      sourceAssignmentCode sourceAssignmentStep head coverageBound
      targetAssignmentCode targetAssignmentStep hsourceDefined hprepend).
  }
  exists bound, targetTailCode, targetTailStep,
    targetHeadCode, targetHeadStep.
  split; [exact htargetTraversal |].
  intros index hindex targetFormula htargetLookup.
  pose proof hsourceTraversal as hsourceFacts.
  destruct hsourceFacts as [_ [_ [hsourceHeadDefined _]]].
  destruct (hsourceHeadDefined index hindex)
    as [sourceFormula hsourceLookup].
  assert (hsourceMember : RawContextListMember M
      sourceContext sourceFormula).
  {
    apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      sourceContext sourceFormula bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      hsourceTraversal)).
    exists index. split; assumption.
  }
  assert (htargetMember : RawContextListMember M
      targetContext targetFormula).
  {
    apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      targetContext targetFormula bound
      targetTailCode targetTailStep targetHeadCode targetHeadStep
      htargetTraversal)).
    exists index. split; assumption.
  }
  pose proof (hshiftRows index hindex sourceFormula targetFormula
    hsourceLookup htargetLookup) as hshift.
  pose proof (raw_contextAllCodesBelow_member M hPA
    sourceContext coverageBound sourceFormula
    hsourceCoverage hsourceMember) as hsourceBelow.
  pose proof (raw_contextAllCodesBelow_member M hPA
    targetContext coverageBound targetFormula
    htargetCoverage htargetMember) as htargetBelow.
  assert (hsourceFormulaDefined : RawCodedAssignmentDefinedThrough M
      sourceAssignmentCode sourceAssignmentStep sourceFormula).
  {
    exact (raw_eigenContext_assignment_defined_of_below M hPA
      sourceAssignmentCode sourceAssignmentStep sourceFormula coverageBound
      hsourceBelow hsourceDefined).
  }
  assert (htargetFormulaDefined : RawCodedAssignmentDefinedThrough M
      targetAssignmentCode targetAssignmentStep targetFormula).
  {
    exact (raw_eigenContext_assignment_defined_of_below M hPA
      targetAssignmentCode targetAssignmentStep targetFormula coverageBound
      htargetBelow htargetDefined).
  }
  assert (hsourceAdmissible : RawFixedLevelTruthAdmissible M level
      sourceFormula sourceAssignmentCode sourceAssignmentStep).
  {
    split.
    - exact (raw_contextAllAtomicallyAdequate_member M hPA
        sourceContext sourceFormula hsourceAtomic hsourceMember).
    - split; [exact hsourceFormulaDefined |].
      exact (raw_contextAllBounded_member M hPA
        level sourceContext sourceFormula hsourceBounded hsourceMember).
  }
  assert (htargetData : RawCodedFormulaTargetAdmissibilityData M
      targetFormula targetAssignmentCode targetAssignmentStep).
  {
    split.
    - exact (raw_codedFormulaShift_target_atomically_adequate M hPA
        (raw_zero M) (rawNumeralValue M 1)
        sourceFormula targetFormula hshift).
    - exact htargetFormulaDefined.
  }
  assert (hlocalPrepend : RawCodedAssignmentPrepend M
      sourceAssignmentCode sourceAssignmentStep head sourceFormula
      targetAssignmentCode targetAssignmentStep).
  {
    exact (raw_codedAssignmentPrepend_restrict M hPA
      sourceAssignmentCode sourceAssignmentStep head
      sourceFormula coverageBound targetAssignmentCode targetAssignmentStep
      hsourceBelow hprepend).
  }
  assert (hassignmentRelation :
      RawCodedFormulaShiftAssignmentRelation M
        (raw_zero M) (rawNumeralValue M 1) sourceFormula
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep).
  {
    exact (raw_codedFormulaUnitShiftAssignmentRelation_of_prepend M hPA
      sourceFormula sourceAssignmentCode sourceAssignmentStep head
      targetAssignmentCode targetAssignmentStep
      hsourceFormulaDefined hlocalPrepend).
  }
  assert (hready : RawFixedLevelFormulaShiftTransportReady M level
      (raw_zero M) (rawNumeralValue M 1) sourceFormula targetFormula
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).
  {
    exact (raw_fixedLevelFormulaShiftTransportReady_of_rankPreservation
      M (raw_codedFormulaShift_rank_preserving_all M hPA) level
      (raw_zero M) (rawNumeralValue M 1) sourceFormula targetFormula
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hshift hassignmentRelation hsourceAdmissible htargetData).
  }
  pose proof (raw_fixedLevelFormulaShiftTarskiStep_scheduled M hPA level
    (raw_zero M) (rawNumeralValue M 1) sourceFormula targetFormula
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready) as htransport.
  pose proof (raw_contextAllSigmaTrue_member M hPA (S level)
    sourceContext sourceAssignmentCode sourceAssignmentStep
    sourceFormula hsourceTruth hsourceMember) as hsourceSigma.
  exact (proj1 (proj1 htransport) hsourceSigma).
Qed.

End PABoundedRawCodedRestrictedProofEigenContextTruth.
