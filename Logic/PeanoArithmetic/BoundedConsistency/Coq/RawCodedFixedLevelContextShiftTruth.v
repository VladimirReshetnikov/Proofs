(**
  Pointwise fixed-level truth transport across a shifted proof context.

  Binder rules shift every formula in their ambient context.  The raw
  context relation already supplies synchronized source and target head
  tables; this module combines those tables with public context membership
  and pointwise formula Tarski transport.  No context code is decoded into a
  metatheoretic list, and the shared traversal length may be nonstandard.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedContextLists
  RawCodedContextFunctionality RawCodedFormulaOperations RawCodedContextShift
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelContextTruth.

Module PABoundedRawCodedFixedLevelContextShiftTruth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelContextTruth.

(** Only the forward Sigma direction is needed for a context assumption.
    Formula-operation Tarski theorems supply this callback uniformly. *)
Definition RawContextShiftSigmaTransport
    (M : RawPAModel) (truthLevel : nat)
    (sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall sourceFormula targetFormula : M,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sourceFormula targetFormula ->
    RawFixedLevelSigmaTruthCertificate M truthLevel
      sourceFormula sourceAssignmentCode sourceAssignmentStep ->
    RawFixedLevelSigmaTruthCertificate M truthLevel
      targetFormula targetAssignmentCode targetAssignmentStep.

Arguments RawContextShiftSigmaTransport
  M truthLevel sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Theorem raw_contextAllSigmaTrue_shift_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall truthLevel
      sourceContext targetContext
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawContextShift M sourceContext targetContext ->
  RawContextAllSigmaTrue M truthLevel sourceContext
    sourceAssignmentCode sourceAssignmentStep ->
  RawContextShiftSigmaTransport M truthLevel
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawContextAllSigmaTrue M truthLevel targetContext
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA truthLevel sourceContext targetContext
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      hsourceTraversal & htargetTraversal & hrows)
    hsourceTruth htransport.
  exists bound, targetTailCode, targetTailStep,
    targetHeadCode, targetHeadStep.
  split; [exact htargetTraversal |].
  intros index hindex targetFormula htargetLookup.
  pose proof hsourceTraversal as hsourceFacts.
  destruct hsourceFacts as [_ [_ [hsourceDefined _]]].
  destruct (hsourceDefined index hindex)
    as [sourceFormula hsourceLookup].
  assert (hsourceMember :
      RawContextListMember M sourceContext sourceFormula).
  {
    apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      sourceContext sourceFormula bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      hsourceTraversal)).
    exists index. split; assumption.
  }
  pose proof (raw_contextAllSigmaTrue_member M hPA truthLevel
    sourceContext sourceAssignmentCode sourceAssignmentStep
    sourceFormula hsourceTruth hsourceMember) as hsourceSigma.
  exact (htransport sourceFormula targetFormula
    (hrows index hindex sourceFormula targetFormula
      hsourceLookup htargetLookup)
    hsourceSigma).
Qed.

End PABoundedRawCodedFixedLevelContextShiftTruth.
