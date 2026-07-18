(**
  Reindexing closed fixed-level truth rows.

  Merging independently built positive-level truth certificates requires
  copying one state traversal after another.  Earlier-state witnesses in the
  copied traversal cannot retain their old numeric indices: every source
  index [i] must become [offset + i].  This module proves the local theorem
  which makes that later accumulator construction possible.

  The offset and all indices are elements of an arbitrary PA model.  Strict
  order is transported by PA's associativity law, and every recursive row
  witness is rebuilt with its shifted index.  Formula codes, assignments,
  lower-level certificates, and binder-prepend evidence are unchanged.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal.

Module PABoundedRawCodedFixedLevelTruthReindexing.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.

Lemma raw_lt_add_left_fixedTruth : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset left right,
  rawLt M left right ->
  rawLt M (raw_add M offset left) (raw_add M offset right).
Proof.
  intros M hPA offset left right [difference hdifference].
  exists difference.
  rewrite raw_add_assoc by exact hPA.
  rewrite hdifference. reflexivity.
Qed.

(** Every source state strictly below [current] is present in the target at
    its offset index.  Functionality of either table is intentionally not
    baked into this interface. *)
Definition RawFixedLevelStateOffsetEmbedding (M : RawPAModel)
    (offset current
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep : M) : Prop :=
  forall index mode code assignmentCode assignmentStep,
    rawLt M index current ->
    RawFixedLevelStateLookup M
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawFixedLevelStateLookup M
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      (raw_add M offset index) mode code assignmentCode assignmentStep.

Arguments RawFixedLevelStateOffsetEmbedding M
  offset current
  sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
  sourceAssignmentCodeCode sourceAssignmentCodeStep
  sourceAssignmentStepCode sourceAssignmentStepStep
  targetModeCode targetModeStep targetFormulaCode targetFormulaStep
  targetAssignmentCodeCode targetAssignmentCodeStep
  targetAssignmentStepCode targetAssignmentStepStep : clear implicits.

Lemma raw_fixedLevelEarlierState_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      offset current
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep,
  RawFixedLevelStateOffsetEmbedding M offset current
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep ->
  RawFixedLevelEarlierState M
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    current childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep ->
  RawFixedLevelEarlierState M
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    (raw_add M offset current) (raw_add M offset childIndex)
    expectedMode childCode childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA offset current
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep hembed [hchild hlookup].
  split.
  - exact (raw_lt_add_left_fixedTruth M hPA offset
      childIndex current hchild).
  - exact (hembed childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep hchild hlookup).
Qed.

(** Rebuild one closed row at its offset index.  The proof follows the exact
    constructor alternatives rather than relying on an informal statement
    that rows are "obviously invariant" under reindexing. *)
Theorem raw_fixedLevelClosedSuccessorRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower lowerSigmaEvidence lowerPiEvidence
      offset current
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      mode code assignmentCode assignmentStep,
  RawFixedLevelStateOffsetEmbedding M offset current
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    current mode code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    (raw_add M offset current) mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    offset current
    sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
    sourceAssignmentCodeCode sourceAssignmentCodeStep
    sourceAssignmentStepCode sourceAssignmentStepStep
    targetModeCode targetModeStep targetFormulaCode targetFormulaStep
    targetAssignmentCodeCode targetAssignmentCodeStep
    targetAssignmentStepCode targetAssignmentStepStep
    mode code assignmentCode assignmentStep hembed hclosed.
  assert (hearlier : forall childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep,
    RawFixedLevelEarlierState M
      sourceModeCode sourceModeStep sourceFormulaCode sourceFormulaStep
      sourceAssignmentCodeCode sourceAssignmentCodeStep
      sourceAssignmentStepCode sourceAssignmentStepStep
      current childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelEarlierState M
      targetModeCode targetModeStep targetFormulaCode targetFormulaStep
      targetAssignmentCodeCode targetAssignmentCodeStep
      targetAssignmentStepCode targetAssignmentStepStep
      (raw_add M offset current) (raw_add M offset childIndex)
      expectedMode childCode childAssignmentCode childAssignmentStep).
  {
    intros. eapply raw_fixedLevelEarlierState_offset; eauto.
  }
  destruct hclosed as [[hmode hsigma] | [hmode hpi]].
  - left. split; [exact hmode |].
    destruct hsigma as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hsigma).
    exists (raw_add M offset leftIndex), leftCode,
      (raw_add M offset rightIndex), rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelSigmaSuccessorWitnessRow in hsigma |- *.
    destruct hsigma as [hdomain hcases]. split; [exact hdomain |].
    destruct hcases as
      [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
    + left. exact hzero.
    + right. left.
      destruct himpLeft as [hcode [hleft hspare]].
      split; [exact hcode |]. split; [exact (hearlier _ _ _ _ _ hleft) |].
      exact hspare.
    + right. right. left.
      destruct himpRight as [hcode [hright hspare]].
      split; [exact hcode |]. split; [exact (hearlier _ _ _ _ _ hright) |].
      exact hspare.
    + right. right. right. left.
      destruct hand as [hcode [hleft hright]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. left.
      destruct hor as [hcode [hleft | hright]].
      * split; [exact hcode |]. left. exact (hearlier _ _ _ _ _ hleft).
      * split; [exact hcode |]. right. exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. right. left.
      destruct hex as [hcode [hprepend hleft]].
      split; [exact hcode |]. split; [exact hprepend |].
      exact (hearlier _ _ _ _ _ hleft).
    + right. right. right. right. right. right. exact hall.
  - right. split; [exact hmode |].
    destruct hpi as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hpi).
    exists (raw_add M offset leftIndex), leftCode,
      (raw_add M offset rightIndex), rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelPiSuccessorWitnessRow in hpi |- *.
    destruct hpi as [hdomain hcases]. split; [exact hdomain |].
    destruct hcases as
      [hzero | [himp | [hand | [hor | [hall | hex]]]]].
    + left. exact hzero.
    + right. left.
      destruct himp as [hcode [hleft [hright hspare]]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * split; [exact (hearlier _ _ _ _ _ hright) | exact hspare].
    + right. right. left.
      destruct hand as [hcode [hleft | hright]].
      * split; [exact hcode |]. left. exact (hearlier _ _ _ _ _ hleft).
      * split; [exact hcode |]. right. exact (hearlier _ _ _ _ _ hright).
    + right. right. right. left.
      destruct hor as [hcode [hleft hright]].
      split; [exact hcode |]. split.
      * exact (hearlier _ _ _ _ _ hleft).
      * exact (hearlier _ _ _ _ _ hright).
    + right. right. right. right. left.
      destruct hall as [hcode [hprepend hleft]].
      split; [exact hcode |]. split; [exact hprepend |].
      exact (hearlier _ _ _ _ _ hleft).
    + right. right. right. right. right. exact hex.
Qed.

End PABoundedRawCodedFixedLevelTruthReindexing.
