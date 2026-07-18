(**
  Soundness of the two eigenvariable rules.

  The recursive premise of All-I and the second recursive premise of Ex-E
  are checked under a shifted context and a prepended assignment.  We use a
  prepend defined through the proof-wide coverage bound to run that recursive
  premise.  Quantifier truth may expose a different, shorter prepend witness;
  assignment locality identifies the two only on the body formula, which is
  precisely the finite prefix that its truth certificate can inspect.
*)

From Stdlib Require Import List Arith Lia Classical.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedContextBounds RawCodedContextFunctionality
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofEndpoints
  RawCodedProofAtomicAdequacy RawCodedProofFormulaCoverage
  RawCodedRestrictedProofTraversal RawCodedRestrictedProofAdmissibility
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelContextTruth RawCodedFixedLevelContextShiftTruth
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFormulaOperationRankPreservation
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedFixedLevelTruthAssignmentInvariance
  RawCodedFixedLevelTruthAssignmentInvariancePositive
  RawCodedRestrictedProofEigenContextTruth
  RawCodedRestrictedProofCoveredSoundness
  RawCodedRestrictedProofPropositionalSoundness
  RawCodedRestrictedProofSpecialSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofEigenSoundness.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelContextShiftTruth.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthAssignmentInvariance.
Import PABoundedRawCodedFixedLevelTruthAssignmentInvariancePositive.
Import PABoundedRawCodedRestrictedProofEigenContextTruth.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.
Import PABoundedRawCodedRestrictedProofPropositionalSoundness.
Import PABoundedRawCodedRestrictedProofSpecialSoundness.

(** Endpoint context resources are scattered across the three orthogonal
    proof certificates.  This packaging lemma keeps the eigen proofs below
    focused on assignment normalization. *)
Lemma raw_restrictedProofCovered_endpoint_context_data : forall
    (M : RawPAModel), RawPASatisfies M -> forall level proof coverageBound
      context conclusion,
  RawRestrictedProof M level proof ->
  RawProofAtomicallyAdequate M proof ->
  RawProofFormulaCoverage M proof coverageBound ->
  RawProofEndpoint M proof context conclusion ->
  RawContextAllBounded M level context /\
  RawContextAllAtomicallyAdequate M context /\
  RawContextAllCodesBelow M context coverageBound /\
  rawLt M conclusion coverageBound.
Proof.
  intros M hPA level proof coverageBound context conclusion
    hrestricted hatomic hcoverage hendpoint.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    proof hatomic context conclusion hendpoint) as
    [hcontextAtomic hconclusionAtomic].
  pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
    proof coverageBound hcoverage context conclusion hendpoint) as
    [hcontextCoverage hconclusionBelow].
  destruct hrestricted as (supportCode & supportStep & hcertificate).
  pose proof (raw_restrictedProofCertificate_root_node M hPA
    level proof supportCode supportStep hcertificate) as hrootNode.
  pose proof (raw_restrictedProofNode_endpoint_occurrence M level
    proof supportCode supportStep hrootNode
    context conclusion hendpoint) as
    [hcontextBounded hconclusionBounded].
  repeat split; assumption.
Qed.

(** Reroot all three proof-wide certificates at the same named recursive
    child, then apply the preceding endpoint package. *)
Lemma raw_restrictedProofCovered_recursive_child_endpoint_context_data :
    forall (M : RawPAModel), RawPASatisfies M -> forall level root
      coverageBound,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  forall nodeContext a b c t child1 child2 child3,
  RawProofConstructorCode M
    root nodeContext a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      nodeContext a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  forall childContext childConclusion,
  RawProofEndpoint M child childContext childConclusion ->
  RawContextAllBounded M level childContext /\
  RawContextAllAtomicallyAdequate M childContext /\
  RawContextAllCodesBelow M childContext coverageBound /\
  rawLt M childConclusion coverageBound.
Proof.
  intros M hPA level root coverageBound
    hrestricted hatomic hcoverage
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild
    childContext childConclusion hendpoint.
  destruct (raw_restrictedProofAtomicallyAdequate_recursive_child M hPA
    level root hrestricted hatomic
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild) as
    [hchildRestricted [hchildAtomic hchildBelow]].
  destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
    root coverageBound hcoverage
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild) as
    [hchildCoverage _].
  exact (raw_restrictedProofCovered_endpoint_context_data M hPA
    level child coverageBound childContext childConclusion
    hchildRestricted hchildAtomic hchildCoverage hendpoint).
Qed.

(** A coverage-wide prepend realizes the unit-shift assignment graph for any
    covered source formula.  The reverse Sigma direction is the one used at
    the end of Ex-E, where the recursive premise proves the shifted goal. *)
Lemma raw_fixedLevelSigmaTruthCertificate_unit_shift_back : forall
    (M : RawPAModel), RawPASatisfies M -> forall level
      source target coverageBound
      sourceCode sourceStep targetCode targetStep witness,
  rawLt M source coverageBound ->
  rawLt M target coverageBound ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) source target ->
  RawCodedAssignmentDefinedThrough M
    sourceCode sourceStep coverageBound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep witness coverageBound targetCode targetStep ->
  RawFixedLevelTruthAdmissible M level source sourceCode sourceStep ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    target targetCode targetStep ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    source sourceCode sourceStep.
Proof.
  intros M hPA level source target coverageBound
    sourceCode sourceStep targetCode targetStep witness
    hsourceBelow htargetBelow hshift hdefined hprepend
    hsourceAdmissible htargetSigma.
  assert (hsourceDefined : RawCodedAssignmentDefinedThrough M
      sourceCode sourceStep source).
  { exact (raw_codedAssignmentDefinedThrough_of_lt M hPA
      sourceCode sourceStep source coverageBound
      hsourceBelow hdefined). }
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    sourceCode sourceStep witness source coverageBound
    targetCode targetStep hsourceBelow hprepend) as hprependSource.
  assert (hassignmentRelation :
      RawCodedFormulaShiftAssignmentRelation M
        (raw_zero M) (rawNumeralValue M 1) source
        sourceCode sourceStep targetCode targetStep).
  { exact (raw_codedFormulaUnitShiftAssignmentRelation_of_prepend M hPA
      source sourceCode sourceStep witness targetCode targetStep
      hsourceDefined hprependSource). }
  pose proof (raw_codedAssignmentPrepend_definedThrough M hPA
    sourceCode sourceStep witness coverageBound targetCode targetStep
    hdefined hprepend) as htargetDefinedSucc.
  assert (htargetBelowSucc : rawLt M target (raw_succ M coverageBound)).
  { exact (raw_assignment_lt_trans M hPA target coverageBound
      (raw_succ M coverageBound) htargetBelow
      (raw_assignment_lt_self_succ M hPA coverageBound)). }
  assert (htargetDefined : RawCodedAssignmentDefinedThrough M
      targetCode targetStep target).
  { exact (raw_codedAssignmentDefinedThrough_of_lt M hPA
      targetCode targetStep target (raw_succ M coverageBound)
      htargetBelowSucc htargetDefinedSucc). }
  assert (htargetData : RawCodedFormulaTargetAdmissibilityData M
      target targetCode targetStep).
  { split.
    - exact (raw_codedFormulaShift_target_atomically_adequate M hPA
        (raw_zero M) (rawNumeralValue M 1) source target hshift).
    - exact htargetDefined. }
  pose proof
    (raw_fixedLevelFormulaShiftTransportReady_of_rankPreservation
      M (raw_codedFormulaShift_rank_preserving_all M hPA)
      level (raw_zero M) (rawNumeralValue M 1) source target
      sourceCode sourceStep targetCode targetStep
      hshift hassignmentRelation hsourceAdmissible htargetData) as hready.
  pose proof (raw_fixedLevelFormulaShiftTarskiStep_scheduled M hPA
    level (raw_zero M) (rawNumeralValue M 1) source target
    sourceCode sourceStep targetCode targetStep hready) as htransport.
  exact (proj2 (proj1 htransport) htargetSigma).
Qed.

(** Endpoint witnesses for the two selected constructor cases. *)
Lemma raw_proofEndpoint_allI_case : forall (M : RawPAModel)
    (root context a b c t child1 child2 child3 : M),
  root = rawListCode M [rawNumeralValue M 11; context; a; child1] ->
  RawProofEndpoint M root context (rawFormulaAllCode M a).
Proof.
  intros M root context a b c t child1 child2 child3 hroot.
  exists context, a, b, c, t, child1, child2, child3.
  split; [reflexivity |]. unfold RawProofEndpointCases.
  do 11 right. left. now split.
Qed.

Lemma raw_proofEndpoint_exE_case : forall (M : RawPAModel)
    (root context a b c t child1 child2 child3 : M),
  root = rawListCode M
    [rawNumeralValue M 14; context; a; b; child1; child2] ->
  RawProofEndpoint M root context b.
Proof.
  intros M root context a b c t child1 child2 child3 hroot.
  exists context, a, b, c, t, child1, child2, child3.
  split; [reflexivity |]. unfold RawProofEndpointCases.
  do 14 right. left. now split.
Qed.

End PABoundedRawCodedRestrictedProofEigenSoundness.
