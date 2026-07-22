(**
  Endpoint admissibility for restricted proof codes.

  Quantifier boundedness and atomic-term adequacy are deliberately separate
  proof-code invariants.  This module joins them only at a genuine proof-rule
  endpoint.  The remaining truth-domain requirement is assignment coverage;
  the canonical all-zero beta assignment supplies it for every model element,
  including nonstandard formula codes.

  The recursive-child corollaries are phrased through the shared constructor
  case table.  They therefore cover every recursive natural-deduction rule
  without duplicating the constructor enumeration here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedAssignmentTotality
  RawCodedContextBounds
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedRestrictedProofTraversal
  RawCodedProofAtomicAdequacy
  RawCodedFixedLevelTruthTotality.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofAdmissibility.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.

(** The conjunction constructor is kept separate from proof syntax.  This is
    useful when a caller already has a global assignment-coverage invariant:
    it only needs to instantiate that invariant at the endpoint formula. *)
Lemma raw_fixedLevelTruthAdmissible_of_bounded_atomic_assignment : forall
    (M : RawPAModel) level formula assignmentCode assignmentStep,
  RawFormulaQuantifierBounded M level formula ->
  RawCodedFormulaAtomicallyAdequate M formula ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep formula ->
  RawFixedLevelTruthAdmissible M level formula
    assignmentCode assignmentStep.
Proof.
  intros M level formula assignmentCode assignmentStep
    hbounded hatomic hdefined.
  unfold RawFixedLevelTruthAdmissible.
  repeat split; assumption.
Qed.

(** Every valid endpoint selected at the root is admissible for fixed-level
    truth under any assignment which covers that conclusion.  Notice that
    this statement quantifies over *every* valid endpoint witness; it does not
    merely use the existential endpoint packaged by the restricted proof
    certificate. *)
Theorem raw_restrictedProof_endpoint_admissible : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  forall context conclusion,
  RawProofEndpoint M root context conclusion ->
  forall assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep conclusion ->
  RawFixedLevelTruthAdmissible M level conclusion
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    context conclusion hendpoint assignmentCode assignmentStep hdefined.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    root hatomicallyAdequate context conclusion hendpoint)
    as [_ hconclusionAtomic].
  destruct hrestricted as
    (supportCode & supportStep & hcertificate).
  pose proof (raw_restrictedProofCertificate_root_node M hPA
    level root supportCode supportStep hcertificate) as hrootNode.
  pose proof (raw_restrictedProofNode_endpoint_occurrence M level
    root supportCode supportStep hrootNode
    context conclusion hendpoint) as [_ hconclusionBounded].
  exact (raw_fixedLevelTruthAdmissible_of_bounded_atomic_assignment
    M level conclusion assignmentCode assignmentStep
    hconclusionBounded hconclusionAtomic hdefined).
Qed.

Theorem raw_restrictedProof_rule_endpoint_admissible : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  forall context conclusion,
  RawProofRuleValid M root context conclusion ->
  forall assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep conclusion ->
  RawFixedLevelTruthAdmissible M level conclusion
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    context conclusion hrule assignmentCode assignmentStep hdefined.
  pose proof (raw_proofRuleValid_endpoint M
    root context conclusion hrule) as hendpoint.
  exact (raw_restrictedProof_endpoint_admissible M hPA
    level root hrestricted hatomicallyAdequate context conclusion
    hendpoint assignmentCode assignmentStep hdefined).
Qed.

(** The canonical zero assignment is defined through every model element, so
    it discharges the only assignment-specific premise of the general root
    endpoint theorem. *)
Corollary raw_restrictedProof_rule_endpoint_admissible_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  forall context conclusion,
  RawProofRuleValid M root context conclusion ->
  RawFixedLevelTruthAdmissible M level conclusion
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    context conclusion hrule.
  exact (raw_restrictedProof_rule_endpoint_admissible M hPA
    level root hrestricted hatomicallyAdequate context conclusion hrule
    (raw_zero M) (raw_zero M)
    (raw_codedZeroAssignment_defined_all M hPA conclusion)).
Qed.

(** Existential proof-wide atomic adequacy restricts to any named recursive
    child.  The support witnesses are retained internally, so no choice or
    external decoding of the proof code is involved. *)
Corollary raw_proofAtomicallyAdequate_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawProofAtomicallyAdequate M root ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawProofAtomicallyAdequate M child /\ rawLt M child root.
Proof.
  intros M hPA root
    (supportCode & supportStep & hadequacy)
    context a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild.
  destruct (raw_proofAtomicAdequacy_recursive_child M hPA
    root supportCode supportStep hadequacy
    context a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild)
    as [hchildAdequacy hchildBelow].
  split.
  - exists supportCode, supportStep. exact hchildAdequacy.
  - exact hchildBelow.
Qed.

(** The two orthogonal proof-wide certificates propagate together. *)
Theorem raw_restrictedProofAtomicallyAdequate_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  RawRestrictedProof M level child /\
  RawProofAtomicallyAdequate M child /\
  rawLt M child root.
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    context a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild.
  destruct (raw_restrictedProof_recursive_child M hPA
    level root hrestricted
    context a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild)
    as [hchildRestricted hchildBelow].
  destruct (raw_proofAtomicallyAdequate_recursive_child M hPA
    root hatomicallyAdequate
    context a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild)
    as [hchildAtomic _].
  repeat split; assumption.
Qed.

(** Consequently every valid endpoint of a named recursive child is already
    in the truth domain at the same external hierarchy level whenever the
    caller's assignment covers the child's conclusion. *)
Corollary raw_restrictedProof_recursive_child_endpoint_admissible :
    forall (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
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
  forall assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion ->
  RawFixedLevelTruthAdmissible M level childConclusion
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild
    childContext childConclusion hchildEndpoint
    assignmentCode assignmentStep hdefined.
  destruct (raw_restrictedProofAtomicallyAdequate_recursive_child M hPA
    level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild)
    as [hchildRestricted [hchildAtomic _]].
  exact (raw_restrictedProof_endpoint_admissible M hPA
    level child hchildRestricted hchildAtomic
    childContext childConclusion hchildEndpoint
    assignmentCode assignmentStep hdefined).
Qed.

Corollary raw_restrictedProof_recursive_child_rule_endpoint_admissible :
    forall (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
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
  RawProofRuleValid M child childContext childConclusion ->
  forall assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion ->
  RawFixedLevelTruthAdmissible M level childConclusion
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild
    childContext childConclusion hchildRule
    assignmentCode assignmentStep hdefined.
  exact (raw_restrictedProof_recursive_child_endpoint_admissible
    M hPA level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild
    childContext childConclusion
    (raw_proofRuleValid_endpoint M child childContext childConclusion
      hchildRule)
    assignmentCode assignmentStep hdefined).
Qed.

(** Canonical-zero specialization of recursive-child admissibility. *)
Corollary raw_restrictedProof_recursive_child_rule_endpoint_admissible_zero :
    forall (M : RawPAModel), RawPASatisfies M -> forall level root,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
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
  RawProofRuleValid M child childContext childConclusion ->
  RawFixedLevelTruthAdmissible M level childConclusion
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild
    childContext childConclusion hchildRule.
  exact (raw_restrictedProof_recursive_child_rule_endpoint_admissible
    M hPA level root hrestricted hatomicallyAdequate
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hcase hroot child hchild
    childContext childConclusion hchildRule
    (raw_zero M) (raw_zero M)
    (raw_codedZeroAssignment_defined_all M hPA childConclusion)).
Qed.

End PABoundedRawCodedRestrictedProofAdmissibility.
