(** Conjunction projections in an arbitrary temporary proof context. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofConjunction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.

Theorem raw_codedPALocalProofOf_andE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context
    (rawAndProjectionConclusion M projection left right)
    (rawProofAndERoot M projection context left right child).
Proof.
  intros M hPA projection context left right child
    [hcoverage hendpoint].
  split.
  - exact (raw_proofAndE_ruleCoverage M hPA projection
      context left right child hcoverage hendpoint).
  - exact (raw_proofAndE_endpoint M
      projection context left right child).
Qed.

Corollary raw_codedPALocalProofOf_andE1 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context left
    (rawProofAndERoot M RawAndLeft context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_andE M hPA RawAndLeft
    context left right child hchild).
Qed.

Corollary raw_codedPALocalProofOf_andE2 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left right) child ->
  RawCodedPALocalProofOf M context right
    (rawProofAndERoot M RawAndRight context left right child).
Proof.
  intros M hPA context left right child hchild.
  exact (raw_codedPALocalProofOf_andE M hPA RawAndRight
    context left right child hchild).
Qed.

End PABoundedRawCodedPALocalProofConjunction.
