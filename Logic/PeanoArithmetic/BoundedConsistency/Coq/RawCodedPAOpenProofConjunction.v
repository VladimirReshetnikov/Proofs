(**
  Conjunction projections inside a one-assumption PA proof.

  These wrappers retain the witnessed PA-axiom base context and place an
  honest [RP_andE1] or [RP_andE2] root over the supplied open proof.  They are
  the field-projection operations needed after the existential witnesses of
  a restricted-proof assumption have been exposed.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedPAOpenProofComposition
  RawCodedProofAndEConstructors.

Module PABoundedRawCodedPAOpenProofConjunction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedProofAndEConstructors.

Theorem raw_codedPAOpenProofOf_andE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      projection witnessList baseContext assumption left right child,
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawFormulaAndCode M left right) child ->
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawAndProjectionConclusion M projection left right)
    (rawProofAndERoot M projection
      (rawListNode M assumption baseContext) left right child).
Proof.
  intros M hPA projection witnessList baseContext assumption
    left right child [hwitness [hcoverage hendpoint]].
  split; [exact hwitness |]. split.
  - exact (raw_proofAndE_ruleCoverage M hPA projection
      (rawListNode M assumption baseContext) left right child
      hcoverage hendpoint).
  - exact (raw_proofAndE_endpoint M projection
      (rawListNode M assumption baseContext) left right child).
Qed.

Corollary raw_codedPAOpenProofOf_andE1 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption left right child,
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawFormulaAndCode M left right) child ->
  RawCodedPAOpenProofOf M witnessList baseContext assumption left
    (rawProofAndERoot M RawAndLeft
      (rawListNode M assumption baseContext) left right child).
Proof.
  intros M hPA witnessList baseContext assumption left right child hopen.
  exact (raw_codedPAOpenProofOf_andE M hPA RawAndLeft
    witnessList baseContext assumption left right child hopen).
Qed.

Corollary raw_codedPAOpenProofOf_andE2 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption left right child,
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawFormulaAndCode M left right) child ->
  RawCodedPAOpenProofOf M witnessList baseContext assumption right
    (rawProofAndERoot M RawAndRight
      (rawListNode M assumption baseContext) left right child).
Proof.
  intros M hPA witnessList baseContext assumption left right child hopen.
  exact (raw_codedPAOpenProofOf_andE M hPA RawAndRight
    witnessList baseContext assumption left right child hopen).
Qed.

End PABoundedRawCodedPAOpenProofConjunction.
