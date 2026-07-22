(**
  Ordinary PA-proof certificates built by binary raw-proof constructors.

  Implication elimination composes two honestly covered proof roots sharing
  one witnessed PA-axiom context.  Sharing is explicit in the interface:
  arbitrary [RawCodedPAProofOf] certificates may use different contexts, and
  silently combining those trees would not be a valid natural-deduction
  rule.  Later compilers retain the decoded context and invoke this field-
  level constructor directly.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRestrictedPAProof
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedPAProvability RawCodedProofBinaryConstructors.

Module PABoundedRawCodedPAProofBinaryCertificates.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofBinaryConstructors.

Definition rawProofImpECertificate (M : RawPAModel)
    (witnessList context antecedent consequent impChild antecedentChild : M)
    : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).

Arguments rawProofImpECertificate
  M witnessList context antecedent consequent impChild antecedentChild
  : clear implicits.

Theorem raw_codedPAProofOf_impE_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context antecedent consequent impChild antecedentChild,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawProofRuleCoverage M impChild ->
  RawProofEndpoint M impChild context
    (rawFormulaImpCode M antecedent consequent) ->
  RawProofRuleCoverage M antecedentChild ->
  RawProofEndpoint M antecedentChild context antecedent ->
  RawCodedPAProofOf M consequent
    (rawProofImpECertificate M witnessList context
      antecedent consequent impChild antecedentChild).
Proof.
  intros M hPA witnessList context antecedent consequent
    impChild antecedentChild hwitness
    himpCoverage himpEndpoint hantecedentCoverage hantecedentEndpoint.
  exists witnessList,
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild), context.
  split.
  - unfold rawProofImpECertificate. reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofImpE_ruleCoverage M hPA
        context antecedent consequent impChild antecedentChild
        himpCoverage himpEndpoint
        hantecedentCoverage hantecedentEndpoint).
    + exact (raw_proofImpE_endpoint M
        context antecedent consequent impChild antecedentChild).
Qed.

End PABoundedRawCodedPAProofBinaryCertificates.
