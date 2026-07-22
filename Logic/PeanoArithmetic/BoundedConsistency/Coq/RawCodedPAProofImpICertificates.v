(**
  Ordinary PA-proof certificates built by implication introduction.

  A premise for [RP_impI] lives under one additional logical assumption and
  therefore is not itself an ordinary PA proof certificate: that temporary
  assumption is deliberately absent from the witnessed PA-axiom list.  This
  module exposes the correct field-level packaging boundary and verifies it
  by constructing the model-coded identity proof [A -> A] over every honest
  witnessed PA context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedContextLists
  RawCodedRestrictedPAProof RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedPAProvability
  RawCodedProofImpIConstructor RawCodedProofAssumptionLeaf.

Module PABoundedRawCodedPAProofImpICertificates.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAssumptionLeaf.

Definition rawProofImpICertificate (M : RawPAModel)
    (witnessList context antecedent consequent child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofImpIRoot M context antecedent consequent child).

Arguments rawProofImpICertificate
  M witnessList context antecedent consequent child : clear implicits.

Theorem raw_codedPAProofOf_impI_from_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context antecedent consequent child,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child
    (rawListNode M antecedent context) consequent ->
  RawCodedPAProofOf M (rawFormulaImpCode M antecedent consequent)
    (rawProofImpICertificate M
      witnessList context antecedent consequent child).
Proof.
  intros M hPA witnessList context antecedent consequent child
    hwitness hcoverage hendpoint.
  exists witnessList,
    (rawProofImpIRoot M context antecedent consequent child), context.
  split.
  - unfold rawProofImpICertificate. reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofImpI_ruleCoverage M hPA
        context antecedent consequent child hcoverage hendpoint).
    + exact (raw_proofImpI_endpoint M
        context antecedent consequent child).
Qed.

(** The context half of a witnessed PA-axiom package already contains a
    complete synchronized list traversal; no fresh decoding is required. *)
Lemma raw_codedPAAxiomWitnessContext_context_realizable : forall
    (M : RawPAModel) witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextListRealizable M context.
Proof.
  intros M witnessList context
    (bound & witnessTailCode & witnessTailStep &
      witnessHeadCode & witnessHeadStep &
      axiomTailCode & axiomTailStep & axiomHeadCode & axiomHeadStep &
      htables).
  unfold RawCodedPAAxiomWitnessContextWithTables in htables.
  destruct htables as [_ [hcontextTraversal _]].
  exists bound, axiomTailCode, axiomTailStep, axiomHeadCode, axiomHeadStep.
  exact hcontextTraversal.
Qed.

Definition rawProofIdentityCertificate (M : RawPAModel)
    (witnessList context formulaCode : M) : M :=
  rawProofImpICertificate M witnessList context formulaCode formulaCode
    (rawProofAssumptionRoot M
      (rawListNode M formulaCode context) formulaCode).

Arguments rawProofIdentityCertificate
  M witnessList context formulaCode : clear implicits.

(** End-to-end deduction test: extend the honest base context, introduce its
    new head as an assumption leaf, and discharge that assumption. *)
Theorem raw_codedPAProofOf_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context formulaCode,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPAProofOf M
    (rawFormulaImpCode M formulaCode formulaCode)
    (rawProofIdentityCertificate M witnessList context formulaCode).
Proof.
  intros M hPA witnessList context formulaCode hwitness.
  unfold rawProofIdentityCertificate.
  apply (raw_codedPAProofOf_impI_from_fields M hPA
    witnessList context formulaCode formulaCode
    (rawProofAssumptionRoot M
      (rawListNode M formulaCode context) formulaCode)).
  - exact hwitness.
  - apply (raw_proofAssumption_cons_head_ruleCoverage M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList context hwitness).
  - exact (raw_proofAssumption_endpoint M
      (rawListNode M formulaCode context) formulaCode).
Qed.

End PABoundedRawCodedPAProofImpICertificates.
