(**
  Existential elimination in arbitrary temporary contexts.

  The earlier [RawCodedPAOpenProofOf] package distinguishes one temporary
  assumption from a witnessed PA-axiom base.  Nested [RP_exE] bodies contain
  several temporary assumptions, so their intermediate proofs need a smaller
  package: coverage plus an exact endpoint in an arbitrary coded context.
  Only the final outer wrapper restores the witnessed PA base.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization RawCodedContextLists
  RawCodedContextShift RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf RawCodedProofExEConstructor
  RawCodedPAOpenProofComposition.

Module PABoundedRawCodedPALocalProofExistential.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedPAOpenProofComposition.

Definition RawCodedPALocalProofOf (M : RawPAModel)
    (context target proof : M) : Prop :=
  RawProofRuleCoverage M proof /\
  RawProofEndpoint M proof context target.

Arguments RawCodedPALocalProofOf M context target proof : clear implicits.

(** A freshly consed local assumption is available whenever its tail context
    has a traversal.  No claim is made that the tail consists of PA axioms. *)
Theorem raw_codedPALocalProofOf_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail assumption,
  RawContextListRealizable M tail ->
  RawCodedPALocalProofOf M
    (rawListNode M assumption tail) assumption
    (rawProofAssumptionRoot M
      (rawListNode M assumption tail) assumption).
Proof.
  intros M hPA tail assumption htail. split.
  - exact (raw_proofAssumption_cons_head_ruleCoverage M hPA
      tail assumption htail).
  - exact (raw_proofAssumption_endpoint M
      (rawListNode M assumption tail) assumption).
Qed.

Theorem raw_codedPALocalProofOf_exE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body conclusion shiftedConclusion
      existentialChild bodyChild,
  RawCodedPALocalProofOf M context
    (rawFormulaExCode M body) existentialChild ->
  RawContextShift M context shiftedContext ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    conclusion shiftedConclusion ->
  RawCodedPALocalProofOf M
    (rawListNode M body shiftedContext) shiftedConclusion bodyChild ->
  RawCodedPALocalProofOf M context conclusion
    (rawProofExERoot M context body conclusion
      existentialChild bodyChild).
Proof.
  intros M hPA context shiftedContext body conclusion shiftedConclusion
    existentialChild bodyChild
    [hexCoverage hexEndpoint] hcontextShift hconclusionShift
    [hbodyCoverage hbodyEndpoint].
  split.
  - exact (raw_proofExE_ruleCoverage M hPA
      context shiftedContext body conclusion shiftedConclusion
      existentialChild bodyChild
      hexCoverage hexEndpoint hcontextShift hconclusionShift
      hbodyCoverage hbodyEndpoint).
  - exact (raw_proofExE_endpoint M
      context body conclusion existentialChild bodyChild).
Qed.

(** Falsity is closed, so shifting it by one variable is again falsity. *)
Lemma raw_codedFormulaShift_bottom_zero_one : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA.
  change (RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawQuotedFormulaCode M pBot)
    (rawQuotedFormulaCode M (Formula.rename S pBot))).
  exact (raw_codedFormulaShift_standard_zero_one M hPA pBot).
Qed.

Corollary raw_codedPALocalProofOf_exE_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context shiftedContext body existentialChild bodyChild,
  RawCodedPALocalProofOf M context
    (rawFormulaExCode M body) existentialChild ->
  RawContextShift M context shiftedContext ->
  RawCodedPALocalProofOf M
    (rawListNode M body shiftedContext)
    (rawFormulaBotCode M) bodyChild ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawProofExERoot M context body (rawFormulaBotCode M)
      existentialChild bodyChild).
Proof.
  intros M hPA context shiftedContext body existentialChild bodyChild
    hex hshift hbody.
  exact (raw_codedPALocalProofOf_exE M hPA
    context shiftedContext body (rawFormulaBotCode M)
    (rawFormulaBotCode M) existentialChild bodyChild
    hex hshift (raw_codedFormulaShift_bottom_zero_one M hPA) hbody).
Qed.

(** Restore the witnessed-base package only at the outermost elimination. *)
Theorem raw_codedPAOpenProofOf_exE_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption shiftedOpenContext body
      existentialChild bodyChild,
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawFormulaExCode M body) existentialChild ->
  RawContextShift M
    (rawListNode M assumption baseContext) shiftedOpenContext ->
  RawCodedPALocalProofOf M
    (rawListNode M body shiftedOpenContext)
    (rawFormulaBotCode M) bodyChild ->
  RawCodedPAOpenProofOf M witnessList baseContext assumption
    (rawFormulaBotCode M)
    (rawProofExERoot M
      (rawListNode M assumption baseContext)
      body (rawFormulaBotCode M) existentialChild bodyChild).
Proof.
  intros M hPA witnessList baseContext assumption shiftedOpenContext body
    existentialChild bodyChild
    [hwitness [hexCoverage hexEndpoint]] hshift hbody.
  split; [exact hwitness |].
  exact (raw_codedPALocalProofOf_exE_bottom M hPA
    (rawListNode M assumption baseContext) shiftedOpenContext body
    existentialChild bodyChild
    (conj hexCoverage hexEndpoint) hshift hbody).
Qed.

End PABoundedRawCodedPALocalProofExistential.
