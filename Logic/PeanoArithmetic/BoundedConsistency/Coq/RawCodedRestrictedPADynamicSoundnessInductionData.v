(**
  Syntax-operation data for the dynamic-soundness induction formula.

  This module deliberately stops at [RawCodedPAClosureInductionData].  A PA
  proof of both induction cases for this predicate would prove
  [forall n, Con_n(PA)] and hence (because every finite proof has a finite
  complexity bound) ordinary consistency.  Gödel's second theorem therefore
  rules out using this formula as the unconditional endpoint.

  The data remains useful and honest: for any supplied model-internal numeral
  trace it certifies every shift, substitution, bound, closure, and diagonal
  operation consumed by the generic closure-induction compiler.  The actual
  uniform theorem must instead induct on coded *provability* of each bounded
  consistency statement.
*)

From Stdlib Require Import Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization
  RawCodedNumeralTermCode RawCodedPAAxiomWitness
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedRestrictedPADynamicSoundnessInductionSyntax
  RawCodedPAClosureInductionCompiler.

Module PABoundedRawCodedRestrictedPADynamicSoundnessInductionData.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedRestrictedPADynamicSoundnessInductionSyntax.
Import PABoundedRawCodedPAClosureInductionCompiler.

Definition rawRestrictedPADynamicSoundnessInductionSourceCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionSourceFormula.

Definition rawRestrictedPADynamicSoundnessInductionShiftedCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionShiftedFormula.

Definition rawRestrictedPADynamicSoundnessInductionSuccessorCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionSuccessorFormula.

Definition rawRestrictedPADynamicSoundnessInductionZeroCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionZeroFormula.

Definition rawRestrictedPADynamicSoundnessInductionSourceAllCode
    (M : RawPAModel) : M :=
  rawFormulaAllCode M
    (rawRestrictedPADynamicSoundnessInductionSourceCode M).

Definition rawRestrictedPADynamicSoundnessInductionStepImpCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawRestrictedPADynamicSoundnessInductionSourceCode M)
    (rawRestrictedPADynamicSoundnessInductionSuccessorCode M).

Definition rawRestrictedPADynamicSoundnessInductionStepAllCode
    (M : RawPAModel) : M :=
  rawFormulaAllCode M
    (rawRestrictedPADynamicSoundnessInductionStepImpCode M).

Definition rawRestrictedPADynamicSoundnessInductionPremiseCode
    (M : RawPAModel) : M :=
  rawFormulaAndCode M
    (rawRestrictedPADynamicSoundnessInductionZeroCode M)
    (rawRestrictedPADynamicSoundnessInductionStepAllCode M).

Definition rawRestrictedPADynamicSoundnessInductionBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionBodyFormula.

Definition rawRestrictedPADynamicSoundnessInductionClosureCount
    (M : RawPAModel) : M :=
  rawNumeralValue M
    (Formula.bound restrictedPADynamicSoundnessInductionBodyFormula).

Definition rawRestrictedPADynamicSoundnessInductionAxiomCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    restrictedPADynamicSoundnessInductionAxiomFormula.

Arguments rawRestrictedPADynamicSoundnessInductionSourceCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionShiftedCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionSuccessorCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionZeroCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionSourceAllCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionStepImpCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionStepAllCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionPremiseCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionBodyCode M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionClosureCount M
  : clear implicits.
Arguments rawRestrictedPADynamicSoundnessInductionAxiomCode M
  : clear implicits.

Theorem raw_codedRestrictedPADynamicSoundnessClosureInductionData : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAClosureInductionData M numeralCode
    (rawRestrictedPADynamicSoundnessInductionSourceCode M)
    (rawRestrictedPADynamicSoundnessInductionAxiomCode M)
    (rawRestrictedPADynamicSoundnessInductionShiftedCode M)
    (rawRestrictedPADynamicSoundnessInductionSuccessorCode M)
    (rawRestrictedPADynamicSoundnessInductionZeroCode M)
    (rawRestrictedPADynamicSoundnessInductionSourceAllCode M)
    (rawRestrictedPADynamicSoundnessInductionStepImpCode M)
    (rawRestrictedPADynamicSoundnessInductionStepAllCode M)
    (rawRestrictedPADynamicSoundnessInductionPremiseCode M)
    (rawRestrictedPADynamicSoundnessInductionBodyCode M)
    (rawRestrictedPADynamicSoundnessInductionClosureCount M).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold rawRestrictedPADynamicSoundnessInductionSourceCode,
      rawRestrictedPADynamicSoundnessInductionShiftedCode,
      restrictedPADynamicSoundnessInductionShiftedFormula,
      standardPAAxiomInductionShifted.
    exact (raw_codedFormulaShift_standard M hPA 1 1
      restrictedPADynamicSoundnessInductionSourceFormula).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawRestrictedPADynamicSoundnessInductionShiftedCode,
      rawRestrictedPADynamicSoundnessInductionSuccessorCode,
      restrictedPADynamicSoundnessInductionSuccessorFormula,
      standardPAAxiomInductionSuccessorInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      (tSucc (tVar 0))
      restrictedPADynamicSoundnessInductionShiftedFormula).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawRestrictedPADynamicSoundnessInductionSourceCode,
      rawRestrictedPADynamicSoundnessInductionZeroCode,
      restrictedPADynamicSoundnessInductionZeroFormula,
      standardPAAxiomInductionZeroInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      tZero restrictedPADynamicSoundnessInductionSourceFormula).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold rawRestrictedPADynamicSoundnessInductionPremiseCode,
      rawRestrictedPADynamicSoundnessInductionStepAllCode,
      rawRestrictedPADynamicSoundnessInductionStepImpCode,
      rawRestrictedPADynamicSoundnessInductionSourceAllCode,
      rawRestrictedPADynamicSoundnessInductionZeroCode,
      rawRestrictedPADynamicSoundnessInductionSuccessorCode,
      rawRestrictedPADynamicSoundnessInductionSourceCode,
      rawRestrictedPADynamicSoundnessInductionBodyCode,
      restrictedPADynamicSoundnessInductionBodyFormula,
      standardPAAxiomInductionBody.
    reflexivity.
  - unfold rawRestrictedPADynamicSoundnessInductionBodyCode,
      rawRestrictedPADynamicSoundnessInductionClosureCount.
    exact (raw_codedFormulaBound_standard M hPA
      restrictedPADynamicSoundnessInductionBodyFormula).
  - unfold rawRestrictedPADynamicSoundnessInductionClosureCount,
      rawRestrictedPADynamicSoundnessInductionBodyCode,
      rawRestrictedPADynamicSoundnessInductionAxiomCode,
      restrictedPADynamicSoundnessInductionAxiomFormula,
      Formula.sealPA.
    exact (raw_codedUniversalClosure_standard M hPA
      (Formula.bound restrictedPADynamicSoundnessInductionBodyFormula)
      restrictedPADynamicSoundnessInductionBodyFormula).
  - apply (raw_codedUniversalClosureSelfInstantiationThrough_of_diagonal
      M hPA numeralCode
      (rawRestrictedPADynamicSoundnessInductionBodyCode M)
      (rawRestrictedPADynamicSoundnessInductionClosureCount M)).
    unfold rawRestrictedPADynamicSoundnessInductionBodyCode.
    exact (raw_codedRestrictedPADynamicSoundnessInductionBody_diagonal
      M hPA numeralBound numeralCode hnumeral).
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessInductionData.
