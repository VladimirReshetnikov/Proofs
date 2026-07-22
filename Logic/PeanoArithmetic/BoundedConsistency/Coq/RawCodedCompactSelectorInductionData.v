(**
  Syntax-operation data for induction on compact selector packages.

  This is the provability-valued counterpart of the earlier dynamic-
  soundness induction data.  It certifies every represented shift,
  substitution, bound, closure, and diagonal operation required by the
  generic closure-induction proof compiler.  It intentionally does not
  assume or manufacture the base and successor proof trees consumed by that
  compiler; those are separate proof-producing obligations.
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
  RawCodedCompactSelectorInductionSyntax
  RawCodedPAClosureInductionCompiler.

Module PABoundedRawCodedCompactSelectorInductionData.

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
Import PABoundedRawCodedCompactSelectorInductionSyntax.
Import PABoundedRawCodedPAClosureInductionCompiler.

Definition rawCompactSelectorInductionSourceCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionSourceFormula.

Definition rawCompactSelectorInductionShiftedCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionShiftedFormula.

Definition rawCompactSelectorInductionSuccessorCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionSuccessorFormula.

Definition rawCompactSelectorInductionZeroCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionZeroFormula.

Definition rawCompactSelectorInductionSourceAllCode (M : RawPAModel) : M :=
  rawFormulaAllCode M (rawCompactSelectorInductionSourceCode M).

Definition rawCompactSelectorInductionStepImpCode (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawCompactSelectorInductionSourceCode M)
    (rawCompactSelectorInductionSuccessorCode M).

Definition rawCompactSelectorInductionStepAllCode (M : RawPAModel) : M :=
  rawFormulaAllCode M (rawCompactSelectorInductionStepImpCode M).

Definition rawCompactSelectorInductionPremiseCode (M : RawPAModel) : M :=
  rawFormulaAndCode M
    (rawCompactSelectorInductionZeroCode M)
    (rawCompactSelectorInductionStepAllCode M).

Definition rawCompactSelectorInductionBodyCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionBodyFormula.

Definition rawCompactSelectorInductionClosureCount (M : RawPAModel) : M :=
  rawNumeralValue M (Formula.bound compactSelectorInductionBodyFormula).

Definition rawCompactSelectorInductionAxiomCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M compactSelectorInductionAxiomFormula.

Arguments rawCompactSelectorInductionSourceCode M : clear implicits.
Arguments rawCompactSelectorInductionShiftedCode M : clear implicits.
Arguments rawCompactSelectorInductionSuccessorCode M : clear implicits.
Arguments rawCompactSelectorInductionZeroCode M : clear implicits.
Arguments rawCompactSelectorInductionSourceAllCode M : clear implicits.
Arguments rawCompactSelectorInductionStepImpCode M : clear implicits.
Arguments rawCompactSelectorInductionStepAllCode M : clear implicits.
Arguments rawCompactSelectorInductionPremiseCode M : clear implicits.
Arguments rawCompactSelectorInductionBodyCode M : clear implicits.
Arguments rawCompactSelectorInductionClosureCount M : clear implicits.
Arguments rawCompactSelectorInductionAxiomCode M : clear implicits.

Theorem raw_codedCompactSelectorClosureInductionData : forall
    (M : RawPAModel), RawPASatisfies M -> forall numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAClosureInductionData M numeralCode
    (rawCompactSelectorInductionSourceCode M)
    (rawCompactSelectorInductionAxiomCode M)
    (rawCompactSelectorInductionShiftedCode M)
    (rawCompactSelectorInductionSuccessorCode M)
    (rawCompactSelectorInductionZeroCode M)
    (rawCompactSelectorInductionSourceAllCode M)
    (rawCompactSelectorInductionStepImpCode M)
    (rawCompactSelectorInductionStepAllCode M)
    (rawCompactSelectorInductionPremiseCode M)
    (rawCompactSelectorInductionBodyCode M)
    (rawCompactSelectorInductionClosureCount M).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold rawCompactSelectorInductionSourceCode,
      rawCompactSelectorInductionShiftedCode,
      compactSelectorInductionShiftedFormula,
      standardPAAxiomInductionShifted.
    exact (raw_codedFormulaShift_standard M hPA 1 1
      compactSelectorInductionSourceFormula).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawCompactSelectorInductionShiftedCode,
      rawCompactSelectorInductionSuccessorCode,
      compactSelectorInductionSuccessorFormula,
      standardPAAxiomInductionSuccessorInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      (tSucc (tVar 0)) compactSelectorInductionShiftedFormula).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawCompactSelectorInductionSourceCode,
      rawCompactSelectorInductionZeroCode,
      compactSelectorInductionZeroFormula,
      standardPAAxiomInductionZeroInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      tZero compactSelectorInductionSourceFormula).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold rawCompactSelectorInductionPremiseCode,
      rawCompactSelectorInductionStepAllCode,
      rawCompactSelectorInductionStepImpCode,
      rawCompactSelectorInductionSourceAllCode,
      rawCompactSelectorInductionZeroCode,
      rawCompactSelectorInductionSuccessorCode,
      rawCompactSelectorInductionSourceCode,
      rawCompactSelectorInductionBodyCode,
      compactSelectorInductionBodyFormula,
      standardPAAxiomInductionBody.
    reflexivity.
  - unfold rawCompactSelectorInductionBodyCode,
      rawCompactSelectorInductionClosureCount.
    exact (raw_codedFormulaBound_standard M hPA
      compactSelectorInductionBodyFormula).
  - unfold rawCompactSelectorInductionClosureCount,
      rawCompactSelectorInductionBodyCode,
      rawCompactSelectorInductionAxiomCode,
      compactSelectorInductionAxiomFormula,
      Formula.sealPA.
    exact (raw_codedUniversalClosure_standard M hPA
      (Formula.bound compactSelectorInductionBodyFormula)
      compactSelectorInductionBodyFormula).
  - apply (raw_codedUniversalClosureSelfInstantiationThrough_of_diagonal
      M hPA numeralCode
      (rawCompactSelectorInductionBodyCode M)
      (rawCompactSelectorInductionClosureCount M)).
    unfold rawCompactSelectorInductionBodyCode.
    exact (raw_codedCompactSelectorInductionBody_diagonal
      M hPA numeralBound numeralCode hnumeral).
Qed.

End PABoundedRawCodedCompactSelectorInductionData.
