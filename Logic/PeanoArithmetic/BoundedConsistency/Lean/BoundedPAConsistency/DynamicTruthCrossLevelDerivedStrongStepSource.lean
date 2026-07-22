import BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

/-!
# Derived-level source syntax for cross-level truth

The old, current, and next levels are not related by interpreted equality.
Only the old level is named; the other two are the literal arithmetic terms
old + 1 and (old + 1) + 1.  Their interpretations therefore have the
meta-level identities required by the semantic constructor theorem once the
source arithmetic reduct has been replaced by its canonical equality model.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-- Arithmetic one in the expanded source language. -/
noncomputable def sourceOne {n : ℕ} : ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![]

/-- The current level, computed from the single named old-level parameter. -/
noncomputable def sourceDerivedCurrentLevel {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
    ![levelTerm 0, sourceOne]

/-- The next level, computed by a second literal successor. -/
noncomputable def sourceDerivedNextLevel {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
    ![sourceDerivedCurrentLevel, sourceOne]

noncomputable def sourceDerivedPredecessorSuccessorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      sourceDerivedCurrentLevel (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ sourcePredecessorUniversalRecordBranch
        (levelTerm 0) (#0) (#1))

noncomputable def sourceDerivedPredecessorSuccessorTruth :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ sourceDerivedPredecessorSuccessorRecordValid (#1) (#0))))

noncomputable def sourceDerivedCurrentDefinitionBody :
    Semisentence SourceLanguage 3 :=
  currentAtom (#0) (#1) (#2) 🡘
    sourceDerivedPredecessorSuccessorTruth

noncomputable def sourceDerivedCurrentDefinition : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceDerivedCurrentDefinitionBody

noncomputable def sourceDerivedCurrentSuccessorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      sourceDerivedNextLevel (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ sourceCurrentUniversalRecordBranch
        sourceDerivedCurrentLevel (#0) (#1))

noncomputable def sourceDerivedCurrentSuccessorTruth :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ sourceDerivedCurrentSuccessorRecordValid (#1) (#0))))

noncomputable def sourceDerivedTargetQuantifierFreeIntroductionBody :
    Semisentence SourceLanguage 3 :=
  sourceQuantifierFreeTruth 🡒 sourceDerivedCurrentSuccessorTruth

noncomputable def sourceDerivedTargetQuantifierFreeIntroduction :
    Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceDerivedTargetQuantifierFreeIntroductionBody

noncomputable def sourceDerivedCurrentSigmaDomain :
    Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isSigmaCodeDef.val)
    sourceDerivedCurrentLevel (#2)

noncomputable def sourceDerivedCurrentPiDomain :
    Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isPiCodeDef.val)
    sourceDerivedCurrentLevel (#2)

noncomputable def sourceDerivedCurrentPiTruth :
    Semisentence SourceLanguage 3 :=
  sourceDerivedCurrentPiDomain ⋏
    (∃⁰
      (liftArithmeticFormula
          ((negGraph ℒₒᵣ).val/[#0, #3]) ⋏
        ∼(currentAtom (#1) (#2) (#0))))

noncomputable def sourceDerivedNextCrossLevelBody :
    Semisentence SourceLanguage 3 :=
  (sourceDerivedCurrentSigmaDomain 🡒
      (sourceDerivedCurrentSuccessorTruth 🡘
        currentAtom (#0) (#1) (#2))) ⋏
    (sourceDerivedCurrentPiDomain 🡒
      (sourceDerivedCurrentSuccessorTruth 🡘
        sourceDerivedCurrentPiTruth))

noncomputable def sourceDerivedNextCrossLevelInvariant :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceDerivedNextCrossLevelBody

/-- All semantic premises, with no relational equality standing in for a
meta-level identity of hierarchy levels. -/
noncomputable def sourceDerivedStrongStepPremises : Sentence SourceLanguage :=
  (sourcePriorCrossLevelContext ⋏
      sourceDerivedTargetQuantifierFreeIntroduction) ⋏
    sourceDerivedCurrentDefinition

noncomputable def sourceDerivedStrongPrefix : Semisentence SourceLanguage 1 :=
  ∀⁰[sourceStrongPrefixGuard]
    (sourceDerivedNextCrossLevelInvariant/[
      (#0 : ClosedSemiterm SourceLanguage 2)])

noncomputable def sourceDerivedStrongStepSentence : Sentence SourceLanguage :=
  Arrow.arrow sourceDerivedStrongStepPremises
    (∀⁰ Arrow.arrow sourceDerivedStrongPrefix
      sourceDerivedNextCrossLevelInvariant)

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepSource
