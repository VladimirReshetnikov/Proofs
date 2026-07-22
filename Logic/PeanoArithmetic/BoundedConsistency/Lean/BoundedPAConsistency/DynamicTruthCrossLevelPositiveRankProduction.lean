import BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep
import BoundedPAConsistency.DynamicTruthCrossLevelStructuralSuccessor
import BoundedPAConsistency.DynamicTruthPredecessorFormula
import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.ModelCodedStrongInduction
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import BoundedPAConsistency.TernaryCongruencePrototype

/-!
# Production compilation of the positive cross-level strong step

The quotient-safe source proof still has two pieces of explicit interface
bookkeeping before it can drive the represented strong-induction compiler:

* its two placeholder-congruence assumptions must be discharged after the
  two model-coded truth predicates have been inserted; and
* its bounded prefix must be identified syntactically with
  `ModelCodedStrongInduction.strongPrefixFormula`.

This module performs those steps without unfolding the large constructor
predicate inside the generic induction adapter.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelPositiveRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Structural translation into the generic strong-step shape -/

private theorem translate_sourceBall
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) {n : ℕ}
    (guard body : Semiproposition CrossLevelSourceLanguage (n + 1)) :
    translateFormula predecessor current parameters (∀⁰[guard] body) =
      ∀⁰[translateFormula predecessor current parameters guard]
        translateFormula predecessor current parameters body := by
  change translateFormula predecessor current parameters
      (∀⁰ (∼guard ⋎ body)) = _
  change
    (∀⁰ (translateFormula predecessor current parameters (∼guard) ⋎
      translateFormula predecessor current parameters body)) = _
  rw [ModelCodedTwoPredicateParameters.translateFormula_neg]
  rfl

private theorem translate_sourceAll
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) {n : ℕ}
    (body : Semiproposition CrossLevelSourceLanguage (n + 1)) :
    translateFormula predecessor current parameters (∀⁰ body) =
      ∀⁰ translateFormula predecessor current parameters body := by
  rfl

private theorem translate_imp
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) {n : ℕ}
    (p q : Semiproposition CrossLevelSourceLanguage n) :
    translateFormula predecessor current parameters (p 🡒 q) =
      (translateFormula predecessor current parameters p 🡒
        translateFormula predecessor current parameters q) := by
  change translateFormula predecessor current parameters (∼p ⋎ q) =
    (∼translateFormula predecessor current parameters p ⋎
      translateFormula predecessor current parameters q)
  simp only [ModelCodedTwoPredicateParameters.translateFormula]
  rw [ModelCodedTwoPredicateParameters.translateFormula_neg]

/-- Expose only the prefix's binder and unary-predicate application. -/
private theorem emb_sourceDerivedStrongPrefix :
    (Rewriting.emb sourceDerivedStrongPrefix :
        Semiproposition CrossLevelSourceLanguage 1) =
      ∀⁰[(Rewriting.emb sourceStrongPrefixGuard :
          Semiproposition CrossLevelSourceLanguage 2)]
        (Rew.subst ![(#0 : SyntacticSemiterm CrossLevelSourceLanguage 2)] ▹
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant :
            Semiproposition CrossLevelSourceLanguage 1)) := by
  unfold sourceDerivedStrongPrefix
  rw [Rewriting.smul_ball]
  simp only [Rew.q_emb]
  rw [Semiformula.coe_subst_eq_subst_coe]
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Expose the outer implication and universal binder of the source step. -/
private theorem emb_sourceDerivedStrongStepSentence :
    (Rewriting.emb sourceDerivedStrongStepSentence :
        Proposition CrossLevelSourceLanguage) =
      Arrow.arrow
        (Rewriting.emb sourceDerivedStrongStepPremises :
          Proposition CrossLevelSourceLanguage)
        (∀⁰ Arrow.arrow
          (Rewriting.emb sourceDerivedStrongPrefix :
            Semiproposition CrossLevelSourceLanguage 1)
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant :
            Semiproposition CrossLevelSourceLanguage 1)) := by
  unfold sourceDerivedStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]
  rw [Rewriting.app_all]
  simp only [Rew.q_emb]
  rw [LogicalConnective.HomClass.map_imply]

private theorem translate_sourceDerivedStrongPrefix_of_target
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V)
    (target : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (htarget :
      translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant) = target) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedStrongPrefix) =
      strongPrefixFormula target := by
  have hguard :
      translateFormula predecessor current parameters
          (Rewriting.emb sourceStrongPrefixGuard) =
        ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb ModelCodedStrongInduction.sourcePrefixGuard) := by
    rfl
  have hsourceApplication :
      translateFormula predecessor current parameters
          (Rew.subst ![(#0 : SyntacticSemiterm CrossLevelSourceLanguage 2)] ▹
            (Rewriting.emb sourceDerivedNextCrossLevelInvariant :
              Semiproposition CrossLevelSourceLanguage 1)) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    rw [ModelCodedTwoPredicateParameters.translateFormula_subst, htarget]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericApplication :
      ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb
            (ModelCodedStrongInduction.sourcePredicateAtom (#0))) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    simp [ModelCodedStrongInduction.sourcePredicateAtom,
      TwoPredicateSourceContextInductionKernel.secondAtom,
      ModelCodedTwoPredicateParameters.translateFormula,
      ModelCodedTwoPredicateParameters.translateTerm]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericShape :
      strongPrefixFormula target =
        ∀⁰
          (ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (∼(Rewriting.emb ModelCodedStrongInduction.sourcePrefixGuard)) ⋎
            ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (Rewriting.emb
                (ModelCodedStrongInduction.sourcePredicateAtom (#0)))) := by
    rfl
  rw [emb_sourceDerivedStrongPrefix,
    translate_sourceBall, hgenericShape]
  rw [ModelCodedTwoPredicateParameters.translateFormula_neg,
    hguard, hsourceApplication, hgenericApplication]
  rfl

/-- The derived source prefix is exactly the generic represented strong
prefix instantiated with the translated constructor predicate. -/
theorem translate_sourceDerivedStrongPrefix
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedStrongPrefix) =
      strongPrefixFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant)) :=
  translate_sourceDerivedStrongPrefix_of_target predecessor current parameters
    _ rfl

/-- The complete fixed-source step translates literally to the premise
accepted by `ModelCodedStrongInduction`. -/
theorem translate_sourceDerivedStrongStepSentence
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedStrongStepSentence) =
      strongStepFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedStrongStepPremises))
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant)) := by
  rw [emb_sourceDerivedStrongStepSentence]
  change
    translateFormula predecessor current parameters
        (Arrow.arrow
          (Rewriting.emb sourceDerivedStrongStepPremises)
          (∀⁰ Arrow.arrow
            (Rewriting.emb sourceDerivedStrongPrefix)
            (Rewriting.emb sourceDerivedNextCrossLevelInvariant))) = _
  rw [translate_imp, translate_sourceAll, translate_imp,
    translate_sourceDerivedStrongPrefix, strongStepFormula_eq]

/-! ## Congruence discharge and compiled strong-step proof -/

private theorem emb_sourceCongruentDerivedStrongStepSentence :
    (Rewriting.emb sourceCongruentDerivedStrongStepSentence :
        Proposition CrossLevelSourceLanguage) =
      Arrow.arrow
        (Rewriting.emb sourcePlaceholderCongruenceContext :
          Proposition CrossLevelSourceLanguage)
        (Rewriting.emb sourceDerivedStrongStepSentence :
          Proposition CrossLevelSourceLanguage) := by
  unfold sourceCongruentDerivedStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- Translation preserves the explicit congruence boundary and identifies
the consequent with the generic represented strong-step formula. -/
theorem translate_sourceCongruentDerivedStrongStepSentence
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceCongruentDerivedStrongStepSentence) =
      (translateFormula predecessor current parameters
          (Rewriting.emb sourcePlaceholderCongruenceContext) 🡒
        strongStepFormula
          (translateFormula predecessor current parameters
            (Rewriting.emb sourceDerivedStrongStepPremises))
          (translateFormula predecessor current parameters
            (Rewriting.emb sourceDerivedNextCrossLevelInvariant))) := by
  rw [emb_sourceCongruentDerivedStrongStepSentence]
  change translateFormula predecessor current parameters
      (Arrow.arrow
        (Rewriting.emb sourcePlaceholderCongruenceContext)
        (Rewriting.emb sourceDerivedStrongStepSentence)) = _
  rw [translate_imp, translate_sourceDerivedStrongStepSentence]

/-- Compile the audited source theorem and discharge both placeholder
congruence assumptions with PA's represented replacement theorem. -/
noncomputable def compiledDerivedStrongStepProof
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V)
    (hpredecessor : predecessor.shift = predecessor)
    (hcurrent : current.shift = current) :
    Peano.internalize V ⊢!
      strongStepFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedStrongStepPremises))
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceDerivedNextCrossLevelInvariant)) := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula predecessor current parameters
        (Rewriting.emb sourceCongruentDerivedStrongStepSentence) :=
    ModelCodedTwoPredicateParameters.compilePeanoTemplate
      predecessor current parameters hpredecessor hcurrent
      sourceCongruentDerivedStrongStepProof
  rw [translate_sourceCongruentDerivedStrongStepSentence] at hcompiled
  exact hcompiled ⨀
    translatedTwoPredicateCongruenceContextProof
      predecessor current parameters

/-! ## Focused translations of the derived hierarchy levels -/

@[simp] theorem translate_sourceDerivedCurrentLevel
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateTerm parameters
        (Rew.emb (sourceDerivedCurrentLevel (n := n)) :
          SyntacticSemiterm CrossLevelSourceLanguage n) =
      Arithmetic.typedNumeral (parameters 0 + 1) := by
  simp [sourceDerivedCurrentLevel, sourceOne,
    ModelCodedTwoPredicateParameters.translateTerm]
  exact (Arithmetic.numeral_succ_pos' hpositive).symm

@[simp] theorem translate_sourceDerivedNextLevel
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateTerm parameters
        (Rew.emb (sourceDerivedNextLevel (n := n)) :
          SyntacticSemiterm CrossLevelSourceLanguage n) =
      Arithmetic.typedNumeral (parameters 0 + 1 + 1) := by
  simp [sourceDerivedNextLevel, sourceOne,
    translate_sourceDerivedCurrentLevel parameters hpositive,
    ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourceDerivedCurrentSuccessorRecordValid
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentSuccessorRecordValid) =
      DynamicTruthFormula.successorRecordValid current
        (parameters 0 + 1) (parameters 0 + 1 + 1) := by
  simp [sourceDerivedCurrentSuccessorRecordValid,
    DynamicTruthFormula.successorRecordValid,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourceDerivedCurrentLevel parameters hpositive,
    translate_sourceDerivedNextLevel parameters hpositive]

@[simp] theorem translate_sourceDerivedCurrentSuccessorTruth
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentSuccessorTruth) =
      DynamicTruthFormula.successorTruthFormula current
        (parameters 0 + 1) (parameters 0 + 1 + 1) := by
  simp [sourceDerivedCurrentSuccessorTruth,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    DynamicTruthFormula.successorTruthFormula,
    Bootstrapping.Semiformula.imp_def,
    translate_sourceDerivedCurrentSuccessorRecordValid
      predecessor current parameters hpositive]
  let memberSource : Semisentence CrossLevelSourceLanguage 5 :=
    apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)
  calc
    translateFormula predecessor current parameters
        (∼(Rewriting.emb memberSource)) =
      ∼translateFormula predecessor current parameters
        (Rewriting.emb memberSource) :=
      ModelCodedTwoPredicateParameters.translateFormula_neg
        predecessor current parameters (Rewriting.emb memberSource)
    _ = _ := by simp [memberSource,
      ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourcePredecessorUniversalRecordBranch
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourcePredecessorUniversalRecordBranch) =
      DynamicTruthFormula.universalRecordBranch predecessor := by
  simp [sourcePredecessorUniversalRecordBranch,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    DynamicTruthFormula.universalRecordBranch,
    DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourceDerivedPredecessorSuccessorRecordValid
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedPredecessorSuccessorRecordValid) =
      DynamicTruthFormula.successorRecordValid predecessor
        (parameters 0) (parameters 0 + 1) := by
  simp [sourceDerivedPredecessorSuccessorRecordValid,
    DynamicTruthFormula.successorRecordValid,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourcePredecessorUniversalRecordBranch
      predecessor current parameters,
    translate_sourceDerivedCurrentLevel parameters hpositive]

@[simp] theorem translate_sourceDerivedPredecessorSuccessorTruth
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedPredecessorSuccessorTruth) =
      DynamicTruthFormula.successorTruthFormula predecessor
        (parameters 0) (parameters 0 + 1) := by
  simp [sourceDerivedPredecessorSuccessorTruth,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    DynamicTruthFormula.successorTruthFormula,
    Bootstrapping.Semiformula.imp_def,
    translate_sourceDerivedPredecessorSuccessorRecordValid
      predecessor current parameters hpositive]
  let memberSource : Semisentence CrossLevelSourceLanguage 5 :=
    apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)
  calc
    translateFormula predecessor current parameters
        (∼(Rewriting.emb memberSource)) =
      ∼translateFormula predecessor current parameters
        (Rewriting.emb memberSource) :=
      ModelCodedTwoPredicateParameters.translateFormula_neg
        predecessor current parameters (Rewriting.emb memberSource)
    _ = _ := by simp [memberSource,
      ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourceDerivedCurrentDefinition
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentDefinition) =
      ∀⁰ ∀⁰ ∀⁰
        (current 🡘 DynamicTruthFormula.successorTruthFormula predecessor
          (parameters 0) (parameters 0 + 1)) := by
  simp [sourceDerivedCurrentDefinition,
    sourceDerivedCurrentDefinitionBody,
    FirstOrder.Semiformula.iff_eq,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourceDerivedPredecessorSuccessorTruth
      predecessor current parameters hpositive]
  constructor

@[simp] theorem translate_sourceDerivedTargetQuantifierFreeIntroduction
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedTargetQuantifierFreeIntroduction) =
      quantifierFreeIntroductionFormula current
        (parameters 0 + 1) (parameters 0 + 1 + 1) := by
  simp [sourceDerivedTargetQuantifierFreeIntroduction,
    sourceDerivedTargetQuantifierFreeIntroductionBody,
    quantifierFreeIntroductionFormula,
    ModelCodedTwoPredicateParameters.translateFormula,
    translate_sourceDerivedCurrentSuccessorTruth
      predecessor current parameters hpositive]
  have hqfNeg :
      translateFormula predecessor current parameters
          (Semiformula.neg
            (Rewriting.emb
              DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth)) =
        ∼quantifierFreeTruthFormula := by
    calc
      _ = ∼translateFormula predecessor current parameters
          (Rewriting.emb
            DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedTwoPredicateParameters.translateFormula_neg
            predecessor current parameters
            (Rewriting.emb
              DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth))
      _ = _ := congrArg (∼·)
        (translate_crossLevelSourceQuantifierFreeTruth
          predecessor current parameters)
  rw [hqfNeg]
  rfl

@[simp] theorem translate_sourceDerivedStrongStepPremises
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedStrongStepPremises) =
      ((directCrossLevelFormula predecessor current (parameters 0) ⋏
          quantifierFreeIntroductionFormula current
            (parameters 0 + 1) (parameters 0 + 1 + 1)) ⋏
        (∀⁰ ∀⁰ ∀⁰
          (current 🡘 DynamicTruthFormula.successorTruthFormula predecessor
            (parameters 0) (parameters 0 + 1)))) := by
  simp [sourceDerivedStrongStepPremises,
    ModelCodedTwoPredicateParameters.translateFormula,
    translate_sourcePriorCrossLevelContext,
    translate_sourceDerivedTargetQuantifierFreeIntroduction
      predecessor current parameters hpositive,
    translate_sourceDerivedCurrentDefinition
      predecessor current parameters hpositive]

@[simp] theorem translate_sourceDerivedCurrentSigmaDomain
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentSigmaDomain) =
      sigmaDomainFormula (parameters 0 + 1) := by
  simp [sourceDerivedCurrentSigmaDomain, sigmaDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourceDerivedCurrentLevel parameters hpositive]

@[simp] theorem translate_sourceDerivedCurrentPiDomain
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentPiDomain) =
      piDomainFormula (parameters 0 + 1) := by
  simp [sourceDerivedCurrentPiDomain, piDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourceDerivedCurrentLevel parameters hpositive]

@[simp] theorem translate_sourceDerivedCurrentPiTruth
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedCurrentPiTruth) =
      lowerPiTruthFormula current (parameters 0 + 1) := by
  simp [sourceDerivedCurrentPiTruth, lowerPiTruthFormula,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    DynamicTruthFormula.apply₃,
    translate_sourceDerivedCurrentPiDomain
      predecessor current parameters hpositive]

@[simp] theorem translate_sourceDerivedNextCrossLevelBody
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedNextCrossLevelBody) =
      crossLevelBodyFormula current
        (parameters 0 + 1) (parameters 0 + 1 + 1) := by
  simp [sourceDerivedNextCrossLevelBody, crossLevelBodyFormula,
    FirstOrder.Semiformula.iff_eq,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    translate_sourceDerivedCurrentPiTruth
      predecessor current parameters hpositive,
    translate_sourceDerivedCurrentSuccessorTruth
      predecessor current parameters hpositive]
  constructor
  · have hsneg :
        translateFormula predecessor current parameters
            (Semiformula.neg
              (Rewriting.emb sourceDerivedCurrentSigmaDomain)) =
          ∼(sigmaDomainFormula (parameters 0 + 1)) := by
      calc
        _ = ∼translateFormula predecessor current parameters
            (Rewriting.emb sourceDerivedCurrentSigmaDomain) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedTwoPredicateParameters.translateFormula_neg
              predecessor current parameters
              (Rewriting.emb sourceDerivedCurrentSigmaDomain))
        _ = _ := congrArg (∼·)
          (translate_sourceDerivedCurrentSigmaDomain
            predecessor current parameters hpositive)
    rw [hsneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]
  · have hpneg :
        translateFormula predecessor current parameters
            (Semiformula.neg
              (Rewriting.emb sourceDerivedCurrentPiDomain)) =
          ∼(piDomainFormula (parameters 0 + 1)) := by
      calc
        _ = ∼translateFormula predecessor current parameters
            (Rewriting.emb sourceDerivedCurrentPiDomain) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedTwoPredicateParameters.translateFormula_neg
              predecessor current parameters
              (Rewriting.emb sourceDerivedCurrentPiDomain))
        _ = _ := congrArg (∼·)
          (translate_sourceDerivedCurrentPiDomain
            predecessor current parameters hpositive)
    rw [hpneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]

@[simp] theorem translate_sourceDerivedNextCrossLevelInvariant
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hpositive : 0 < parameters 0) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceDerivedNextCrossLevelInvariant) =
      crossLevelPredicateFormula current
        (parameters 0 + 1) (parameters 0 + 1 + 1) := by
  simp [sourceDerivedNextCrossLevelInvariant,
    crossLevelPredicateFormula,
    ModelCodedTwoPredicateParameters.translateFormula,
    translate_sourceDerivedNextCrossLevelBody
      predecessor current parameters hpositive]

/-! ## Positive-orbit specialization -/

section Orbit

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Parameters used to pass from the positive field at index `n` to the
next positive field.  The old level is `n + 1`, hence it is provably
positive even when `n` is nonstandard. -/
noncomputable def orbitParameters (n : V) : Fin 3 → V :=
  ![n + 1, n + 1 + 1, n + 1 + 1 + 1]

/-- Exact translated antecedent of the derived source theorem. -/
noncomputable def orbitDerivedStrongStepContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula (truthFormula n) (truthFormula (n + 1))
    (orbitParameters n) (Rewriting.emb sourceDerivedStrongStepPremises)

/-- Exact translated unary constructor predicate. -/
noncomputable def orbitDerivedCrossLevelPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula (truthFormula n) (truthFormula (n + 1))
    (orbitParameters n)
    (Rewriting.emb sourceDerivedNextCrossLevelInvariant)

/-- The source's definitional premise becomes a literal reflexive
biconditional after adjacent orbit formulas are inserted. -/
noncomputable def orbitCurrentDefinitionFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰ (truthFormula (n + 1) 🡘 truthFormula (n + 1))

@[simp] theorem translate_sourceDerivedNextCrossLevelInvariant_orbit
    (n : V) :
    orbitDerivedCrossLevelPredicate n = nextCrossLevelPredicate n := by
  unfold orbitDerivedCrossLevelPredicate nextCrossLevelPredicate
  rw [translate_sourceDerivedNextCrossLevelInvariant
    (truthFormula n) (truthFormula (n + 1)) (orbitParameters n)
    (by simp [orbitParameters])]
  simp [orbitParameters]

@[simp] theorem translate_sourceDerivedStrongStepPremises_orbit (n : V) :
    orbitDerivedStrongStepContext n =
      ((orbitSuccessorCrossLevelFormula n ⋏
          orbitQuantifierFreeIntroductionFormula (n + 1)) ⋏
        orbitCurrentDefinitionFormula n) := by
  unfold orbitDerivedStrongStepContext
  rw [translate_sourceDerivedStrongStepPremises
    (truthFormula n) (truthFormula (n + 1)) (orbitParameters n)
    (by simp [orbitParameters])]
  simp [orbitParameters, orbitCurrentDefinitionFormula,
    orbitQuantifierFreeIntroductionFormula,
    orbitSuccessorCrossLevelFormula,
    quantifierFreeIntroductionFormula,
    truthFormula_succ]

/-- The definition-identification component of the source antecedent becomes
a pure logical reflexivity after the adjacent orbit formulas are inserted.
The three generalizations are genuine represented proof constructors; they
do not inspect the code of the (possibly nonstandard) truth formula. -/
noncomputable def orbitCurrentDefinitionProof (n : V) :
    Peano.internalize V ⊢! orbitCurrentDefinitionFormula n := by
  unfold orbitCurrentDefinitionFormula
  apply TProof.all
  simp [Bootstrapping.Semiformula.free]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free,
    LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  exact Entailment.E_Id (𝓢 := Peano.internalize V)

/-- The already available cross-level field supplies the source antecedent:
the quantifier-free component is a PA theorem, and the last component is the
reflexive definition theorem above. -/
noncomputable def orbitDerivedStrongStepContextProofFromCross (n : V) :
    Peano.internalize V ⊢!
      orbitSuccessorCrossLevelFormula n 🡒
        orbitDerivedStrongStepContext n := by
  rw [translate_sourceDerivedStrongStepPremises_orbit]
  exact Entailment.CK_of_C_of_C
    (Entailment.CK_of_C_of_C
      Entailment.C_id
      (Entailment.C_of_conseq
        (orbitQuantifierFreeIntroductionProof (n + 1))))
    (Entailment.C_of_conseq (orbitCurrentDefinitionProof n))

/-- Positive-to-next-positive constructor step, compiled from the audited
fixed source derivation.  Expanding `strongStepFormula` only at this final
composition point makes the change of antecedent an ordinary Hilbert
implication transitivity. -/
noncomputable def orbitCrossLevelStrongStepProof (n : V) :
    Peano.internalize V ⊢!
      strongStepFormula
        (orbitSuccessorCrossLevelFormula n)
        (nextCrossLevelPredicate n) := by
  have hcompiled : Peano.internalize V ⊢!
      strongStepFormula
        (orbitDerivedStrongStepContext n)
        (orbitDerivedCrossLevelPredicate n) := by
    simpa only [orbitDerivedStrongStepContext,
      orbitDerivedCrossLevelPredicate] using
      (compiledDerivedStrongStepProof
        (truthFormula n) (truthFormula (n + 1))
        (orbitParameters n)
        (truthFormula_shift n) (truthFormula_shift (n + 1)))
  rw [translate_sourceDerivedNextCrossLevelInvariant_orbit] at hcompiled
  rw [strongStepFormula_eq] at hcompiled ⊢
  exact Entailment.C_trans
    (orbitDerivedStrongStepContextProofFromCross n) hcompiled

/-- Closedness of the prior cross-level context, obtained by transporting
the fixed source sentence through the two-predicate translator. -/
@[simp] theorem orbitSuccessorCrossLevelFormula_shift (n : V) :
    (orbitSuccessorCrossLevelFormula n).shift =
      orbitSuccessorCrossLevelFormula n := by
  rw [← translate_sourcePriorCrossLevelContext_orbit n]
  rw [← ModelCodedTwoPredicateParameters.translateFormula_shift
    (truthFormula n) (truthFormula (n + 1))
    ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
    (truthFormula_shift n) (truthFormula_shift (n + 1))]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- PA's represented induction axiom turns the compiled strong step into the
universal next cross-level field.  Both closedness obligations are syntactic
translation lemmas, so this remains uniform for nonstandard `n`. -/
noncomputable def orbitCrossLevelStructuralUniversalProof (n : V) :
    Peano.internalize V ⊢!
      orbitSuccessorCrossLevelFormula n 🡒
        ∀⁰ nextCrossLevelPredicate n :=
  ModelCodedStrongInduction.strongInductionProof
    (orbitSuccessorCrossLevelFormula n)
    (nextCrossLevelPredicate n)
    (orbitSuccessorCrossLevelFormula_shift n)
    (nextCrossLevelPredicate_shift n)
    (orbitCrossLevelStrongStepProof n)

/-- Production induction kernel for the positive cross-level successor. -/
noncomputable def orbitCrossLevelInductionKernel (n : V) :
    PAInductionKernel (orbitSuccessorCrossLevelFormula n) :=
  kernelOfStructuralUniversalProof n
    (orbitCrossLevelStructuralUniversalProof n)

/-! ## Installation under the production staged context -/

/-- At a positive certificate transition, the preceding master sentence is
the certificate at index `n + 1`.  Its cross-level projection is exactly the
minimal antecedent consumed above; the newly established local field remains
available as the right conjunct of the staged context. -/
noncomputable def proveOrbitCrossFromPositiveLocalContext (n : V) :
    Peano.internalize V ⊢!
      localContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields (n + 1))
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction (n + 1)) 🡒
        orbitSuccessorCrossLevelFormula n := by
  unfold localContext
  exact Entailment.C_trans Entailment.and₁ <| by
    simpa only [PATruthCertificateFamily.fields,
      compiledDynamicTruthCertificateFamily_crossLevel_succ] using
      (TruthCertificateFields.proveCrossLevel
        (T := Peano.internalize V)
        ((compiledDynamicTruthCertificateFamily (V := V)).fields (n + 1)))

/-- Cross-level induction kernel in the exact context expected by the staged
certificate compiler for every positive-to-next-positive transition. -/
noncomputable def stagedPositiveCrossLevelInductionKernel (n : V) :
    PAInductionKernel
      (localContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields (n + 1))
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction (n + 1))) :=
  PAInductionKernel.recontextualize
    (proveOrbitCrossFromPositiveLocalContext n)
    (orbitCrossLevelInductionKernel n)

end Orbit

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelPositiveRankProduction
