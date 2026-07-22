import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor
import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.ModelCodedStrongInduction
import BoundedPAConsistency.TernaryCongruencePrototype

/-!
# Production compilation of positive-rank substitution invariance

The fixed one-predicate source theorem proves the constructor-wise strong
step with equality congruence for its opaque ternary predicate kept as an
explicit antecedent.  This module compiles that theorem into represented PA,
discharges congruence by formula replacement, specializes it to the dynamic
truth orbit, and installs the resulting induction kernel under the exact
staged substitution context.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Congruence-safe compilation into the generic strong step -/

private theorem emb_sourceCongruentStrongStepSentence :
    (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceCongruentStrongStepSentence :
        Proposition DynamicTruthTemplateFormula.SourceLanguage) =
      Arrow.arrow
        (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceLowerCongruenceSentence :
          Proposition DynamicTruthTemplateFormula.SourceLanguage)
        (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.sourceStrongStepSentence :
          Proposition DynamicTruthTemplateFormula.SourceLanguage) := by
  unfold LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceCongruentStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- Translation preserves the explicit one-placeholder congruence boundary,
while the source module's structural theorem identifies the consequent with
the generic represented strong-step premise. -/
theorem translate_sourceCongruentStrongStepSentence
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceCongruentStrongStepSentence) =
      (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceLowerCongruenceSentence) 🡒
        strongStepFormula
          (LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.availableContextFormula
            lower lowerLevel upperLevel)
          (substitutionInvariantPredicateFormula
            lower lowerLevel upperLevel)) := by
  rw [emb_sourceCongruentStrongStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.translate_sourceStrongStepSentence]

/-- Compile the audited fixed-source proof and discharge its sole opaque
relation congruence hypothesis with represented PA replacement. -/
noncomputable def compiledStrongStepProof
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      strongStepFormula
        (LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.availableContextFormula
          lower lowerLevel upperLevel)
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel) := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceCongruentStrongStepSentence) :=
    ModelCodedPredicateParameters.compilePeanoTemplate
      lower ![lowerLevel, upperLevel] hlower
      LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof.sourceCongruentStrongStepProof
  rw [translate_sourceCongruentStrongStepSentence] at hcompiled
  exact hcompiled ⨀
    translatedOnePredicateCongruenceProof
      lower ![lowerLevel, upperLevel]

/-! ## Exact dynamic-orbit specialization -/

section Orbit

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- All fields available immediately before substitution induction.  The
quantifier-free introduction theorem remains present in the augmented local
field, because the valid-domain source proof uses it at atomic leaves. -/
noncomputable def orbitAvailableContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  orbitCompiledLocalBundleWithQuantifierFreeIntroduction n ⋏
    (orbitSuccessorCrossLevelFormula n ⋏
      orbitSuccessorShiftInvariantFormula n)

/-- The rich fixed-source antecedent specializes literally to the three
staged orbit fields above. -/
@[simp] theorem availableContextFormula_orbit (n : V) :
    LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.availableContextFormula
        (truthFormula n) (n + 1) (n + 1 + 1) =
      orbitAvailableContext n := by
  simp [LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.availableContextFormula, orbitAvailableContext,
    orbitCompiledLocalBundleWithQuantifierFreeIntroduction,
    orbitCompiledLocalBundle, orbitLocalProjectionFormula,
    DynamicTruthLocalProjectionTemplate.localProjectionFormula,
    orbitMemberValidityFormula, orbitUniversalLeafProjectionFormula,
    orbitQuantifierFreeIntroductionFormula,
    quantifierFreeIntroductionFormula,
    orbitSuccessorCrossLevelFormula,
    orbitSuccessorShiftInvariantFormula, truthFormula_succ]

/-- Direct source-translation spelling used to prove coded closedness without
unfolding any model-indexed field. -/
@[simp] theorem translate_sourceAvailableContext_orbit (n : V) :
    translateFormula (truthFormula n) ![n + 1, n + 1 + 1]
        (Rewriting.emb LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.sourceAvailableContext) =
      orbitAvailableContext n := by
  rw [LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource.translate_sourceAvailableContext,
    availableContextFormula_orbit]

/-- The audited source derivation specialized to the exact substitution
strong-step premise at recurrence index `n`. -/
noncomputable def orbitSubstitutionInvariantStrongStepProof (n : V) :
    Peano.internalize V ⊢!
      strongStepFormula (orbitAvailableContext n)
        (nextSubstitutionInvariantPredicate n) := by
  simpa only [availableContextFormula_orbit,
    nextSubstitutionInvariantPredicate] using
    (compiledStrongStepProof
      (truthFormula n) (n + 1) (n + 1 + 1)
      (truthFormula_shift n))

/-- The complete pre-substitution context is closed under represented
free-variable shift.  This follows structurally by translating the fixed
source sentence. -/
@[simp] theorem orbitAvailableContext_shift (n : V) :
    (orbitAvailableContext n).shift = orbitAvailableContext n := by
  rw [← translate_sourceAvailableContext_orbit n]
  rw [← ModelCodedPredicateParameters.translateFormula_shift
    (truthFormula n) ![n + 1, n + 1 + 1]
    (truthFormula_shift n)]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Represented strong induction proves the complete next positive
substitution-invariance field at every model-coded recurrence index. -/
noncomputable def orbitSubstitutionInvariantStructuralUniversalProof
    (n : V) :
    Peano.internalize V ⊢!
      orbitAvailableContext n 🡒
        ∀⁰ nextSubstitutionInvariantPredicate n :=
  ModelCodedStrongInduction.strongInductionProof
    (orbitAvailableContext n)
    (nextSubstitutionInvariantPredicate n)
    (orbitAvailableContext_shift n)
    (nextSubstitutionInvariantPredicate_shift n)
    (orbitSubstitutionInvariantStrongStepProof n)

/-- Minimal-context induction kernel for the next substitution field. -/
noncomputable def orbitSubstitutionInvariantInductionKernel (n : V) :
    PAInductionKernel (orbitAvailableContext n) :=
  kernelOfStructuralUniversalProof
    (orbitAvailableContext n) n
    (orbitSubstitutionInvariantStructuralUniversalProof n)

/-- The production staged context proves exactly the rich source antecedent;
unlike the older zero-premise projection, this bridge deliberately retains
the quantifier-free introduction conjunct. -/
noncomputable def proveOrbitAvailableFromProductionShiftContext (n : V) :
    Peano.internalize V ⊢!
      shiftContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n) 🡒
        orbitAvailableContext n := by
  simpa only [orbitAvailableContext] using
    (LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero.proveAvailableFromShiftContext
      ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
      (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
      (orbitSuccessorCrossLevelFormula n)
      (orbitSuccessorShiftInvariantFormula n))

/-- Install the substitution kernel under the exact context expected by the
staged certificate compiler. -/
noncomputable def stagedSubstitutionInvariantInductionKernel (n : V) :
    PAInductionKernel
      (shiftContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
        (orbitSuccessorCrossLevelFormula n)
        (orbitSuccessorShiftInvariantFormula n)) :=
  PAInductionKernel.recontextualize
    (proveOrbitAvailableFromProductionShiftContext n)
    (orbitSubstitutionInvariantInductionKernel n)

end Orbit

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankProduction
