import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource
import BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
import BoundedPAConsistency.ModelCodedStrongInduction
import BoundedPAConsistency.TernaryCongruencePrototype

/-!
# Production compilation of the positive-rank shift-invariance step

The audited fixed-source theorem proves the constructor-wise strong step in
the shared two-predicate language.  This module performs the remaining
proof-code plumbing: it identifies the source prefix with the generic
model-coded strong-induction prefix, compiles the theorem into PA, discharges
both opaque-predicate congruence assumptions, and specializes the result to
the dynamic truth orbit.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
open LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
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
    (guard body : Semiproposition
      LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
      (n + 1)) :
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
    (body : Semiproposition
      LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
      (n + 1)) :
    translateFormula predecessor current parameters (∀⁰ body) =
      ∀⁰ translateFormula predecessor current parameters body := by
  rfl

private theorem translate_imp
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) {n : ℕ}
    (p q : Semiproposition
      LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
      n) :
    translateFormula predecessor current parameters (p 🡒 q) =
      (translateFormula predecessor current parameters p 🡒
        translateFormula predecessor current parameters q) := by
  change translateFormula predecessor current parameters (∼p ⋎ q) =
    (∼translateFormula predecessor current parameters p ⋎
      translateFormula predecessor current parameters q)
  simp only [ModelCodedTwoPredicateParameters.translateFormula]
  rw [ModelCodedTwoPredicateParameters.translateFormula_neg]

private theorem emb_sourceStrongPrefix :
    (Rewriting.emb
        LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix :
        Semiproposition
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
          1) =
      ∀⁰[(Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourcePrefixGuard :
          Semiproposition
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
            2)]
        (Rew.subst ![(#0 : SyntacticSemiterm
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
            2)] ▹
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate :
            Semiproposition
              LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
              1)) := by
  unfold LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix
  rw [Rewriting.smul_ball]
  simp only [Rew.q_emb]
  rw [Semiformula.coe_subst_eq_subst_coe]
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

private theorem emb_sourceStrongStepSentence :
    (Rewriting.emb
        LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence :
        Proposition
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage) =
      Arrow.arrow
        (Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceAvailableContext :
          Proposition
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage)
        (∀⁰ Arrow.arrow
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix :
            Semiproposition
              LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
              1)
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate :
            Semiproposition
              LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
              1)) := by
  unfold LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]
  rw [Rewriting.app_all]
  simp only [Rew.q_emb]
  rw [LogicalConnective.HomClass.map_imply]

private theorem translate_sourceStrongPrefix_of_target
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V)
    (target : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (htarget :
      translateFormula predecessor current parameters
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate) =
        target) :
    translateFormula predecessor current parameters
        (Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix) =
      strongPrefixFormula target := by
  have hguard :
      translateFormula predecessor current parameters
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourcePrefixGuard) =
        translateFormula (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb ModelCodedStrongInduction.sourcePrefixGuard) := by
    rfl
  have hsourceApplication :
      translateFormula predecessor current parameters
          (Rew.subst ![(#0 : SyntacticSemiterm
              LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
              2)] ▹
            (Rewriting.emb
              LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate :
              Semiproposition
                LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource.ShiftSourceLanguage
                1)) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    rw [ModelCodedTwoPredicateParameters.translateFormula_subst, htarget]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericApplication :
      translateFormula (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
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
          (translateFormula (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (∼(Rewriting.emb ModelCodedStrongInduction.sourcePrefixGuard)) ⋎
            translateFormula (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (Rewriting.emb
                (ModelCodedStrongInduction.sourcePredicateAtom (#0)))) := by
    rfl
  rw [emb_sourceStrongPrefix, translate_sourceBall, hgenericShape]
  rw [ModelCodedTwoPredicateParameters.translateFormula_neg,
    hguard, hsourceApplication, hgenericApplication]
  rfl

/-- The fixed-source shift prefix is exactly the generic represented
strong-induction prefix instantiated with the translated target. -/
theorem translate_sourceStrongPrefix
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix) =
      strongPrefixFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate)) :=
  translate_sourceStrongPrefix_of_target predecessor current parameters _ rfl

/-- The complete fixed-source shift step translates literally to the premise
accepted by `ModelCodedStrongInduction`. -/
theorem translate_sourceStrongStepSentence
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence) =
      strongStepFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceAvailableContext))
        (translateFormula predecessor current parameters
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate)) := by
  rw [emb_sourceStrongStepSentence]
  change translateFormula predecessor current parameters
      (Arrow.arrow
        (Rewriting.emb
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceAvailableContext)
        (∀⁰ Arrow.arrow
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix)
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource.sourceNextShiftInvariantPredicate))) = _
  rw [translate_imp, translate_sourceAll, translate_imp,
    translate_sourceStrongPrefix, strongStepFormula_eq]

/-! ## Congruence discharge and compiled strong-step proof -/

private theorem emb_sourceCongruentStrongStepSentence :
    (Rewriting.emb sourceCongruentStrongStepSentence :
        Proposition ShiftSourceLanguage) =
      Arrow.arrow
        (Rewriting.emb sourcePlaceholderCongruenceContext :
          Proposition ShiftSourceLanguage)
        (Rewriting.emb sourceStrongStepSentence :
          Proposition ShiftSourceLanguage) := by
  unfold sourceCongruentStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- Translation preserves the explicit congruence boundary and identifies
its consequent with the represented strong-step formula. -/
theorem translate_sourceCongruentStrongStepSentence
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    translateFormula predecessor current parameters
        (Rewriting.emb sourceCongruentStrongStepSentence) =
      (translateFormula predecessor current parameters
          (Rewriting.emb sourcePlaceholderCongruenceContext) 🡒
        strongStepFormula
          (translateFormula predecessor current parameters
            (Rewriting.emb sourceAvailableContext))
          (translateFormula predecessor current parameters
            (Rewriting.emb sourceNextShiftInvariantPredicate))) := by
  rw [emb_sourceCongruentStrongStepSentence]
  change translateFormula predecessor current parameters
      (Arrow.arrow
        (Rewriting.emb sourcePlaceholderCongruenceContext)
        (Rewriting.emb sourceStrongStepSentence)) = _
  rw [translate_imp, translate_sourceStrongStepSentence]

/-- Compile the audited constructor theorem and discharge the two
coordinatewise placeholder-congruence hypotheses with represented PA
replacement. -/
noncomputable def compiledStrongStepProof
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V)
    (hpredecessor : predecessor.shift = predecessor)
    (hcurrent : current.shift = current) :
    Peano.internalize V ⊢!
      strongStepFormula
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceAvailableContext))
        (translateFormula predecessor current parameters
          (Rewriting.emb sourceNextShiftInvariantPredicate)) := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula predecessor current parameters
        (Rewriting.emb sourceCongruentStrongStepSentence) :=
    ModelCodedTwoPredicateParameters.compilePeanoTemplate
      predecessor current parameters hpredecessor hcurrent
      sourceCongruentStrongStepProof
  rw [translate_sourceCongruentStrongStepSentence] at hcompiled
  exact hcompiled ⨀
    translatedTwoPredicateCongruenceContextProof
      predecessor current parameters

/-! ## Exact dynamic-orbit specialization -/

section Orbit

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Named levels used by the shift source at recurrence index `n`. -/
noncomputable def orbitParameters (n : V) : Fin 3 → V :=
  ![n, n + 1, n + 1 + 1]

/-- Exact translation of the source's two-field antecedent. -/
noncomputable def orbitTranslatedAvailableContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula (predecessorTruthFormula n) (truthFormula n)
    (orbitParameters n) (Rewriting.emb sourceAvailableContext)

/-- Exact translation of the unary shift-invariance target. -/
noncomputable def orbitTranslatedShiftInvariantPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula (predecessorTruthFormula n) (truthFormula n)
    (orbitParameters n)
    (Rewriting.emb sourceNextShiftInvariantPredicate)

@[simp] theorem translate_sourceAvailableContext_orbit_exact (n : V) :
    orbitTranslatedAvailableContext n = orbitAvailableContext n := by
  unfold orbitTranslatedAvailableContext orbitParameters
  rw [translate_sourceAvailableContext_orbit]
  rfl

@[simp] theorem translate_sourceNextShiftInvariantPredicate_orbit_exact
    (n : V) :
    orbitTranslatedShiftInvariantPredicate n =
      nextShiftInvariantPredicate n := by
  unfold orbitTranslatedShiftInvariantPredicate orbitParameters
  rw [translate_sourceNextShiftInvariantPredicate_orbit]

/-- The audited source derivation specialized to the exact strong-step
premise consumed by model-coded induction on the next shift law. -/
noncomputable def orbitShiftInvariantStrongStepProof (n : V) :
    Peano.internalize V ⊢!
      strongStepFormula (orbitAvailableContext n)
        (nextShiftInvariantPredicate n) := by
  have hcompiled : Peano.internalize V ⊢!
      strongStepFormula
        (orbitTranslatedAvailableContext n)
        (orbitTranslatedShiftInvariantPredicate n) := by
    simpa only [orbitTranslatedAvailableContext,
      orbitTranslatedShiftInvariantPredicate] using
      (compiledStrongStepProof
        (predecessorTruthFormula n) (truthFormula n)
        (orbitParameters n)
        (predecessorTruthFormula_shift n) (truthFormula_shift n))
  simpa only [translate_sourceAvailableContext_orbit_exact,
    translate_sourceNextShiftInvariantPredicate_orbit_exact] using hcompiled

/-- The two-field source antecedent is closed under the represented
free-variable shift.  The proof transports the fixed source sentence rather
than unfolding either model-coded truth field. -/
@[simp] theorem orbitAvailableContext_shift (n : V) :
    (orbitAvailableContext n).shift = orbitAvailableContext n := by
  unfold orbitAvailableContext
  rw [← translate_sourceAvailableContext_orbit n]
  rw [← ModelCodedTwoPredicateParameters.translateFormula_shift
    (predecessorTruthFormula n) (truthFormula n)
    ![n, n + 1, n + 1 + 1]
    (predecessorTruthFormula_shift n) (truthFormula_shift n)]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Represented strong induction proves the complete next positive
shift-invariance field uniformly at every (possibly nonstandard) index. -/
noncomputable def orbitShiftInvariantStructuralUniversalProof (n : V) :
    Peano.internalize V ⊢!
      orbitAvailableContext n 🡒 ∀⁰ nextShiftInvariantPredicate n :=
  ModelCodedStrongInduction.strongInductionProof
    (orbitAvailableContext n)
    (nextShiftInvariantPredicate n)
    (orbitAvailableContext_shift n)
    (nextShiftInvariantPredicate_shift n)
    (orbitShiftInvariantStrongStepProof n)

/-- Minimal-context induction kernel for the next shift-invariance field. -/
noncomputable def orbitShiftInvariantInductionKernel (n : V) :
    PAInductionKernel (orbitAvailableContext n) :=
  kernelOfStructuralUniversalProof
    (orbitAvailableContext n) n
    (orbitShiftInvariantStructuralUniversalProof n)

/-- Install the shift kernel under the precise context available after the
new local and cross-level fields have been compiled by the staged package. -/
noncomputable def stagedShiftInvariantInductionKernel (n : V) :
    PAInductionKernel
      (crossContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
        (orbitSuccessorCrossLevelFormula n)) :=
  PAInductionKernel.recontextualize
    (proveOrbitAvailableFromAugmentedCrossContext n)
    (orbitShiftInvariantInductionKernel n)

end Orbit

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankProduction
