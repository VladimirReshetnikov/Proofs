import BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero
import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
import BoundedPAConsistency.ModelCodedStrongInduction
import Foundation.FirstOrder.Completeness

/-!
# Fixed-source strong step for dynamic substitution invariance

The staged successor certificate proves simultaneous-substitution invariance
after the new local, cross-level, and shift laws have been installed.  Formula
codes at a nonstandard hierarchy index cannot be decoded in Lean, so the
remaining argument must be a represented strong induction on the code.

This module fixes that induction problem in the original one-predicate,
two-parameter source language.  In particular, its context contains the
actual four local laws (including quantifier-free introduction), cross-level
coherence, and shift invariance.  The induction predicate is exactly
`sourceSubstitutionInvariantPredicate`; no opaque source atom stands in for
either the context or the target.

The off-domain branch below is already a complete lifted-PA derivation.  It
is separated from the constructor-wise valid-domain branch so that later
work cannot accidentally hide the latter behind a semantic premise.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Exact staged source context -/

/-- The three local eliminators already compiled for a dynamic successor. -/
noncomputable def sourceLocalEliminationBundle : Sentence SourceLanguage :=
  localProjectionSentence ⋏
    (memberValiditySentence ⋏ universalLeafProjectionSentence)

/-- All laws available before the substitution stage.

The grouping mirrors the typed production field:
`(local eliminators ⋏ qf introduction) ⋏ (cross ⋏ shift)`.
Keeping the quantifier-free introduction law here is essential for atomic
and Boolean leaves of the represented structural induction. -/
noncomputable def sourceAvailableContext : Sentence SourceLanguage :=
  (sourceLocalEliminationBundle ⋏
      sourceQuantifierFreeIntroductionSentence) ⋏
    (sourceCrossLevelSentence ⋏ sourceShiftInvariantSentence)

/-! ## Strong-induction syntax -/

/-- Arithmetic guard `y < x` below the prefix quantifier. -/
noncomputable def sourcePrefixGuard : Semisentence SourceLanguage 2 :=
  .rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2))
    ![(#0 : ClosedSemiterm SourceLanguage 2),
      (#1 : ClosedSemiterm SourceLanguage 2)]

/-- The strong prefix `forall y < x, SubstitutionInvariant(y)`. -/
noncomputable def sourceStrongPrefix : Semisentence SourceLanguage 1 :=
  ∀⁰[sourcePrefixGuard]
    (sourceSubstitutionInvariantPredicate/[
      (#0 : ClosedSemiterm SourceLanguage 2)])

/-- Complete represented strong-step premise for substitution invariance. -/
noncomputable def sourceStrongStepSentence : Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      sourceSubstitutionInvariantPredicate)

/-- Expose the embedded prefix without asking reduction to traverse the large
substitution-invariance formula.  The substitution/coercion compatibility
theorem keeps that formula opaque and rewrites only its outer application. -/
private theorem emb_sourceStrongPrefix :
    (Rewriting.emb sourceStrongPrefix :
        Semiproposition SourceLanguage 1) =
      ∀⁰[(Rewriting.emb sourcePrefixGuard :
          Semiproposition SourceLanguage 2)]
        (Rew.subst ![(#0 : SyntacticSemiterm SourceLanguage 2)] ▹
          (Rewriting.emb sourceSubstitutionInvariantPredicate :
            Semiproposition SourceLanguage 1)) := by
  unfold sourceStrongPrefix
  rw [Rewriting.smul_ball]
  simp only [Rew.q_emb]
  rw [Semiformula.coe_subst_eq_subst_coe]
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Structural embedding of the complete source premise.  Applying the
logical-homomorphism laws one layer at a time prevents eager expansion of
the fixed but sizeable target formula. -/
private theorem emb_sourceStrongStepSentence :
    (Rewriting.emb sourceStrongStepSentence : Proposition SourceLanguage) =
      Arrow.arrow
        (Rewriting.emb sourceAvailableContext : Proposition SourceLanguage)
        (∀⁰ Arrow.arrow
          (Rewriting.emb sourceStrongPrefix :
            Semiproposition SourceLanguage 1)
          (Rewriting.emb sourceSubstitutionInvariantPredicate :
            Semiproposition SourceLanguage 1)) := by
  unfold sourceStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]
  rw [Rewriting.app_all]
  simp only [Rew.q_emb]
  rw [LogicalConnective.HomClass.map_imply]

/-- Unary test saying that the induction code is in the advertised
quantifier-group domain.  The arity-specific well-formedness hypothesis stays
inside `sourceSubstitutionInvariantBody`; failure of this smaller guard is
already enough to make every instance of that body vacuous. -/
noncomputable def sourceBoundedDomainAtFormulaCode :
    Semisentence SourceLanguage 1 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (parameterTerm 0) (#0)

/-- Valid-domain portion of the strong step. -/
noncomputable def sourceValidDomainStrongStepSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      (Arrow.arrow sourceBoundedDomainAtFormulaCode
        sourceSubstitutionInvariantPredicate))

/-- Complementary off-domain portion. -/
noncomputable def sourceOffDomainStrongStepSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      (Arrow.arrow (∼sourceBoundedDomainAtFormulaCode)
        sourceSubstitutionInvariantPredicate))

/-- The seven-variable body and the unary domain test inspect the same
formula code and named lower hierarchy level. -/
private theorem eval_sourceBoundedDomain_iff_unary
    {M : Type*} [Structure SourceLanguage M]
    (p subBound terms termBound free bound arity : M) :
    (Semiformula.Eval
        ![arity, bound, free, termBound, terms, subBound, p]
        Empty.elim)
        DynamicTruthSubstitutionInvariantFormula.sourceBoundedDomain ↔
      (Semiformula.Eval ![p] Empty.elim)
        sourceBoundedDomainAtFormulaCode := by
  simp [DynamicTruthSubstitutionInvariantFormula.sourceBoundedDomain,
    sourceBoundedDomainAtFormulaCode,
    DynamicTruthTemplateFormula.apply₂, parameterTerm]

set_option maxHeartbeats 800000 in
/-- Outside the represented hierarchy domain every arity instance of the
target implication is vacuous.  This is an actual derivation in the fixed
source theory; the context and strong prefix remain literal antecedents. -/
noncomputable def sourceOffDomainStrongStepProof :
    parameterTemplatePeano 3 2 ⊢! sourceOffDomainStrongStepSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceOffDomainStrongStepSentence,
      sourceStrongPrefix, sourceBoundedDomainAtFormulaCode,
      sourceSubstitutionInvariantPredicate,
      sourceSubstitutionInvariantBody,
      DynamicTruthSubstitutionInvariantFormula.sourceBoundedDomain]
    intro ambient _structure _models _context p _prefix houtside
      subBound terms termBound free bound arity
      _termVector _boundLength _environment _semiformula hbounded
    exfalso
    apply houtside
    exact (eval_sourceBoundedDomain_iff_unary
      p subBound terms termBound free bound arity).mp hbounded).get

/-! ## Honest remaining source obligation -/

/-- A derivation of the constructor-wise valid-domain branch.  This record
does not add an axiom to the source theory: its field is itself a proof term
in lifted PA.  The production construction must eventually provide a closed
value of this type. -/
structure SourceValidDomainStep where
  proof : parameterTemplatePeano 3 2 ⊢!
    sourceValidDomainStrongStepSentence

set_option maxHeartbeats 800000 in
/-- Recombine valid and off-domain derivations by fixed first-order logic. -/
noncomputable def SourceValidDomainStep.proveStrongStep
    (step : SourceValidDomainStep) :
    parameterTemplatePeano 3 2 ⊢! sourceStrongStepSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro _ambient _structure hmodels
    have hvalid := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          sourceValidDomainStrongStepSentence from ⟨step.proof⟩)
    have hoff := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          sourceOffDomainStrongStepSentence from
        ⟨sourceOffDomainStrongStepProof⟩)
    simp [models_iff, sourceValidDomainStrongStepSentence,
      sourceOffDomainStrongStepSentence]
      at hvalid hoff
    simp [models_iff, sourceStrongStepSentence]
    intro hcontext p hprefix
    by_cases hdomain :
        (Semiformula.Eval ![p] Empty.elim)
          sourceBoundedDomainAtFormulaCode
    · exact hvalid hcontext p hprefix hdomain
    · exact hoff hcontext p hprefix hdomain).get

/-! ## Exact specialization to model-coded syntax -/

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Translation preserves a bounded universal while leaving its two source
subformulas opaque.  This small structural lemma avoids normalizing the
entire substitution-invariance predicate during the compiler splice. -/
private theorem translate_sourceBall
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) {n : ℕ}
    (guard body : Semiproposition SourceLanguage (n + 1)) :
    translateFormula lower parameters (∀⁰[guard] body) =
      ∀⁰[translateFormula lower parameters guard]
        translateFormula lower parameters body := by
  change translateFormula lower parameters
      (∀⁰ (∼guard ⋎ body)) = _
  change
    (∀⁰ (translateFormula lower parameters (∼guard) ⋎
      translateFormula lower parameters body)) = _
  rw [ModelCodedPredicateParameters.translateFormula_neg]
  rfl

/-- Translation commutes with one ordinary universal binder, stated
separately so its body is never unfolded by simplification. -/
private theorem translate_sourceAll
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) {n : ℕ}
    (body : Semiproposition SourceLanguage (n + 1)) :
    translateFormula lower parameters (∀⁰ body) =
      ∀⁰ translateFormula lower parameters body := by
  rfl

/-- Typed spelling of the fixed source context. -/
noncomputable def availableContextFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ((localProjectionFormula lower lowerLevel upperLevel ⋏
      (memberValidityFormula lower lowerLevel upperLevel ⋏
        universalLeafProjectionFormula lower lowerLevel upperLevel)) ⋏
    quantifierFreeIntroductionFormula lower lowerLevel upperLevel) ⋏
  (crossLevelFormula lower lowerLevel upperLevel ⋏
    shiftInvariantFormula lower lowerLevel upperLevel)

/-- Literal specialization of the complete staged source context. -/
@[simp] theorem translate_sourceAvailableContext
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAvailableContext) =
      availableContextFormula lower lowerLevel upperLevel := by
  simp [sourceAvailableContext, sourceLocalEliminationBundle,
    availableContextFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! The two private lemmas below keep the translated predicate opaque while
normalizing the source syntax.  This is more than a performance device: it
makes clear that the splice is structural and does not inspect the very large
definition of substitution invariance. -/

private theorem translate_sourceStrongPrefix_of_target
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (target : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (htarget :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceSubstitutionInvariantPredicate) = target) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceStrongPrefix) =
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongPrefixFormula
        target := by
  have hguard :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourcePrefixGuard) =
        LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb
            LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.sourcePrefixGuard) := by
    rfl
  have hsourceApplication :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rew.subst ![(#0 : SyntacticSemiterm SourceLanguage 2)] ▹
            (Rewriting.emb sourceSubstitutionInvariantPredicate :
              Semiproposition SourceLanguage 1)) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    rw [ModelCodedPredicateParameters.translateFormula_subst,
      htarget]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericApplication :
      LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb
            (LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.sourcePredicateAtom
              (#0))) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    simp [
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.sourcePredicateAtom,
      TwoPredicateSourceContextInductionKernel.secondAtom,
      LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula,
      LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateTerm]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericShape :
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongPrefixFormula
          target =
        ∀⁰
          (LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (∼(Rewriting.emb
                LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.sourcePrefixGuard)) ⋎
            LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (Rewriting.emb
                (LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.sourcePredicateAtom
                  (#0)))) := by
    rfl
  rw [emb_sourceStrongPrefix, translate_sourceBall, hgenericShape]
  rw [LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters.translateFormula_neg,
    hguard, hsourceApplication, hgenericApplication]
  rfl

/-- The fixed-source bounded prefix specializes to the exact prefix used by
the generic represented strong-induction compiler. -/
@[simp] theorem translate_sourceStrongPrefix
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceStrongPrefix) =
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongPrefixFormula
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel) :=
  translate_sourceStrongPrefix_of_target lower lowerLevel upperLevel
    (substitutionInvariantPredicateFormula lower lowerLevel upperLevel)
    (translate_sourceSubstitutionInvariantPredicate lower lowerLevel upperLevel)

private theorem translate_sourceStrongStepSentence_of_target
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (target : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceAvailableContext) = context)
    (htarget :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceSubstitutionInvariantPredicate) = target)
    (hprefix :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceStrongPrefix) =
        LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongPrefixFormula
          target) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceStrongStepSentence) =
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongStepFormula
        context target := by
  rw [emb_sourceStrongStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceAll,
    DynamicTruthTemplateFormula.translate_imp,
    hcontext, hprefix, htarget,
    LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongStepFormula_eq]

/-- The whole rich-source premise is syntactically the premise consumed by
`ModelCodedStrongInduction`; no semantic equivalence or decoded formula is
used at the splice. -/
@[simp] theorem translate_sourceStrongStepSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceStrongStepSentence) =
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongStepFormula
        (availableContextFormula lower lowerLevel upperLevel)
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel) :=
  translate_sourceStrongStepSentence_of_target lower lowerLevel upperLevel
    (availableContextFormula lower lowerLevel upperLevel)
    (substitutionInvariantPredicateFormula lower lowerLevel upperLevel)
    (translate_sourceAvailableContext lower lowerLevel upperLevel)
    (translate_sourceSubstitutionInvariantPredicate lower lowerLevel upperLevel)
    (translate_sourceStrongPrefix lower lowerLevel upperLevel)

/-- Compile any completed valid-domain construction into the exact typed
strong-step premise at arbitrary model-coded lower syntax and levels. -/
noncomputable def compiledStrongStepProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower)
    (step : SourceValidDomainStep) :
    Peano.internalize V ⊢!
      LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction.strongStepFormula
        (availableContextFormula lower lowerLevel upperLevel)
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel) := by
  rw [← translate_sourceStrongStepSentence]
  exact compilePeanoTemplate lower ![lowerLevel, upperLevel]
    hlower step.proveStrongStep

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource
