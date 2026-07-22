import BoundedPAConsistency.DynamicTruthLowerExistentialInterface
import BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
import BoundedPAConsistency.ModelCodedPredicateEqualityQuotient

/-!
# Compiling the restricted-soundness strong step

The local sequent-calculus theorem in `AbstractSoundness` requires five
semantic inputs for one represented truth successor: adjacency of its two
levels, the lower predicate's existential law, and the target successor's
cross-level, shift, substitution, and PA-axiom laws.  This module packages
those inputs as one fixed source context and proves the derivation-soundness
strong step under that context.

The opaque lower predicate is protected by the standard equality-quotient
antecedent.  Consequently the fixed source proof is sound for arbitrary
relation interpretations, while its later arithmetic specialization can
discharge congruence by PA's represented replacement theorem.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Fixed source context -/

/-- The second named level is the arithmetic successor of the first. -/
noncomputable def sourceAdjacentLevels : Sentence L :=
  .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
    ![parameterTerm 1,
      sourceLowerLevelSuccessor]

/-- Every semantic assumption consumed by the local restricted-calculus
soundness theorem.  The association is kept explicit because the translated
formula will later be reconstructed from separately compiled PA proofs. -/
noncomputable def sourceSoundnessLawContext : Sentence L :=
  sourceAdjacentLevels ⋏
    (sourceLowerExistentialLawsSentence ⋏
      (DynamicTruthCrossLevelFormula.sourceCrossLevelSentence ⋏
        (DynamicTruthShiftInvariantFormula.sourceShiftInvariantSentence ⋏
          (DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantSentence ⋏
            DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessSentence))))

/-- Context-relative strong-step theorem. -/
noncomputable def sourceRestrictedSoundnessStrongStepSentence : Sentence L :=
  sourceSoundnessLawContext 🡒 sourceDerivationSoundnessStrongStep

/-- Equality-safe form submitted to source completeness. -/
noncomputable def sourceCongruentRestrictedSoundnessStrongStepSentence :
    Sentence L :=
  placeholderCongruenceSentence 3 2 🡒
    sourceRestrictedSoundnessStrongStepSentence

/-! ## Semantics of the source context -/

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [Structure.ORing L M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

include hArithmeticReduct in
/-- Read equality in the distinguished arithmetic summand from the reduct
equation.  The expanded source language also has an `ORing` instance, but
using the reduct explicitly avoids asking typeclass reduction to identify
that instance's equality symbol with `Sum.inl Language.Eq.eq`. -/
private theorem source_eq_iff (a b : M) :
    Structure.rel (L := L)
      (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) ![a, b] ↔ a = b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.rel ℒₒᵣ M s 2 Language.Eq.eq ![a, b])
    hArithmeticReduct
  simpa using h

include hArithmeticReduct in
private theorem source_one_eq :
    Structure.func (L := L)
      (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![] = (1 : M) := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 0 Language.One.one ![])
    hArithmeticReduct
  simpa using h

include hArithmeticReduct in
private theorem source_add_eq (a b : M) :
    Structure.func (L := L)
      (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2)) ![a, b] = a + b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 2 Language.Add.add ![a, b])
    hArithmeticReduct
  simpa using h

include hArithmeticReduct in
@[simp] theorem eval_sourceAdjacentLevels :
    sourceAdjacentLevels.Evalb (M := M) ![] ↔
      DynamicTruthTemplateSemantics.level (M := M) 1 =
        DynamicTruthTemplateSemantics.level (M := M) 0 + 1 := by
  simp [sourceAdjacentLevels, parameterTerm,
    sourceLowerLevelSuccessor, sourceOne,
    DynamicTruthTemplateSemantics.level,
    source_eq_iff hArithmeticReduct,
    source_add_eq hArithmeticReduct,
    source_one_eq hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceSoundnessLawContext :
    sourceSoundnessLawContext.Evalb (M := M) ![] ↔
      (DynamicTruthTemplateSemantics.level (M := M) 1 =
        DynamicTruthTemplateSemantics.level (M := M) 0 + 1) ∧
      ExistentialLaws (lowerRelation (M := M)) ∧
      (∀ p : M, SuccessorCrossLaws
        lowerRelation
          (DynamicTruthTemplateSemantics.level (M := M) 0)
          (DynamicTruthTemplateSemantics.level (M := M) 1) p) ∧
      (∀ p : M, ShiftInvariantAt
        (SuccessorTruth lowerRelation
          (DynamicTruthTemplateSemantics.level (M := M) 0)
          (DynamicTruthTemplateSemantics.level (M := M) 1))
        (DynamicTruthTemplateSemantics.level (M := M) 0) p) ∧
      (∀ p : M, SubstitutionInvariantAt
        (SuccessorTruth lowerRelation
          (DynamicTruthTemplateSemantics.level (M := M) 0)
          (DynamicTruthTemplateSemantics.level (M := M) 1))
        (DynamicTruthTemplateSemantics.level (M := M) 0) p) ∧
      (∀ p : M, p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class →
        CodedHierarchy.QuantifierBoundedCode ℒₒᵣ
          (DynamicTruthTemplateSemantics.level (M := M) 0) p →
        ∀ free : M, Arithmetic.Seq free →
          SuccessorTruth lowerRelation
            (DynamicTruthTemplateSemantics.level (M := M) 0)
            (DynamicTruthTemplateSemantics.level (M := M) 1)
            0 free p) := by
  simp [sourceSoundnessLawContext,
    eval_sourceAdjacentLevels hArithmeticReduct,
    DynamicTruthLowerExistentialInterface.eval_sourceLowerExistentialLawsSentence
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_sourceCrossLevelSentence
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_sourceShiftInvariantSentence
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_sourceSubstitutionInvariantSentence
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_sourceAxiomSoundnessSentence
      hArithmeticReduct]

/-! ## Source proof -/

set_option maxHeartbeats 1600000 in
/-- The local rule analysis is now compiled once, for the fixed source
language.  Completeness is used only after quotienting the placeholder by
the explicit congruence antecedent; the arithmetic reduct of that canonical
model is the standard PA structure. -/
noncomputable def sourceCongruentRestrictedSoundnessStrongStepProof :
    parameterTemplatePeano 3 2 ⊢!
      sourceCongruentRestrictedSoundnessStrongStepSentence := by
  simpa [sourceCongruentRestrictedSoundnessStrongStepSentence] using
    (complete_underPlaceholderCongruence
      sourceRestrictedSoundnessStrongStepSentence
      (fun X ↦ by
        intro _ _ _ _
        have hArithmeticReduct :=
          DynamicTruthTemplateSemantics.arithmeticReduct_eq_standardModel
            (M := X)
        have hArithmeticPA : X↓[ℒₒᵣ] ⊧* Peano := by
          constructor
          intro sigma hsigma
          rw [← hArithmeticReduct]
          exact Semiformula.models_lMap.mp <|
            (inferInstance : X↓[L] ⊧*
              parameterTemplatePeano 3 2).models _
                ⟨sigma, hsigma, rfl⟩
        letI : X↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
        letI : X↓[ℒₒᵣ] ⊧* ISigma 1 :=
          models_of_subtheory hArithmeticPA
        simp [models_iff, sourceRestrictedSoundnessStrongStepSentence,
          eval_sourceSoundnessLawContext hArithmeticReduct,
          eval_sourceDerivationSoundnessStrongStep hArithmeticReduct]
        intro hnext hlowerExs hcross hshift hsubstitution hAx d ih hd
        exact restrictedDerivation_sequent_strongStep Peano
          (nextTruth_laws_of_lower_exs
            hnext hcross hlowerExs hshift hsubstitution)
          (fun p hp hbounded free hfree ↦
            hAx p hp
              (OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mp
                hbounded)
              free hfree)
          d ih hd))

end LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep
