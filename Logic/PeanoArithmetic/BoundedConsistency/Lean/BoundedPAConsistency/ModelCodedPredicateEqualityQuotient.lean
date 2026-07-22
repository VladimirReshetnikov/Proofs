import BoundedPAConsistency.ModelCodedPredicateParameters
import Foundation.FirstOrder.Completeness

/-!
# Equality completion for one-predicate proof templates

This is the one-placeholder companion of
`ModelCodedTwoPredicateEqualityQuotient`.  Lifted PA supplies equality
congruence for the arithmetic summand, while a single explicit `relExt`
sentence supplies congruence for the opaque relation.  Named parameters are
nullary functions, so their congruence axiom follows from reflexivity.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-- Bundle the arithmetic operator instances inherited by the expanded
sum language. -/
instance (arity count : ℕ) :
    (parameterTemplateLanguage arity count).ORing where
  eq := Language.Eq.eq
  lt := Language.LT.lt
  zero := Language.Zero.zero
  one := Language.One.one
  add := Language.Add.add
  mul := Language.Mul.mul

/-- The unique opaque relation symbol in the parameter-template language. -/
def placeholderRelation (arity count : ℕ) :
    (parameterTemplateLanguage arity count).Rel arity :=
  Sum.inr (Sum.inl PlaceholderRel.predicate)

/-- Coordinatewise congruence for the opaque relation placeholder. -/
noncomputable def placeholderCongruenceSentence (arity count : ℕ) :
    Sentence (parameterTemplateLanguage arity count) :=
  Theory.Eq.relExt (placeholderRelation arity count)

section Models

variable {arity count : ℕ}

private abbrev L (arity count : ℕ) : Language :=
  parameterTemplateLanguage arity count

/-- Lifted PA plus placeholder congruence satisfies every equality axiom of
the expanded one-predicate language. -/
theorem models_fullEquality
    {M : Type*} [Nonempty M] [Structure (L arity count) M]
    (hPA : M↓[L arity count] ⊧* parameterTemplatePeano arity count)
    (hcong : M↓[L arity count] ⊧
      placeholderCongruenceSentence arity count) :
    M↓[L arity count] ⊧* 𝗘𝗤 (L arity count) := by
  /- Reason semantically in the arithmetic reduct.  This avoids normalizing
  mapped equality syntax and works for arbitrary prestructures. -/
  letI : Structure ℒₒᵣ M :=
    (inferInstance : Structure (L arity count) M).lMap
      (ModelCodedPredicateParameters.arithmeticHom arity count)
  have hArithmeticPA : M↓[ℒₒᵣ] ⊧* Peano := by
    constructor
    intro sigma hsigma
    exact Semiformula.models_lMap.mp <|
      hPA.models _ ⟨sigma, hsigma, rfl⟩
  letI : M↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
  letI : M↓[ℒₒᵣ] ⊧* 𝗘𝗤 ℒₒᵣ := models_of_subtheory hArithmeticPA
  constructor
  intro sigma hsigma
  cases hsigma with
  | refl =>
      simp [models_iff, Theory.Eq.refl]
      intro x
      change Structure.Eq.eqv ℒₒᵣ x x
      exact Structure.Eq.eqv_refl (L := ℒₒᵣ) x
  | symm =>
      simp [models_iff, Theory.Eq.symm]
      intro x y hxy
      change Structure.Eq.eqv ℒₒᵣ x y at hxy
      change Structure.Eq.eqv ℒₒᵣ y x
      exact Structure.Eq.eqv_symm (L := ℒₒᵣ) hxy
  | trans =>
      simp [models_iff, Theory.Eq.trans]
      intro x y z hxy hyz
      change Structure.Eq.eqv ℒₒᵣ x y at hxy
      change Structure.Eq.eqv ℒₒᵣ y z at hyz
      change Structure.Eq.eqv ℒₒᵣ x z
      exact Structure.Eq.eqv_trans (L := ℒₒᵣ) hxy hyz
  | @funcExt k f =>
      rcases f with f | f
      · simp [models_iff, Theory.Eq.funcExt]
        intro v hv
        change ∀ i, Structure.Eq.eqv ℒₒᵣ
          (v (Fin.addCast k i)) (v (i.addNat k)) at hv
        change Structure.Eq.eqv ℒₒᵣ
          (Structure.func f (fun i ↦ v (Fin.addCast k i)))
          (Structure.func f (fun i ↦ v (i.addNat k)))
        exact Structure.Eq.eqv_funcExt (L := ℒₒᵣ) f hv
      · rcases f with f | f
        · exact PEmpty.elim f
        · cases f with
          | parameter i =>
              simp [models_iff, Theory.Eq.funcExt]
              change Structure.Eq.eqv ℒₒᵣ (M := M) _ _
              apply Structure.Eq.eqv_refl (L := ℒₒᵣ) (M := M)
  | @relExt k r =>
      rcases r with r | r
      · simp [models_iff, Theory.Eq.relExt]
        intro v hv
        change ∀ i, Structure.Eq.eqv ℒₒᵣ
          (v (Fin.addCast k i)) (v (i.addNat k)) at hv
        exact (Structure.Eq.eqv_relExt (L := ℒₒᵣ) r hv).mp
      · rcases r with r | r
        · cases r
          simpa [placeholderCongruenceSentence,
            placeholderRelation] using hcong
        · exact PEmpty.elim r

set_option maxHeartbeats 800000 in
/-- Completeness through the equality quotient for one-predicate templates. -/
noncomputable def complete_underPlaceholderCongruence
    (sigma : Sentence (L arity count))
    (H : ∀ (X : Type)
        [ORingStructure X]
        [Structure (L arity count) X]
        [Structure.ORing (L arity count) X]
        [X↓[L arity count] ⊧* parameterTemplatePeano arity count],
        X↓[L arity count] ⊧ sigma) :
    parameterTemplatePeano arity count ⊢!
      Arrow.arrow (placeholderCongruenceSentence arity count) sigma :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ hPA ↦ by
    simp [models_iff]
    intro hcong
    letI : M↓[L arity count] ⊧* 𝗘𝗤 (L arity count) :=
      models_fullEquality hPA hcong

    let Q := Structure.Eq.QuotEq (L arity count) M
    letI : Nonempty Q := Structure.Eq.QuotEq.inhabited
    letI : Structure (L arity count) Q := Structure.Eq.QuotEq.struc
    letI : Structure.Eq (L arity count) Q :=
      Structure.Eq.QuotEq.structureEq
    have quotientElementary : Q ≡ₑ[L arity count] M :=
      Structure.Eq.QuotEq.elementaryEquiv (L arity count) M
    have hQPA : Q↓[L arity count] ⊧*
        parameterTemplatePeano arity count :=
      quotientElementary.modelsTheory.mpr hPA

    let X := Structure.Model (L arity count) Q
    letI : X↓[L arity count] ⊧*
        parameterTemplatePeano arity count :=
      Structure.ElementaryEquiv.modelsTheory.mp hQPA
    have modelElementary : Q ≡ₑ[L arity count] X := inferInstance
    have hX : X↓[L arity count] ⊧ sigma := H X
    exact quotientElementary.models.mp (modelElementary.models.mpr hX)).get

end Models

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
