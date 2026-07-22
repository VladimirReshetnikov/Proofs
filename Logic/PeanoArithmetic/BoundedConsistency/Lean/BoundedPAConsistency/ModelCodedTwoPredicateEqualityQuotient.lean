import BoundedPAConsistency.ModelCodedTwoPredicateParameters
import Foundation.FirstOrder.Completeness

/-!
# Equality completion for two-predicate proof templates

The source theory used by the model-coded proof compiler is PA lifted through
the arithmetic summand.  Consequently it contains congruence axioms for the
arithmetic symbols, but it does not automatically contain congruence for the
two opaque predicate placeholders.  This distinction matters at a
completeness boundary: an arbitrary first-order prestructure may interpret
its equality relation by a nontrivial equivalence relation.

This module isolates the two missing relational congruence sentences.  Once
they hold, every equality axiom of the expanded source language holds.  We
can therefore quotient by interpreted equality, then wrap the quotient in
`Structure.Model`; the resulting elementarily equivalent model has genuine
Lean equality and canonical operations while retaining the interpretations
of both placeholders and all named parameters.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters

/-- Bundle the six arithmetic operator instances inherited from the left
summand.  `Language.add` supplies the component instances separately, but
does not synthesize the aggregate `Language.ORing` class automatically. -/
instance (arity₀ arity₁ count : ℕ) :
    (twoPredicateParameterLanguage arity₀ arity₁ count).ORing where
  eq := Language.Eq.eq
  lt := Language.LT.lt
  zero := Language.Zero.zero
  one := Language.One.one
  add := Language.Add.add
  mul := Language.Mul.mul

/-! ## The two missing congruence sentences -/

/-- The first opaque relation inside the nested four-way sum language. -/
def firstPlaceholderRelation (arity₀ arity₁ count : ℕ) :
    (twoPredicateParameterLanguage arity₀ arity₁ count).Rel arity₀ :=
  Sum.inr (Sum.inl PlaceholderRel.predicate)

/-- The second opaque relation inside the nested four-way sum language. -/
def secondPlaceholderRelation (arity₀ arity₁ count : ℕ) :
    (twoPredicateParameterLanguage arity₀ arity₁ count).Rel arity₁ :=
  Sum.inr (Sum.inr (Sum.inl PlaceholderRel.predicate))

/-- Coordinatewise congruence for the first placeholder relation.  The
standard equality axiom `relExt` universally quantifies two copies of every
coordinate and transports the relation from the first tuple to the second. -/
noncomputable def firstPlaceholderCongruenceSentence
    (arity₀ arity₁ count : ℕ) :
    Sentence (twoPredicateParameterLanguage arity₀ arity₁ count) :=
  Theory.Eq.relExt (firstPlaceholderRelation arity₀ arity₁ count)

/-- Coordinatewise congruence for the second placeholder relation. -/
noncomputable def secondPlaceholderCongruenceSentence
    (arity₀ arity₁ count : ℕ) :
    Sentence (twoPredicateParameterLanguage arity₀ arity₁ count) :=
  Theory.Eq.relExt (secondPlaceholderRelation arity₀ arity₁ count)

/-- Both opaque-relation congruence laws as one antecedent. -/
noncomputable def placeholderCongruenceContext
    (arity₀ arity₁ count : ℕ) :
    Sentence (twoPredicateParameterLanguage arity₀ arity₁ count) :=
  firstPlaceholderCongruenceSentence arity₀ arity₁ count ⋏
    secondPlaceholderCongruenceSentence arity₀ arity₁ count

section Models

variable {arity₀ arity₁ count : ℕ}

private abbrev L (arity₀ arity₁ count : ℕ) : Language :=
  twoPredicateParameterLanguage arity₀ arity₁ count

/-- Lifted PA together with the two opaque-relation congruence laws satisfies
the complete equality theory of the expanded language.

The nested sum analysis is the substantive point:

* arithmetic functions and relations are covered by mapped PA equality;
* both placeholder languages have no function symbols;
* named parameters are nullary, so their function congruence is reflexivity;
* the parameter language has no relations; and
* the two remaining relation cases are exactly the stated premises. -/
theorem models_fullEquality
    {M : Type*} [Nonempty M] [Structure (L arity₀ arity₁ count) M]
    (hPA : M↓[L arity₀ arity₁ count] ⊧*
      twoPredicateParameterPeano arity₀ arity₁ count)
    (h₀ : M↓[L arity₀ arity₁ count] ⊧
      firstPlaceholderCongruenceSentence arity₀ arity₁ count)
    (h₁ : M↓[L arity₀ arity₁ count] ⊧
      secondPlaceholderCongruenceSentence arity₀ arity₁ count) :
    M↓[L arity₀ arity₁ count] ⊧*
      𝗘𝗤 (L arity₀ arity₁ count) := by
  /- Work in the reduct induced by the arithmetic inclusion.  Keeping this
  as a local instance makes the equality-relation semantics definitionally
  identical on both sides while avoiding any formula-level `lMap`
  normalization. -/
  letI : Structure ℒₒᵣ M :=
    (inferInstance : Structure (L arity₀ arity₁ count) M).lMap
      (ModelCodedTwoPredicateParameters.arithmeticHom
        arity₀ arity₁ count)
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
          simpa [firstPlaceholderCongruenceSentence,
            firstPlaceholderRelation] using h₀
        · rcases r with r | r
          · cases r
            simpa [secondPlaceholderCongruenceSentence,
              secondPlaceholderRelation] using h₁
          · exact PEmpty.elim r

/-! ## Quotient-model completeness -/

set_option maxHeartbeats 800000 in
/-- Prove a source sentence under the two missing congruence laws by working
only with canonical equality models.

The semantic callback receives an expanded structure whose arithmetic
operators agree with its `ORingStructure`.  Internally we first quotient the
arbitrary completeness model by its interpreted equality relation and then
apply `Structure.Model`.  Both steps are elementary equivalences, so lifted
PA, the opaque predicate interpretations, the named parameters, and the
conclusion all transport without decoding any model element. -/
noncomputable def complete_underPlaceholderCongruence
    (sigma : Sentence (L arity₀ arity₁ count))
    (H : ∀ (X : Type)
        [ORingStructure X]
        [Structure (L arity₀ arity₁ count) X]
        [Structure.ORing (L arity₀ arity₁ count) X]
        [X↓[L arity₀ arity₁ count] ⊧*
          twoPredicateParameterPeano arity₀ arity₁ count],
        X↓[L arity₀ arity₁ count] ⊧ sigma) :
    twoPredicateParameterPeano arity₀ arity₁ count ⊢!
      Arrow.arrow
        (placeholderCongruenceContext arity₀ arity₁ count)
        sigma :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ hPA ↦ by
    simp [models_iff, placeholderCongruenceContext]
    intro h₀ h₁
    letI : M↓[L arity₀ arity₁ count] ⊧*
        𝗘𝗤 (L arity₀ arity₁ count) :=
      models_fullEquality hPA h₀ h₁

    let Q := Structure.Eq.QuotEq (L arity₀ arity₁ count) M
    letI : Nonempty Q := Structure.Eq.QuotEq.inhabited
    letI : Structure (L arity₀ arity₁ count) Q :=
      Structure.Eq.QuotEq.struc
    letI : Structure.Eq (L arity₀ arity₁ count) Q :=
      Structure.Eq.QuotEq.structureEq
    have quotientElementary :
        Q ≡ₑ[L arity₀ arity₁ count] M :=
      Structure.Eq.QuotEq.elementaryEquiv
        (L arity₀ arity₁ count) M
    have hQPA : Q↓[L arity₀ arity₁ count] ⊧*
        twoPredicateParameterPeano arity₀ arity₁ count :=
      quotientElementary.modelsTheory.mpr hPA

    let X := Structure.Model (L arity₀ arity₁ count) Q
    letI : X↓[L arity₀ arity₁ count] ⊧*
        twoPredicateParameterPeano arity₀ arity₁ count :=
      Structure.ElementaryEquiv.modelsTheory.mp hQPA
    have modelElementary :
        Q ≡ₑ[L arity₀ arity₁ count] X := inferInstance
    have hX : X↓[L arity₀ arity₁ count] ⊧ sigma := H X
    exact quotientElementary.models.mp (modelElementary.models.mpr hX)).get

end Models

end LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
