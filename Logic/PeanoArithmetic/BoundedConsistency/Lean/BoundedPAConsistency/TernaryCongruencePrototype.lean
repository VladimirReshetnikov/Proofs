import BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
import BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory

namespace LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

private noncomputable def boundLeftTuple :
    Fin 3 → Bootstrapping.Semiterm V ℒₒᵣ 6 :=
  fun i ↦ Semiterm.bvar (i.addCast 3)

private noncomputable def boundRightTuple :
    Fin 3 → Bootstrapping.Semiterm V ℒₒᵣ 6 :=
  fun i ↦ Semiterm.bvar (i.addNat 3)

private noncomputable def boundCongruenceContext :
    Bootstrapping.Semiformula V ℒₒᵣ 6 :=
  (boundLeftTuple 0 ≐ boundRightTuple 0) ⋏
    ((boundLeftTuple 1 ≐ boundRightTuple 1) ⋏
      ((boundLeftTuple 2 ≐ boundRightTuple 2) ⋏ ⊤))

noncomputable def ternaryReplacementBody
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 6 :=
  boundCongruenceContext 🡒
    predicate.subst boundLeftTuple 🡒
      predicate.subst boundRightTuple

noncomputable def ternaryReplacementFormula
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰* ternaryReplacementBody predicate

private noncomputable def generalizationTuple :
    Fin 6 → Bootstrapping.Term V ℒₒᵣ :=
  ![Bootstrapping.Semiterm.fvar 0,
    Bootstrapping.Semiterm.fvar 1,
    Bootstrapping.Semiterm.fvar (1 + 1),
    Bootstrapping.Semiterm.fvar (1 + 1 + 1),
    Bootstrapping.Semiterm.fvar (1 + 1 + 1 + 1),
    Bootstrapping.Semiterm.fvar (1 + 1 + 1 + 1 + 1)]

/- `TProof` currently provides one- and two-variable generalization helpers.
This six-variable specialization keeps the bookkeeping below independent of
the (potentially nonstandard) formula being generalized. -/
private noncomputable def allSix
    {T : InternalTheory V ℒₒᵣ}
    {formula : Bootstrapping.Semiformula V ℒₒᵣ 6}
    (h : T ⊢!
      formula.shift.shift.shift.shift.shift.shift.subst
        generalizationTuple) :
    T ⊢! ∀⁰* formula := by
  simp only [allClosure_succ, allClosure_zero]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]
  apply TProof.all
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]
  apply TProof.all
  simpa [Bootstrapping.Semiformula.free, SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,
    generalizationTuple] using h

/-! ## The free-variable replacement chain -/

private noncomputable def shiftedPredicate
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  predicate.shift.shift.shift.shift.shift.shift

private noncomputable def leftTuple :
    Fin 3 → Bootstrapping.Term V ℒₒᵣ :=
  ![Bootstrapping.Semiterm.fvar 0,
    Bootstrapping.Semiterm.fvar 1,
    Bootstrapping.Semiterm.fvar (1 + 1)]

private noncomputable def rightTuple :
    Fin 3 → Bootstrapping.Term V ℒₒᵣ :=
  ![Bootstrapping.Semiterm.fvar (1 + 1 + 1),
    Bootstrapping.Semiterm.fvar (1 + 1 + 1 + 1),
    Bootstrapping.Semiterm.fvar (1 + 1 + 1 + 1 + 1)]

private noncomputable def afterFirstTuple :
    Fin 3 → Bootstrapping.Term V ℒₒᵣ :=
  ![rightTuple 0, leftTuple 1, leftTuple 2]

private noncomputable def afterSecondTuple :
    Fin 3 → Bootstrapping.Term V ℒₒᵣ :=
  ![rightTuple 0, rightTuple 1, leftTuple 2]

private noncomputable def freeCongruenceContext :
    Bootstrapping.Formula V ℒₒᵣ :=
  (leftTuple 0 ≐ rightTuple 0) ⋏
    ((leftTuple 1 ≐ rightTuple 1) ⋏
      ((leftTuple 2 ≐ rightTuple 2) ⋏ ⊤))

private noncomputable def freeReplacementFormula
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Formula V ℒₒᵣ :=
  freeCongruenceContext 🡒
    (shiftedPredicate predicate).subst leftTuple 🡒
      (shiftedPredicate predicate).subst rightTuple

private noncomputable def firstCoordinateFormula
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (shiftedPredicate predicate).subst
    ![Bootstrapping.Semiterm.bvar 0,
      (leftTuple 1).bShift, (leftTuple 2).bShift]

private noncomputable def secondCoordinateFormula
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (shiftedPredicate predicate).subst
    ![(rightTuple 0).bShift,
      Bootstrapping.Semiterm.bvar 0, (leftTuple 2).bShift]

private noncomputable def thirdCoordinateFormula
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (shiftedPredicate predicate).subst
    ![(rightTuple 0).bShift, (rightTuple 1).bShift,
      Bootstrapping.Semiterm.bvar 0]

private noncomputable def freeReplacementProof
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Peano.internalize V ⊢! freeReplacementFormula predicate := by
  have h₀ := LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.replace
    Peano (firstCoordinateFormula predicate) (leftTuple 0) (rightTuple 0)
  have h₁ := LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.replace
    Peano (secondCoordinateFormula predicate) (leftTuple 1) (rightTuple 1)
  have h₂ := LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.replace
    Peano (thirdCoordinateFormula predicate) (leftTuple 2) (rightTuple 2)
  have h₀' : Peano.internalize V ⊢
      (leftTuple 0 ≐ rightTuple 0) 🡒
        (shiftedPredicate predicate).subst leftTuple 🡒
          (shiftedPredicate predicate).subst afterFirstTuple := by
    simpa [firstCoordinateFormula,
      Bootstrapping.Semiformula.substs_substs,
      leftTuple, rightTuple, afterFirstTuple,
      Function.comp_def, Matrix.constant_eq_singleton] using h₀
  have h₁' : Peano.internalize V ⊢
      (leftTuple 1 ≐ rightTuple 1) 🡒
        (shiftedPredicate predicate).subst afterFirstTuple 🡒
          (shiftedPredicate predicate).subst afterSecondTuple := by
    simpa [secondCoordinateFormula,
      Bootstrapping.Semiformula.substs_substs,
      leftTuple, rightTuple, afterFirstTuple, afterSecondTuple,
      Function.comp_def, Matrix.constant_eq_singleton] using h₁
  have h₂' : Peano.internalize V ⊢
      (leftTuple 2 ≐ rightTuple 2) 🡒
        (shiftedPredicate predicate).subst afterSecondTuple 🡒
          (shiftedPredicate predicate).subst rightTuple := by
    simpa [thirdCoordinateFormula,
      Bootstrapping.Semiformula.substs_substs,
      leftTuple, rightTuple, afterSecondTuple,
      Function.comp_def, Matrix.constant_eq_singleton] using h₂
  unfold freeReplacementFormula freeCongruenceContext
  let context : Bootstrapping.Formula V ℒₒᵣ :=
    (leftTuple 0 ≐ rightTuple 0) ⋏
      ((leftTuple 1 ≐ rightTuple 1) ⋏
        ((leftTuple 2 ≐ rightTuple 2) ⋏ ⊤))
  let initial : Bootstrapping.Formula V ℒₒᵣ :=
    (shiftedPredicate predicate).subst leftTuple
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) :=
    [initial, context]
  suffices Γ ⊢[Peano.internalize V]!
      (shiftedPredicate predicate).subst rightTuple by
    apply Entailment.FiniteContext.deduct'
    apply Entailment.FiniteContext.deduct
    simpa [Γ, initial, context] using this
  have hinitial : Γ ⊢[Peano.internalize V]!
      (shiftedPredicate predicate).subst leftTuple := by
    simpa [Γ, initial] using
      (Entailment.FiniteContext.byAxm₀ :
        ((shiftedPredicate predicate).subst leftTuple ::
          context :: []) ⊢[Peano.internalize V]!
            (shiftedPredicate predicate).subst leftTuple)
  have hcontext : Γ ⊢[Peano.internalize V]! context := by
    simpa [Γ, initial] using
      (Entailment.FiniteContext.byAxm₁ :
        ((shiftedPredicate predicate).subst leftTuple ::
          context :: []) ⊢[Peano.internalize V]! context)
  have heq₀ : Γ ⊢[Peano.internalize V]!
      leftTuple 0 ≐ rightTuple 0 :=
    Entailment.K_left hcontext
  have htail₀ : Γ ⊢[Peano.internalize V]!
      (leftTuple 1 ≐ rightTuple 1) ⋏
        ((leftTuple 2 ≐ rightTuple 2) ⋏ ⊤) :=
    Entailment.K_right hcontext
  have heq₁ : Γ ⊢[Peano.internalize V]!
      leftTuple 1 ≐ rightTuple 1 :=
    Entailment.K_left htail₀
  have htail₁ : Γ ⊢[Peano.internalize V]!
      (leftTuple 2 ≐ rightTuple 2) ⋏ ⊤ :=
    Entailment.K_right htail₀
  have heq₂ : Γ ⊢[Peano.internalize V]!
      leftTuple 2 ≐ rightTuple 2 :=
    Entailment.K_left htail₁
  have hafterFirst : Γ ⊢[Peano.internalize V]!
      (shiftedPredicate predicate).subst afterFirstTuple :=
    (Entailment.FiniteContext.of (Γ := Γ) h₀'.get) ⨀ heq₀ ⨀ hinitial
  have hafterSecond : Γ ⊢[Peano.internalize V]!
      (shiftedPredicate predicate).subst afterSecondTuple :=
    (Entailment.FiniteContext.of (Γ := Γ) h₁'.get) ⨀ heq₁ ⨀ hafterFirst
  exact (Entailment.FiniteContext.of (Γ := Γ) h₂'.get) ⨀ heq₂ ⨀ hafterSecond

private theorem generalizationTuple_boundLeft (i : Fin 3) :
    (boundLeftTuple (V := V) i).shift.shift.shift.shift.shift.shift.subst
        (generalizationTuple (V := V)) = leftTuple (V := V) i := by
  cases i using Fin.cases with
  | zero =>
      simp only [boundLeftTuple, Bootstrapping.Semiterm.shift_bvar,
        Bootstrapping.Semiterm.substs_bvar, leftTuple]
      rw [show Fin.addCast 3 (0 : Fin 3) = (0 : Fin 6) by
        apply Fin.ext
        rfl]
      rfl
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          simp only [boundLeftTuple, Bootstrapping.Semiterm.shift_bvar,
            Bootstrapping.Semiterm.substs_bvar, leftTuple]
          rw [show Fin.addCast 3 (Fin.succ (0 : Fin 2)) =
              (1 : Fin 6) by
            apply Fin.ext
            rfl]
          rfl
      | succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          simp only [boundLeftTuple, Bootstrapping.Semiterm.shift_bvar,
            Bootstrapping.Semiterm.substs_bvar, leftTuple]
          rw [show Fin.addCast 3 ((Fin.succ (0 : Fin 1)).succ) =
              (2 : Fin 6) by
            apply Fin.ext
            rfl]
          rfl

private theorem generalizationTuple_boundRight (i : Fin 3) :
    (boundRightTuple (V := V) i).shift.shift.shift.shift.shift.shift.subst
        (generalizationTuple (V := V)) = rightTuple (V := V) i := by
  cases i using Fin.cases with
  | zero =>
      simp [boundRightTuple, generalizationTuple, rightTuple]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          simp [boundRightTuple, generalizationTuple, rightTuple]
      | succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          simp [boundRightTuple, generalizationTuple, rightTuple]

private theorem generalize_leftPredicate
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    (predicate.subst boundLeftTuple).shift.shift.shift.shift.shift.shift.subst
        generalizationTuple =
      (shiftedPredicate predicate).subst leftTuple := by
  simp only [Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  exact generalizationTuple_boundLeft i

private theorem generalize_rightPredicate
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    (predicate.subst boundRightTuple).shift.shift.shift.shift.shift.shift.subst
        generalizationTuple =
      (shiftedPredicate predicate).subst rightTuple := by
  simp only [Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  exact generalizationTuple_boundRight i

private theorem generalize_ternaryReplacementBody
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    (ternaryReplacementBody predicate).shift.shift.shift.shift.shift.shift.subst
        generalizationTuple =
      freeReplacementFormula predicate := by
  simp only [ternaryReplacementBody, boundCongruenceContext,
    freeReplacementFormula, freeCongruenceContext,
    Bootstrapping.Semiformula.shift_imp,
    Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.shift_verum,
    LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.shift_equals,
    Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,
    LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.substs_equals,
    Bootstrapping.Semiformula.substs_verum,
    generalizationTuple_boundLeft,
    generalizationTuple_boundRight,
    generalize_leftPredicate,
    generalize_rightPredicate]

noncomputable def ternaryReplacementProof
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Peano.internalize V ⊢! ternaryReplacementFormula predicate := by
  unfold ternaryReplacementFormula
  apply allSix
  rw [generalize_ternaryReplacementBody]
  exact freeReplacementProof predicate

/-! ## Specialization of source-language congruence premises -/

variable {count : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem translate_onePredicateCongruence
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    ModelCodedPredicateParameters.translateFormula predicate parameters
        (Rewriting.emb
          (ModelCodedPredicateEqualityQuotient.placeholderCongruenceSentence
            3 count)) =
      ternaryReplacementFormula predicate := by
  let sourceContext :
      Semiproposition (parameterTemplateLanguage 3 count) 6 :=
    Matrix.conj fun i : Fin 3 ↦
      .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
        ![(#(i.addCast 3) :
            ClosedSemiterm (parameterTemplateLanguage 3 count) 6),
          (#(i.addNat 3) :
            ClosedSemiterm (parameterTemplateLanguage 3 count) 6)]
  let sourceLeft :
      Semiproposition (parameterTemplateLanguage 3 count) 6 :=
    .rel (Sum.inr (Sum.inl
        ModelCodedPredicateTemplate.PlaceholderRel.predicate))
      (fun i ↦ (#(i.addCast 3) :
        ClosedSemiterm (parameterTemplateLanguage 3 count) 6))
  simp [ModelCodedPredicateEqualityQuotient.placeholderCongruenceSentence,
    ModelCodedPredicateEqualityQuotient.placeholderRelation,
    Theory.Eq.relExt,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    ternaryReplacementFormula, ternaryReplacementBody,
    boundCongruenceContext, boundLeftTuple, boundRightTuple,
    allClosure_succ, allClosure_zero, Rewriting.app_all,
    Function.comp_def, Matrix.conj, Matrix.vecTail]
  simp [ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    LO.FirstOrder.Semiformula.neg,
    Bootstrapping.Semiformula.imp_def]
  constructor
  · constructor
    · rfl
    · constructor <;> rfl
  · constructor
    · congr 1
    · congr 1

/-- PA proves the specialization of the one-placeholder congruence premise
for every model-coded ternary arithmetic formula. -/
noncomputable def translatedOnePredicateCongruenceProof
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    Peano.internalize V ⊢!
      ModelCodedPredicateParameters.translateFormula predicate parameters
        (Rewriting.emb
          (ModelCodedPredicateEqualityQuotient.placeholderCongruenceSentence
            3 count)) := by
  rw [translate_onePredicateCongruence]
  exact ternaryReplacementProof predicate

set_option backward.isDefEq.respectTransparency false in
theorem translate_twoPredicateFirstCongruence
    (predicate₀ predicate₁ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.firstPlaceholderCongruenceSentence
            3 3 count)) =
      ternaryReplacementFormula predicate₀ := by
  let sourceContext :
      Semiproposition (twoPredicateParameterLanguage 3 3 count) 6 :=
    Matrix.conj fun i : Fin 3 ↦
      .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
        ![(#(i.addCast 3) :
            ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6),
          (#(i.addNat 3) :
            ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6)]
  let sourceLeft :
      Semiproposition (twoPredicateParameterLanguage 3 3 count) 6 :=
    .rel (Sum.inr (Sum.inl
        ModelCodedPredicateTemplate.PlaceholderRel.predicate))
      (fun i ↦ (#(i.addCast 3) :
        ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6))
  simp [ModelCodedTwoPredicateEqualityQuotient.firstPlaceholderCongruenceSentence,
    ModelCodedTwoPredicateEqualityQuotient.firstPlaceholderRelation,
    Theory.Eq.relExt,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    ternaryReplacementFormula, ternaryReplacementBody,
    boundCongruenceContext, boundLeftTuple, boundRightTuple,
    allClosure_succ, allClosure_zero, Rewriting.app_all,
    Function.comp_def, Matrix.conj, Matrix.vecTail]
  simp [ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    LO.FirstOrder.Semiformula.neg,
    Bootstrapping.Semiformula.imp_def]
  constructor
  · constructor
    · rfl
    · constructor <;> rfl
  · constructor
    · congr 1
    · congr 1

set_option backward.isDefEq.respectTransparency false in
theorem translate_twoPredicateSecondCongruence
    (predicate₀ predicate₁ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.secondPlaceholderCongruenceSentence
            3 3 count)) =
      ternaryReplacementFormula predicate₁ := by
  let sourceContext :
      Semiproposition (twoPredicateParameterLanguage 3 3 count) 6 :=
    Matrix.conj fun i : Fin 3 ↦
      .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
        ![(#(i.addCast 3) :
            ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6),
          (#(i.addNat 3) :
            ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6)]
  let sourceLeft :
      Semiproposition (twoPredicateParameterLanguage 3 3 count) 6 :=
    .rel (Sum.inr (Sum.inr (Sum.inl
        ModelCodedPredicateTemplate.PlaceholderRel.predicate)))
      (fun i ↦ (#(i.addCast 3) :
        ClosedSemiterm (twoPredicateParameterLanguage 3 3 count) 6))
  simp [ModelCodedTwoPredicateEqualityQuotient.secondPlaceholderCongruenceSentence,
    ModelCodedTwoPredicateEqualityQuotient.secondPlaceholderRelation,
    Theory.Eq.relExt,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    ternaryReplacementFormula, ternaryReplacementBody,
    boundCongruenceContext, boundLeftTuple, boundRightTuple,
    allClosure_succ, allClosure_zero, Rewriting.app_all,
    Function.comp_def, Matrix.conj, Matrix.vecTail]
  simp [ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    LO.FirstOrder.Semiformula.neg,
    Bootstrapping.Semiformula.imp_def]
  constructor
  · constructor
    · rfl
    · constructor <;> rfl
  · constructor
    · congr 1
    · congr 1

theorem translate_twoPredicateCongruenceContext
    (predicate₀ predicate₁ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.placeholderCongruenceContext
            3 3 count)) =
      ternaryReplacementFormula predicate₀ ⋏
        ternaryReplacementFormula predicate₁ := by
  change
    ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.firstPlaceholderCongruenceSentence
            3 3 count)) ⋏
      ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.secondPlaceholderCongruenceSentence
            3 3 count)) = _
  rw [translate_twoPredicateFirstCongruence,
    translate_twoPredicateSecondCongruence]

/-- PA proves both specialized placeholder congruence laws as one conjunctive
context.  This is the proof consumed by two-predicate strong-step adapters. -/
noncomputable def translatedTwoPredicateCongruenceContextProof
    (predicate₀ predicate₁ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin count → V) :
    Peano.internalize V ⊢!
      ModelCodedTwoPredicateParameters.translateFormula
        predicate₀ predicate₁ parameters
        (Rewriting.emb
          (ModelCodedTwoPredicateEqualityQuotient.placeholderCongruenceContext
            3 3 count)) := by
  rw [translate_twoPredicateCongruenceContext]
  exact Entailment.K_intro
    (ternaryReplacementProof predicate₀)
    (ternaryReplacementProof predicate₁)

end LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
