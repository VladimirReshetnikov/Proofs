import BoundedPAConsistency.ModelCodedPredicateParameters

/-!
# Proof templates with two model-coded predicates and named parameters

Uniform truth-certificate induction simultaneously mentions two pieces of
arbitrary syntax from the ambient arithmetic model:

* a closed formula representing the preceding master certificate; and
* a ternary formula representing the preceding partial-truth predicate.

Neither formula can be decoded when its code is nonstandard.  This module
extends the finite-template compiler with two distinguished relation symbols
and any fixed number of named constants.  A standard source derivation is
translated constructor by constructor, replacing the two relations by typed
substitution into the supplied model-coded formulas.

The source theory still contains only PA, lifted through the arithmetic
inclusion.  Thus the extra predicates and constants may occur in logical
reasoning, but no unproved axiom about them is introduced.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## The source language -/

/-- Arithmetic, two independently arity-indexed relation placeholders, and
`count` nullary parameter symbols. -/
@[reducible] def twoPredicateParameterLanguage
    (arity₀ arity₁ count : ℕ) : Language :=
  Language.add ℒₒᵣ
    (Language.add (placeholderLanguage arity₀)
      (Language.add (placeholderLanguage arity₁)
        (parameterLanguage count)))

instance (arity₀ arity₁ count : ℕ) :
    (twoPredicateParameterLanguage arity₀ arity₁ count).DecidableEq where
  func := fun k ↦ by
    change DecidableEq
      ((ℒₒᵣ).Func k ⊕
        ((placeholderLanguage arity₀).Func k ⊕
          ((placeholderLanguage arity₁).Func k ⊕
            (parameterLanguage count).Func k)))
    infer_instance
  rel := fun k ↦ by
    change DecidableEq
      ((ℒₒᵣ).Rel k ⊕
        ((placeholderLanguage arity₀).Rel k ⊕
          ((placeholderLanguage arity₁).Rel k ⊕
            (parameterLanguage count).Rel k)))
    infer_instance

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity₀ arity₁ count n m : ℕ}

/-! ## Specialization into typed arithmetic syntax -/

/-- Arithmetic terms are retained and a named constant is interpreted by
the corresponding typed numeral.  Both placeholder languages are purely
relational. -/
noncomputable def translateTerm
    (parameters : Fin count → V) :
    SyntacticSemiterm
        (twoPredicateParameterLanguage arity₀ arity₁ count) n →
      Bootstrapping.Semiterm V ℒₒᵣ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func (Sum.inl f) v =>
      .func f (fun i ↦ translateTerm parameters (v i))
  | .func (Sum.inr (Sum.inl f)) _ => nomatch f
  | .func (Sum.inr (Sum.inr (Sum.inl f))) _ => nomatch f
  | .func (Sum.inr (Sum.inr (Sum.inr (.parameter i)))) _ =>
      Arithmetic.typedNumeral (parameters i)

/-- Replace the first and second relation placeholders independently while
retaining every arithmetic and logical constructor. -/
noncomputable def translateFormula
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V) :
    {n : ℕ} →
      Semiproposition
        (twoPredicateParameterLanguage arity₀ arity₁ count) n →
      Bootstrapping.Semiformula V ℒₒᵣ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, .rel (Sum.inl r) v =>
      .rel r (fun i ↦ translateTerm parameters (v i))
  | _, .rel (Sum.inr (Sum.inl .predicate)) v =>
      S₀.subst (fun i ↦ translateTerm parameters (v i))
  | _, .rel (Sum.inr (Sum.inr (Sum.inl .predicate))) v =>
      S₁.subst (fun i ↦ translateTerm parameters (v i))
  | _, .rel (Sum.inr (Sum.inr (Sum.inr r))) _ => nomatch r
  | _, .nrel (Sum.inl r) v =>
      .nrel r (fun i ↦ translateTerm parameters (v i))
  | _, .nrel (Sum.inr (Sum.inl .predicate)) v =>
      ∼(S₀.subst (fun i ↦ translateTerm parameters (v i)))
  | _, .nrel (Sum.inr (Sum.inr (Sum.inl .predicate))) v =>
      ∼(S₁.subst (fun i ↦ translateTerm parameters (v i)))
  | _, .nrel (Sum.inr (Sum.inr (Sum.inr r))) _ => nomatch r
  | _, p ⋏ q => translateFormula S₀ S₁ parameters p ⋏
      translateFormula S₀ S₁ parameters q
  | _, p ⋎ q => translateFormula S₀ S₁ parameters p ⋎
      translateFormula S₀ S₁ parameters q
  | _, ∀⁰ p => ∀⁰ translateFormula S₀ S₁ parameters p
  | _, ∃⁰ p => ∃⁰ translateFormula S₀ S₁ parameters p

/-! ## Compatibility with rewriting -/

@[simp] theorem translateTerm_shift
    (parameters : Fin count → V)
    (t : SyntacticSemiterm
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateTerm parameters (Rew.shift t) =
      (translateTerm parameters t).shift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · rcases f with f | f
        · exact PEmpty.elim f
        · rcases f with f | f
          · exact PEmpty.elim f
          · cases f
            simp [translateTerm, Arithmetic.typedNumeral, Semiterm.shift]

@[simp] theorem translateTerm_bShift
    (parameters : Fin count → V)
    (t : SyntacticSemiterm
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateTerm parameters (Rew.bShift t) =
      (translateTerm parameters t).bShift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · rcases f with f | f
        · exact PEmpty.elim f
        · rcases f with f | f
          · exact PEmpty.elim f
          · cases f
            simp [translateTerm, Arithmetic.typedNumeral, Semiterm.bShift]

@[simp] theorem translateTerm_subst
    (parameters : Fin count → V)
    (w : Fin n → SyntacticSemiterm
      (twoPredicateParameterLanguage arity₀ arity₁ count) m)
    (t : SyntacticSemiterm
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateTerm parameters (Rew.subst w t) =
      (translateTerm parameters t).subst
        (fun i ↦ translateTerm parameters (w i)) := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · rcases f with f | f
        · exact PEmpty.elim f
        · rcases f with f | f
          · exact PEmpty.elim f
          · cases f with
            | parameter i =>
                symm
                exact Arithmetic.subst_numeral
                  (w := fun j ↦ translateTerm parameters (w j))
                  (parameters i)

@[simp] theorem translateFormula_neg
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (p : Semiproposition
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateFormula S₀ S₁ parameters (∼p) =
      ∼translateFormula S₀ S₁ parameters p := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | hrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · rcases r with r | r
        · cases r; simp [translateFormula]
        · rcases r with r | r
          · cases r; simp [translateFormula]
          · exact PEmpty.elim r
  | hnrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · rcases r with r | r
        · cases r; simp [translateFormula]
        · rcases r with r | r
          · cases r; simp [translateFormula]
          · exact PEmpty.elim r
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_shift
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁)
    (p : Semiproposition
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateFormula S₀ S₁ parameters (Rewriting.shift p) =
      (translateFormula S₀ S₁ parameters p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.shift_substs, hS₀,
            Matrix.map, Function.comp_def]
        · rcases r with r | r
          · cases r
            simp [translateFormula, Semiformula.shift_substs, hS₁,
              Matrix.map, Function.comp_def]
          · exact PEmpty.elim r
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.shift_substs, hS₀,
            Matrix.map, Function.comp_def]
        · rcases r with r | r
          · cases r
            simp [translateFormula, Semiformula.shift_substs, hS₁,
              Matrix.map, Function.comp_def]
          · exact PEmpty.elim r
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_subst
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (w : Fin n → SyntacticSemiterm
      (twoPredicateParameterLanguage arity₀ arity₁ count) m)
    (p : Semiproposition
      (twoPredicateParameterLanguage arity₀ arity₁ count) n) :
    translateFormula S₀ S₁ parameters (Rew.subst w ▹ p) =
      (translateFormula S₀ S₁ parameters p).subst
        (fun i ↦ translateTerm parameters (w i)) := by
  induction p using FirstOrder.Semiformula.rec' generalizing m with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.substs_substs,
            translateTerm_subst, Matrix.map, Function.comp_def]
        · rcases r with r | r
          · cases r
            simp [translateFormula, Semiformula.substs_substs,
              translateTerm_subst, Matrix.map, Function.comp_def]
          · exact PEmpty.elim r
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.substs_substs,
            translateTerm_subst, Matrix.map, Function.comp_def]
        · rcases r with r | r
          · cases r
            simp [translateFormula, Semiformula.substs_substs,
              translateTerm_subst, Matrix.map, Function.comp_def]
          · exact PEmpty.elim r
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp =>
      simp only [Rewriting.app_all, translateFormula,
        Semiformula.substs_all]
      rw [Rew.q_subst, hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [SemitermVec.q, translateTerm_bShift, Matrix.map]
  | hexs p hp =>
      simp only [Rewriting.app_exs, translateFormula,
        Semiformula.substs_ex]
      rw [Rew.q_subst, hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [SemitermVec.q, translateTerm_bShift, Matrix.map]

@[simp] theorem translateFormula_free
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁)
    (p : Semiproposition
      (twoPredicateParameterLanguage arity₀ arity₁ count) 1) :
    translateFormula S₀ S₁ parameters (Rewriting.free p) =
      (translateFormula S₀ S₁ parameters p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst,
    translateFormula_shift S₀ S₁ parameters hS₀ hS₁]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-! ## The generic proof compiler instance -/

noncomputable def translation
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    TypedTemplateTranslation V
      (twoPredicateParameterLanguage arity₀ arity₁ count) ℒₒᵣ where
  term := translateTerm parameters
  formula := translateFormula S₀ S₁ parameters
  formula_neg := translateFormula_neg S₀ S₁ parameters
  formula_and := fun _ _ ↦ rfl
  formula_or := fun _ _ ↦ rfl
  formula_verum := rfl
  formula_all := fun _ ↦ rfl
  formula_exs := fun _ ↦ rfl
  formula_shift := translateFormula_shift S₀ S₁ parameters hS₀ hS₁
  formula_free := translateFormula_free S₀ S₁ parameters hS₀ hS₁
  formula_subst₁ := fun p t ↦ by
    simpa [Matrix.constant_eq_singleton] using
      translateFormula_subst S₀ S₁ parameters ![t] p

/-! ## Lifted arithmetic and PA templates -/

/-- Inclusion of arithmetic into the four-way sum language. -/
noncomputable def arithmeticHom (arity₀ arity₁ count : ℕ) :
    ℒₒᵣ →ᵥ twoPredicateParameterLanguage arity₀ arity₁ count :=
  Language.Hom.add₁ ℒₒᵣ
    (Language.add (placeholderLanguage arity₀)
      (Language.add (placeholderLanguage arity₁)
        (parameterLanguage count)))

@[simp] theorem arithmeticHom_func (f : (ℒₒᵣ).Func k) :
    (arithmeticHom arity₀ arity₁ count).func f = Sum.inl f := rfl

@[simp] theorem arithmeticHom_rel (r : (ℒₒᵣ).Rel k) :
    (arithmeticHom arity₀ arity₁ count).rel r = Sum.inl r := rfl

@[simp] theorem translateTerm_lMap_arithmetic
    (parameters : Fin count → V)
    (t : SyntacticSemiterm ℒₒᵣ n) :
    translateTerm parameters
        (t.lMap (arithmeticHom arity₀ arity₁ count)) =
      (⌜t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih =>
      simp only [FirstOrder.Semiterm.lMap_func,
        arithmeticHom_func, translateTerm]
      apply Bootstrapping.Semiterm.ext
      simp [ih, Matrix.map, Function.comp_def]

@[simp] theorem translateFormula_lMap_arithmetic
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (p : ArithmeticSemiproposition n) :
    translateFormula S₀ S₁ parameters
        (p.lMap (arithmeticHom arity₀ arity₁ count)) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      simp only [FirstOrder.Semiformula.lMap_rel,
        arithmeticHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_arithmetic, Matrix.map, Function.comp_def]
  | hnrel r v =>
      simp only [FirstOrder.Semiformula.lMap_nrel,
        arithmeticHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_arithmetic, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_lMap_arithmetic_emb
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V) (sigma : ArithmeticSentence) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb
          (sigma.lMap (arithmeticHom arity₀ arity₁ count)) :
          Proposition
            (twoPredicateParameterLanguage arity₀ arity₁ count)) =
      (⌜sigma⌝ : Bootstrapping.Formula V ℒₒᵣ) := by
  rw [← FirstOrder.Semiformula.lMap_emb]
  simpa [Sentence.typed_quote_def] using
    translateFormula_lMap_arithmetic S₀ S₁ parameters
      (Rewriting.emb sigma : ArithmeticProposition)

/-- PA lifted into the language containing both predicates and the named
constants. -/
noncomputable def twoPredicateParameterPeano
    (arity₀ arity₁ count : ℕ) :
    Theory (twoPredicateParameterLanguage arity₀ arity₁ count) :=
  Theory.lMap (arithmeticHom arity₀ arity₁ count) Peano

noncomputable def theoryTranslation
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    TypedTheoryTemplateTranslation
      (twoPredicateParameterPeano arity₀ arity₁ count)
      (Peano.internalize V) where
  toTypedTemplateTranslation :=
    translation S₀ S₁ parameters hS₀ hS₁
  axiom_mem := by
    intro sigma hsigma
    rcases hsigma with ⟨tau, htau, rfl⟩
    change translateFormula S₀ S₁ parameters
      (Rewriting.emb
        (tau.lMap (arithmeticHom arity₀ arity₁ count)) :
        Proposition
          (twoPredicateParameterLanguage arity₀ arity₁ count)) ∈'
      (Peano.internalize V).theory
    rw [translateFormula_lMap_arithmetic_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff'' (T := Peano)).mpr htau

/-- Compile one fixed proof after independently inserting both model-coded
predicates and the named model parameters. -/
noncomputable def compilePeanoTemplate
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁)
    {sigma : Sentence
      (twoPredicateParameterLanguage arity₀ arity₁ count)}
    (d : twoPredicateParameterPeano arity₀ arity₁ count ⊢! sigma) :
    Peano.internalize V ⊢!
      translateFormula S₀ S₁ parameters (Rewriting.emb sigma) :=
  (theoryTranslation S₀ S₁ parameters hS₀ hS₁).compileProof d

set_option backward.isDefEq.respectTransparency false in
theorem compilePeanoTemplate_isPAProof
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁)
    {sigma : Sentence
      (twoPredicateParameterLanguage arity₀ arity₁ count)}
    (d : twoPredicateParameterPeano arity₀ arity₁ count ⊢! sigma) :
    Proof Peano
      (compilePeanoTemplate S₀ S₁ parameters hS₀ hS₁ d).val
      (translateFormula S₀ S₁ parameters
        (Rewriting.emb sigma)).val := by
  simpa [compilePeanoTemplate, Proof] using
    (compilePeanoTemplate S₀ S₁ parameters hS₀ hS₁ d).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
