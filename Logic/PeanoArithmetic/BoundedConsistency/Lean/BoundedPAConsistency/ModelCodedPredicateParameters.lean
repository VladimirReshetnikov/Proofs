import BoundedPAConsistency.ModelCodedPredicateTemplate

/-!
# Proof templates with a model-coded predicate and named parameters

`ModelCodedPredicateTemplate` specializes one relation symbol to an arbitrary
typed arithmetic formula.  Uniform truth proofs also have to mention the
current (possibly nonstandard) hierarchy levels.  Treating those elements as
free variables makes the translated induction predicate carry parameters,
which in turn forces the full universal-closure branch of PA's coded
induction recognizer.

This module provides the more economical alternative used by the uniform
compiler.  A standard source language contains one predicate symbol and a
fixed finite family of nullary function symbols.  At specialization time the
nullary symbols become typed numerals for chosen elements of the ambient PA
model.  Consequently a source induction predicate with no ordinary free
variables translates to a shift-fixed model-coded predicate, even when its
named parameters and predicate code are nonstandard.

Only the syntax translation is established here.  The later certificate
module chooses the concrete parameter tuple and the finite proof templates.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate

/-! ## The source language -/

/-- Exactly `count` nullary function symbols and no symbols at other
arities. -/
inductive ParameterFunc (count : ℕ) : ℕ → Type
  | parameter (i : Fin count) : ParameterFunc count 0
  deriving DecidableEq

noncomputable instance (count k : ℕ) : Encodable (ParameterFunc count k) where
  encode f := by
    cases f with
    | parameter i => exact i.val
  decode x := by
    by_cases hk : k = 0
    · subst k
      exact if hx : x < count then some (.parameter ⟨x, hx⟩) else none
    · exact none
  encodek := by
    intro f
    cases f with
    | parameter i => simp [i.isLt]

/-- The parameter symbols as a relationally empty language. -/
@[reducible] def parameterLanguage (count : ℕ) : Language where
  Func := ParameterFunc count
  Rel := fun _ ↦ PEmpty

instance (count k : ℕ) : DecidableEq ((parameterLanguage count).Rel k) :=
  fun r _ ↦ nomatch r

instance (count k : ℕ) : Encodable ((parameterLanguage count).Rel k) :=
  IsEmpty.toEncodable

instance (count : ℕ) : (parameterLanguage count).DecidableEq where
  func := fun _ ↦ inferInstance
  rel := fun _ ↦ inferInstance

/-- Arithmetic together with one distinguished relation and finitely many
named constants.  The nesting leaves arithmetic as the left summand, which
makes lifted PA axioms easy to identify later. -/
@[reducible] def parameterTemplateLanguage (arity count : ℕ) : Language :=
  Language.add ℒₒᵣ
    (Language.add (placeholderLanguage arity) (parameterLanguage count))

instance (arity count : ℕ) :
    (parameterTemplateLanguage arity count).DecidableEq where
  func := fun k ↦ by
    change DecidableEq
      ((ℒₒᵣ).Func k ⊕
        ((placeholderLanguage arity).Func k ⊕
          (parameterLanguage count).Func k))
    infer_instance
  rel := fun k ↦ by
    change DecidableEq
      ((ℒₒᵣ).Rel k ⊕
        ((placeholderLanguage arity).Rel k ⊕
          (parameterLanguage count).Rel k))
    infer_instance

/-! ## Specialization into typed arithmetic syntax -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity count n m : ℕ}

/-- Arithmetic terms are retained, while a named source constant becomes
the typed numeral for the corresponding ambient-model parameter. -/
noncomputable def translateTerm
    (parameters : Fin count → V) :
    SyntacticSemiterm (parameterTemplateLanguage arity count) n →
      Bootstrapping.Semiterm V ℒₒᵣ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func (Sum.inl f) v =>
      .func f (fun i ↦ translateTerm parameters (v i))
  | .func (Sum.inr (Sum.inl f)) _ => nomatch f
  | .func (Sum.inr (Sum.inr (.parameter i))) _ =>
      Arithmetic.typedNumeral (parameters i)

/-- Replace the distinguished relation by substitution into `S`, interpret
the named constants by `parameters`, and retain all arithmetic and logical
constructors literally. -/
noncomputable def translateFormula
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) :
    {n : ℕ} →
      Semiproposition (parameterTemplateLanguage arity count) n →
      Bootstrapping.Semiformula V ℒₒᵣ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, .rel (Sum.inl r) v =>
      .rel r (fun i ↦ translateTerm parameters (v i))
  | _, .rel (Sum.inr (Sum.inl .predicate)) v =>
      S.subst (fun i ↦ translateTerm parameters (v i))
  | _, .rel (Sum.inr (Sum.inr r)) _ => nomatch r
  | _, .nrel (Sum.inl r) v =>
      .nrel r (fun i ↦ translateTerm parameters (v i))
  | _, .nrel (Sum.inr (Sum.inl .predicate)) v =>
      ∼(S.subst (fun i ↦ translateTerm parameters (v i)))
  | _, .nrel (Sum.inr (Sum.inr r)) _ => nomatch r
  | _, p ⋏ q => translateFormula S parameters p ⋏
      translateFormula S parameters q
  | _, p ⋎ q => translateFormula S parameters p ⋎
      translateFormula S parameters q
  | _, ∀⁰ p => ∀⁰ translateFormula S parameters p
  | _, ∃⁰ p => ∃⁰ translateFormula S parameters p

@[simp] theorem translateTerm_shift
    (parameters : Fin count → V)
    (t : SyntacticSemiterm (parameterTemplateLanguage arity count) n) :
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
        · cases f
          simp [translateTerm, Arithmetic.typedNumeral, Semiterm.shift]

@[simp] theorem translateTerm_bShift
    (parameters : Fin count → V)
    (t : SyntacticSemiterm (parameterTemplateLanguage arity count) n) :
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
        · cases f
          simp [translateTerm, Arithmetic.typedNumeral, Semiterm.bShift]

@[simp] theorem translateTerm_subst
    (parameters : Fin count → V)
    (w : Fin n →
      SyntacticSemiterm (parameterTemplateLanguage arity count) m)
    (t : SyntacticSemiterm (parameterTemplateLanguage arity count) n) :
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
        · cases f with
          | parameter i =>
              symm
              exact Arithmetic.subst_numeral
                (w := fun j ↦ translateTerm parameters (w j))
                (parameters i)

@[simp] theorem translateFormula_neg
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V)
    (p : Semiproposition (parameterTemplateLanguage arity count) n) :
    translateFormula S parameters (∼p) =
      ∼translateFormula S parameters p := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | hrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · rcases r with r | r
        · cases r; simp [translateFormula]
        · exact PEmpty.elim r
  | hnrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · rcases r with r | r
        · cases r; simp [translateFormula]
        · exact PEmpty.elim r
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_shift
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S)
    (p : Semiproposition (parameterTemplateLanguage arity count) n) :
    translateFormula S parameters (Rewriting.shift p) =
      (translateFormula S parameters p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.shift_substs, hS,
            Matrix.map, Function.comp_def]
        · exact PEmpty.elim r
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · rcases r with r | r
        · cases r
          simp [translateFormula, Semiformula.shift_substs, hS,
            Matrix.map, Function.comp_def]
        · exact PEmpty.elim r
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_subst
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V)
    (w : Fin n →
      SyntacticSemiterm (parameterTemplateLanguage arity count) m)
    (p : Semiproposition (parameterTemplateLanguage arity count) n) :
    translateFormula S parameters (Rew.subst w ▹ p) =
      (translateFormula S parameters p).subst
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
        · exact PEmpty.elim r
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
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
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [SemitermVec.q, translateTerm_bShift, Matrix.map]
  | hexs p hp =>
      simp only [Rewriting.app_exs, translateFormula,
        Semiformula.substs_ex]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [SemitermVec.q, translateTerm_bShift, Matrix.map]

@[simp] theorem translateFormula_free
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S)
    (p : Semiproposition (parameterTemplateLanguage arity count) 1) :
    translateFormula S parameters (Rewriting.free p) =
      (translateFormula S parameters p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst, translateFormula_shift S parameters hS]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- The translation record consumed by the generic typed proof compiler. -/
noncomputable def translation
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S) :
    TypedTemplateTranslation V
      (parameterTemplateLanguage arity count) ℒₒᵣ where
  term := translateTerm parameters
  formula := translateFormula S parameters
  formula_neg := translateFormula_neg S parameters
  formula_and := fun _ _ ↦ rfl
  formula_or := fun _ _ ↦ rfl
  formula_verum := rfl
  formula_all := fun _ ↦ rfl
  formula_exs := fun _ ↦ rfl
  formula_shift := translateFormula_shift S parameters hS
  formula_free := translateFormula_free S parameters hS
  formula_subst₁ := fun p t ↦ by
    simpa [Matrix.constant_eq_singleton] using
      translateFormula_subst S parameters ![t] p

/-! ## Compiling lifted PA proof templates

The source theory below contains only the ordinary PA axioms, lifted into the
larger language.  Its proofs may nevertheless use the predicate placeholder
and named constants in purely logical steps.  This is exactly what a finite
certificate-successor template needs: PA supplies the arithmetic facts, the
constants carry nonstandard model parameters, and the placeholder carries the
previous truth predicate.
-/

/-- The inclusion of arithmetic into the language with a predicate and named
constants. -/
noncomputable def arithmeticHom (arity count : ℕ) :
    ℒₒᵣ →ᵥ parameterTemplateLanguage arity count :=
  Language.Hom.add₁ ℒₒᵣ
    (Language.add (placeholderLanguage arity) (parameterLanguage count))

@[simp] theorem arithmeticHom_func (f : (ℒₒᵣ).Func k) :
    (arithmeticHom arity count).func f = Sum.inl f := rfl

@[simp] theorem arithmeticHom_rel (r : (ℒₒᵣ).Rel k) :
    (arithmeticHom arity count).rel r = Sum.inl r := rfl

/-- Arithmetic terms are translated to their ordinary typed quotations;
neither the predicate nor any named constant can occur in such a term. -/
@[simp] theorem translateTerm_lMap_arithmetic
    (parameters : Fin count → V)
    (t : SyntacticSemiterm ℒₒᵣ n) :
    translateTerm parameters (t.lMap (arithmeticHom arity count)) =
      (⌜t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih =>
      simp only [FirstOrder.Semiterm.lMap_func,
        arithmeticHom_func, translateTerm]
      apply Bootstrapping.Semiterm.ext
      simp [ih, Matrix.map, Function.comp_def]

/-- Arithmetic formulas are likewise unaffected by specialization. -/
@[simp] theorem translateFormula_lMap_arithmetic
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V)
    (p : ArithmeticSemiproposition n) :
    translateFormula S parameters (p.lMap (arithmeticHom arity count)) =
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
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V)
    (sigma : ArithmeticSentence) :
    translateFormula S parameters
        (Rewriting.emb (sigma.lMap (arithmeticHom arity count)) :
          Proposition (parameterTemplateLanguage arity count)) =
      (⌜sigma⌝ : Bootstrapping.Formula V ℒₒᵣ) := by
  rw [← FirstOrder.Semiformula.lMap_emb]
  simpa [Sentence.typed_quote_def] using
    translateFormula_lMap_arithmetic S parameters
      (Rewriting.emb sigma : ArithmeticProposition)

/-- PA lifted into the language with a predicate and named constants. -/
noncomputable def parameterTemplatePeano (arity count : ℕ) :
    Theory (parameterTemplateLanguage arity count) :=
  Theory.lMap (arithmeticHom arity count) Peano

/-- Source PA axioms specialize back to represented PA axioms.  Named
constants and the predicate remain available in the intervening logical
derivation, but are absent from every source-theory axiom. -/
noncomputable def theoryTranslation
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S) :
    TypedTheoryTemplateTranslation (parameterTemplatePeano arity count)
      (Peano.internalize V) where
  toTypedTemplateTranslation := translation S parameters hS
  axiom_mem := by
    intro sigma hsigma
    rcases hsigma with ⟨tau, htau, rfl⟩
    change translateFormula S parameters
      (Rewriting.emb (tau.lMap (arithmeticHom arity count)) :
        Proposition (parameterTemplateLanguage arity count)) ∈'
      (Peano.internalize V).theory
    rw [translateFormula_lMap_arithmetic_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff'' (T := Peano)).mpr htau

/-- Compile a fixed ordinary proof template after replacing its predicate and
named constants by arbitrary (possibly nonstandard) syntax and model values. -/
noncomputable def compilePeanoTemplate
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S)
    {sigma : Sentence (parameterTemplateLanguage arity count)}
    (d : parameterTemplatePeano arity count ⊢! sigma) :
    Peano.internalize V ⊢!
      translateFormula S parameters (Rewriting.emb sigma) :=
  (theoryTranslation S parameters hS).compileProof d

set_option backward.isDefEq.respectTransparency false in
theorem compilePeanoTemplate_isPAProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S)
    {sigma : Sentence (parameterTemplateLanguage arity count)}
    (d : parameterTemplatePeano arity count ⊢! sigma) :
    Proof Peano (compilePeanoTemplate S parameters hS d).val
      (translateFormula S parameters (Rewriting.emb sigma)).val := by
  simpa [compilePeanoTemplate, Proof] using
    (compilePeanoTemplate S parameters hS d).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
