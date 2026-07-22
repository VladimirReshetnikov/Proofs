import BoundedPAConsistency.ModelCodedTwoPredicateParameters
import BoundedPAConsistency.TruthCertificateProofCompiler

/-!
# Induction templates with a structural two-predicate source context

`TwoPredicateParameterizedInductionKernel` interprets a distinguished
nullary atom as an opaque target context.  Some truth-law induction arguments
need more structure: their preceding law must occur as an ordinary source
formula, so a fixed proof can specialize, eliminate, and reassemble its
quantifiers and connectives before model-coded syntax is inserted.

This module provides that second interface.  A `Template` carries an
arbitrary closed source `context`, a unary source induction predicate, and
ordinary finite lifted-PA proofs of the context-relative zero and successor
cases.  Both relation placeholders may have arbitrary arities, and named
source constants specialize to arbitrary elements of the ambient arithmetic
model.  The result is a `PAInductionKernel` whose context is literally the
translation of the complete source context.
-/

namespace LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Source syntax -/

/-- Arithmetic with two independently interpreted relation placeholders and
`count` named nullary constants. -/
abbrev Language (arity₀ arity₁ count : ℕ) :=
  twoPredicateParameterLanguage arity₀ arity₁ count

/-- Apply the first relation placeholder to source terms. -/
def firstAtom {arity₀ arity₁ count n : ℕ}
    (terms : Fin arity₀ → ClosedSemiterm (Language arity₀ arity₁ count) n) :
    Semisentence (Language arity₀ arity₁ count) n :=
  .rel (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate)) terms

/-- Apply the second relation placeholder to source terms. -/
def secondAtom {arity₀ arity₁ count n : ℕ}
    (terms : Fin arity₁ → ClosedSemiterm (Language arity₀ arity₁ count) n) :
    Semisentence (Language arity₀ arity₁ count) n :=
  .rel (Sum.inr (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate))) terms

/-- A named source constant.  Specialization replaces it by the typed
numeral of the corresponding element of the ambient model. -/
def namedParameterTerm {arity₀ arity₁ count n : ℕ} (i : Fin count) :
    ClosedSemiterm (Language arity₀ arity₁ count) n :=
  .func (Sum.inr (Sum.inr (Sum.inr
    (ModelCodedPredicateParameters.ParameterFunc.parameter i)))) ![]

/-- Arithmetic zero lifted into the expanded source language. -/
noncomputable def zeroTerm (arity₀ arity₁ count : ℕ) :
    ClosedSemiterm (Language arity₀ arity₁ count) 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap
    (arithmeticHom arity₀ arity₁ count)

/-- The successor of the induction variable, lifted into the source
language. -/
noncomputable def successorTerm (arity₀ arity₁ count : ℕ) :
    ClosedSemiterm (Language arity₀ arity₁ count) 1 :=
  ((‘#0 + 1’ : ArithmeticSemiterm Empty 1)).lMap
    (arithmeticHom arity₀ arity₁ count)

/-- Context-relative base case for a unary source predicate. -/
noncomputable def zeroSentence {arity₀ arity₁ count : ℕ}
    (context : Sentence (Language arity₀ arity₁ count))
    (predicate : Semisentence (Language arity₀ arity₁ count) 1) :
    Sentence (Language arity₀ arity₁ count) :=
  Arrow.arrow context
    (predicate/[zeroTerm arity₀ arity₁ count])

/-- Context-relative successor case for a unary source predicate. -/
noncomputable def successorSentence {arity₀ arity₁ count : ℕ}
    (context : Sentence (Language arity₀ arity₁ count))
    (predicate : Semisentence (Language arity₀ arity₁ count) 1) :
    Sentence (Language arity₀ arity₁ count) :=
  Arrow.arrow context
    (∀⁰ Arrow.arrow predicate
      (predicate/[successorTerm arity₀ arity₁ count]))

/-- A fixed pair of lifted-PA induction premises under a complete source
context.

The source theory contains no axioms about either relation placeholder or
the named constants.  Every use of `context` in the two proofs is therefore
an ordinary antecedent that remains structurally visible to the proof. -/
structure Template (arity₀ arity₁ count : ℕ) where
  context : Sentence (Language arity₀ arity₁ count)
  predicate : Semisentence (Language arity₀ arity₁ count) 1
  proveZero : twoPredicateParameterPeano arity₀ arity₁ count ⊢!
    zeroSentence context predicate
  proveSuccessor : twoPredicateParameterPeano arity₀ arity₁ count ⊢!
    successorSentence context predicate

/-! ## Exact specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Translate the entire source context, retaining all of its logical
structure. -/
noncomputable def specializedContext {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula S₀ S₁ parameters
    (Rewriting.emb template.context)

/-- Translate the unary source induction predicate under the same
interpretation. -/
noncomputable def specializedPredicate {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula S₀ S₁ parameters
    (Rewriting.emb template.predicate)

/-- The first placeholder specializes independently to substitution into
`S₀`. -/
@[simp] theorem translateFormula_firstAtom
    {arity₀ arity₁ count n : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (terms : Fin arity₀ →
      ClosedSemiterm (Language arity₀ arity₁ count) n) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb (firstAtom terms)) =
      S₀.subst (fun i ↦ translateTerm parameters (Rew.emb (terms i))) := by
  simp [firstAtom, translateFormula, Function.comp_def]

/-- The second placeholder specializes independently to substitution into
`S₁`. -/
@[simp] theorem translateFormula_secondAtom
    {arity₀ arity₁ count n : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (terms : Fin arity₁ →
      ClosedSemiterm (Language arity₀ arity₁ count) n) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb (secondAtom terms)) =
      S₁.subst (fun i ↦ translateTerm parameters (Rew.emb (terms i))) := by
  simp [secondAtom, translateFormula, Function.comp_def]

/-- Named constants specialize exactly to typed model numerals. -/
@[simp] theorem translateTerm_namedParameterTerm
    {arity₀ arity₁ count n : ℕ}
    (parameters : Fin count → V) (i : Fin count) :
    translateTerm parameters
        (Rew.emb (namedParameterTerm (arity₀ := arity₀)
          (arity₁ := arity₁) (n := n) i)) =
      Arithmetic.typedNumeral (parameters i) := by
  simp [namedParameterTerm, translateTerm]

/-- Lifted arithmetic terms specialize exactly to their typed quotations. -/
@[simp] theorem translateTerm_lMap_arithmetic_emb
    {arity₀ arity₁ count n : ℕ}
    (parameters : Fin count → V) (t : ClosedSemiterm ℒₒᵣ n) :
    translateTerm parameters
        (Rew.emb (t.lMap (arithmeticHom arity₀ arity₁ count)) :
          SyntacticSemiterm (Language arity₀ arity₁ count) n) =
      (⌜(Rew.emb t : ArithmeticSemiterm ℕ n)⌝ :
        Bootstrapping.Semiterm V ℒₒᵣ n) := by
  simpa only [Rew.emb, Semiterm.lMap_map] using
    ModelCodedTwoPredicateParameters.translateTerm_lMap_arithmetic
      parameters (Rew.emb t)

/-- Exact context equation, kept as a named rewrite point for downstream
templates. -/
theorem translateFormula_templateContext
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb template.context) =
      specializedContext S₀ S₁ parameters template := rfl

/-- Exact unary-predicate equation under the same specialization. -/
theorem translateFormula_templatePredicate
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb template.predicate) =
      specializedPredicate S₀ S₁ parameters template := rfl

/-- A closed source context remains shift-fixed after both placeholders and
all named constants are specialized. -/
@[simp] theorem specializedContext_shift
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    (specializedContext S₀ S₁ parameters template).shift =
      specializedContext S₀ S₁ parameters template := by
  unfold specializedContext
  rw [← translateFormula_shift S₀ S₁ parameters hS₀ hS₁]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- The specialized unary induction predicate is also shift-fixed. -/
@[simp] theorem specializedPredicate_shift
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    (specializedPredicate S₀ S₁ parameters template).shift =
      specializedPredicate S₀ S₁ parameters template := by
  unfold specializedPredicate
  rw [← translateFormula_shift S₀ S₁ parameters hS₀ hS₁]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Specializing the source base proof produces exactly the zero premise of
the target `PAInductionKernel`. -/
@[simp] theorem translateFormula_zeroSentence
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb
          (zeroSentence template.context template.predicate) :
          Proposition (Language arity₀ arity₁ count)) =
      Arrow.arrow (specializedContext S₀ S₁ parameters template)
        ((specializedPredicate S₀ S₁ parameters template).subst
          ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝]) := by
  simp [zeroSentence, specializedContext, specializedPredicate, zeroTerm,
    Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · exact translateFormula_neg S₀ S₁ parameters
      (Rewriting.emb template.context)
  · congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl

/-- Specializing the source successor proof produces exactly the successor
premise of the target `PAInductionKernel`. -/
@[simp] theorem translateFormula_successorSentence
    {arity₀ arity₁ count : ℕ}
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (template : Template arity₀ arity₁ count) :
    translateFormula S₀ S₁ parameters
        (Rewriting.emb
          (successorSentence template.context template.predicate) :
          Proposition (Language arity₀ arity₁ count)) =
      Arrow.arrow (specializedContext S₀ S₁ parameters template)
        (∀⁰ Arrow.arrow
          (specializedPredicate S₀ S₁ parameters template)
          ((specializedPredicate S₀ S₁ parameters template).subst
            ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) := by
  simp [successorSentence, specializedContext, specializedPredicate,
    successorTerm, Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · exact translateFormula_neg S₀ S₁ parameters
      (Rewriting.emb template.context)
  · constructor
    · exact translateFormula_neg S₀ S₁ parameters
        (Rewriting.emb template.predicate)
    · congr 1
      funext i
      simp

/-! ## Compilation -/

/-- Compile a structural source-context template into the represented PA
induction interface.

The kernel context is exactly the translation of `template.context`; no
opaque atom or additional source-theory axiom is introduced. -/
noncomputable def Template.toPAInductionKernel
    {arity₀ arity₁ count : ℕ}
    (template : Template arity₀ arity₁ count)
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    PAInductionKernel
      (translateFormula S₀ S₁ parameters
        (Rewriting.emb template.context)) where
  predicate := specializedPredicate S₀ S₁ parameters template
  shiftFixed := by
    have h := congrArg Bootstrapping.Semiformula.val
      (specializedPredicate_shift S₀ S₁ parameters template hS₀ hS₁)
    simpa using h
  proveZero := by
    simpa only [translateFormula_zeroSentence,
      translateFormula_templateContext] using
      compilePeanoTemplate S₀ S₁ parameters hS₀ hS₁
        template.proveZero
  proveSuccessor := by
    simpa only [translateFormula_successorSentence,
      translateFormula_templateContext] using
      compilePeanoTemplate S₀ S₁ parameters hS₀ hS₁
        template.proveSuccessor

end LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
