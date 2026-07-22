import BoundedPAConsistency.ModelCodedTwoPredicateParameters
import BoundedPAConsistency.ParameterizedInductionKernel
import BoundedPAConsistency.TruthCertificateProofCompiler

/-!
# Compiling two-predicate parameterized induction templates

The one-predicate parameterized kernel handles a nullary model-coded context.
Cross-level truth laws also refer to an independently chosen lower truth
predicate.  This module provides the corresponding reusable compiler for
source formulas containing a nullary context placeholder, a second
placeholder of arbitrary arity, and finitely many named constants.

Both predicates are interpreted by typed formula syntax in an arbitrary
model of I Sigma 1.  A source Template stores ordinary finite PA proofs of
its zero and successor cases.  Specialization compiles those proofs into the
exact premises required by PAInductionKernel; no axiom about either
placeholder is added to the source theory.
-/

namespace LeanProofs.BoundedPAConsistency.TwoPredicateParameterizedInductionKernel

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Fixed source syntax -/

/-- Arithmetic with a nullary context placeholder, an independently
interpreted lowerArity-ary predicate, and count named constants. -/
abbrev Language (lowerArity count : ℕ) :=
  twoPredicateParameterLanguage 0 lowerArity count

/-- The first, nullary relation placeholder.  It specializes to the
preceding master-certificate sentence. -/
def contextAtom (lowerArity count : ℕ) :
    Sentence (Language lowerArity count) :=
  .rel (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate)) ![]

/-- Apply the second placeholder to an arbitrary vector of closed source
terms.  This is the independently interpreted lower predicate. -/
def lowerAtom {lowerArity count n : ℕ}
    (terms : Fin lowerArity →
      ClosedSemiterm (Language lowerArity count) n) :
    Semisentence (Language lowerArity count) n :=
  .rel (Sum.inr (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate))) terms

/-- A named nullary source term.  Specialization replaces it by the typed
numeral of the corresponding ambient-model element. -/
def namedParameterTerm {lowerArity count n : ℕ} (i : Fin count) :
    ClosedSemiterm (Language lowerArity count) n :=
  .func (Sum.inr (Sum.inr (Sum.inr
    (ModelCodedPredicateParameters.ParameterFunc.parameter i)))) ![]

/-- Arithmetic zero lifted into the expanded source language. -/
noncomputable def zeroTerm (lowerArity count : ℕ) :
    ClosedSemiterm (Language lowerArity count) 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap
    (arithmeticHom 0 lowerArity count)

/-- The successor of the induction variable, lifted into the expanded
source language. -/
noncomputable def successorTerm (lowerArity count : ℕ) :
    ClosedSemiterm (Language lowerArity count) 1 :=
  ((‘#0 + 1’ : ArithmeticSemiterm Empty 1)).lMap
    (arithmeticHom 0 lowerArity count)

/-- The context-relative zero case of the unary source predicate. -/
noncomputable def zeroSentence {lowerArity count : ℕ}
    (predicate : Semisentence (Language lowerArity count) 1) :
    Sentence (Language lowerArity count) :=
  Arrow.arrow (contextAtom lowerArity count)
    (predicate/[zeroTerm lowerArity count])

/-- The context-relative successor case of the unary source predicate. -/
noncomputable def successorSentence {lowerArity count : ℕ}
    (predicate : Semisentence (Language lowerArity count) 1) :
    Sentence (Language lowerArity count) :=
  Arrow.arrow (contextAtom lowerArity count)
    (∀⁰ Arrow.arrow predicate
      (predicate/[successorTerm lowerArity count]))

/-- A standard finite pair of PA proof templates for induction.

The source theory contains lifted PA only.  Thus these proofs cannot appeal
to an extra axiom about either placeholder. -/
structure Template (lowerArity count : ℕ) where
  predicate : Semisentence (Language lowerArity count) 1
  proveZero : twoPredicateParameterPeano 0 lowerArity count ⊢!
    zeroSentence predicate
  proveSuccessor : twoPredicateParameterPeano 0 lowerArity count ⊢!
    successorSentence predicate

/-! ## Exact specialization in an arbitrary arithmetic model -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Specialize the unary source predicate by independently inserting the
context formula, lower predicate, and named model parameters. -/
noncomputable def specializedPredicate {lowerArity count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (template : Template lowerArity count) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula context lower parameters
    (Rewriting.emb template.predicate)

/-- The first placeholder specializes literally to context. -/
@[simp] theorem translateFormula_contextAtom {lowerArity count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V) :
    translateFormula context lower parameters
        (Rewriting.emb (contextAtom lowerArity count) :
          Proposition (Language lowerArity count)) =
      context := by
  simp [contextAtom, translateFormula]

/-- The second placeholder specializes literally to substitution into
lower; the two interpreted predicates therefore remain independent. -/
@[simp] theorem translateFormula_lowerAtom {lowerArity count n : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (terms : Fin lowerArity →
      ClosedSemiterm (Language lowerArity count) n) :
    translateFormula context lower parameters
        (Rewriting.emb (lowerAtom terms)) =
      lower.subst (fun i ↦
        translateTerm parameters (Rew.emb (terms i))) := by
  simp [lowerAtom, translateFormula, Function.comp_def]

/-- Named constants specialize to the corresponding typed numerals. -/
@[simp] theorem translateTerm_namedParameterTerm
    {lowerArity count n : ℕ}
    (parameters : Fin count → V) (i : Fin count) :
    translateTerm parameters
        (Rew.emb (namedParameterTerm (lowerArity := lowerArity)
          (n := n) i)) =
      Arithmetic.typedNumeral (parameters i) := by
  simp [namedParameterTerm, translateTerm]

/-- Lifted closed arithmetic terms specialize to their represented
quotations, aligning source terms exactly with PAInductionKernel. -/
@[simp] theorem translateTerm_lMap_arithmetic_emb
    {lowerArity count n : ℕ}
    (parameters : Fin count → V) (t : ClosedSemiterm ℒₒᵣ n) :
    translateTerm parameters
        (Rew.emb (t.lMap (arithmeticHom 0 lowerArity count)) :
          SyntacticSemiterm (Language lowerArity count) n) =
      (⌜(Rew.emb t : ArithmeticSemiterm ℕ n)⌝ :
        Bootstrapping.Semiterm V ℒₒᵣ n) := by
  simpa only [Rew.emb, Semiterm.lMap_map] using
    ModelCodedTwoPredicateParameters.translateTerm_lMap_arithmetic
      parameters (Rew.emb t)

/-- Closed specialization is shift-fixed when both inserted predicates are
shift-fixed.  Named constants become closed typed numerals and introduce no
additional side condition. -/
@[simp] theorem specializedPredicate_shift {lowerArity count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (template : Template lowerArity count)
    (hcontext : context.shift = context)
    (hlower : lower.shift = lower) :
    (specializedPredicate context lower parameters template).shift =
      specializedPredicate context lower parameters template := by
  unfold specializedPredicate
  rw [← translateFormula_shift context lower parameters hcontext hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Specialization of the source zero proof has exactly the target expected
by the represented PA induction kernel. -/
@[simp] theorem translateFormula_zeroSentence {lowerArity count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (template : Template lowerArity count) :
    translateFormula context lower parameters
        (Rewriting.emb (zeroSentence template.predicate) :
          Proposition (Language lowerArity count)) =
      Arrow.arrow context
        ((specializedPredicate context lower parameters template).subst
          ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝]) := by
  simp [zeroSentence, specializedPredicate, zeroTerm,
    Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · simp [contextAtom, Semiformula.neg, translateFormula]
  · congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl

/-- Specialization of the source successor proof has exactly the target
expected by the represented PA induction kernel. -/
@[simp] theorem translateFormula_successorSentence
    {lowerArity count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (template : Template lowerArity count) :
    translateFormula context lower parameters
        (Rewriting.emb (successorSentence template.predicate) :
          Proposition (Language lowerArity count)) =
      Arrow.arrow context
        (∀⁰ Arrow.arrow
          (specializedPredicate context lower parameters template)
          ((specializedPredicate context lower parameters template).subst
            ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) := by
  simp [successorSentence, specializedPredicate, successorTerm,
    Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · calc
      translateFormula context lower parameters
          (Semiformula.neg
            (Rewriting.emb (contextAtom lowerArity count))) =
          ∼translateFormula context lower parameters
            (Rewriting.emb (contextAtom lowerArity count)) :=
        translateFormula_neg context lower parameters
          (Rewriting.emb (contextAtom lowerArity count))
      _ = ∼context := congrArg (fun p ↦ ∼p)
        (translateFormula_contextAtom context lower parameters)
  · constructor
    · exact translateFormula_neg context lower parameters
        (Rewriting.emb template.predicate)
    · congr 1
      funext i
      simp

/-! ## Compilation to the existing induction kernel -/

/-- Compile the two fixed source derivations into a model-coded PA induction
kernel.

The finite source proofs are standard metatheoretic objects.  The context,
lower-predicate code, and named parameters may all be nonstandard elements
of the ambient arithmetic model. -/
noncomputable def Template.toPAInductionKernel
    {lowerArity count : ℕ}
    (template : Template lowerArity count)
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ lowerArity)
    (parameters : Fin count → V)
    (hcontext : context.shift = context)
    (hlower : lower.shift = lower) :
    PAInductionKernel context where
  predicate := specializedPredicate context lower parameters template
  shiftFixed := by
    have h := congrArg Bootstrapping.Semiformula.val
      (specializedPredicate_shift context lower parameters template
        hcontext hlower)
    simpa using h
  proveZero := by
    simpa only [translateFormula_zeroSentence] using
      compilePeanoTemplate context lower parameters hcontext hlower
        template.proveZero
  proveSuccessor := by
    simpa only [translateFormula_successorSentence] using
      compilePeanoTemplate context lower parameters hcontext hlower
        template.proveSuccessor

end LeanProofs.BoundedPAConsistency.TwoPredicateParameterizedInductionKernel
