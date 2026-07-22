import BoundedPAConsistency.ModelCodedPredicateParameters
import BoundedPAConsistency.TruthCertificateProofCompiler

/-!
# Compiling closed parameterized induction templates

`ModelCodedPredicateParameters` turns fixed proofs in an expanded standard
language into represented PA proofs after its nullary symbols are interpreted
by arbitrary elements of a PA model.  This module packages the particular
source formulas required by `PAInductionKernel`.

The sole predicate placeholder is nullary and denotes the preceding master
certificate.  The induction predicate itself is a closed source
semisentence; it may mention any of the named constants.  Consequently its
specialization can depend on nonstandard levels and syntax codes while still
being fixed by free-variable shift, as required by PA's represented induction
axiom recognizer.
-/

namespace LeanProofs.BoundedPAConsistency.ParameterizedInductionKernel

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-- The expanded source language, with a nullary context placeholder. -/
abbrev Language (count : ℕ) := parameterTemplateLanguage 0 count

/-- The nullary atom which becomes the preceding master certificate. -/
def contextAtom (count : ℕ) : Sentence (Language count) :=
  .rel (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate)) ![]

/-- The arithmetic zero term lifted into the expanded language. -/
noncomputable def zeroTerm (count : ℕ) : ClosedSemiterm (Language count) 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap (arithmeticHom 0 count)

/-- The successor of the induction variable, lifted into the expanded
language. -/
noncomputable def successorTerm (count : ℕ) :
    ClosedSemiterm (Language count) 1 :=
  ((‘#0 + 1’ : ArithmeticSemiterm Empty 1)).lMap
    (arithmeticHom 0 count)

/-- The context-relative zero case of a closed unary predicate. -/
noncomputable def zeroSentence {count : ℕ}
    (predicate : Semisentence (Language count) 1) :
    Sentence (Language count) :=
  contextAtom count 🡒 predicate/[zeroTerm count]

/-- The context-relative successor case of a closed unary predicate. -/
noncomputable def successorSentence {count : ℕ}
    (predicate : Semisentence (Language count) 1) :
    Sentence (Language count) :=
  contextAtom count 🡒
    ∀⁰ (predicate 🡒 predicate/[successorTerm count])

/-- A fixed standard proof template for the two premises of induction. -/
structure Template (count : ℕ) where
  predicate : Semisentence (Language count) 1
  proveZero : parameterTemplatePeano 0 count ⊢! zeroSentence predicate
  proveSuccessor :
    parameterTemplatePeano 0 count ⊢! successorSentence predicate

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Specialize the closed source predicate at a model-coded context and a
tuple of named model parameters. -/
noncomputable def specializedPredicate {count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V) (template : Template count) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula context parameters (Rewriting.emb template.predicate)

@[simp] theorem translateFormula_contextAtom {count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V) :
    translateFormula context parameters
        (Rewriting.emb (contextAtom count) : Proposition (Language count)) =
      context := by
  simp [contextAtom, translateFormula]

/-- A lifted closed arithmetic term specializes to the ordinary represented
quotation of that term.  This small commuting lemma is what makes the source
zero and successor terms line up definitionally with `PAInductionKernel`. -/
@[simp] theorem translateTerm_lMap_arithmetic_emb {count n : ℕ}
    (parameters : Fin count → V) (t : ClosedSemiterm ℒₒᵣ n) :
    translateTerm parameters
        (Rew.emb (t.lMap (arithmeticHom 0 count)) :
          SyntacticSemiterm (Language count) n) =
      (⌜(Rew.emb t : ArithmeticSemiterm ℕ n)⌝ :
        Bootstrapping.Semiterm V ℒₒᵣ n) := by
  simpa only [Rew.emb, Semiterm.lMap_map] using
    translateTerm_lMap_arithmetic parameters (Rew.emb t)

/-- Closed source predicates remain closed after their named constants and
context atom are specialized. -/
@[simp] theorem specializedPredicate_shift {count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V) (template : Template count)
    (hcontext : context.shift = context) :
    (specializedPredicate context parameters template).shift =
      specializedPredicate context parameters template := by
  unfold specializedPredicate
  rw [← translateFormula_shift context parameters hcontext]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Specializing the source zero premise produces exactly the represented
zero premise expected by the induction kernel. -/
@[simp] theorem translateFormula_zeroSentence {count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V) (template : Template count) :
    translateFormula context parameters
        (Rewriting.emb (zeroSentence template.predicate) :
          Proposition (Language count)) =
      context 🡒
        (specializedPredicate context parameters template).subst
          ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] := by
  simp [zeroSentence, specializedPredicate, zeroTerm,
    Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · simp [contextAtom, Semiformula.neg, translateFormula]
  · congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl

/-- Specializing the source successor premise produces exactly the
represented successor premise expected by the induction kernel. -/
@[simp] theorem translateFormula_successorSentence {count : ℕ}
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V) (template : Template count) :
    translateFormula context parameters
        (Rewriting.emb (successorSentence template.predicate) :
          Proposition (Language count)) =
      context 🡒
        ∀⁰ ((specializedPredicate context parameters template) 🡒
          (specializedPredicate context parameters template).subst
            ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝]) := by
  simp [successorSentence, specializedPredicate, successorTerm,
    Semiformula.imp_def, translateFormula,
    Rewriting.emb_subst_eq_subst_coe₁]
  constructor
  · calc
      translateFormula context parameters
          (Semiformula.neg (Rewriting.emb (contextAtom count))) =
          ∼translateFormula context parameters
            (Rewriting.emb (contextAtom count)) :=
        translateFormula_neg context parameters
          (Rewriting.emb (contextAtom count))
      _ = ∼context := congrArg (fun p ↦ ∼p)
        (translateFormula_contextAtom context parameters)
  · constructor
    · exact translateFormula_neg context parameters
        (Rewriting.emb template.predicate)
    · congr 1
      funext i
      simp

/-- Compile the two fixed source derivations into a model-coded induction
kernel.  The source derivations are standard finite objects, while `context`
and `parameters` may be arbitrary elements of a nonstandard PA model. -/
noncomputable def Template.toPAInductionKernel {count : ℕ}
    (template : Template count)
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (parameters : Fin count → V)
    (hcontext : context.shift = context) :
    PAInductionKernel context where
  predicate := specializedPredicate context parameters template
  shiftFixed := by
    have h := congrArg Bootstrapping.Semiformula.val
      (specializedPredicate_shift context parameters template hcontext)
    simpa using h
  proveZero := by
    simpa only [translateFormula_zeroSentence] using
      compilePeanoTemplate context parameters hcontext template.proveZero
  proveSuccessor := by
    simpa only [translateFormula_successorSentence] using
      compilePeanoTemplate context parameters hcontext template.proveSuccessor

end LeanProofs.BoundedPAConsistency.ParameterizedInductionKernel
