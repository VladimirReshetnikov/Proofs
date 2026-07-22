import BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-!
# Audit: structural two-predicate source-context induction

The checks below expose both placeholder specializations, named-constant
specialization, exact context and predicate equations, both shift equations,
the zero/successor equations, and the final `PAInductionKernel` compiler.
-/

namespace LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernelAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

#check TwoPredicateSourceContextInductionKernel.Language
#check firstAtom
#check secondAtom
#check namedParameterTerm
#check zeroTerm
#check successorTerm
#check zeroSentence
#check successorSentence
#check Template
#check specializedContext
#check specializedPredicate
#check translateFormula_firstAtom
#check translateFormula_secondAtom
#check translateTerm_namedParameterTerm
#check translateTerm_lMap_arithmetic_emb
#check translateFormula_templateContext
#check translateFormula_templatePredicate
#check specializedContext_shift
#check specializedPredicate_shift
#check translateFormula_zeroSentence
#check translateFormula_successorSentence
#check Template.toPAInductionKernel

#print axioms translateFormula_firstAtom
#print axioms translateFormula_secondAtom
#print axioms translateTerm_namedParameterTerm
#print axioms translateTerm_lMap_arithmetic_emb
#print axioms translateFormula_templateContext
#print axioms translateFormula_templatePredicate
#print axioms specializedContext_shift
#print axioms specializedPredicate_shift
#print axioms translateFormula_zeroSentence
#print axioms translateFormula_successorSentence
#print axioms Template.toPAInductionKernel

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

noncomputable section

/-- The compiler's context is definitionally the translation of the complete
source context, not the interpretation of a nullary context atom. -/
example {arity₀ arity₁ count : ℕ}
    (template : Template arity₀ arity₁ count)
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V)
    (hS₀ : S₀.shift = S₀) (hS₁ : S₁.shift = S₁) :
    PAInductionKernel
      (translateFormula S₀ S₁ parameters
        (Rewriting.emb template.context)) :=
  template.toPAInductionKernel S₀ S₁ parameters hS₀ hS₁

/-- The exact translated context is available separately for rewriting in
downstream structural source proofs. -/
example {arity₀ arity₁ count : ℕ}
    (template : Template arity₀ arity₁ count)
    (S₀ : Bootstrapping.Semiformula V ℒₒᵣ arity₀)
    (S₁ : Bootstrapping.Semiformula V ℒₒᵣ arity₁)
    (parameters : Fin count → V) :
    specializedContext S₀ S₁ parameters template =
      translateFormula S₀ S₁ parameters
        (Rewriting.emb template.context) := rfl

end

end LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernelAudit
