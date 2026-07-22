import BoundedPAConsistency.ModelCodedPredicateParameters

/-!
Kernel-facing audit for proof templates carrying named model parameters.

The endpoint checked below is deliberately stated for an arbitrary tuple of
ambient-model elements.  In particular, neither the tuple nor the specialized
predicate is assumed to be the quotation of standard Lean syntax.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateParametersAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

#check ParameterFunc
#check parameterLanguage
#check parameterTemplateLanguage
#check translateTerm
#check translateFormula
#check translateTerm_shift
#check translateTerm_bShift
#check translateTerm_subst
#check translateFormula_neg
#check translateFormula_shift
#check translateFormula_subst
#check translateFormula_free
#check translation
#check arithmeticHom
#check translateTerm_lMap_arithmetic
#check translateFormula_lMap_arithmetic
#check translateFormula_lMap_arithmetic_emb
#check parameterTemplatePeano
#check theoryTranslation
#check compilePeanoTemplate
#check compilePeanoTemplate_isPAProof

#print axioms translateFormula_shift
#print axioms translateFormula_subst
#print axioms translateFormula_free
#print axioms translateFormula_lMap_arithmetic_emb
#print axioms theoryTranslation
#print axioms compilePeanoTemplate
#print axioms compilePeanoTemplate_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The public compiler produces a represented PA proof after interpreting
both a model-coded predicate and arbitrary named model elements. -/
example {arity count : ℕ}
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (parameters : Fin count → V) (hS : S.shift = S)
    {sigma : Sentence (parameterTemplateLanguage arity count)}
    (d : parameterTemplatePeano arity count ⊢! sigma) :
    Proof Peano (compilePeanoTemplate S parameters hS d).val
      (translateFormula S parameters (Rewriting.emb sigma)).val :=
  compilePeanoTemplate_isPAProof S parameters hS d

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateParametersAudit
