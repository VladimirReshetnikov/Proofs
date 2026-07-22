import BoundedPAConsistency.ModelCodedPredicateTemplate

/-! Kernel audit for specialization of one model-coded predicate. -/

namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate

#check PlaceholderRel
#check placeholderLanguage
#check templateLanguage
#check translateTerm
#check translateFormula
#check translateTerm_shift
#check translateTerm_bShift
#check translateTerm_subst
#check translateFormula_neg
#check translateFormula_shift
#check translateFormula_subst
#check translateFormula_free
#check modelCodedPredicateTranslation
#check translateTerm_lMap_add₁
#check translateFormula_lMap_add₁
#check translateFormula_lMap_add₁_emb
#check templatePeano
#check modelCodedPredicateTheoryTranslation
#check compilePeanoTemplate
#check compilePeanoTemplate_isPAProof

#print axioms translateFormula_shift
#print axioms translateFormula_subst
#print axioms translateFormula_free
#print axioms translateFormula_lMap_add₁_emb
#print axioms modelCodedPredicateTheoryTranslation
#print axioms compilePeanoTemplate
#print axioms compilePeanoTemplate_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The public endpoint returns the represented PA proof judgment for an
arbitrary shift-fixed predicate, not merely a standard quotation. -/
example {arity : ℕ}
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S) {sigma : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! sigma) :
    Proof Peano (compilePeanoTemplate S hS d).val
      (translateFormula S (Rewriting.emb sigma)).val :=
  compilePeanoTemplate_isPAProof S hS d

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplateAudit
