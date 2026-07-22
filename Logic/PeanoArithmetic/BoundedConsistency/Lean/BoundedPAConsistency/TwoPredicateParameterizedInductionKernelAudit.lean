import BoundedPAConsistency.TwoPredicateParameterizedInductionKernel

/-!
# Audit: two-predicate parameterized induction kernels

These checks expose the source syntax, exact specialization equations, shift
theorem, and final PAInductionKernel compiler to Lean's axiom auditor.
-/

namespace LeanProofs.BoundedPAConsistency.TwoPredicateParameterizedInductionKernelAudit

open LeanProofs.BoundedPAConsistency.TwoPredicateParameterizedInductionKernel

#check Language
#check contextAtom
#check lowerAtom
#check namedParameterTerm
#check zeroTerm
#check successorTerm
#check zeroSentence
#check successorSentence
#check Template
#check specializedPredicate
#check translateFormula_contextAtom
#check translateFormula_lowerAtom
#check translateTerm_namedParameterTerm
#check translateTerm_lMap_arithmetic_emb
#check specializedPredicate_shift
#check translateFormula_zeroSentence
#check translateFormula_successorSentence
#check Template.toPAInductionKernel

#print axioms translateFormula_contextAtom
#print axioms translateFormula_lowerAtom
#print axioms translateTerm_namedParameterTerm
#print axioms translateTerm_lMap_arithmetic_emb
#print axioms specializedPredicate_shift
#print axioms translateFormula_zeroSentence
#print axioms translateFormula_successorSentence
#print axioms Template.toPAInductionKernel

end LeanProofs.BoundedPAConsistency.TwoPredicateParameterizedInductionKernelAudit
