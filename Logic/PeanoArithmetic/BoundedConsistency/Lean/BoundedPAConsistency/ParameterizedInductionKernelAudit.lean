import BoundedPAConsistency.ParameterizedInductionKernel

/-!
# Audit for parameterized PA induction-template compilation

This file keeps the kernel-facing API visible and asks Lean to report every
axiom on which the final compiler depends.  In particular, the audit checks
the theorem that closed specialization is shift-fixed, the exact zero and
successor target equalities, and the assembled `PAInductionKernel`.
-/

namespace LeanProofs.BoundedPAConsistency.ParameterizedInductionKernelAudit

open LeanProofs.BoundedPAConsistency.ParameterizedInductionKernel

#check contextAtom
#check zeroTerm
#check successorTerm
#check zeroSentence
#check successorSentence
#check Template
#check specializedPredicate
#check translateTerm_lMap_arithmetic_emb
#check specializedPredicate_shift
#check translateFormula_zeroSentence
#check translateFormula_successorSentence
#check Template.toPAInductionKernel

#print axioms translateTerm_lMap_arithmetic_emb
#print axioms specializedPredicate_shift
#print axioms translateFormula_zeroSentence
#print axioms translateFormula_successorSentence
#print axioms Template.toPAInductionKernel

end LeanProofs.BoundedPAConsistency.ParameterizedInductionKernelAudit
