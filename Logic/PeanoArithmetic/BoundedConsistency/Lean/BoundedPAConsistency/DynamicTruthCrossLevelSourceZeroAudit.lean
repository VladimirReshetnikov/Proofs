import BoundedPAConsistency.DynamicTruthCrossLevelSourceZero

/-!
# Audit: zero case for structural cross-level source induction

These checks expose the elementary arithmetic coding theorem, its transport
to the expanded source language, and the exact derivation expected by the
zero field of `TwoPredicateSourceContextInductionKernel.Template`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceZeroAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceZero

#check arithmeticZeroDomainsSentence
#check arithmeticZeroDomainsProof
#check liftedArithmeticZeroDomainsProof
#check sourceZeroSentence
#check sourceZeroProof

#print axioms arithmeticZeroDomainsProof
#print axioms liftedArithmeticZeroDomainsProof
#print axioms sourceZeroProof

noncomputable section

/-- The endpoint has literally the type of the outstanding structural
template's base-case field. -/
example : twoPredicateParameterPeano 3 3 3 ⊢!
    zeroSentence sourcePriorCrossLevelContext
      sourceNextCrossLevelInvariant := by
  simpa [sourceZeroSentence] using sourceZeroProof

end

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceZeroAudit
