import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor

/-!
# Audit for the structural cross-level successor decomposition

This audit records the literal source-theory types.  In particular,
`SourceSuccessorCases.proveSuccessor` returns exactly the field required by
`TwoPredicateSourceContextInductionKernel.Template`, while
`sourceSuccessorOffDomainProof` certifies the maximal guard-only fragment
that needs no constructor-local truth laws.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorAudit

open LO FirstOrder
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor

#check sourceSuccessorSentence
#check sourceSuccessorBody
#check sourceSuccessorSigmaClause
#check sourceSuccessorPiClause
#check sourceSuccessorSigmaSentence
#check sourceSuccessorPiSentence
#check SourceSuccessorCases
#check SourceSuccessorCases.proveSuccessor
#check sourceSuccessorOffDomainSentence
#check sourceSuccessorOffDomainProof
#check sourceQuantifierFreeDomain
#check sourceQuantifierFreeTruth
#check sourceMissingQuantifierFreeAnchorBody
#check sourceMissingQuantifierFreeAnchor

noncomputable section

example : sourceSuccessorSentence =
    successorSentence sourcePriorCrossLevelContext
      sourceNextCrossLevelInvariant := by
  rfl

example (cases : SourceSuccessorCases) :
    twoPredicateParameterPeano 3 3 3 ⊢!
      successorSentence sourcePriorCrossLevelContext
        sourceNextCrossLevelInvariant := by
  exact cases.proveSuccessor

example : twoPredicateParameterPeano 3 3 3 ⊢!
    sourceSuccessorOffDomainSentence :=
  sourceSuccessorOffDomainProof

end

#print axioms sourceNextCrossLevelBody_eq_clauses
#print axioms sourceSuccessorBody_eq_clauses
#print axioms subst_sourceNextCrossLevelInvariant_successor
#print axioms subst_sourceNextSigmaInvariant_successor
#print axioms subst_sourceNextPiInvariant_successor
#print axioms SourceSuccessorCases.proveSuccessor
#print axioms sourceSuccessorOffDomainProof

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorAudit
