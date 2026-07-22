import BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient

/-!
# Axiom audit for two-predicate equality completion

This file intentionally contains no new proof.  It fixes the public API and
asks Lean to report the transitive axiom dependencies of the model theorem
and the quotient-completeness bridge.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotientAudit

open LO FirstOrder
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient

#check firstPlaceholderRelation
#check secondPlaceholderRelation
#check firstPlaceholderCongruenceSentence
#check secondPlaceholderCongruenceSentence
#check placeholderCongruenceContext
#check models_fullEquality
#check complete_underPlaceholderCongruence

#print axioms models_fullEquality
#print axioms complete_underPlaceholderCongruence

end LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotientAudit
