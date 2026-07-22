import BoundedPAConsistency.TernaryCongruencePrototype

/-!
# Axiom audit for represented ternary congruence

The quotient-completeness bridge deliberately leaves opaque-relation
congruence as a source antecedent.  These declarations verify the separate
syntactic discharge step: after a model-coded ternary arithmetic formula is
inserted, PA itself proves the translated `relExt` sentence.
-/

namespace LeanProofs.BoundedPAConsistency.TernaryCongruencePrototypeAudit

open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype

#check ternaryReplacementBody
#check ternaryReplacementFormula
#check ternaryReplacementProof
#check translate_onePredicateCongruence
#check translatedOnePredicateCongruenceProof
#check translate_twoPredicateFirstCongruence
#check translate_twoPredicateSecondCongruence
#check translate_twoPredicateCongruenceContext
#check translatedTwoPredicateCongruenceContextProof

#print axioms ternaryReplacementProof
#print axioms translate_onePredicateCongruence
#print axioms translatedOnePredicateCongruenceProof
#print axioms translate_twoPredicateCongruenceContext
#print axioms translatedTwoPredicateCongruenceContextProof

end LeanProofs.BoundedPAConsistency.TernaryCongruencePrototypeAudit
