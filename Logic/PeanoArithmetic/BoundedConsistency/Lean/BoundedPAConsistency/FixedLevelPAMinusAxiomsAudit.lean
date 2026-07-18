import BoundedPAConsistency.FixedLevelPAMinusAxioms

/-!
# Axiom audit for fixed-level Peano-minus axioms

These checks keep the quotation-adequacy bridge and its finite-recognizer
corollary visible to Lean's kernel audit.  In particular, no semantic bridge
is introduced as an axiom.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxiomsAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms

#check termValue_quote_iff_val
#check quotedBoundAssignment_seqCons
#check quantifierBoundedCode_quote_iff_standard
#check sigmaTrue_succ_quote_iff_eval
#check sigmaTrue_succ_sentence_quote_iff_models
#check sigmaTrue_succ_of_mem_peanoMinus_delta1Class
#check sigmaTrue_succ_of_mem_peanoMinus_delta1Class_of_seq

#print axioms termValue_quote_iff_val
#print axioms quotedBoundAssignment_seqCons
#print axioms quantifierBoundedCode_quote_iff_standard
#print axioms sigmaTrue_succ_quote_iff_eval
#print axioms sigmaTrue_succ_sentence_quote_iff_models
#print axioms sigmaTrue_succ_of_mem_peanoMinus_delta1Class
#print axioms sigmaTrue_succ_of_mem_peanoMinus_delta1Class_of_seq

end LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxiomsAudit
