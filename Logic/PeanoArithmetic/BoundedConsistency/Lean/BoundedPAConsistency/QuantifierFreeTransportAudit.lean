import BoundedPAConsistency.QuantifierFreeTransport

/-!
# Kernel audit for coded rank-zero semantic transport

These examples pin the transport API to arbitrary arithmetic-model elements,
rather than externally decoded syntax.  The axiom reports expose any use of
unchecked declarations in the internal structural-induction proofs.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTransportAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

#check qfValue_neg
#check qfTrue_neg_iff
#check qfFalse_neg_iff
#check qfValue_shift_of_isFreeTail
#check qfValue_shift_of_isFreeHead
#check qfTrue_shift_iff_of_isFreeTail
#check qfValue_subst_of_isSubstitutionBound
#check qfValue_subst_of_isSubstitutionEnvironment
#check qfTrue_subst_iff_of_isSubstitutionBound

example {bound free p : V} (hp : IsQuantifierFreeCode p) :
    qfValue bound free (neg ℒₒᵣ p) = bitNot (qfValue bound free p) :=
  qfValue_neg hp

example {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound shifted (shift ℒₒᵣ p) = qfValue bound free p :=
  qfValue_shift_of_isFreeTail hfree hp

example {bound free n w subBound p : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (hp : IsSemiformula ℒₒᵣ n p) :
    qfValue bound free (subst ℒₒᵣ w p) = qfValue subBound free p :=
  qfValue_subst_of_isSubstitutionBound hw hsub hp

#print axioms qfValue_neg
#print axioms qfTrue_neg_iff
#print axioms qfValue_shift_of_isFreeTail
#print axioms qfValue_shift_of_isFreeHead
#print axioms qfTrue_shift_iff_of_isFreeTail
#print axioms qfValue_subst_of_isSubstitutionBound
#print axioms qfValue_subst_of_isSubstitutionEnvironment
#print axioms qfTrue_subst_iff_of_isSubstitutionBound

end LeanProofs.BoundedPAConsistency.QuantifierFreeTransportAudit
