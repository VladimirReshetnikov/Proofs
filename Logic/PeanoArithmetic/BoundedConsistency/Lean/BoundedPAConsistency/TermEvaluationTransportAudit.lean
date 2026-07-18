import BoundedPAConsistency.TermEvaluationTransport

/-!
# Kernel audit for coded-term semantic transport

The examples pin down the nonstandard-model API and the axiom reports make
any accidental use of an unchecked declaration visible in build logs.
-/

namespace LeanProofs.BoundedPAConsistency.TermEvaluationTransportAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

#check exists_isFreeHead
#check exists_isFreeTail
#check termValue_termShift_of_isFreeTail
#check termValue_termShift_of_isFreeHead
#check termValues_termShiftVec_of_isFreeTail
#check exists_isSubstitutionEnvironment
#check termValue_termSubst_of_isSubstitutionBound
#check termValue_termSubst_of_isSubstitutionEnvironment
#check termValues_termSubstVec_of_isSubstitutionBound

-- These types deliberately quantify over model elements, rather than over
-- externally decoded Lean syntax.
example {bound shifted free t : V}
    (hfree : IsFreeTail shifted free)
    (ht : IsUTerm ℒₒᵣ t) :
    termValue bound shifted (termShift ℒₒᵣ t) =
      termValue bound free t :=
  termValue_termShift_of_isFreeTail hfree ht

-- This is the assignment orientation used when validating a shift rule: an
-- arbitrary genuine target assignment supplies an unshifted premise tail.
example {shifted : V} (hshifted : Seq shifted) :
    ∃ free, Seq free ∧ lh free = lh shifted - 1 ∧ IsFreeTail shifted free :=
  exists_isFreeTail hshifted

example {bound free n w subBound t : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termValue bound free (termSubst ℒₒᵣ w t) =
      termValue subBound free t :=
  termValue_termSubst_of_isSubstitutionBound hw hsub ht

#print axioms exists_isFreeHead
#print axioms exists_isFreeTail
#print axioms termValue_termShift_of_isFreeTail
#print axioms termValues_termShiftVec_of_isFreeTail
#print axioms exists_isSubstitutionEnvironment
#print axioms termValue_termSubst_of_isSubstitutionBound
#print axioms termValues_termSubstVec_of_isSubstitutionBound

end LeanProofs.BoundedPAConsistency.TermEvaluationTransportAudit
