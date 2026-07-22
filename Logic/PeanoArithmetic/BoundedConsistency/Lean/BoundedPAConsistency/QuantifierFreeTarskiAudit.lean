import BoundedPAConsistency.QuantifierFreeTarski

/-!
# Kernel audit for the rank-zero Tarski interface

The structural characterization is the important nonstandard-code theorem:
although hierarchy level is defined as the lesser of two polarity ranks, a
well-formed formula has level zero only when both ranks vanish.  The remaining
checks expose the resulting Boolean and atomic Tarski clauses.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTarskiAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

#check quantifierGroupsCode_eq_zero_iff
#check isQuantifierFreeCode_iff
#check isQuantifierFreeCode_and_iff
#check isQuantifierFreeCode_or_iff
#check not_isQuantifierFreeCode_all
#check not_isQuantifierFreeCode_exs
#check qfValue_and_eq_zero_iff
#check qfValue_or_eq_zero_iff
#check qfTrue_and_iff
#check qfFalse_and_iff
#check qfTrue_or_iff
#check qfFalse_or_iff
#check qfTrue_eq_atom_iff
#check qfFalse_nlt_atom_iff

#print axioms quantifierGroupsCode_eq_zero_iff
#print axioms isQuantifierFreeCode_iff
#print axioms isQuantifierFreeCode_and_iff
#print axioms qfValue_and_eq_zero_iff
#print axioms qfTrue_and_iff
#print axioms qfFalse_and_iff
#print axioms qfTrue_eq_atom_iff
#print axioms qfFalse_nlt_atom_iff

end LeanProofs.BoundedPAConsistency.QuantifierFreeTarskiAudit
