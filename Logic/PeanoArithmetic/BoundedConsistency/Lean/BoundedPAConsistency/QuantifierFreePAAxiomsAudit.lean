import BoundedPAConsistency.QuantifierFreePAAxioms

/-!
# Kernel audit for the rank-zero PA axiom argument

These checks expose both boundaries of the result.  The model-theoretic
theorem is uniform over arbitrary, possibly nonstandard, models of PA and
arbitrary internal formula codes.  Completeness then turns that result into
an actual PA derivation of the externally fixed rank-zero consistency
sentence.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreePAAxiomsAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms

variable {V : Type*} [ORingStructure V] [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

#check not_isQuantifierFreeCode_indBodyVal
#check not_isQuantifierFreeCode_of_inductionUnivR
#check mem_pa_delta1Class_iff
#check mem_peanoMinus_delta1Class_iff
#check isQuantifierFreeCode_quote_absolute
#check qfValue_quote_absolute
#check qfValue_peanoMinus_axiom_nat
#check qfTrue_of_mem_pa_delta1Class
#check restrictedConsistent_pa_zero
#check pa_proves_restrictedConsistency_zero

example : RestrictedConsistent (V := V) Peano (0 : V) :=
  restrictedConsistent_pa_zero

example : Peano ⊢
    (paRestrictedConsistencySentence 0 : ArithmeticSentence) :=
  pa_proves_restrictedConsistency_zero

#print axioms not_isQuantifierFreeCode_of_inductionUnivR
#print axioms mem_peanoMinus_delta1Class_iff
#print axioms qfValue_peanoMinus_axiom_nat
#print axioms qfTrue_of_mem_pa_delta1Class
#print axioms restrictedConsistent_pa_zero
#print axioms pa_proves_restrictedConsistency_zero

end LeanProofs.BoundedPAConsistency.QuantifierFreePAAxiomsAudit
