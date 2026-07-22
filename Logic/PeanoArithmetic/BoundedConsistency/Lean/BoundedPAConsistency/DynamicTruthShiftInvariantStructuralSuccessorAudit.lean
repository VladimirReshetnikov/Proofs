import BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor

/-! Assumption and type audit for the dynamic shift structural endpoint. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessorAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor

#check nextShiftInvariantPredicate
#check all_nextShiftInvariantPredicate_eq_orbit
#check nextShiftInvariantPredicate_shift
#check nextShiftInvariantPredicate_shift_val
#check kernelOfStructuralUniversalProof
#check compileKernelOfStructuralUniversalProof

#print axioms all_nextShiftInvariantPredicate_eq_orbit
#print axioms nextShiftInvariantPredicate_shift
#print axioms nextShiftInvariantPredicate_shift_val
#print axioms kernelOfStructuralUniversalProof
#print axioms compileKernelOfStructuralUniversalProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The public splice has exactly the next positive shift field as target. -/
noncomputable example (context : Bootstrapping.Formula V ℒₒᵣ) (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextShiftInvariantPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
    Peano.internalize V ⊢!
      orbitSuccessorShiftInvariantFormula (n + 1) :=
  compileKernelOfStructuralUniversalProof context n proof hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessorAudit
