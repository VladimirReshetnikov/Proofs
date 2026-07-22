import BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor

/-! Assumption and type audit for the substitution structural endpoint. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessorAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor

#check nextSubstitutionInvariantPredicate
#check all_nextSubstitutionInvariantPredicate_eq_orbit
#check nextSubstitutionInvariantPredicate_shift
#check nextSubstitutionInvariantPredicate_shift_val
#check kernelOfStructuralUniversalProof
#check compileKernelOfStructuralUniversalProof

#print axioms all_nextSubstitutionInvariantPredicate_eq_orbit
#print axioms nextSubstitutionInvariantPredicate_shift
#print axioms nextSubstitutionInvariantPredicate_shift_val
#print axioms kernelOfStructuralUniversalProof
#print axioms compileKernelOfStructuralUniversalProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The public splice has exactly the next positive substitution field as its
target. -/
noncomputable example (context : Bootstrapping.Formula V ℒₒᵣ) (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextSubstitutionInvariantPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
    Peano.internalize V ⊢!
      orbitSuccessorSubstitutionInvariantFormula n :=
  compileKernelOfStructuralUniversalProof context n proof hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessorAudit
