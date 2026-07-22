import BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor

/-! Assumption and type audit for the PA-axiom-soundness structural endpoint. -/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessorAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor

#check nextAxiomSoundnessPredicate
#check all_nextAxiomSoundnessPredicate_eq_orbit
#check nextAxiomSoundnessPredicate_shift
#check nextAxiomSoundnessPredicate_shift_val
#check kernelOfStructuralUniversalProof
#check compileKernelOfStructuralUniversalProof

#print axioms all_nextAxiomSoundnessPredicate_eq_orbit
#print axioms nextAxiomSoundnessPredicate_shift
#print axioms nextAxiomSoundnessPredicate_shift_val
#print axioms kernelOfStructuralUniversalProof
#print axioms compileKernelOfStructuralUniversalProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The public splice has exactly the next positive axiom-soundness field as
its target. -/
noncomputable example (context : Bootstrapping.Formula V ℒₒᵣ) (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextAxiomSoundnessPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
    Peano.internalize V ⊢!
      orbitSuccessorAxiomSoundnessFormula n :=
  compileKernelOfStructuralUniversalProof context n proof hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessorAudit
