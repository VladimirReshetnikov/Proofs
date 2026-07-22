import BoundedPAConsistency.ModelCodedInductionAxiom

/-! Kernel-facing audit for induction on model-coded formulas. -/

namespace LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiomAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom

#check indBody_mem_peano_of_shift_fixed
#check paInductionProofOfShiftFixed
#check paInductionOfShiftFixed

#print axioms indBody_mem_peano_of_shift_fixed
#print axioms paInductionProofOfShiftFixed
#print axioms paInductionOfShiftFixed

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The exported proof has exactly the typed induction body as its endpoint. -/
noncomputable example (K : Semiformula V ℒₒᵣ 1)
    (hKshift : shift ℒₒᵣ K.val = K.val) :
    Peano.internalize V ⊢! indBody K :=
  paInductionProofOfShiftFixed K hKshift

/-- The derived eliminator has the expected base/step/result orientation. -/
noncomputable example (K : Semiformula V ℒₒᵣ 1)
    (hKshift : shift ℒₒᵣ K.val = K.val)
    (hzero : Peano.internalize V ⊢!
      K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    (hsucc : Peano.internalize V ⊢!
      ∀⁰ (K 🡒 K.subst
        ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) :
    Peano.internalize V ⊢! ∀⁰ K :=
  paInductionOfShiftFixed K hKshift hzero hsucc

end LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiomAudit
