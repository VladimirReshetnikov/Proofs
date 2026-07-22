import BoundedPAConsistency.DynamicTruthCompiledLocalBundle

/-!
# Kernel audit for the compiled dynamic local-law bundle

The checks below keep the public surface small and make the proof-producing
and representability claims visible to Lean's axiom auditor.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundleAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle

#check orbitCompiledLocalBundle
#check orbitCompiledLocalBundleProof
#check proveOrbitCompiledLocalBundleFrom
#check orbitCompiledLocalBundleProof_isPAProof
#check orbitCompiledLocalBundleCode_definable

#print axioms orbitCompiledLocalBundleProof
#print axioms proveOrbitCompiledLocalBundleFrom
#print axioms orbitCompiledLocalBundleProof_isPAProof
#print axioms orbitCompiledLocalBundleCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The bundle has exactly the advertised right-associated syntax. -/
example (n : V) :
    orbitCompiledLocalBundle n =
      DynamicTruthLocalProjectionTemplate.orbitLocalProjectionFormula n ⋏
        (DynamicTruthMemberValidityTemplate.orbitMemberValidityFormula n ⋏
          DynamicTruthUniversalLeafTemplate.orbitUniversalLeafProjectionFormula n) :=
  rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundleAudit
