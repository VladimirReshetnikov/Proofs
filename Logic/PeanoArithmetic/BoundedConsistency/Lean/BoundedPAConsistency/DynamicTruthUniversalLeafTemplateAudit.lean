import BoundedPAConsistency.DynamicTruthUniversalLeafTemplate

/-!
Kernel-facing audit for the isolated universal-record leaf projection.

The checked endpoint is deliberately specialized at an arbitrary element of
an arbitrary model of `I Sigma 1`; no standardness or decoding premise is
available for the dynamic truth level.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate

#check decodedLeafWitness
#check universalLeafLocalLaw
#check universalLeafProjectionSentence
#check sourceProof
#check decodedLeafWitnessFormula
#check universalLeafProjectionFormula
#check translate_universalLeafProjectionSentence
#check compiledUniversalLeafProjectionProof
#check compiledUniversalLeafProjectionProof_isPAProof
#check orbitUniversalLeafProjectionFormula
#check orbitUniversalLeafProjectionProof
#check orbitUniversalLeafProjectionProof_isPAProof

#print axioms sourceProof
#print axioms translate_universalLeafProjectionSentence
#print axioms compiledUniversalLeafProjectionProof_isPAProof
#print axioms orbitUniversalLeafProjectionProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The nonstandard-orbit endpoint contains both a typed PA derivation and a
proof-code witness accepted by the represented PA proof predicate. -/
example (n : V) :
    Proof Peano (orbitUniversalLeafProjectionProof n).val
      (orbitUniversalLeafProjectionFormula n).val :=
  orbitUniversalLeafProjectionProof_isPAProof n

end LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplateAudit
