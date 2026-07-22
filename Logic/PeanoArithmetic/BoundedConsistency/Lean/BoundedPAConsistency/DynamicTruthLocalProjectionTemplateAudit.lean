import BoundedPAConsistency.DynamicTruthLocalProjectionTemplate

/-!
# Audit: compiled local projection for dynamic truth

The checks below keep the distinction between the fixed source theorem, its
arbitrary model-coded specialization, and the exact nonstandard-orbit instance
visible at the public interface.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate

#check hasStateProjection
#check localProjectionSentence
#check sourceProof
#check localProjectionFormula
#check translate_localProjectionSentence
#check compiledLocalProjectionProof
#check compiledLocalProjectionProof_isPAProof
#check orbitLocalProjectionFormula
#check orbitLocalProjectionProof
#check orbitLocalProjectionProof_isPAProof

#print axioms sourceProof
#print axioms translate_localProjectionSentence
#print axioms compiledLocalProjectionProof
#print axioms compiledLocalProjectionProof_isPAProof
#print axioms orbitLocalProjectionProof
#print axioms orbitLocalProjectionProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The endpoint is literally a represented PA proof of the orbit formula,
including when `n` is nonstandard. -/
example (n : V) :
    Proof Peano (orbitLocalProjectionProof n).val
      (orbitLocalProjectionFormula n).val :=
  orbitLocalProjectionProof_isPAProof n

/-- Expose the exact antecedent in the orbit field, guarding against a future
regression to a merely translated but unidentified source formula. -/
example (n : V) : orbitLocalProjectionFormula n =
    ∀⁰ ∀⁰ ∀⁰
      (truthFormula (n + 1) 🡒
        ∃⁰ (⌜LeanProofs.BoundedPAConsistency.FixedLevelTruth.hasTruthStateDef.val⌝ :
          Bootstrapping.Semiformula V ℒₒᵣ 4)) := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplateAudit
