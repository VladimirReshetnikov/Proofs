import BoundedPAConsistency.NamedTruthTransportTemplate

/-!
Kernel-facing audit for named truth transport.

The source proof below is universal elimination, not an assumed truth law.
Its compiled target permits every named constant to denote an arbitrary
element of the ambient PA model, including a nonstandard formula or
environment code.
-/

namespace LeanProofs.BoundedPAConsistency.NamedTruthTransportTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.NamedTruthTransportTemplate

#check truthSlice
#check transportSentence
#check sourceProof
#check specializedSlice
#check transportFormula
#check translate_transportSentence
#check compiledTransportProof
#check compilerOutput_isPAProof
#check compiledTransportProof_isPAProof

#print axioms sourceProof
#print axioms translate_transportSentence
#print axioms compilerOutput_isPAProof
#print axioms compiledTransportProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The raw endpoint is exactly a PA proof of the advertised transport
formula, for arbitrary model-valued names. -/
example (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hS : S.shift = S) :
    Proof Peano (compilePeanoTemplate S parameters hS sourceProof).val
      (transportFormula S parameters).val :=
  compilerOutput_isPAProof S parameters hS

end LeanProofs.BoundedPAConsistency.NamedTruthTransportTemplateAudit
