import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula

/-!
# Kernel audit for the dynamic PA-axiom-soundness field
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormulaAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula

#check sourceRecognizedPAAxiom
#check sourceAxiomBoundedDomain
#check sourceFreeSequence
#check sourceAxiomSoundnessSentence
#check recognizedPAAxiomFormula
#check axiomSoundnessFormula
#check translate_sourceAxiomSoundnessSentence
#check baseAxiomSoundnessFormula
#check baseAxiomSoundnessFormula_eq_upper
#check orbitSuccessorAxiomSoundnessFormula
#check orbitSuccessorAxiomSoundnessFormula_eq_upper
#check orbitSuccessorAxiomSoundnessFormulaCode_definable

#print axioms translate_sourceAxiomSoundnessSentence
#print axioms baseAxiomSoundnessFormula_eq_upper
#print axioms orbitSuccessorAxiomSoundnessFormula_eq_upper
#print axioms orbitSuccessorAxiomSoundnessFormulaCode_definable

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Positive orbit sanity check: no standardness premise occurs in the
field's exact upper-predicate view. -/
example (n : V) :
    orbitSuccessorAxiomSoundnessFormula n =
      upperAxiomSoundnessFormula (truthFormula (n + 1)) (n + 1) :=
  orbitSuccessorAxiomSoundnessFormula_eq_upper n

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormulaAudit
