import BoundedPAConsistency.DynamicTruthBaseAxiomSoundness

/-!
# Audit for the genuine base axiom-soundness proof

The checks expose the standard sentence, its literal typed-quotation bridge,
the outer PA proof, and the final internal proof object.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundnessAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundness

#check standardApply₁
#check typedQuote_standardApply₁
#check standardRecognizedPAAxiomFormula
#check standardZeroAxiomBoundedDomainFormula
#check standardAxiomFreeSequenceFormula
#check standardBaseAxiomSoundnessBody
#check standardBaseAxiomSoundnessSentence
#check typedQuote_standardBaseAxiomSoundnessSentence
#check standardBaseAxiomSoundnessProof
#check baseAxiomSoundnessProof

#print axioms typedQuote_standardBaseAxiomSoundnessSentence
#print axioms standardBaseAxiomSoundnessProof
#print axioms baseAxiomSoundnessProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

noncomputable section

/-- The delivered proof concludes the exact pre-existing base field. -/
example : Peano.internalize V ⊢!
    baseAxiomSoundnessFormula (V := V) :=
  baseAxiomSoundnessProof (V := V)

end


end LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundnessAudit
