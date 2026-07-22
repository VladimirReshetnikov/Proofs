import BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant

/-!
# Audit for the genuine base substitution-invariance proof
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariantAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant

#check standardApply₅
#check typedQuote_standardApply₅
#check standardBaseSemitermVectorFormula
#check standardBaseBoundLengthFormula
#check standardBaseSubstitutionEnvironmentFormula
#check standardBaseSemiformulaFormula
#check standardBaseSubstitutionBoundedDomainFormula
#check standardBaseSubstitutedTruthWitnessFormula
#check standardBaseSubstitutionInvariantBody
#check standardBaseSubstitutionInvariantSentence
#check typedQuote_standardBaseSubstitutionInvariantSentence
#check standardBaseSubstitutionInvariantProof
#check baseSubstitutionInvariantProof

#print axioms typedQuote_standardBaseSubstitutionInvariantSentence
#print axioms standardBaseSubstitutionInvariantProof
#print axioms baseSubstitutionInvariantProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

noncomputable section

/-- The delivered proof has the exact pre-existing base-field type. -/
example : Peano.internalize V ⊢!
    baseSubstitutionInvariantFormula (V := V) :=
  baseSubstitutionInvariantProof (V := V)

end

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariantAudit
