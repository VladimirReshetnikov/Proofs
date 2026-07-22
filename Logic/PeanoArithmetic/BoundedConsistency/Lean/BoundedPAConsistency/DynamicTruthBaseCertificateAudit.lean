import BoundedPAConsistency.DynamicTruthBaseCertificate

/-!
# Audit for the proof-producing dynamic-truth base fields

These checks expose the ordinary syntax, literal quotation bridges, outer PA
derivations, and transported internal derivations for the shift and
cross-level coordinates.  The eventual six-field conjunction is assembled
only after the independently audited substitution and axiom coordinates are
available.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificate

#check standardBaseShiftInvariantSentence
#check typedQuote_standardBaseShiftInvariantSentence
#check standardBaseShiftInvariantProof
#check baseShiftInvariantProof
#check standardBaseCrossLevelSentence
#check typedQuote_standardBaseCrossLevelSentence
#check standardBaseCrossLevelProof
#check baseCrossLevelProof

#print axioms typedQuote_standardBaseShiftInvariantSentence
#print axioms standardBaseShiftInvariantProof
#print axioms baseShiftInvariantProof
#print axioms typedQuote_standardBaseCrossLevelSentence
#print axioms standardBaseCrossLevelProof
#print axioms baseCrossLevelProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

noncomputable section

example : Peano.internalize V ⊢!
    baseShiftInvariantFormula (V := V) :=
  baseShiftInvariantProof (V := V)

example : Peano.internalize V ⊢!
    baseCrossLevelFormula (V := V) :=
  baseCrossLevelProof (V := V)

end

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificateAudit
