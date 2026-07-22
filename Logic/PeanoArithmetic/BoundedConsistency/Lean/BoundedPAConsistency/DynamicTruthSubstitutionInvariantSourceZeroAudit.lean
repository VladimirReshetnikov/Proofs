import BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero

/-!
# Audit for the structural substitution-invariance zero premise

The checks expose the genuine source antecedent, the arithmetic non-domain
fact, its finite source derivation, exact model-coded compilation, and the
Hilbert projection from the complete staged context.  No successor premise
or completed induction kernel is claimed here.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZeroAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

#check sourceAvailableContext
#check availableContextFormula
#check translate_sourceAvailableContext
#check arithmeticZeroSemiformulaSentence
#check arithmeticZeroSemiformulaProof
#check liftedArithmeticZeroSemiformulaProof
#check sourceZeroTerm
#check typedSourceZeroTerm
#check typedSourceZeroTerm_eq_zero
#check translate_sourceZeroTerm
#check sourceZeroSentence
#check sourceZeroProof
#check translate_sourceZeroSentence
#check compiledSubstitutionInvariantZeroProof
#check orbitAvailableContext
#check availableContextFormula_orbit
#check orbitSubstitutionInvariantZeroProof
#check proveAvailableFromShiftContext
#check proveOrbitAvailableFromShiftContext
#check orbitSubstitutionInvariantZeroProofFromShiftContext

#print axioms arithmeticZeroSemiformulaProof
#print axioms sourceZeroProof
#print axioms translate_sourceZeroSentence
#print axioms compiledSubstitutionInvariantZeroProof
#print axioms proveAvailableFromShiftContext
#print axioms orbitSubstitutionInvariantZeroProofFromShiftContext

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

noncomputable section

/-- The final theorem has exactly the zero-premise type required by an
induction kernel under the staged substitution context. -/
example (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      shiftContext previous
          (orbitCompiledLocalBundle n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n) 🡒
        (substitutionInvariantPredicateFormula
          (truthFormula n) (n + 1) (n + 1 + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  orbitSubstitutionInvariantZeroProofFromShiftContext previous n

end

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZeroAudit
