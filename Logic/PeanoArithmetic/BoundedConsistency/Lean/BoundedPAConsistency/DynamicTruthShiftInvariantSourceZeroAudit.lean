import BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero

/-!
# Audit for the dynamic shift-invariance zero premise

These checks expose the fixed arithmetic non-domain theorem, its lifted
source derivation, exact specialization at arbitrary model-coded syntax, and
the final implication under the staged cross-level context.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZeroAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

#check arithmeticZeroNotBoundedSentence
#check arithmeticZeroNotBoundedProof
#check liftedArithmeticZeroNotBoundedProof
#check sourceZeroTerm
#check sourceZeroSentence
#check sourceZeroProof
#check typedSourceZeroTerm
#check typedSourceZeroTerm_eq_zero
#check translate_sourceZeroTerm
#check translate_sourceZeroSentence
#check compiledShiftInvariantZeroProof
#check orbitShiftInvariantZeroProof
#check orbitShiftInvariantZeroProofFromCrossContext

#print axioms arithmeticZeroNotBoundedProof
#print axioms sourceZeroProof
#print axioms translate_sourceZeroSentence
#print axioms compiledShiftInvariantZeroProof
#print axioms orbitShiftInvariantZeroProofFromCrossContext

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

noncomputable section

/-- The public endpoint is exactly the base field expected by the staged
shift-invariance induction kernel. -/
example (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      crossContext previous
          (orbitCompiledLocalBundle n)
          (orbitSuccessorCrossLevelFormula n) 🡒
        (shiftInvariantPredicateFormula
          (truthFormula n) (n + 1) (n + 1 + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  orbitShiftInvariantZeroProofFromCrossContext previous n

end

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZeroAudit
