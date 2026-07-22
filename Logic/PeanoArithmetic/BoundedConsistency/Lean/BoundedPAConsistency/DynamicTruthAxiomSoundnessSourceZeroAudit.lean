import BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZero

/-!
# Audit for the dynamic PA-axiom-soundness zero premise

The public endpoint below has the exact base-premise type required by the
axiom-soundness induction kernel after the local, cross-level, shift, and
substitution fields have been accumulated.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZeroAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZero
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

#check sourceFormulaCodeZeroTerm
#check sourceAxiomSoundnessZeroSentence
#check sourceAxiomSoundnessZeroProof
#check typedFormulaCodeZeroTerm
#check typedFormulaCodeZeroTerm_eq_zero
#check translate_sourceFormulaCodeZeroTerm
#check translate_sourceAxiomSoundnessZeroSentence
#check compiledAxiomSoundnessZeroProof
#check orbitAxiomSoundnessZeroProof
#check orbitAxiomSoundnessZeroProofFromSubstitutionContext

#print axioms sourceAxiomSoundnessZeroProof
#print axioms translate_sourceAxiomSoundnessZeroSentence
#print axioms compiledAxiomSoundnessZeroProof
#print axioms orbitAxiomSoundnessZeroProofFromSubstitutionContext

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

noncomputable section

example (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      substitutionContext previous
          (orbitCompiledLocalBundle n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n)
          (orbitSuccessorSubstitutionInvariantFormula n) 🡒
        (axiomSoundnessPredicateFormula
          (truthFormula (n + 1)) (n + 1)).subst
            ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
              Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  orbitAxiomSoundnessZeroProofFromSubstitutionContext previous n

end

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZeroAudit
