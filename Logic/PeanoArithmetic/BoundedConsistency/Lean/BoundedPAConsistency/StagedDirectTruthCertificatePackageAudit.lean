import BoundedPAConsistency.StagedDirectTruthCertificatePackage

/-!
# Audit: direct packages from staged certificate compilation

The audit exposes the staged successor family, the concrete package extension
lemma, and both selector endpoints.  Lean also reports every axiom used by
the proof-code bridge.
-/

namespace LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackageAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackage
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

#check HasStagedTruthCertificateSuccessor
#check exists_directTruthCertificatePackage_succ_of_staged
#check paRestrictedConsistencyProofSelectorIn_of_stagedDirectTruthCertificates
#check paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates
#check paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates_and_fieldCodes

#print axioms exists_directTruthCertificatePackage_succ_of_staged
#print axioms paRestrictedConsistencyProofSelectorIn_of_stagedDirectTruthCertificates
#print axioms paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates
#print axioms paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates_and_fieldCodes

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- The public endpoint contains no primitive-recursive proof-code compiler:
only five field graphs, one typed base proof, and staged witnesses remain. -/
example (family : PATruthCertificateFamily (V := V))
    (localStepDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.localStep n).val))
    (crossLevelDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.crossLevel n).val))
    (shiftInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.shiftInvariant n).val))
    (substitutionInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.substitutionInvariant n).val))
    (axiomSoundDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.axiomSound n).val))
    (baseCertificate :
      Peano.internalize V ⊢! (family.fields 0).sentence)
    (successorTemplates : HasStagedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V :=
  paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates_and_fieldCodes
    family localStepDefinable crossLevelDefinable shiftInvariantDefinable
      substitutionInvariantDefinable axiomSoundDefinable
      baseCertificate successorTemplates

end LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackageAudit
