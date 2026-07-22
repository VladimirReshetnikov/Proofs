import BoundedPAConsistency.DirectTruthCertificatePackage
import BoundedPAConsistency.StagedTruthCertificateProofCompiler

/-!
# Direct proof packages from staged truth-certificate steps

The direct package selector only needs an existential successor proof code.
The dependency-aware staged compiler produces exactly such a code, but its
step type differs from the earlier parallel-context compiler.  This module
connects the two interfaces without introducing a new package relation.

At level n, a staged witness supplies a
PAStagedTruthCertificateStep for the six fields of the current family and an
equality identifying its public target sentence with the family code at
n + 1.  Given an incoming direct package proof, the staged compiler's value
is therefore a direct package witness at the successor level.  Sigma-one
package induction and final-field extraction are then inherited unchanged
from DirectTruthCertificatePackage.
-/

namespace LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackage

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability
open LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackage
open LeanProofs.BoundedPAConsistency.UniformInternalProvability
open LeanProofs.BoundedPAConsistency.UniformProofPackage

variable {V : Type*} [ORingStructure V]
variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-! ## Staged successor witnesses -/

/-- A dependency-aware staged successor at every model index.

The equality is intentionally on raw public sentence codes.  Intermediate
cumulative contexts are private to the staged compiler; after compilation,
the result is the same six-field master-certificate shape used by
PATruthCertificateFamily. -/
def HasStagedTruthCertificateSuccessor
    (family : PATruthCertificateFamily (V := V)) : Prop :=
  ∀ n : V,
    ∃ step : PAStagedTruthCertificateStep (family.fields n),
      step.target.sentence.val = family.code (n + 1)

/-- One staged successor witness extends any incoming direct package proof.

The witness is the actual value of the typed staged compilation.  Its PA
proof judgment comes from compile_isPAProof, and the supplied target-code
equality changes only the conclusion code to the next family member. -/
lemma exists_directTruthCertificatePackage_succ_of_staged
    (family : PATruthCertificateFamily (V := V))
    (successorTemplates : HasStagedTruthCertificateSuccessor family)
    {n d : V}
    (hd : DirectTruthCertificatePackage family n d) :
    ∃ d' : V, DirectTruthCertificatePackage family (n + 1) d' := by
  rcases successorTemplates n with ⟨step, htarget⟩
  let previous : Peano.internalize V ⊢! (family.fields n).sentence :=
    family.toTProof hd
  let next := step.compile previous
  refine ⟨next.val, ?_⟩
  have hproof : Proof Peano next.val step.target.sentence.val :=
    step.compile_isPAProof previous
  change Proof Peano next.val (family.code (n + 1))
  rw [← htarget]
  exact hproof

/-! ## Direct staged selector -/

/-- A base master proof and staged successor witnesses give the
model-internal proof selector.

The induction is the existing Sigma-one direct-package induction.  This
theorem contributes only the successor witness construction above; package
definability and extraction of the forced final consistency field are reused
verbatim. -/
theorem paRestrictedConsistencyProofSelectorIn_of_stagedDirectTruthCertificates
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate : ∃ d : V, Proof Peano d (family.code 0))
    (successorTemplates : HasStagedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_package
    (Package := DirectTruthCertificatePackage family)
  · exact directTruthCertificatePackage_definable family
      masterCodeDefinable
  · exact baseCertificate
  · intro n d hd
    exact exists_directTruthCertificatePackage_succ_of_staged
      family successorTemplates hd
  · intro n d hd
    exact family.exists_finalProof_of_masterProof hd

/-- Typed-base form of the staged direct selector.

Concrete truth constructions normally assemble their level-zero certificate
as a typed proof, so this form avoids a manual conversion to the raw proof
predicate. -/
theorem paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate :
      Peano.internalize V ⊢! (family.fields 0).sentence)
    (successorTemplates : HasStagedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_stagedDirectTruthCertificates
    family masterCodeDefinable
  · refine ⟨baseCertificate.val, ?_⟩
    set_option backward.isDefEq.respectTransparency false in
      simpa [Proof, PATruthCertificateFamily.code] using
        baseCertificate.derivationOf
  · exact successorTemplates

/-! ## Endpoint requiring only the five variable field graphs -/

/-- Public staged endpoint for a concrete dynamic truth family.

The five premises represent exactly the variable field-code functions.  The
sixth field is forced to be the requested bounded-consistency formula, and
TruthCertificateCodeDefinability assembles the complete master-code graph. -/
theorem paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates_and_fieldCodes
    (family : PATruthCertificateFamily (V := V))
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
    PARestrictedConsistencyProofSelectorIn V := by
  apply
    paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates
      family
      (LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability.PATruthCertificateFamily.code_definable_of_fields
        family localStepDefinable
        crossLevelDefinable shiftInvariantDefinable
        substitutionInvariantDefinable axiomSoundDefinable)
      baseCertificate successorTemplates

end LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackage
