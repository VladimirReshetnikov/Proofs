import BoundedPAConsistency.TruthCertificateCodeDefinability

/-!
# Direct existential packages of truth-certificate proofs

The uniform selector does not require a canonical primitive-recursive choice
of the proof at each level.  Sigma-one induction only requires that the
*existence* of a suitable proof code be Sigma-one, that one such code exists
at zero, and that any code at level `n` can be extended to some code at level
`n + 1`.

This observation removes an avoidable implementation burden from
`PrimitiveRecursiveTruthCertificate`: the `.val` of the typed proof compiler
does not itself have to be presented as a `PR.Construction`.  We take the
package relation to be the represented PA proof predicate directly.  Since
that predicate is Delta-one and the target-code function is Sigma-one
definable, the package relation is Sigma-one.  The existing typed certificate
compiler then supplies the existential successor witness.

The only mathematical inputs left at the public endpoint are therefore the
five dynamic field-code graphs, a genuine base certificate, and one typed
successor template at every model element.
-/

namespace LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackage

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability
open LeanProofs.BoundedPAConsistency.UniformInternalProvability
open LeanProofs.BoundedPAConsistency.UniformProofPackage

variable {V : Type*} [ORingStructure V]
variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The package witness is already the proof code of the exact six-field
certificate.  There is no auxiliary compiler state and no canonical-choice
requirement. -/
def DirectTruthCertificatePackage
    (family : PATruthCertificateFamily (V := V)) (n d : V) : Prop :=
  Proof Peano d (family.code n)

/-- Direct proof packages form a Sigma-one relation as soon as the exact
master-formula code is Sigma-one definable. -/
lemma directTruthCertificatePackage_definable
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code) :
    HierarchySymbol.sigmaOne.DefinableRel
      (DirectTruthCertificatePackage family) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁ family.code :=
    masterCodeDefinable
  unfold DirectTruthCertificatePackage
  definability

variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-- A fixed typed successor template at every (possibly nonstandard) level.

The code equality says that the compiler's six target fields are exactly the
next member of `family`.  No equation for the generated proof code is needed:
its existence is enough for Sigma-one package induction. -/
def HasTypedTruthCertificateSuccessor
    (family : PATruthCertificateFamily (V := V)) : Prop :=
  ∀ n : V,
    ∃ step : PAInductiveTruthCertificateStep (family.fields n),
      step.target.sentence.val = family.code (n + 1)

/-- A base master proof and typed successor templates give the arbitrary-model
selector required by the literal uniform theorem.

This theorem performs genuine PA-model induction through
`paRestrictedConsistencyProofSelectorIn_of_package`; it is not an external
recursion over standard naturals. -/
theorem paRestrictedConsistencyProofSelectorIn_of_directTruthCertificates
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate : ∃ d : V, Proof Peano d (family.code 0))
    (successorTemplates : HasTypedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_package
    (Package := DirectTruthCertificatePackage family)
  · exact directTruthCertificatePackage_definable family
      masterCodeDefinable
  · exact baseCertificate
  · intro n d hd
    rcases successorTemplates n with ⟨step, htarget⟩
    let previous : Peano.internalize V ⊢! (family.fields n).sentence :=
      family.toTProof hd
    let next := step.compile previous
    refine ⟨next.val, ?_⟩
    have hproof : Proof Peano next.val step.target.sentence.val :=
      step.compile_isPAProof previous
    exact htarget ▸ hproof
  · intro n d hd
    exact family.exists_finalProof_of_masterProof hd

/-- Typed form of the base premise.  This is convenient for concrete
constructions, which normally assemble their six field proofs with
`TruthCertificateFields.intro`. -/
theorem paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate :
      Peano.internalize V ⊢! (family.fields 0).sentence)
    (successorTemplates : HasTypedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_directTruthCertificates
    family masterCodeDefinable
  · refine ⟨baseCertificate.val, ?_⟩
    set_option backward.isDefEq.respectTransparency false in
      simpa [Proof, PATruthCertificateFamily.code] using
        baseCertificate.derivationOf
  · exact successorTemplates

/-! ## Endpoint requiring only the five concrete field graphs -/

/-- The final selector bridge for a concrete dynamic family.

The sixth field is definitionally the required `Con_n` formula, so the five
listed code graphs, a typed base proof, and typed successor templates are the
complete remaining interface. -/
theorem paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates_and_fieldCodes
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
    (successorTemplates : HasTypedTruthCertificateSuccessor family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_directTypedTruthCertificates
    family
    (family.code_definable_of_fields localStepDefinable
      crossLevelDefinable shiftInvariantDefinable
      substitutionInvariantDefinable axiomSoundDefinable)
    baseCertificate successorTemplates

end LeanProofs.BoundedPAConsistency.DirectTruthCertificatePackage
