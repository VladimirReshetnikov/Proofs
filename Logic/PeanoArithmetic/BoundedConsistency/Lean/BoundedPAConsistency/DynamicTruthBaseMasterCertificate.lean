import BoundedPAConsistency.DynamicTruthBaseCertificate
import BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant
import BoundedPAConsistency.DynamicTruthBaseAxiomSoundness

/-!
# The complete proof-producing base master certificate

The dynamic truth recursion starts with one proof code for the full six-field
certificate at model index zero.  The component derivations have been proved
independently: the compiled local bundle, cross-level coherence, shift and
substitution invariance, PA-axiom soundness, and the exact restricted-
consistency target.  This file packs those derivations with
`TruthCertificateFields.intro` and verifies that the resulting value is
accepted by PA's represented proof predicate for the concrete family code.

This is the actual zero seed of the eventual primitive recursion; it is not
merely an external existence theorem about standard proofs.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificate
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundness
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The forced final coordinate at model zero is literally the standard base
formula already equipped with a PA proof.  Equality is established through
their common represented substitution code. -/
theorem paRestrictedConsistencyFormula_zero_eq_base :
    paRestrictedConsistencyFormula (V := V) 0 =
      baseFinalConsistencyFormula := by
  apply Bootstrapping.Semiformula.ext
  rw [paRestrictedConsistencyFormula_val,
    baseFinalConsistencyFormula_val_eq_target]

/-- A genuine typed PA derivation of the exact six-field master sentence at
index zero. -/
noncomputable def compiledDynamicTruthBaseCertificateProof :
    Peano.internalize V ⊢!
      ((compiledDynamicTruthCertificateFamily (V := V)).fields 0).sentence :=
  TruthCertificateFields.intro
    ((compiledDynamicTruthCertificateFamily (V := V)).fields 0)
    (by
      simpa only [PATruthCertificateFamily.fields,
        compiledDynamicTruthCertificateFamily_localStep_zero] using
        (baseAugmentedLocalBundleProof (V := V)))
    (by
      simpa only [PATruthCertificateFamily.fields,
        compiledDynamicTruthCertificateFamily_crossLevel_zero] using
        (baseCrossLevelProof (V := V)))
    (by
      simpa only [PATruthCertificateFamily.fields,
        compiledDynamicTruthCertificateFamily_shiftInvariant_zero] using
        (baseShiftInvariantProof (V := V)))
    (by
      simpa only [PATruthCertificateFamily.fields,
        compiledDynamicTruthCertificateFamily_substitutionInvariant_zero]
        using (baseSubstitutionInvariantProof (V := V)))
    (by
      simpa only [PATruthCertificateFamily.fields,
        compiledDynamicTruthCertificateFamily_axiomSound_zero] using
        (baseAxiomSoundnessProof (V := V)))
    (by
      change Peano.internalize V ⊢!
        paRestrictedConsistencyFormula (V := V) 0
      rw [paRestrictedConsistencyFormula_zero_eq_base (V := V)]
      exact baseFinalConsistencyProof (V := V))

set_option backward.isDefEq.respectTransparency false in
/-- The base master certificate's value is recognized by the public PA proof
predicate at exactly the concrete family code. -/
theorem compiledDynamicTruthBaseCertificateProof_isPAProof :
    Proof Peano
      (compiledDynamicTruthBaseCertificateProof (V := V)).val
      ((compiledDynamicTruthCertificateFamily (V := V)).code 0) := by
  simpa [PATruthCertificateFamily.code, Proof] using
    (compiledDynamicTruthBaseCertificateProof (V := V)).derivationOf

/-- Existential form used as the zero graph witness of a represented proof
recursion. -/
theorem exists_compiledDynamicTruthBaseCertificateProof :
    ∃ d : V, Proof Peano d
      ((compiledDynamicTruthCertificateFamily (V := V)).code 0) :=
  ⟨(compiledDynamicTruthBaseCertificateProof (V := V)).val,
    compiledDynamicTruthBaseCertificateProof_isPAProof (V := V)⟩

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificate
