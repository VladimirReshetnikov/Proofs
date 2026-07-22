import BoundedPAConsistency.PrimitiveRecursiveTruthCertificate

/-!
# Definability of assembled truth-certificate codes

`PrimitiveRecursiveTruthCertificate` reduces the uniform-selector problem to
a represented recursion whose state is a proof of a six-field master
certificate.  Its interface deliberately asks for a Sigma-one graph of the
master formula's raw code.  This file discharges that syntax-side obligation
compositionally.

The first five fields may be supplied by any concrete dynamic truth
construction.  We require only Sigma-one graphs for their raw code functions.
The sixth field is fixed by `PATruthCertificateFamily.fields` to the requested
bounded-consistency formula, and its graph is already represented by
Foundation's `substNumeral` construction.  Pairing the fields uses the raw
conjunction-code constructor, whose graph is Delta-zero (and hence
Sigma-one).  No decoding or standardness hypothesis occurs.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Reusable outer-state coders -/

/-- Assemble the six raw formula codes in exactly the right-associated shape
used by `TruthCertificateFields.sentence`.

This deliberately operates on arbitrary model elements.  Well-formedness of
the six inputs is a separate invariant of a concrete truth construction; the
represented code operation itself remains total. -/
noncomputable def assembleTruthCertificateCode
    (localStep crossLevel shiftInvariant substitutionInvariant axiomSound
      finalConsistency : V) : V :=
  localStep ^⋏
    (crossLevel ^⋏
      (shiftInvariant ^⋏
        (substitutionInvariant ^⋏
          (axiomSound ^⋏ finalConsistency))))

/-- The six-input outer certificate-code constructor has a Sigma-one graph.
This is the reusable pairing primitive behind the family-specific theorem
below. -/
instance assembleTruthCertificateCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction
      (fun v : Fin 6 → V ↦
        assembleTruthCertificateCode
          (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold assembleTruthCertificateCode
  definability

/-- Pair an assembled certificate formula code with the proof/compiler state
that certifies it.  A represented recursion may use this total coder as its
state type while keeping formula-code and proof-code invariants separate. -/
noncomputable def truthCertificateCompilerStateCode
    (localStep crossLevel shiftInvariant substitutionInvariant axiomSound
      finalConsistency proofState : V) : V :=
  ⟨assembleTruthCertificateCode localStep crossLevel shiftInvariant
      substitutionInvariant axiomSound finalConsistency, proofState⟩

/-- The seven-input compiler-state pairing operation is Sigma-one definable.
The actual recursion's zero and successor proofs remain the responsibility of
the concrete truth-certificate compiler. -/
instance truthCertificateCompilerStateCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction
      (fun v : Fin 7 → V ↦
        truthCertificateCompilerStateCode
          (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold truthCertificateCompilerStateCode
  definability

/-! ## The fixed final-field graph -/

/-- The raw code of the fixed final field is Sigma-one definable.

The proof is only composition: `paRestrictedConsistencyFormula_val` exposes
the represented substitution function and `definability` uses its existing
Sigma-one graph. -/
theorem paRestrictedConsistencyFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (paRestrictedConsistencyFormula n).val) := by
  simp_rw [paRestrictedConsistencyFormula_val]
  definability

/-- Expose the exact raw-code shape of a family certificate.  In particular,
the last coordinate is syntactically the represented numeral-substitution
code, not merely a semantically equivalent sentence. -/
@[simp] theorem PATruthCertificateFamily.code_eq_assemble
    (family : PATruthCertificateFamily (V := V)) (n : V) :
    family.code n =
      assembleTruthCertificateCode
        (family.localStep n).val
        (family.crossLevel n).val
        (family.shiftInvariant n).val
        (family.substitutionInvariant n).val
        (family.axiomSound n).val
        (substNumeral
          (⌜UniformInternalProvability.paRestrictedConsistencyTemplate⌝ : V) n) := by
  simp [PATruthCertificateFamily.code, PATruthCertificateFamily.fields,
    TruthCertificateFields.sentence, assembleTruthCertificateCode]

/-! ## Compositional assembly of the six-field code -/

/-- Sigma-one graphs for the five variable field-code functions suffice for
the graph of the complete right-associated master certificate.

The final field needs no premise: its graph is supplied by
`paRestrictedConsistencyFormulaCode_definable`.  Keeping the hypotheses
explicit (instead of installing local global instances at construction time)
makes this theorem convenient for independently developed truth packages. -/
theorem PATruthCertificateFamily.code_definable_of_fields
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
        (fun n : V ↦ (family.axiomSound n).val)) :
    HierarchySymbol.sigmaOne.DefinableFunction₁ family.code := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.localStep n).val) := localStepDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.crossLevel n).val) := crossLevelDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.shiftInvariant n).val) := shiftInvariantDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.substitutionInvariant n).val) :=
    substitutionInvariantDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.axiomSound n).val) := axiomSoundDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (paRestrictedConsistencyFormula n).val) :=
    paRestrictedConsistencyFormulaCode_definable
  simp_rw [family.code_eq_assemble]
  unfold assembleTruthCertificateCode
  definability

/-! ## Selector bridges with only field-code premises -/

variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-- Feed five field-code graphs directly to the represented-recursion
selector theorem.  The assembled master-code graph and fixed final target
are discharged by this module. -/
theorem paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage_and_fieldCodes
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
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
      Proof Peano (compiler.zero parameters) (family.code 0))
    (successorCertificate : ∀ n d : V,
      Proof Peano d (family.code n) →
      Proof Peano (compiler.succ parameters n d) (family.code (n + 1))) :
    UniformInternalProvability.PARestrictedConsistencyProofSelectorIn V := by
  apply
    paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage
      compiler parameters family
      (family.code_definable_of_fields localStepDefinable
        crossLevelDefinable shiftInvariantDefinable
        substitutionInvariantDefinable axiomSoundDefinable)
      baseCertificate successorCertificate

/-- Typed-successor version of the preceding bridge.  Once a concrete
compiler supplies the five field graphs, base proof, and typed successor
realization, no separate master-code definability premise remains. -/
theorem paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage_and_fieldCodes
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
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
      Proof Peano (compiler.zero parameters) (family.code 0))
    (successorRealization :
      RealizesTypedCertificateSuccessor compiler parameters family) :
    UniformInternalProvability.PARestrictedConsistencyProofSelectorIn V := by
  apply
    paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage
      compiler parameters family
      (family.code_definable_of_fields localStepDefinable
        crossLevelDefinable shiftInvariantDefinable
        substitutionInvariantDefinable axiomSoundDefinable)
      baseCertificate successorRealization

end LeanProofs.BoundedPAConsistency.TruthCertificateCodeDefinability
