import BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
import BoundedPAConsistency.DynamicTruthMemberValidityTemplate
import BoundedPAConsistency.DynamicTruthUniversalLeafTemplate

/-!
# A compiled bundle of the first dynamic local truth laws

The dynamic successor formula already has three proof-producing elimination
laws: an accepted truth state exposes its certificate, every member of that
certificate satisfies the local record predicate, and a record in the
universal branch exposes the stored lower-truth counterexample.  They were
previously available only as independent checkpoint sentences.

This file packages those sentences as one right-associated local field.  The
bundle has a typed PA proof at every element of an arbitrary PA model, an
implication from any closed context (the form required by the staged
certificate compiler), and a Sigma-one graph for its raw formula code.

The name deliberately says `CompiledLocalBundle`, not `CompleteLocalLaws`:
additional constructor-specific introduction and elimination laws can be
adjoined later without overstating what the present three conjuncts prove.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The three currently compiled local laws, in a stable right-associated
shape suitable for use as one truth-certificate field. -/
noncomputable def orbitCompiledLocalBundle (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  orbitLocalProjectionFormula n ⋏
    (orbitMemberValidityFormula n ⋏
      orbitUniversalLeafProjectionFormula n)

/-- Pack the three independently compiled derivations into one typed PA
proof.  This constructor manipulates proof objects only; it does not appeal
to semantic soundness or decode the possibly nonstandard index `n`. -/
noncomputable def orbitCompiledLocalBundleProof (n : V) :
    Peano.internalize V ⊢! orbitCompiledLocalBundle n :=
  Entailment.K_intro (orbitLocalProjectionProof n) <|
    Entailment.K_intro (orbitMemberValidityProof n)
      (orbitUniversalLeafProjectionProof n)

/-- A theorem already proved without hypotheses may be weakened to an
implication from any closed certificate context.  This is exactly the first
stage expected by `PAStagedTruthCertificateStep.proveLocalStep`. -/
noncomputable def proveOrbitCompiledLocalBundleFrom
    (context : Bootstrapping.Formula V ℒₒᵣ) (n : V) :
    Peano.internalize V ⊢! context 🡒 orbitCompiledLocalBundle n :=
  Entailment.C_of_conseq (orbitCompiledLocalBundleProof n)

set_option backward.isDefEq.respectTransparency false in
/-- The packed typed derivation is recognized by the public represented PA
proof predicate. -/
theorem orbitCompiledLocalBundleProof_isPAProof (n : V) :
    Proof Peano (orbitCompiledLocalBundleProof n).val
      (orbitCompiledLocalBundle n).val := by
  simpa [Proof] using (orbitCompiledLocalBundleProof n).derivationOf

/-! ## Representability of the bundled field code -/

/-- The formula code of the bundled field has a Sigma-one graph.

After exposing the three source-specialized formulas, every operation is a
represented syntax constructor.  The sole recursively varying subterm is
`truthFormula n`, whose graph is already supplied by `DynamicTruthOrbit`. -/
theorem orbitCompiledLocalBundleCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitCompiledLocalBundle n).val) := by
  simp only [orbitCompiledLocalBundle,
    orbitLocalProjectionFormula, localProjectionFormula,
    orbitMemberValidityFormula, memberValidityFormula,
    acceptedCertificateAtRecordFormula,
    orbitUniversalLeafProjectionFormula, universalLeafProjectionFormula,
    decodedLeafWitnessFormula,
    Semiformula.val_and, Semiformula.val_all, Semiformula.val_imp,
    Semiformula.val_exs, Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,
    LeanProofs.BoundedPAConsistency.DynamicTruthOrbit.truthFormula_val]
  definability

end LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
