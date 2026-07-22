import BoundedPAConsistency.DynamicTruthCompiledLocalBundle

/-!
# The model-indexed compiled local truth bundle

The three compiled local elimination laws are stated in
`DynamicTruthCompiledLocalBundle` for a positive successor of the represented
truth orbit.  A concrete certificate family also needs a genuine value at
index zero.  This module specializes the same fixed source proofs to the base
predicate, packages them, and splices that base bundle with the positive
orbit bundles.

Only the three laws already proved by fixed source templates are included.
Accordingly, this remains a *compiled local bundle*, not a claim that all
constructor-specific truth laws needed by the final soundness proof have
already been supplied.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The genuine base bundle -/

/-- The three compiled laws for the first positive truth predicate, obtained
by applying the dynamic successor constructor to quantifier-free base truth. -/
noncomputable def baseCompiledLocalBundle :
    Bootstrapping.Formula V ℒₒᵣ :=
  localProjectionFormula baseTruthFormula 0 1 ⋏
    (memberValidityFormula baseTruthFormula 0 1 ⋏
      universalLeafProjectionFormula baseTruthFormula 0 1)

/-- Typed PA proof of the genuine base bundle.  Each component comes from the
same fixed standard source theorem used at nonstandard orbit indices. -/
noncomputable def baseCompiledLocalBundleProof :
    Peano.internalize V ⊢! baseCompiledLocalBundle :=
  Entailment.K_intro
    (compiledLocalProjectionProof baseTruthFormula 0 1
      (Semiformula.ext (baseTruthFormula_shift (V := V)))) <|
    Entailment.K_intro
      (compiledMemberValidityProof baseTruthFormula 0 1
        (Semiformula.ext (baseTruthFormula_shift (V := V))))
      (compiledUniversalLeafProjectionProof baseTruthFormula 0 1
        (Semiformula.ext (baseTruthFormula_shift (V := V))))

/-- The base bundle may be weakened to an implication from any closed
certificate context. -/
noncomputable def proveBaseCompiledLocalBundleFrom
    (context : Bootstrapping.Formula V ℒₒᵣ) :
    Peano.internalize V ⊢! context 🡒 baseCompiledLocalBundle :=
  Entailment.C_of_conseq baseCompiledLocalBundleProof

set_option backward.isDefEq.respectTransparency false in
/-- The typed base derivation is recognized by the public PA proof
predicate. -/
theorem baseCompiledLocalBundleProof_isPAProof :
    Proof Peano (baseCompiledLocalBundleProof (V := V)).val
      (baseCompiledLocalBundle (V := V)).val := by
  simpa [Proof] using
    (baseCompiledLocalBundleProof (V := V)).derivationOf

/-! ## The total model-indexed field -/

/-- At index zero select the genuine base bundle; at a nonzero model index
select the positive bundle over its model predecessor. -/
noncomputable def modelIndexedCompiledLocalBundle (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseCompiledLocalBundle
  else
    orbitCompiledLocalBundle (n - 1)

@[simp] theorem modelIndexedCompiledLocalBundle_zero :
    modelIndexedCompiledLocalBundle (V := V) 0 =
      baseCompiledLocalBundle := by
  simp [modelIndexedCompiledLocalBundle]

/-- The successor value is literally the bundle for the successor built over
orbit member `n`, including at nonstandard `n`. -/
@[simp] theorem modelIndexedCompiledLocalBundle_succ (n : V) :
    modelIndexedCompiledLocalBundle (n + 1) =
      orbitCompiledLocalBundle n := by
  simp [modelIndexedCompiledLocalBundle]

/-- The exact local-stage implication needed when constructing certificate
level `n + 1` from an arbitrary previous certificate context. -/
noncomputable def proveModelIndexedCompiledLocalBundleSuccFrom
    (context : Bootstrapping.Formula V ℒₒᵣ) (n : V) :
    Peano.internalize V ⊢!
      context 🡒 modelIndexedCompiledLocalBundle (n + 1) := by
  simpa only [modelIndexedCompiledLocalBundle_succ] using
    proveOrbitCompiledLocalBundleFrom context n

/-! ## The represented raw-code function -/

/-- Raw code of the total model-indexed local bundle. -/
noncomputable def modelIndexedCompiledLocalBundleCode (n : V) : V :=
  (modelIndexedCompiledLocalBundle n).val

@[simp] theorem modelIndexedCompiledLocalBundleCode_zero :
    modelIndexedCompiledLocalBundleCode (V := V) 0 =
      (baseCompiledLocalBundle (V := V)).val := by
  simp [modelIndexedCompiledLocalBundleCode]

@[simp] theorem modelIndexedCompiledLocalBundleCode_succ (n : V) :
    modelIndexedCompiledLocalBundleCode (n + 1) =
      (orbitCompiledLocalBundle n).val := by
  simp [modelIndexedCompiledLocalBundleCode]

/-- The complete local-field code has a Sigma-one graph. -/
theorem modelIndexedCompiledLocalBundleCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedCompiledLocalBundleCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitCompiledLocalBundle n).val) :=
    orbitCompiledLocalBundleCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitCompiledLocalBundle (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦ (orbitCompiledLocalBundle n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitCompiledLocalBundle (n - 1)).val) := hpositive
  have hgraphFor (baseCode : V) (positiveCode : V → V)
      [HierarchySymbol.sigmaOne.DefinableFunction₁ positiveCode] :
      HierarchySymbol.sigmaOne.Definable
        (fun v : Fin 2 → V ↦
          (v 1 = 0 ∧ v 0 = baseCode) ∨
          (v 1 ≠ 0 ∧ v 0 = positiveCode (v 1))) := by
    definability
  have hgraph :=
    hgraphFor
      (baseCompiledLocalBundle (V := V)).val
      (fun n : V ↦ (orbitCompiledLocalBundle (n - 1)).val)
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedCompiledLocalBundleCode,
      modelIndexedCompiledLocalBundle, hn]
  · simp [modelIndexedCompiledLocalBundleCode,
      modelIndexedCompiledLocalBundle, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalOrbit
