import BoundedPAConsistency.DynamicTruthCompiledLocalOrbit
import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor

/-!
# The complete currently proved local dynamic-truth bundle

The original model-indexed local field contained three certificate
eliminators.  Cross-level structural induction also needs the positive
quantifier-free constructor: without it, an arbitrary current predicate can
agree with its predecessor on the previous oriented domain while disagreeing
at new quantifier-free leaves.

`DynamicTruthQuantifierFreeAnchor` proves that constructor independently.
This module adjoins it to the genuine base and every positive orbit member,
provides the corresponding typed PA proofs, and represents the total field
code.  The resulting four-law bundle is the local coordinate that should be
used by the production certificate family.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Genuine base field -/

/-- The quantifier-free introduction law for the first positive truth
predicate `truthFormula 0`. -/
noncomputable def baseQuantifierFreeIntroductionFormula :
    Bootstrapping.Formula V ℒₒᵣ :=
  quantifierFreeIntroductionFormula baseTruthFormula 0 1

/-- The base law is a fixed source theorem specialized at quantifier-free
truth; it is therefore an actual typed internal PA derivation. -/
noncomputable def baseQuantifierFreeIntroductionProof :
    Peano.internalize V ⊢! baseQuantifierFreeIntroductionFormula :=
  compiledQuantifierFreeIntroductionProof baseTruthFormula 0 1
    (Semiformula.ext (baseTruthFormula_shift (V := V)))

/-- The four local laws stored at certificate index zero. -/
noncomputable def baseAugmentedLocalBundle :
    Bootstrapping.Formula V ℒₒᵣ :=
  baseCompiledLocalBundle ⋏ baseQuantifierFreeIntroductionFormula

/-- Exact proof-object assembly for the genuine base bundle. -/
noncomputable def baseAugmentedLocalBundleProof :
    Peano.internalize V ⊢! baseAugmentedLocalBundle :=
  Entailment.K_intro baseCompiledLocalBundleProof
    baseQuantifierFreeIntroductionProof

set_option backward.isDefEq.respectTransparency false in
/-- The base proof's value is recognized by the public represented PA proof
predicate. -/
theorem baseAugmentedLocalBundleProof_isPAProof :
    Proof Peano (baseAugmentedLocalBundleProof (V := V)).val
      (baseAugmentedLocalBundle (V := V)).val := by
  simpa [Proof] using
    (baseAugmentedLocalBundleProof (V := V)).derivationOf

/-! ## Total model-indexed field -/

/-- Select the genuine base bundle at zero and the four-law positive bundle
over the model predecessor at every nonzero (possibly nonstandard) index. -/
noncomputable def modelIndexedAugmentedLocalBundle (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  if n = 0 then
    baseAugmentedLocalBundle
  else
    orbitCompiledLocalBundleWithQuantifierFreeIntroduction (n - 1)

@[simp] theorem modelIndexedAugmentedLocalBundle_zero :
    modelIndexedAugmentedLocalBundle (V := V) 0 =
      baseAugmentedLocalBundle := by
  simp [modelIndexedAugmentedLocalBundle]

/-- The successor field is literally the already proved augmented orbit
bundle, including at nonstandard indices. -/
@[simp] theorem modelIndexedAugmentedLocalBundle_succ (n : V) :
    modelIndexedAugmentedLocalBundle (n + 1) =
      orbitCompiledLocalBundleWithQuantifierFreeIntroduction n := by
  simp [modelIndexedAugmentedLocalBundle]

/-- The direct local stage under any preceding certificate context. -/
noncomputable def proveModelIndexedAugmentedLocalBundleSuccFrom
    (context : Bootstrapping.Formula V ℒₒᵣ) (n : V) :
    Peano.internalize V ⊢!
      context 🡒 modelIndexedAugmentedLocalBundle (n + 1) := by
  rw [modelIndexedAugmentedLocalBundle_succ]
  exact Entailment.C_of_conseq
    (orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof n)

/-! ## Represented raw-code function -/

noncomputable def modelIndexedAugmentedLocalBundleCode (n : V) : V :=
  (modelIndexedAugmentedLocalBundle n).val

@[simp] theorem modelIndexedAugmentedLocalBundleCode_zero :
    modelIndexedAugmentedLocalBundleCode (V := V) 0 =
      (baseAugmentedLocalBundle (V := V)).val := by
  simp [modelIndexedAugmentedLocalBundleCode]

@[simp] theorem modelIndexedAugmentedLocalBundleCode_succ (n : V) :
    modelIndexedAugmentedLocalBundleCode (n + 1) =
      (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n).val := by
  simp [modelIndexedAugmentedLocalBundleCode]

set_option maxHeartbeats 800000 in
/-- The complete four-law local field has a Sigma-one graph.  The branch
selection is represented by a zero test and model predecessor, while the
positive bundle graph was proved with the quantifier-free anchor. -/
theorem modelIndexedAugmentedLocalBundleCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (modelIndexedAugmentedLocalBundleCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n).val) :=
    orbitCompiledLocalBundleWithQuantifierFreeIntroductionCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction
          (n - 1)).val) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := fun n : V ↦
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n).val)
        hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction
          (n - 1)).val) := hpositive
  have hgraph : HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧
          v 0 = (baseAugmentedLocalBundle (V := V)).val) ∨
        (v 1 ≠ 0 ∧
          v 0 =
            (orbitCompiledLocalBundleWithQuantifierFreeIntroduction
              (v 1 - 1)).val)) := by
    definability
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [modelIndexedAugmentedLocalBundleCode,
      modelIndexedAugmentedLocalBundle, hn]
  · simp [modelIndexedAugmentedLocalBundleCode,
      modelIndexedAugmentedLocalBundle, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit
