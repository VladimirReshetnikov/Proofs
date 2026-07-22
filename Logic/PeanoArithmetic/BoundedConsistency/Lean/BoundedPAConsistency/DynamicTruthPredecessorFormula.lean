import BoundedPAConsistency.DynamicTruthOrbit

/-!
# The uniform predecessor of the represented truth orbit

The represented orbit starts at `truthFormula 0`, which is already one
successor layer above quantifier-free truth.  Structural arguments about an
arbitrary orbit index `n` nevertheless need the lower formula from which
`truthFormula n` was constructed.  At zero this lower formula is
`baseTruthFormula`; at a positive, possibly nonstandard, index it is the
preceding member of the represented orbit.

This file packages that zero/successor splice as a typed formula, proves the
exact reconstruction equation for the dynamic successor constructor, and
shows that its raw code is still Sigma-one definable.  The definition uses
model subtraction only in the nonzero branch, so it does not identify the
quantifier-free base with `truthFormula 0`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Typed predecessor formula -/

/-- The lower truth predicate used to construct the orbit member at `n`.

At zero it is quantifier-free truth.  Away from zero, `n - 1` is the genuine
model predecessor because Robinson arithmetic proves that every nonzero
element is a successor. -/
noncomputable def predecessorTruthFormula (n : V) :
    Semiformula V ℒₒᵣ 3 :=
  if n = 0 then
    baseTruthFormula
  else
    truthFormula (n - 1)

/-- The predecessor at the first represented orbit member is the named
quantifier-free truth formula. -/
@[simp] theorem predecessorTruthFormula_zero :
    predecessorTruthFormula (V := V) 0 = baseTruthFormula := by
  simp [predecessorTruthFormula]

/-- At a successor index, including a nonstandard one, the uniform
predecessor is exactly the preceding represented orbit member. -/
@[simp] theorem predecessorTruthFormula_succ (n : V) :
    predecessorTruthFormula (n + 1) = truthFormula n := by
  simp [predecessorTruthFormula]

/-- Every uniform predecessor is closed under the coded free-variable
shift.  This is the typed form needed by source-formula translation. -/
@[simp] theorem predecessorTruthFormula_shift (n : V) :
    (predecessorTruthFormula n).shift = predecessorTruthFormula n := by
  by_cases hn : n = 0
  · subst n
    rw [predecessorTruthFormula_zero]
    apply Semiformula.ext
    exact baseTruthFormula_shift (V := V)
  · simp only [predecessorTruthFormula, hn, if_false]
    exact truthFormula_shift (n - 1)

/-- Raw-code form of `predecessorTruthFormula_shift`, used by proof-code
constructors whose interfaces are stated directly with `shift`. -/
@[simp] theorem predecessorTruthFormula_val_shift (n : V) :
    shift ℒₒᵣ (predecessorTruthFormula n).val =
      (predecessorTruthFormula n).val := by
  exact congrArg Semiformula.val (predecessorTruthFormula_shift n)

/-- Applying one dynamic successor layer to the uniform predecessor
reconstructs the orbit member at the same index.

The levels are deliberately `n` and `n + 1`: at `n = 0` this is the first
positive truth formula, while at `n = k + 1` it is exactly the successor
equation for `truthFormula k`. -/
@[simp] theorem successorTruthFormula_predecessor_eq (n : V) :
    successorTruthFormula (predecessorTruthFormula n) n (n + 1) =
      truthFormula n := by
  rcases zero_or_succ n with rfl | ⟨k, rfl⟩
  · simp [levelZeroTruthFormula]
  · simp

/-! ## Represented raw-code function -/

/-- Raw code of the uniform predecessor formula. -/
noncomputable def predecessorTruthFormulaCode (n : V) : V :=
  (predecessorTruthFormula n).val

@[simp] theorem predecessorTruthFormula_val (n : V) :
    (predecessorTruthFormula n).val = predecessorTruthFormulaCode n := rfl

@[simp] theorem predecessorTruthFormulaCode_zero :
    predecessorTruthFormulaCode (V := V) 0 =
      (baseTruthFormula (V := V)).val := by
  simp [predecessorTruthFormulaCode]

@[simp] theorem predecessorTruthFormulaCode_succ (n : V) :
    predecessorTruthFormulaCode (n + 1) = truthFormulaCode n := by
  simp [predecessorTruthFormulaCode]

/-- The raw predecessor-code function has a Sigma-one graph over every
model of `I Sigma 1`.

The graph exposes the zero and nonzero branches.  The positive branch is the
composition of represented predecessor with the already represented truth
orbit, so no decoding of a possibly nonstandard formula code occurs. -/
theorem predecessorTruthFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (predecessorTruthFormulaCode (V := V)) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (truthFormulaCode (V := V)) := truthFormulaCode_definable
  have hpositive : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ truthFormulaCode (n - 1)) := by
    have hpred : HierarchySymbol.sigmaOne.DefinableFunction
        (fun v : Fin 1 → V ↦ v 0 - 1) := by
      definability
    simpa using
      (HierarchySymbol.DefinableFunction₁.comp
        (F := truthFormulaCode (V := V)) hpred)
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ truthFormulaCode (n - 1)) := hpositive
  have hgraph : HierarchySymbol.sigmaOne.Definable
      (fun v : Fin 2 → V ↦
        (v 1 = 0 ∧ v 0 = (baseTruthFormula (V := V)).val) ∨
        (v 1 ≠ 0 ∧ v 0 = truthFormulaCode (v 1 - 1))) := by
    definability
  apply hgraph.of_iff
  intro v
  by_cases hn : v 1 = 0
  · simp [predecessorTruthFormulaCode, predecessorTruthFormula, hn]
  · simp [predecessorTruthFormulaCode, predecessorTruthFormula,
      truthFormula_val, hn]

end LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula
