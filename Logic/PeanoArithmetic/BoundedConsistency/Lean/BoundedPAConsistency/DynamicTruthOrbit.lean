import BoundedPAConsistency.DynamicTruthFormula
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# A represented orbit of model-coded partial-truth formulae

`DynamicTruthFormula` constructs one successor formula from an arbitrary
model-coded ternary formula.  This file iterates that operation *inside every
model of* `I Sigma 1`, using Foundation's `PR.Construction`.  Consequently the
construction exists at arbitrary, possibly nonstandard, model indices.

Large fixed syntax codes are supplied as formal parameters of the primitive
recursion.  This is mathematically the usual primitive-recursive construction
with constants, and avoids expanding those codes into enormous ordinary PA
numerals.  The blueprint itself remains one fixed, parameter-free Sigma-one
formula.

The indexing is the one required by bounded consistency:

* `truthFormulaCode 0` is the first positive truth predicate, obtained from
  quantifier-free truth;
* `truthFormulaCode (n + 1)` applies a further successor layer with lower
  level `n + 1` and upper level `n + 2`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthOrbit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## A small successor program with formal constant parameters -/

/-- Number of fixed syntax values carried by the represented recursion. -/
abbrev parameterArity : ℕ := 10

/-- The successor code operation before its formal constants are
specialized.

The parameter order is:

1. the base truth-formula code (unused by the successor);
2. the vector `[^#4, ^#3, ^#0]`;
3. the universal-record-prefix formula code;
4. the codes `^#0` and `^#1`;
5. the record-domain and positive-record-branch formula codes;
6. the vector `[^#1, ^#0]`;
7. the already-substituted HFS-membership application;
8. the truth-state formula code.
-/
noncomputable def successorCodeWithParameters
    (params : Fin parameterArity → V) (index previous : V) : V :=
  let universalBranch :=
    ^∃ ^∃ ^∃ ^∃ ^∃
      (params 2 ^⋏ neg ℒₒᵣ (subst ℒₒᵣ (params 1) previous))
  let recordValid :=
    subst ℒₒᵣ
        (Bootstrapping.Arithmetic.numeral (index + 1 + 1) ∷
          params 3 ∷ params 4 ∷ 0)
        (params 5) ^⋏
      (params 6 ^⋎
        subst ℒₒᵣ
          (Bootstrapping.Arithmetic.numeral (index + 1) ∷
            params 3 ∷ params 4 ∷ 0)
          universalBranch)
  ^∃
    (params 9 ^⋏
      ^∀ (imp ℒₒᵣ (params 8)
        (subst ℒₒᵣ (params 7) recordValid)))

/-- Fixed Sigma-one graph for the base function.  Its ten apparent constants
are variables of the blueprint, not parameters of the formula syntax. -/
noncomputable def truthFormulaZeroDef :
    HierarchySymbol.sigmaOne.Semisentence (parameterArity + 1) := .mkSigma
  “y base lowerVector prefixCode bvar0 bvar1 domain positive validVector member state.
    y = base”

/-- Fixed Sigma-one graph of one successor program.

`PR.Construction` orders these variables as `(output, previous, index,
parameters...)`.  Every intermediate syntax node is exposed through the
corresponding represented graph. -/
noncomputable def truthFormulaSuccDef :
    HierarchySymbol.sigmaOne.Semisentence (parameterArity + 3) := .mkSigma
  “y previous index base lowerVector prefixCode bvar0 bvar1 domain positive
      validVector member state.
    ∃ lowerSubst,
      !(substsGraph ℒₒᵣ) lowerSubst lowerVector previous ∧
    ∃ negLowerSubst, !(negGraph ℒₒᵣ) negLowerSubst lowerSubst ∧
    ∃ universalAnd, !qqAndDef universalAnd prefixCode negLowerSubst ∧
    ∃ universalEx1, !qqExsDef universalEx1 universalAnd ∧
    ∃ universalEx2, !qqExsDef universalEx2 universalEx1 ∧
    ∃ universalEx3, !qqExsDef universalEx3 universalEx2 ∧
    ∃ universalEx4, !qqExsDef universalEx4 universalEx3 ∧
    ∃ universalBranch, !qqExsDef universalBranch universalEx4 ∧

    ∃ upperNumeral,
      !Bootstrapping.Arithmetic.numeralGraph upperNumeral (index + 1 + 1) ∧
    ∃ upperTail1, !adjoinDef upperTail1 bvar1 0 ∧
    ∃ upperTail2, !adjoinDef upperTail2 bvar0 upperTail1 ∧
    ∃ upperVector, !adjoinDef upperVector upperNumeral upperTail2 ∧
    ∃ domainApplication,
      !(substsGraph ℒₒᵣ) domainApplication upperVector domain ∧

    ∃ lowerNumeral,
      !Bootstrapping.Arithmetic.numeralGraph lowerNumeral (index + 1) ∧
    ∃ lowerTail1, !adjoinDef lowerTail1 bvar1 0 ∧
    ∃ lowerTail2, !adjoinDef lowerTail2 bvar0 lowerTail1 ∧
    ∃ lowerApplicationVector,
      !adjoinDef lowerApplicationVector lowerNumeral lowerTail2 ∧
    ∃ universalApplication,
      !(substsGraph ℒₒᵣ) universalApplication
        lowerApplicationVector universalBranch ∧
    ∃ recordBranches,
      !qqOrDef recordBranches positive universalApplication ∧
    ∃ recordValid,
      !qqAndDef recordValid domainApplication recordBranches ∧

    ∃ validApplication,
      !(substsGraph ℒₒᵣ) validApplication validVector recordValid ∧
    ∃ implication,
      !(impGraph ℒₒᵣ) implication member validApplication ∧
    ∃ universalCheck, !qqAllDef universalCheck implication ∧
    ∃ truthBody, !qqAndDef truthBody state universalCheck ∧
    !qqExsDef y truthBody”

/-- The fixed primitive-recursion blueprint. -/
noncomputable def blueprint : PR.Blueprint parameterArity where
  zero := truthFormulaZeroDef
  succ := truthFormulaSuccDef

/-- A represented construction for the parameterized successor program. -/
noncomputable def construction : PR.Construction V blueprint where
  zero params := params 0
  succ params index previous :=
    successorCodeWithParameters params index previous
  zero_defined := .mk fun v ↦ by
    simp [blueprint, truthFormulaZeroDef]
  succ_defined := .mk fun v ↦ by
    simp [blueprint, truthFormulaSuccDef, successorCodeWithParameters,
      parameterArity]

/-! ## Canonical specialization -/

/-- The ten concrete values used by the dynamic truth hierarchy. -/
noncomputable def truthFormulaParameters : Fin parameterArity → V :=
  ![(levelZeroTruthFormula (V := V)).val,
    (?[(^#4 : V), (^#3 : V), (^#0 : V)] : V),
    (⌜universalRecordPrefixDef.val⌝ : V),
    (^#0 : V),
    (^#1 : V),
    (⌜recordDomainDef.val⌝ : V),
    (⌜positiveRecordBranchesDef.val⌝ : V),
    (?[(^#1 : V), (^#0 : V)] : V),
    subst ℒₒᵣ (?[(^#0 : V), (^#1 : V)] : V) (⌜hfsMemDef.val⌝ : V),
    (⌜hasTruthStateDef.val⌝ : V)]

/-- Specializing the formal constants recovers exactly the successor
constructor from `DynamicTruthFormula`. -/
theorem successorCodeWithParameters_eq
    (index previous : V) :
    successorCodeWithParameters truthFormulaParameters index previous =
      successorTruthFormulaCode previous (index + 1) (index + 1 + 1) := by
  simp [successorCodeWithParameters, truthFormulaParameters,
    successorTruthFormulaCode, successorRecordValidCode,
    universalRecordBranchCode]

/-- Code of the truth formula at an arbitrary model index. -/
noncomputable def truthFormulaCode (n : V) : V :=
  construction.result truthFormulaParameters n

@[simp] theorem truthFormulaCode_zero :
    truthFormulaCode (V := V) 0 =
      (levelZeroTruthFormula (V := V)).val := by
  simp [truthFormulaCode, construction, truthFormulaParameters,
    parameterArity]

@[simp] theorem truthFormulaCode_succ (n : V) :
    truthFormulaCode (n + 1) =
      successorTruthFormulaCode (truthFormulaCode n)
        (n + 1) (n + 1 + 1) := by
  rw [truthFormulaCode, PR.Construction.result_succ]
  exact successorCodeWithParameters_eq n (truthFormulaCode n)

/-- The generic fixed Sigma-one graph of the represented computation before
its ten constants are specialized. -/
noncomputable def truthFormulaComputationGraph :
    HierarchySymbol.sigmaOne.Semisentence (parameterArity + 2) :=
  blueprint.resultDef

theorem truthFormulaComputation_defined :
    HierarchySymbol.DefinedFunction (V := V)
      (fun v ↦ construction.result (v ·.succ) (v 0))
      truthFormulaComputationGraph := by
  simpa [truthFormulaComputationGraph] using
    (construction (V := V)).result_defined

/-- After substituting the ten canonical constants, the unary orbit function
remains Sigma-one definable. -/
instance truthFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁ (V := V)
      truthFormulaCode := by
  let inputs : Fin (parameterArity + 1) → (Fin 1 → V) → V :=
    fun i ↦ Fin.cases (fun z ↦ z 0)
      (fun j _ ↦ truthFormulaParameters j) i
  have h := HierarchySymbol.DefinableFunction.substitution
    (f := inputs) (construction (V := V)).result_definable (by
      intro i
      cases i using Fin.cases with
      | zero => exact HierarchySymbol.DefinableFunction.var 0
      | succ i =>
          exact HierarchySymbol.DefinableFunction.const
            (truthFormulaParameters i))
  change HierarchySymbol.sigmaOne.DefinableFunction
    (fun z : Fin 1 → V ↦
      construction.result truthFormulaParameters (z 0))
  simpa [inputs] using h

/-! ## Syntactic invariants along the nonstandard orbit -/

/-- Every member of the represented orbit is a ternary formula code.  This
uses model-internal Sigma-one successor induction, not recursion on `Nat`. -/
theorem truthFormulaCode_isSemiformula (n : V) :
    IsSemiformula ℒₒᵣ 3 (truthFormulaCode n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [truthFormulaCode_zero]
    exact (levelZeroTruthFormula (V := V)).isSemiformula
  case succ n ih =>
    rw [truthFormulaCode_succ]
    let lower : Semiformula V ℒₒᵣ 3 :=
      ⟨truthFormulaCode n, ih⟩
    simpa [lower] using
      (successorTruthFormula_isSemiformula lower (n + 1) (n + 1 + 1))

/-- Typed view of the formula at an arbitrary model index. -/
noncomputable def truthFormula (n : V) : Semiformula V ℒₒᵣ 3 :=
  ⟨truthFormulaCode n, truthFormulaCode_isSemiformula n⟩

@[simp] theorem truthFormula_val (n : V) :
    (truthFormula n).val = truthFormulaCode n := rfl

@[simp] theorem truthFormula_zero :
    truthFormula (V := V) 0 = levelZeroTruthFormula := by
  apply Semiformula.ext
  exact truthFormulaCode_zero

@[simp] theorem truthFormula_succ (n : V) :
    truthFormula (n + 1) =
      successorTruthFormula (truthFormula n) (n + 1) (n + 1 + 1) := by
  apply Semiformula.ext
  simp

/-- Every formula in the represented orbit is shift-closed. -/
theorem truthFormulaCode_shift (n : V) :
    shift ℒₒᵣ (truthFormulaCode n) = truthFormulaCode n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    simpa using (levelZeroTruthFormula_shift (V := V))
  case succ n ih =>
    rw [truthFormulaCode_succ]
    let lower : Semiformula V ℒₒᵣ 3 := truthFormula n
    simpa [lower] using
      (successorTruthFormula_val_shift_of_lower lower
        (n + 1) (n + 1 + 1) ih)

@[simp] theorem truthFormula_shift (n : V) :
    (truthFormula n).shift = truthFormula n := by
  apply Semiformula.ext
  exact truthFormulaCode_shift n

end LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
