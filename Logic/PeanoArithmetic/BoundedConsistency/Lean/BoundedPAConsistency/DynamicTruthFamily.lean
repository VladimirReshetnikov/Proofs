import BoundedPAConsistency.DynamicTruthFormula

/-!
# The standard orbit of the dynamic truth-formula successor

`DynamicTruthFormula.successorTruthFormula` accepts a formula code from an
arbitrary arithmetic model.  That is the operation needed at nonstandard
levels.  Before constructing its represented, model-indexed orbit, it is
useful to record the ordinary `Nat`-indexed orbit and verify that it agrees
exactly with the existing externally indexed partial-truth predicates.

This module deliberately does **not** manufacture a
`PATruthCertificateFamily`.  Such a family is indexed by an arbitrary model
element `n : V`, whereas recursion below is metatheoretic recursion on
`n : Nat`.  Conflating the two would lose precisely the nonstandard cases
needed by the uniform theorem.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthFamily

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Ordinary syntax and its typed quotation -/

/-- The standard formula at external truth level `n`.

Level zero is quantifier-free truth.  A successor stores one HFS certificate
layer and uses the immediately preceding formula for its opposite-polarity
universal leaves. -/
noncomputable def standardDynamicTruthSyntax :
    ℕ → ArithmeticSemisentence 3
  | 0 => qfTruthDef.val
  | n + 1 =>
      standardSuccessorTruthFormula (standardDynamicTruthSyntax n) n (n + 1)

/-- The same standard orbit, assembled directly with typed model-coded
constructors.  Its definition is useful because the successor case remains
meaningful for arbitrary model-coded lower formulas. -/
noncomputable def standardDynamicTruthFormula :
    ℕ → Semiformula V ℒₒᵣ 3
  | 0 => baseTruthFormula
  | n + 1 =>
      successorTruthFormula (standardDynamicTruthFormula n)
        (ORingStructure.numeral n) (ORingStructure.numeral (n + 1))

/-- At every standard level, direct typed assembly is exactly quotation of
the corresponding ordinary arithmetic syntax. -/
@[simp] theorem standardDynamicTruthFormula_eq_typedQuote (n : ℕ) :
    standardDynamicTruthFormula (V := V) n =
      (⌜(standardDynamicTruthSyntax n)⌝ : Semiformula V ℒₒᵣ 3) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [standardDynamicTruthFormula, standardDynamicTruthSyntax, ih]
      symm
      exact typedQuote_standardSuccessorTruthFormula
        (standardDynamicTruthSyntax n) n (n + 1)

/-- Raw-code version of the quotation theorem. -/
@[simp] theorem standardDynamicTruthFormula_val_eq_quote (n : ℕ) :
    (standardDynamicTruthFormula (V := V) n).val =
      (⌜(standardDynamicTruthSyntax n)⌝ : V) := by
  rw [standardDynamicTruthFormula_eq_typedQuote]
  rfl

/-- Every standard member of the orbit is closed under the coded free-
variable shift.  The induction uses the same preservation theorem that is
available for a genuinely nonstandard lower formula. -/
@[simp] theorem standardDynamicTruthFormula_shift (n : ℕ) :
    shift ℒₒᵣ (standardDynamicTruthFormula (V := V) n).val =
      (standardDynamicTruthFormula (V := V) n).val := by
  induction n with
  | zero => exact baseTruthFormula_shift
  | succ n ih =>
      exact successorTruthFormula_val_shift_of_lower
        (standardDynamicTruthFormula n)
        (ORingStructure.numeral n) (ORingStructure.numeral (n + 1)) ih

/-! ## Semantic identification -/

/-- One standard successor formula has exactly the certificate semantics
used by `SigmaTrue` at the next external level. -/
@[simp] theorem eval_standardSuccessorTruthFormula_iff
    (lower : ArithmeticSemisentence 3) (lowerLevel upperLevel : ℕ)
    (v : Fin 3 → V) :
    (standardSuccessorTruthFormula lower lowerLevel upperLevel).Evalb
        (M := V) v ↔
      ∃ C,
        HasTruthState C (v 0) (v 1) (v 2) ∧
        ∀ r ∈ C,
          SigmaRecordValid
            (fun bound free p ↦ lower.Evalb (M := V) ![bound, free, p])
            (ORingStructure.numeral lowerLevel)
            (ORingStructure.numeral upperLevel) C r := by
  simp [standardSuccessorTruthFormula, standardApply₂]

/-- The standard dynamic orbit represents the externally indexed truth
predicate at the matching level, including on nonstandard formula codes and
nonstandard environments in `V`. -/
@[simp] theorem eval_standardDynamicTruthSyntax_iff
    (n : ℕ) (v : Fin 3 → V) :
    (standardDynamicTruthSyntax n).Evalb (M := V) v ↔
      SigmaTrue n (v 0) (v 1) (v 2) := by
  induction n generalizing v with
  | zero =>
      simp [standardDynamicTruthSyntax, qfTruthDef, QFTrue,
        IsQuantifierFreeCode]
  | succ n ih =>
      simp only [standardDynamicTruthSyntax,
        eval_standardSuccessorTruthFormula_iff, sigmaTrue_succ]
      have hlower :
          (fun bound free p ↦
            (standardDynamicTruthSyntax n).Evalb
              (M := V) ![bound, free, p]) =
            SigmaTrue n := by
        funext bound free p
        exact propext (ih ![bound, free, p])
      rw [hlower]

/-! ## The bounded-consistency indexing convention -/

/-- The truth formula used to prove consistency at quantifier-group bound
`n` has one spare positive level, namely `SigmaTrue (n + 1)`. -/
noncomputable def standardBoundedTruthFormula (n : ℕ) :
    Semiformula V ℒₒᵣ 3 :=
  standardDynamicTruthFormula (n + 1)

@[simp] theorem standardBoundedTruthFormula_zero :
    standardBoundedTruthFormula (V := V) 0 = levelZeroTruthFormula := by
  rfl

@[simp] theorem eval_standardBoundedTruthSyntax_iff
    (n : ℕ) (v : Fin 3 → V) :
    (standardDynamicTruthSyntax (n + 1)).Evalb (M := V) v ↔
      SigmaTrue (n + 1) (v 0) (v 1) (v 2) :=
  eval_standardDynamicTruthSyntax_iff n.succ v

end LeanProofs.BoundedPAConsistency.DynamicTruthFamily
