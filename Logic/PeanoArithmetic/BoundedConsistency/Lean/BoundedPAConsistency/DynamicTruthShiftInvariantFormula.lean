import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula
import BoundedPAConsistency.TermEvaluationTransport

/-!
# The model-coded shift-invariance field

The truth certificate used by the uniform bounded-consistency construction
needs a syntactic field expressing invariance under free-variable shift.  A
meta-level occurrence of `shift p` would not suffice here: at a nonstandard
stage, `p` is merely a formula code in an arbitrary model.  We therefore use
the represented graph `shiftGraph` and expose the shifted code by an
existential witness.

The source formula lives in the fixed language with one ternary predicate
placeholder and two named hierarchy levels.  Its specialization theorem is
literal syntactic equality for arbitrary model-coded lower syntax and
arbitrary (possibly nonstandard) model levels.  This file only fixes and
represents the certificate field; it deliberately does not claim that the
full PA induction kernel proving the field has already been constructed.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

/-! ## A stable arithmetic name for the semantic free-tail relation -/

/-- Arithmetic syntax for `IsFreeTail shifted free`.

The two `znth` graphs are written universally rather than by choosing their
values existentially.  Since `znthDef` represents a total function, the
formula says exactly that lookup at `x + 1` in `shifted` equals lookup at `x`
in `free`.  This presentation is Pi-one and, unlike an anonymous
`DefinableRel` witness, is stable syntax that may be quoted by the certificate
compiler. -/
noncomputable def isFreeTailDef : HierarchySymbol.piOne.Semisentence 2 :=
  .mkPi
    “shifted free.
      ∀ x, ∀ shiftedValue, !znthDef shiftedValue shifted (x + 1) →
        ∀ freeValue, !znthDef freeValue free x →
          shiftedValue = freeValue”

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The displayed formula really defines the semantic free-tail relation in
every model of `IΣ1`. -/
instance isFreeTail_defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.piOne
      IsFreeTail isFreeTailDef := .mk fun v ↦ by
  simp [isFreeTailDef, IsFreeTail]

@[simp] theorem eval_isFreeTailDef (v : Fin 2 → V) :
    isFreeTailDef.val.Evalb v ↔ IsFreeTail (v 0) (v 1) :=
  isFreeTail_defined.iff

/-! ## Fixed source syntax -/

/-- The free-environment tail premise in a four-variable context ordered as
`(bound, shifted, free, formula)`. -/
noncomputable def sourceFreeTail : Semisentence SourceLanguage 4 :=
  apply₂ (liftArithmeticFormula isFreeTailDef.val) (#1) (#2)

/-- The formula code lies in the hierarchy fragment one level below the
successor predicate. -/
noncomputable def sourceBoundedDomain : Semisentence SourceLanguage 4 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (parameterTerm 0) (#3)

/-- A represented shifted code together with the desired truth equivalence.

Under the existential binder, the witness is `#0`, while the four outer
variables become `#1` through `#4`.  In particular `shiftGraph #0 #4`
asserts that the witness is the coded shift of the original formula `#4`.
-/
noncomputable def sourceShiftedTruthWitness :
    Semisentence SourceLanguage 4 :=
  ∃⁰
    (apply₂ (liftArithmeticFormula (shiftGraph ℒₒᵣ)) (#0) (#4) ⋏
      LogicalConnective.iff
        (apply₃ successorTruthFormula (#1) (#2) (#0))
        (apply₃ successorTruthFormula (#1) (#3) (#4)))

/-- Shift invariance at fixed `(bound, shifted, free, formula)`. -/
noncomputable def sourceShiftInvariantBody :
    Semisentence SourceLanguage 4 :=
  Arrow.arrow (sourceFreeTail ⋏ sourceBoundedDomain)
    sourceShiftedTruthWitness

/-- Unary induction predicate: only the formula code remains free. -/
noncomputable def sourceShiftInvariantPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ ∀⁰ sourceShiftInvariantBody

/-- Universally closed shift-invariance certificate field. -/
noncomputable def sourceShiftInvariantSentence : Sentence SourceLanguage :=
  ∀⁰ sourceShiftInvariantPredicate

/-! ## Typed model-coded syntax -/

/-- Apply the named free-tail relation in the four-variable certificate
context. -/
noncomputable def freeTailFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 4 :=
  (⌜isFreeTailDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Semiterm.bvar (1 : Fin 4), Semiterm.bvar (2 : Fin 4)]

/-- Apply the named bounded-code relation at a model-coded lower level. -/
noncomputable def boundedDomainFormula (lowerLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 4 :=
  (⌜(quantifierBoundedCodeDef ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral lowerLevel,
      Semiterm.bvar (3 : Fin 4)]

/-- Typed represented-shift witness for an arbitrary model-coded upper truth
predicate. -/
noncomputable def shiftedTruthWitnessFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 4 :=
  ∃⁰
    (((⌜(shiftGraph ℒₒᵣ).val⌝ :
          Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Semiterm.bvar (0 : Fin 5), Semiterm.bvar (4 : Fin 5)]) ⋏
      LogicalConnective.iff
        (DynamicTruthFormula.apply₃ upper
            (Semiterm.bvar (1 : Fin 5))
            (Semiterm.bvar (2 : Fin 5))
            (Semiterm.bvar (0 : Fin 5)))
        (DynamicTruthFormula.apply₃ upper
            (Semiterm.bvar (1 : Fin 5))
            (Semiterm.bvar (3 : Fin 5))
            (Semiterm.bvar (4 : Fin 5))))

/-- Typed body of the shift-invariance law for one successor constructor. -/
noncomputable def shiftInvariantBodyFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 4 :=
  Arrow.arrow (freeTailFormula ⋏ boundedDomainFormula lowerLevel)
    (shiftedTruthWitnessFormula
      (DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel))

/-- Unary predicate intended for the later PA induction kernel. -/
noncomputable def shiftInvariantPredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ ∀⁰ ∀⁰
    shiftInvariantBodyFormula lower lowerLevel upperLevel

/-- Universally closed concrete shift-invariance certificate field. -/
noncomputable def shiftInvariantFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ shiftInvariantPredicateFormula lower lowerLevel upperLevel

/-! ## Exact source specialization -/

@[simp] theorem translate_sourceFreeTail
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceFreeTail) =
      freeTailFormula := by
  simp [sourceFreeTail, freeTailFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceBoundedDomain
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceBoundedDomain) =
      boundedDomainFormula lowerLevel := by
  simp [sourceBoundedDomain, boundedDomainFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceShiftedTruthWitness
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceShiftedTruthWitness) =
      shiftedTruthWitnessFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel) := by
  simp [sourceShiftedTruthWitness, shiftedTruthWitnessFormula,
    LogicalConnective.iff,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.apply₃]
  constructor
  · let sourceLeft : Semisentence SourceLanguage 5 :=
      apply₃ successorTruthFormula (#1) (#2) (#0)
    let typedLeft : Bootstrapping.Semiformula V ℒₒᵣ 5 :=
      DynamicTruthFormula.apply₃
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        (Semiterm.bvar (1 : Fin 5))
        (Semiterm.bvar (2 : Fin 5))
        (Semiterm.bvar (0 : Fin 5))
    have hneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourceLeft)) =
          ∼typedLeft := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourceLeft) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourceLeft))
        _ = _ := congrArg (∼·) (by
          simp [sourceLeft, typedLeft,
            ModelCodedPredicateParameters.translateTerm,
            DynamicTruthFormula.apply₃])
    rw [show
      translateFormula lower ![lowerLevel, upperLevel]
          (Semiformula.neg
            (Rewriting.emb
              (apply₃ successorTruthFormula (#1) (#2) (#0)))) =
        ∼typedLeft by simpa [sourceLeft] using hneg]
    simp [typedLeft, DynamicTruthFormula.apply₃,
      Bootstrapping.Semiformula.imp_def]
  · let sourceRight : Semisentence SourceLanguage 5 :=
      apply₃ successorTruthFormula (#1) (#3) (#4)
    let typedRight : Bootstrapping.Semiformula V ℒₒᵣ 5 :=
      DynamicTruthFormula.apply₃
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        (Semiterm.bvar (1 : Fin 5))
        (Semiterm.bvar (3 : Fin 5))
        (Semiterm.bvar (4 : Fin 5))
    have hneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourceRight)) =
          ∼typedRight := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourceRight) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourceRight))
        _ = _ := congrArg (∼·) (by
          simp [sourceRight, typedRight,
            ModelCodedPredicateParameters.translateTerm,
            DynamicTruthFormula.apply₃])
    rw [show
      translateFormula lower ![lowerLevel, upperLevel]
          (Semiformula.neg
            (Rewriting.emb
              (apply₃ successorTruthFormula (#1) (#3) (#4)))) =
        ∼typedRight by simpa [sourceRight] using hneg]
    simp [typedRight, DynamicTruthFormula.apply₃,
      Bootstrapping.Semiformula.imp_def]

@[simp] theorem translate_sourceShiftInvariantBody
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceShiftInvariantBody) =
      shiftInvariantBodyFormula lower lowerLevel upperLevel := by
  simp [sourceShiftInvariantBody, shiftInvariantBodyFormula,
    Bootstrapping.Semiformula.imp_def,
    ModelCodedPredicateParameters.translateFormula]

@[simp] theorem translate_sourceShiftInvariantPredicate
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceShiftInvariantPredicate) =
      shiftInvariantPredicateFormula lower lowerLevel upperLevel := by
  simp [sourceShiftInvariantPredicate, shiftInvariantPredicateFormula,
    ModelCodedPredicateParameters.translateFormula]

/-- Arbitrary model-coded specialization of the fixed source sentence is
literally the advertised shift-invariance field. -/
@[simp] theorem translate_sourceShiftInvariantSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceShiftInvariantSentence) =
      shiftInvariantFormula lower lowerLevel upperLevel := by
  simp [sourceShiftInvariantSentence, shiftInvariantFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! ## The represented orbit instances -/

/-- The same field constructor when its upper truth predicate is supplied
directly.  This small view makes the orbit equalities below state the actual
member `truthFormula k`, rather than merely the successor expression from
which that member was built. -/
noncomputable def upperShiftInvariantFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (boundedLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰
    (Arrow.arrow (freeTailFormula ⋏ boundedDomainFormula boundedLevel)
      (shiftedTruthWitnessFormula upper))

/-- Base field for `truthFormula 0 = levelZeroTruthFormula`: formulas with
quantifier-group bound zero are evaluated by the first positive truth
predicate. -/
noncomputable def baseShiftInvariantFormula :
    Bootstrapping.Formula V ℒₒᵣ :=
  shiftInvariantFormula baseTruthFormula 0 1

/-- The base field's upper predicate is literally the zeroth member of the
represented positive orbit. -/
theorem baseShiftInvariantFormula_eq_upper :
    baseShiftInvariantFormula (V := V) =
      upperShiftInvariantFormula (truthFormula 0) 0 := by
  simp [baseShiftInvariantFormula, upperShiftInvariantFormula,
    shiftInvariantFormula, shiftInvariantPredicateFormula,
    shiftInvariantBodyFormula, truthFormula_zero,
    DynamicTruthFormula.levelZeroTruthFormula]

/-- Positive successor field.  The successor over `truthFormula n` is
`truthFormula (n + 1)` and handles formula codes bounded at `n + 1`. -/
noncomputable def orbitSuccessorShiftInvariantFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  shiftInvariantFormula (truthFormula n) (n + 1) (n + 1 + 1)

/-- Expose the exact upper predicate used by the positive branch. -/
theorem orbitSuccessorShiftInvariantFormula_upper (n : V) :
    orbitSuccessorShiftInvariantFormula n =
      upperShiftInvariantFormula (truthFormula (n + 1)) (n + 1) := by
  simp [orbitSuccessorShiftInvariantFormula, upperShiftInvariantFormula,
    shiftInvariantFormula, shiftInvariantPredicateFormula,
    shiftInvariantBodyFormula, truthFormula_succ]

/-! ## Representability of the positive-branch code -/

/-- The raw code of the positive shift field is Sigma-one definable as a
function of its possibly nonstandard predecessor index.

All displayed logical and substitution operations are represented syntax
constructors.  The sole recursively varying input is `truthFormulaCode`,
whose graph was established in `DynamicTruthOrbit`. -/
theorem orbitSuccessorShiftInvariantFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorShiftInvariantFormula n).val) := by
  simp only [orbitSuccessorShiftInvariantFormula, shiftInvariantFormula,
    shiftInvariantPredicateFormula, shiftInvariantBodyFormula,
    shiftedTruthWitnessFormula, freeTailFormula, boundedDomainFormula,
    DynamicTruthFormula.apply₃_val,
    Semiformula.val_all, Semiformula.val_imp, Semiformula.val_and,
    Semiformula.val_exs, Semiformula.val_iff,
    Bootstrapping.Semiformula.val_substs]
  definability

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
