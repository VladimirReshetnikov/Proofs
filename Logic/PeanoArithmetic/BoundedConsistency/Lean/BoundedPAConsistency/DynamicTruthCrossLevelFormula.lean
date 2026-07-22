import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula

/-!
# The model-coded cross-level truth law

The partial-truth hierarchy needs a coherence field saying that one
successor certificate agrees with its lower predicate on the lower
hierarchy domains.  This module fixes the *syntax* of that field before the
structural-induction proof is assembled.

There are two oriented clauses.  On the Sigma domain the successor agrees
directly with the lower predicate.  On the Pi domain it agrees with the
usual dual presentation: the code is Pi and the lower predicate does not
hold of its coded negation.  The coded negation is exposed through
`negGraph`; no meta-level decoding of formula codes occurs.

The source version lives in the fixed language with one ternary predicate
placeholder and two named hierarchy levels.  The main theorem establishes
literal syntactic equality after arbitrary model-coded specialization.  It
therefore supplies a stable target for the later PA induction template.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## Fixed source syntax -/

/-- The lower Sigma-domain assertion for the formula-code variable `#2`.

The surrounding three variables are `(bound, free, formula)`, in that
de-Bruijn order. -/
noncomputable def sourceSigmaDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isSigmaCodeDef.val)
    (parameterTerm 0) (#2)

/-- The corresponding lower Pi-domain assertion. -/
noncomputable def sourcePiDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isPiCodeDef.val)
    (parameterTerm 0) (#2)

/-- Lower Pi truth, expressed using the lower Sigma predicate on the coded
negation.

Under the existential binder the outer variables become `#1`, `#2`, and
`#3`; the fresh negation code is `#0`.  Keeping the graph witness explicit
is essential for nonstandard formula codes. -/
noncomputable def sourceLowerPiTruth : Semisentence SourceLanguage 3 :=
  sourcePiDomain ⋏
    (∃⁰
      (liftArithmeticFormula
          ((negGraph ℒₒᵣ).val/[#0, #3]) ⋏
        ∼(lowerAtom (#1) (#2) (#0))))

/-- Both oriented coherence clauses for fixed `(bound, free, formula)`.

`successorTruthFormula` is the upper predicate constructed from the source
placeholder. -/
noncomputable def sourceCrossLevelBody : Semisentence SourceLanguage 3 :=
  (sourceSigmaDomain 🡒
      (successorTruthFormula 🡘 lowerAtom (#0) (#1) (#2))) ⋏
    (sourcePiDomain 🡒
      (successorTruthFormula 🡘 sourceLowerPiTruth))

/-- Unary induction predicate: the formula code remains free, while bound
and free-variable environments are universally quantified. -/
noncomputable def sourceCrossLevelPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceCrossLevelBody

/-- The complete cross-level certificate field. -/
noncomputable def sourceCrossLevelSentence : Sentence SourceLanguage :=
  ∀⁰ sourceCrossLevelPredicate

/-! ## Typed model-coded syntax -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Apply the named Sigma-domain formula at an arbitrary model level. -/
noncomputable def sigmaDomainFormula (lowerLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (⌜isSigmaCodeDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral lowerLevel,
      Semiterm.bvar (2 : Fin 3)]

/-- Apply the named Pi-domain formula at an arbitrary model level. -/
noncomputable def piDomainFormula (lowerLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (⌜isPiCodeDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral lowerLevel,
      Semiterm.bvar (2 : Fin 3)]

/-- Typed lower Pi truth with an explicit represented-negation witness. -/
noncomputable def lowerPiTruthFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel : V) : Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  piDomainFormula lowerLevel ⋏
    (∃⁰
      ((⌜((negGraph ℒₒᵣ).val/[#0, #3] :
          ArithmeticSemisentence 4)⌝ :
          Bootstrapping.Semiformula V ℒₒᵣ 4) ⋏
        ∼(DynamicTruthFormula.apply₃ lower
          (Semiterm.bvar (1 : Fin 4))
          (Semiterm.bvar (2 : Fin 4))
          (Semiterm.bvar (0 : Fin 4)))))

/-- Typed body of the two coherence clauses. -/
noncomputable def crossLevelBodyFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (sigmaDomainFormula lowerLevel 🡒
      (DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel 🡘 lower)) ⋏
    (piDomainFormula lowerLevel 🡒
      (DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel 🡘
          lowerPiTruthFormula lower lowerLevel))

/-- Unary predicate consumed by `PAInductionKernel`. -/
noncomputable def crossLevelPredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ ∀⁰ crossLevelBodyFormula lower lowerLevel upperLevel

/-- Universally closed cross-level certificate field. -/
noncomputable def crossLevelFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ crossLevelPredicateFormula lower lowerLevel upperLevel

/-! ## Exact source specialization -/

@[simp] theorem translate_sourceSigmaDomain
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSigmaDomain) =
      sigmaDomainFormula lowerLevel := by
  simp [sourceSigmaDomain, sigmaDomainFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourcePiDomain
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourcePiDomain) =
      piDomainFormula lowerLevel := by
  simp [sourcePiDomain, piDomainFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceLowerPiTruth
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceLowerPiTruth) =
      lowerPiTruthFormula lower lowerLevel := by
  simp [sourceLowerPiTruth, lowerPiTruthFormula,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourceCrossLevelBody
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCrossLevelBody) =
      crossLevelBodyFormula lower lowerLevel upperLevel := by
  simp [sourceCrossLevelBody, crossLevelBodyFormula,
    FirstOrder.Semiformula.iff_eq,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm]
  constructor
  · have hsneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourceSigmaDomain)) =
          ∼(sigmaDomainFormula lowerLevel) := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourceSigmaDomain) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourceSigmaDomain))
        _ = _ := congrArg (∼·)
          (translate_sourceSigmaDomain lower lowerLevel upperLevel)
    rw [hsneg]
    have hlower :
        lower.subst
            ![Semiterm.bvar (0 : Fin 3), Semiterm.bvar (1 : Fin 3),
              Semiterm.bvar (2 : Fin 3)] = lower := by
      apply Bootstrapping.Semiformula.subst_eq_self
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              cases i using Fin.cases with
              | zero => rfl
              | succ i => exact i.elim0
    simp [Bootstrapping.Semiformula.imp_def,
      LogicalConnective.iff, hlower]
  · have hpneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourcePiDomain)) =
          ∼(piDomainFormula lowerLevel) := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourcePiDomain) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourcePiDomain))
        _ = _ := congrArg (∼·)
          (translate_sourcePiDomain lower lowerLevel upperLevel)
    rw [hpneg]
    simp [Bootstrapping.Semiformula.imp_def,
      LogicalConnective.iff]

@[simp] theorem translate_sourceCrossLevelPredicate
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCrossLevelPredicate) =
      crossLevelPredicateFormula lower lowerLevel upperLevel := by
  simp [sourceCrossLevelPredicate, crossLevelPredicateFormula,
    ModelCodedPredicateParameters.translateFormula]

/-- Arbitrary model-coded specialization of the fixed source sentence is
literally the advertised cross-level field. -/
@[simp] theorem translate_sourceCrossLevelSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCrossLevelSentence) =
      crossLevelFormula lower lowerLevel upperLevel := by
  simp [sourceCrossLevelSentence, crossLevelFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! ## The represented orbit instances -/

/-- Base field: the first positive truth formula is compared with the named
quantifier-free truth predicate. -/
noncomputable def baseCrossLevelFormula : Bootstrapping.Formula V ℒₒᵣ :=
  crossLevelFormula baseTruthFormula 0 1

/-- Positive successor field, comparing `truthFormula (n + 1)` with
`truthFormula n` at the exact model-coded levels used by the orbit. -/
noncomputable def orbitSuccessorCrossLevelFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  crossLevelFormula (truthFormula n) (n + 1) (n + 1 + 1)

/-- The upper predicate in the positive successor field is literally the
next orbit member. -/
theorem orbitSuccessorCrossLevelFormula_upper (n : V) :
    orbitSuccessorCrossLevelFormula n =
      crossLevelFormula (truthFormula n) (n + 1) (n + 1 + 1) := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
