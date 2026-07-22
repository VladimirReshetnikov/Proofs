import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.TermEvaluation

/-!
# Internal truth for coded quantifier-free arithmetic formulas

This file is the base level of the partial-satisfaction construction needed
for bounded reflection.  It evaluates *codes* of negation-normal arithmetic
formulas in an arbitrary (possibly nonstandard) model of `I Sigma 1`.  Thus it
does not decode a model element into a Lean inductive formula.

The generic coded-formula recursor supplies the finite HFS evaluation
certificate: its fixed point records the value of every proper subformula.
At the quantifier-free level the recursive value is a Boolean.  Atomic terms
are evaluated by `TermEvaluation.termValues`; equality and order are then
tested in the ambient arithmetic model.  Quantifier constructors deliberately
return zero.  Consequently the evaluator is semantically advertised only on
`IsQuantifierFreeCode`, although it remains a total represented function on
all model elements.

This is not yet truth for formulas with quantifiers.  Higher levels must add
the alternating existential/universal clauses while retaining the same
nonstandard-code discipline.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTruth

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Boolean operations used by the evaluator -/

/-- Boolean negation, totalized by regarding every nonzero value as true. -/
noncomputable def bitNot (x : V) : V := if x = 0 then 1 else 0

/-- Boolean conjunction, totalized by regarding every nonzero value as true. -/
noncomputable def bitAnd (x y : V) : V :=
  if x = 0 then 0 else if y = 0 then 0 else 1

/-- Boolean disjunction, totalized by regarding every nonzero value as true. -/
noncomputable def bitOr (x y : V) : V :=
  if x = 0 then (if y = 0 then 0 else 1) else 1

/-- Truth value of an encoded arithmetic relation applied to an encoded list
of already evaluated arguments.  The only relation symbols of `ℒₒᵣ` are
equality (code zero) and strict order (code one). -/
noncomputable def atomicBit (relation values : V) : V :=
  if relation = 0 then
    if values.[0] = values.[1] then 1 else 0
  else
    if values.[0] < values.[1] then 1 else 0

noncomputable def atomicBitGraph : HierarchySymbol.sigmaOne.Semisentence 3 := .mkSigma
  “y relation values.
    ∃ a, !nthDef a values 0 ∧ ∃ b, !nthDef b values 1 ∧
      ((relation = 0 ∧ a = b ∧ y = 1) ∨
       (relation = 0 ∧ a ≠ b ∧ y = 0) ∨
       (relation ≠ 0 ∧ a < b ∧ y = 1) ∨
       (relation ≠ 0 ∧ b ≤ a ∧ y = 0))”

instance atomicBit.defined :
    HierarchySymbol.DefinedFunction₂ (V := V) HierarchySymbol.sigmaOne
      (atomicBit : V → V → V) atomicBitGraph := .mk fun v ↦ by
  simp [atomicBitGraph, atomicBit]
  by_cases hr : v 1 = 0 <;>
    by_cases heq : (v 2).[0] = (v 2).[1] <;>
    by_cases hlt : (v 2).[0] < (v 2).[1] <;>
    simp [hr, heq, hlt]
  exact fun _ ↦ not_lt.mp hlt

instance atomicBit.definable :
    HierarchySymbol.DefinableFunction₂ (V := V) HierarchySymbol.sigmaOne
      (atomicBit : V → V → V) :=
  atomicBit.defined.to_definable

@[simp] theorem atomicBit_eq_index {values : V} :
    atomicBit (Arithmetic.eqIndex : V) values =
      (if values.[0] = values.[1] then 1 else 0) := by
  rw [show (Arithmetic.eqIndex : V) = 0 by
    simp [show Arithmetic.eqIndex = 0 by rfl]]
  simp [atomicBit]

@[simp] theorem atomicBit_lt_index {values : V} :
    atomicBit (Arithmetic.ltIndex : V) values =
      (if values.[0] < values.[1] then 1 else 0) := by
  rw [show (Arithmetic.ltIndex : V) = 1 by
    simp [show Arithmetic.ltIndex = 1 by rfl]]
  simp [atomicBit]

theorem bitNot_isBit (x : V) : bitNot x = 0 ∨ bitNot x = 1 := by
  by_cases h : x = 0 <;> simp [bitNot, h]

theorem bitAnd_isBit (x y : V) : bitAnd x y = 0 ∨ bitAnd x y = 1 := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [bitAnd, hx, hy]

theorem bitOr_isBit (x y : V) : bitOr x y = 0 ∨ bitOr x y = 1 := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [bitOr, hx, hy]

theorem atomicBit_isBit (R values : V) :
    atomicBit R values = 0 ∨ atomicBit R values = 1 := by
  by_cases hR : R = 0 <;>
    by_cases heq : values.[0] = values.[1] <;>
    by_cases hlt : values.[0] < values.[1] <;>
    simp [atomicBit, hR, heq, hlt]

/-! ## Coded formula evaluation -/

namespace Evaluation

/-- Recursive clauses for quantifier-free truth.  The parameter is the pair
`(bound environment, free environment)`.  It is kept unchanged at Boolean
nodes.  Quantifier clauses are total dummy clauses and therefore must not be
used as semantic truth clauses. -/
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma
    “y param k R terms.
      ∃ bound, !pi₁Def bound param ∧ ∃ free, !pi₂Def free param ∧
      ∃ values, !termValuesGraph values bound free k terms ∧
        !atomicBitGraph y R values”
  nrel := .mkSigma
    “y param k R terms.
      ∃ bound, !pi₁Def bound param ∧ ∃ free, !pi₂Def free param ∧
      ∃ values, !termValuesGraph values bound free k terms ∧
      ∃ positive, !atomicBitGraph positive R values ∧
        ((positive = 0 ∧ y = 1) ∨ (positive ≠ 0 ∧ y = 0))”
  verum := .mkSigma “y param. y = 1”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma
    “y param p₁ p₂ y₁ y₂.
      (y₁ = 0 ∧ y = 0) ∨
      (y₁ ≠ 0 ∧ y₂ = 0 ∧ y = 0) ∨
      (y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y = 1)”
  or := .mkSigma
    “y param p₁ p₂ y₁ y₂.
      (y₁ = 0 ∧ y₂ = 0 ∧ y = 0) ∨
      (y₁ = 0 ∧ y₂ ≠ 0 ∧ y = 1) ∨
      (y₁ ≠ 0 ∧ y = 1)”
  all := .mkSigma “y param p y₁. y = 0”
  exs := .mkSigma “y param p y₁. y = 0”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel param k R terms :=
    atomicBit R (termValues (π₁ param) (π₂ param) k terms)
  nrel param k R terms :=
    bitNot (atomicBit R (termValues (π₁ param) (π₂ param) k terms))
  verum _ := 1
  falsum _ := 0
  and _ _ _ y₁ y₂ := bitAnd y₁ y₂
  or _ _ _ y₁ y₂ := bitOr y₁ y₂
  all _ _ _ := 0
  exs _ _ _ := 0
  allChanges param := param
  exsChanges param := param
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by
    simp [blueprint, bitNot]
    by_cases h : atomicBit (v 3)
        (termValues (π₁ (v 1)) (π₂ (v 1)) (v 2) (v 4)) = 0 <;>
      simp [h]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by
    simp [blueprint, bitAnd]
    by_cases h₁ : v 4 = 0 <;> by_cases h₂ : v 5 = 0 <;> simp [h₁, h₂]
  or_defined := .mk fun v ↦ by
    simp [blueprint, bitOr]
    by_cases h₁ : v 4 = 0 <;> by_cases h₂ : v 5 = 0 <;> simp [h₁, h₂]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end Evaluation

open Evaluation

/-- Total coded quantifier-free evaluation under bound and free environments. -/
noncomputable def qfValue (bound free p : V) : V :=
  construction.result ℒₒᵣ ⟪bound, free⟫ p

/-- Sigma-one formula for the graph of `qfValue`.

The intermediate `param` is existential because pairing is represented in
the arithmetic language rather than being a primitive term constructor. -/
noncomputable def qfValueGraph : HierarchySymbol.sigmaOne.Semisentence 4 := .mkSigma
  “y bound free p. ∃ param, !pairDef param bound free ∧
    !(blueprint.result ℒₒᵣ) y param p”

instance qfValue.defined :
    HierarchySymbol.DefinedFunction₃ (V := V) HierarchySymbol.sigmaOne
      (qfValue : V → V → V → V) qfValueGraph := .mk fun v ↦ by
  simpa [qfValueGraph, qfValue] using!
    (construction (V := V)).result_defined.defined
      ![v 0, ⟪v 1, v 2⟫, v 3]

instance qfValue.definable :
    HierarchySymbol.DefinableFunction₃ (V := V) HierarchySymbol.sigmaOne
      (qfValue : V → V → V → V) :=
  qfValue.defined.to_definable

instance qfValue.definable' :
    Γ-[k + 1]-Function₃ (qfValue : V → V → V → V) :=
  qfValue.definable.of_sigmaOne

/-! ## Constructor equations -/

@[simp] theorem qfValue_rel {bound free k R terms : V}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    qfValue bound free (^rel k R terms) =
      atomicBit R (termValues bound free k terms) := by
  simp [qfValue, hR, hterms, construction]

@[simp] theorem qfValue_nrel {bound free k R terms : V}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    qfValue bound free (^nrel k R terms) =
      bitNot (atomicBit R (termValues bound free k terms)) := by
  simp [qfValue, hR, hterms, construction]

@[simp] theorem qfValue_verum {bound free : V} :
    qfValue bound free ^⊤ = 1 := by simp [qfValue, construction]

@[simp] theorem qfValue_falsum {bound free : V} :
    qfValue bound free ^⊥ = 0 := by simp [qfValue, construction]

@[simp] theorem qfValue_and {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋏ q) =
      bitAnd (qfValue bound free p) (qfValue bound free q) := by
  simp [qfValue, hp, hq, construction]

@[simp] theorem qfValue_or {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋎ q) =
      bitOr (qfValue bound free p) (qfValue bound free q) := by
  simp [qfValue, hp, hq, construction]

@[simp] theorem qfValue_all {bound free p : V} (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound free (^∀ p) = 0 := by
  simp [qfValue, hp, construction]

@[simp] theorem qfValue_exs {bound free p : V} (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound free (^∃ p) = 0 := by
  simp [qfValue, hp, construction]

/-! The next four lemmas connect the generic relation clause to the intended
arithmetic semantics.  They are stated at Boolean value one because that is
the form used by the truth predicate below. -/

@[simp] theorem qfValue_eq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    qfValue bound free
        (^rel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) = 1 ↔
      termValue bound free t₀ = termValue bound free t₁ := by
  rw [qfValue_rel (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁, atomicBit_eq_index]
  by_cases h : termValue bound free t₀ = termValue bound free t₁ <;>
    simp [h]

@[simp] theorem qfValue_neq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    qfValue bound free
        (^nrel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) = 1 ↔
      termValue bound free t₀ ≠ termValue bound free t₁ := by
  rw [qfValue_nrel (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁, atomicBit_eq_index]
  by_cases h : termValue bound free t₀ = termValue bound free t₁ <;>
    simp [bitNot, h]

@[simp] theorem qfValue_lt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    qfValue bound free
        (^rel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) = 1 ↔
      termValue bound free t₀ < termValue bound free t₁ := by
  rw [qfValue_rel (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁, atomicBit_lt_index]
  by_cases h : termValue bound free t₀ < termValue bound free t₁ <;>
    simp [h]

@[simp] theorem qfValue_nlt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    qfValue bound free
        (^nrel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) = 1 ↔
      ¬termValue bound free t₀ < termValue bound free t₁ := by
  rw [qfValue_nrel (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁, atomicBit_lt_index]
  by_cases h : termValue bound free t₀ < termValue bound free t₁ <;>
    simp [bitNot, h]

/-! ## The represented quantifier-free truth predicate -/

/-- A well-formed formula code is quantifier-free when its least hierarchy
level is zero.  Reusing the genuine Delta-one bounded-code predicate makes
the evaluator's domain line up definitionally with the rank restriction used
by `RestrictedDerivation`; this is the `n = 0` specialization of that same
representation, not a second ad-hoc syntax test. -/
def IsQuantifierFreeCode (p : V) : Prop :=
  QuantifierBoundedCode ℒₒᵣ 0 p

instance IsQuantifierFreeCode.definable :
    HierarchySymbol.DefinablePred (V := V) HierarchySymbol.deltaOne
      IsQuantifierFreeCode := by
  unfold IsQuantifierFreeCode
  definability

instance IsQuantifierFreeCode.definable' :
    Γ-[k + 1]-Predicate (IsQuantifierFreeCode : V → Prop) :=
  (IsQuantifierFreeCode.definable (V := V)).of_deltaOne

/-- Internal quantifier-free truth. -/
def QFTrue (bound free p : V) : Prop :=
  IsQuantifierFreeCode p ∧ qfValue bound free p = 1

/-- Internal quantifier-free falsity, using the same evaluation certificate. -/
def QFFalse (bound free p : V) : Prop :=
  IsQuantifierFreeCode p ∧ qfValue bound free p = 0

instance QFTrue.definable :
    HierarchySymbol.DefinableRel₃ (V := V) HierarchySymbol.sigmaOne QFTrue := by
  unfold QFTrue
  definability

instance QFFalse.definable :
    HierarchySymbol.DefinableRel₃ (V := V) HierarchySymbol.sigmaOne QFFalse := by
  unfold QFFalse
  definability

/-- The coded evaluator always returns an actual Boolean on every well-formed
formula, including outside the quantifier-free semantic domain. -/
theorem qfValue_isBit {bound free p : V} (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound free p = 0 ∨ qfValue bound free p = 1 := by
  simpa [qfValue] using
    (construction.uformula_result_induction (L := ℒₒᵣ)
      (P := fun _ _ y : V ↦ y = 0 ∨ y = 1)
      (by definability)
      (fun param k R terms hR hterms ↦ by
        simpa [construction] using atomicBit_isBit R
          (termValues (π₁ param) (π₂ param) k terms))
      (fun param k R terms hR hterms ↦ by
        simpa [construction] using bitNot_isBit
          (atomicBit R (termValues (π₁ param) (π₂ param) k terms)))
      (fun _ ↦ by simp [construction])
      (fun _ ↦ by simp [construction])
      (fun _ _ _ _ _ _ _ ↦ by
        simpa [construction] using bitAnd_isBit _ _)
      (fun _ _ _ _ _ _ _ ↦ by
        simpa [construction] using bitOr_isBit _ _)
      (fun _ _ _ _ ↦ by simp [construction])
      (fun _ _ _ _ ↦ by simp [construction])
      hp)

@[simp] theorem qfValue_and_eq_one_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋏ q) = 1 ↔
      qfValue bound free p = 1 ∧ qfValue bound free q = 1 := by
  rw [qfValue_and hp hq]
  rcases qfValue_isBit (bound := bound) (free := free) hp with h₁ | h₁ <;>
    rcases qfValue_isBit (bound := bound) (free := free) hq with h₂ | h₂ <;>
    simp [bitAnd, h₁, h₂]

@[simp] theorem qfValue_or_eq_one_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋎ q) = 1 ↔
      qfValue bound free p = 1 ∨ qfValue bound free q = 1 := by
  rw [qfValue_or hp hq]
  rcases qfValue_isBit (bound := bound) (free := free) hp with h₁ | h₁ <;>
    rcases qfValue_isBit (bound := bound) (free := free) hq with h₂ | h₂ <;>
    simp [bitOr, h₁, h₂]

/-- On its intended domain, truth and falsity are complementary. -/
theorem qfTrue_iff_not_qfFalse {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    QFTrue bound free p ↔ ¬QFFalse bound free p := by
  rcases qfValue_isBit (bound := bound) (free := free) hp.1 with h | h
  · simp [QFTrue, QFFalse, hp, h]
  · simp [QFTrue, QFFalse, hp, h]

end LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
