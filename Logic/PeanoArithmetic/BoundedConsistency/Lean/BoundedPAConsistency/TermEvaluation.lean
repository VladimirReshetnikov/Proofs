import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Functions
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions

/-!
# Evaluation of coded arithmetic terms

The bounded-reflection argument eventually has to evaluate terms occurring in
nonstandard codes of formulae.  This file supplies that first semantic layer.
It deliberately uses Foundation's coded `TermRec`, rather than decoding a term
to Lean syntax: its graph is therefore represented by a Sigma-one formula in
every model of `I Sigma 1`.

There are two coded environments.  Free variables are read in their natural
order.  Bound variables use the usual de Bruijn convention: the most recently
appended value has index zero.  Thus bound variable `z` is read at
`length(bound) - (z + 1)`.  Both lookups use total zero-defaulting `znth`; this
makes the evaluator a total function even when an environment is malformed or
too short, while the intended equations below apply to well-formed terms.
-/

namespace LeanProofs.BoundedPAConsistency.TermEvaluation

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Position used to read de Bruijn variable `z` from a coded bound-variable
environment.  Truncated subtraction and `znth` make this convention total. -/
noncomputable def boundPosition (bound z : V) : V := lh bound - (z + 1)

/-- Interpret one arithmetic function symbol after all of its arguments have
already been evaluated into `values`.

The definition is total on arbitrary codes.  On genuine `ℒₒᵣ` symbols the
four branches are exactly zero, one, addition, and multiplication, because
Foundation encodes the two nullary symbols by `0, 1` and likewise the two
binary symbols by `0, 1`.
-/
noncomputable def applyFunction (arity symbol values : V) : V :=
  if arity = 0 then
    if symbol = 0 then 0 else 1
  else if symbol = 0 then
    values.[0] + values.[1]
  else
    values.[0] * values.[1]

namespace CodedTermEval

/-- Recursive clauses for coded term evaluation.  The two parameters are,
in order, the bound-variable and free-variable environments. -/
def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma
    “y z bound free.
      ∃ l, !lhDef l bound ∧ ∃ i, !subDef i l (z + 1) ∧ !znthDef y bound i”
  fvar := .mkSigma “y x bound free. !znthDef y free x”
  func := .mkSigma
    “y k f terms values bound free.
      (k = 0 ∧ f = 0 ∧ y = 0) ∨
      (k = 0 ∧ f ≠ 0 ∧ y = 1) ∨
      (k ≠ 0 ∧ f = 0 ∧
        ∃ y₀, !nthDef y₀ values 0 ∧
        ∃ y₁, !nthDef y₁ values 1 ∧ y = y₀ + y₁) ∨
      (k ≠ 0 ∧ f ≠ 0 ∧
        ∃ y₀, !nthDef y₀ values 0 ∧
        ∃ y₁, !nthDef y₁ values 1 ∧ y = y₀ * y₁)”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar param z := znth (param 0) (boundPosition (param 0) z)
  fvar param x := znth (param 1) x
  func _ k f _ values := applyFunction k f values
  bvar_defined := .mk fun v ↦ by
    simp [blueprint, boundPosition]
  fvar_defined := .mk fun v ↦ by
    simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp [blueprint, applyFunction]
    by_cases hk : v 1 = 0 <;> by_cases hf : v 2 = 0 <;> simp [hk, hf]

end CodedTermEval

open CodedTermEval

/-- Total value of the coded term `t` under `bound` and `free`.

`TermRec.result` returns zero on a code which is not a well-formed arithmetic
term, as specified by Foundation's generic recursor.
-/
noncomputable def termValue (bound free t : V) : V :=
  construction.result ℒₒᵣ ![bound, free] t

/-- Simultaneously evaluate a coded vector of `k` terms. -/
noncomputable def termValues (bound free k terms : V) : V :=
  construction.resultVec ℒₒᵣ ![bound, free] k terms

/-- A Sigma-one formula representing the graph of `termValue`.

Its free variables are ordered `(value, bound, free, term)`. -/
noncomputable def termValueGraph : HierarchySymbol.sigmaOne.Semisentence 4 :=
  (blueprint.result ℒₒᵣ).rew <| Rew.subst ![#0, #3, #1, #2]

/-- A Sigma-one formula representing the graph of vector evaluation.

Its free variables are ordered `(values, bound, free, length, terms)`. -/
noncomputable def termValuesGraph : HierarchySymbol.sigmaOne.Semisentence 5 :=
  (blueprint.resultVec ℒₒᵣ).rew <| Rew.subst ![#0, #3, #4, #1, #2]

instance termValue.defined :
    HierarchySymbol.DefinedFunction₃ (V := V) HierarchySymbol.sigmaOne
      (termValue : V → V → V → V) termValueGraph := .mk fun v ↦ by
  simpa [termValueGraph, termValue, Matrix.constant_eq_singleton,
    Matrix.comp_vecCons'] using
    construction.result_defined.defined ![v 0, v 3, v 1, v 2]

@[simp] theorem eval_termValueGraph (v : Fin 4 → V) :
    termValueGraph.val.Evalb v ↔
      v 0 = termValue (v 1) (v 2) (v 3) :=
  termValue.defined.iff

instance termValue.definable :
    HierarchySymbol.DefinableFunction₃ (V := V) HierarchySymbol.sigmaOne
      (termValue : V → V → V → V) :=
  termValue.defined.to_definable

instance termValue.definable' :
    Γ-[k + 1]-Function₃ (termValue : V → V → V → V) :=
  termValue.definable.of_sigmaOne

instance termValues.defined :
    HierarchySymbol.DefinedFunction₄ (V := V) HierarchySymbol.sigmaOne
      (termValues : V → V → V → V → V) termValuesGraph := .mk fun v ↦ by
  simpa [termValuesGraph, termValues, Matrix.constant_eq_singleton,
    Matrix.comp_vecCons', Function.comp_def] using!
    (construction (V := V)).resultVec_defined (L := ℒₒᵣ) |>.defined
      ![v 0, v 3, v 4, v 1, v 2]

@[simp] theorem eval_termValuesGraph (v : Fin 5 → V) :
    termValuesGraph.val.Evalb v ↔
      v 0 = termValues (v 1) (v 2) (v 3) (v 4) :=
  termValues.defined.iff

instance termValues.definable :
    HierarchySymbol.DefinableFunction₄ (V := V) HierarchySymbol.sigmaOne
      (termValues : V → V → V → V → V) :=
  termValues.defined.to_definable

instance termValues.definable' :
    Γ-[k + 1]-Function₄ (termValues : V → V → V → V → V) :=
  termValues.definable.of_sigmaOne

@[simp] theorem termValue_bvar (bound free z : V) :
    termValue bound free (^#z) = znth bound (boundPosition bound z) := by
  simp [termValue, construction]

@[simp] theorem termValue_fvar (bound free x : V) :
    termValue bound free (^&x) = znth free x := by
  simp [termValue, construction]

/-- A freshly appended binder is exactly de Bruijn variable zero.  This is the
environment equation needed by the quantifier clauses of partial truth. -/
@[simp] theorem termValue_bvar_zero_seqCons {bound free a : V}
    (hbound : Seq bound) :
    termValue (bound ⁀' a) free (^#(0 : V)) = a := by
  rw [termValue_bvar]
  have hmem : ⟪lh bound, a⟫ ∈ bound ⁀' a := by simp
  simpa [boundPosition, hbound] using
    (hbound.seqCons a).znth_eq_of_mem hmem

/-- Lookup of a free variable agrees with any explicitly known entry of a
well-formed coded environment. -/
theorem termValue_fvar_eq_of_mem {bound free x a : V}
    (hfree : Seq free) (hmem : ⟪x, a⟫ ∈ free) :
    termValue bound free (^&x) = a := by
  rw [termValue_fvar]
  exact hfree.znth_eq_of_mem hmem

@[simp] theorem length_termValues {bound free k terms : V}
    (hterms : IsUTermVec ℒₒᵣ k terms) :
    len (termValues bound free k terms) = k :=
  construction.resultVec_lh ℒₒᵣ _ hterms

@[simp] theorem nth_termValues {bound free k terms i : V}
    (hterms : IsUTermVec ℒₒᵣ k terms) (hi : i < k) :
    (termValues bound free k terms).[i] = termValue bound free terms.[i] :=
  construction.nth_resultVec ℒₒᵣ _ hterms hi

@[simp] theorem termValues_nil (bound free : V) :
    termValues bound free 0 0 = 0 :=
  construction.resultVec_nil ℒₒᵣ _

theorem termValues_cons {bound free k t terms : V}
    (ht : IsUTerm ℒₒᵣ t) (hterms : IsUTermVec ℒₒᵣ k terms) :
    termValues bound free (k + 1) (t ∷ terms) =
      termValue bound free t ∷ termValues bound free k terms :=
  construction.resultVec_cons ℒₒᵣ _ hterms ht

@[simp] theorem termValues_pair {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    termValues bound free 2 ?[t₀, t₁] =
      ?[termValue bound free t₀, termValue bound free t₁] := by
  rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two],
    termValues_cons, termValues_cons] <;> simp [ht₀, ht₁]

theorem termValue_func {bound free k f terms : V}
    (hf : (ℒₒᵣ).IsFunc k f) (hterms : IsUTermVec ℒₒᵣ k terms) :
    termValue bound free (^func k f terms) =
      applyFunction k f (termValues bound free k terms) := by
  simp [termValue, termValues, construction, hf, hterms]

/-- Evaluation equation for the coded constant zero. -/
@[simp] theorem termValue_zero {bound free : V} :
    termValue bound free (^func 0 (Arithmetic.zeroIndex : V) 0) = 0 := by
  rw [termValue_func (by simp) (by simp)]
  simp [applyFunction, Arithmetic.coe_zeroIndex_eq]

/-- Evaluation equation for the coded constant one. -/
@[simp] theorem termValue_one {bound free : V} :
    termValue bound free (^func 0 (Arithmetic.oneIndex : V) 0) = 1 := by
  rw [termValue_func (by simp) (by simp)]
  simp [applyFunction, Arithmetic.coe_oneIndex_eq]

/-- Evaluation equation for the coded addition constructor. -/
@[simp] theorem termValue_add {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    termValue bound free
        (^func 2 (Arithmetic.addIndex : V) ?[t₀, t₁]) =
      termValue bound free t₀ + termValue bound free t₁ := by
  rw [termValue_func (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁]
  simp [applyFunction, Arithmetic.coe_addIndex_eq]

/-- Evaluation equation for the coded multiplication constructor. -/
@[simp] theorem termValue_mul {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    termValue bound free
        (^func 2 (Arithmetic.mulIndex : V) ?[t₀, t₁]) =
      termValue bound free t₀ * termValue bound free t₁ := by
  rw [termValue_func (by simp) (by simp [ht₀, ht₁]),
    termValues_pair ht₀ ht₁]
  simp [applyFunction, Arithmetic.coe_mulIndex_eq]

end LeanProofs.BoundedPAConsistency.TermEvaluation
