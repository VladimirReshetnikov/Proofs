import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions

/-!
# A coded quantifier-group rank for arithmetical formulas

`Basic.lean` defines the intended hierarchy rank on the separate `PAHF`
syntax.  The eventual internal bounded-reflection argument instead needs to
inspect *Gödel codes* of formulas inside an arbitrary model of arithmetic.
This file supplies that code-level half of the construction.

The recursion returns the pair `(Sigma-rank, Pi-rank)`.  Keeping the two
polarities together is important: at conjunction and disjunction both
components are combined independently, so a conjunction of a Sigma-one and a
Pi-one formula normally has rank two.  A recursion which merely counts changes
of quantifier along each branch would incorrectly assign that example rank
one.

All functions below are built with Foundation's `UformulaRec1` fixed-point
recursor.  Consequently their graphs are represented by Sigma-one formulas in
every model of `I Sigma 1` (and hence in every model of PA).  No appeal to
standardness of the formula code is made in their definitions.
-/

namespace LeanProofs.BoundedPAConsistency.CodedHierarchy

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

namespace RankPair

/-
The result clauses use the standard pairing function.  If a recursive result
is `y`, then `pi₁ y` and `pi₂ y` are respectively its Sigma and Pi ranks.
The formula fields spell those projections out through `pairDef`, because the
blueprint language only contains arithmetic terms while pairing is a
represented (rather than primitive-language) function.
-/
def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !pairDef y 0 0”
  nrel := .mkSigma “y param k R v. !pairDef y 0 0”
  verum := .mkSigma “y param. !pairDef y 0 0”
  falsum := .mkSigma “y param. !pairDef y 0 0”
  and := .mkSigma
    “y param p₁ p₂ y₁ y₂.
      ∃ s₁, ∃ r₁, !pairDef y₁ s₁ r₁ ∧
      ∃ s₂, ∃ r₂, !pairDef y₂ s₂ r₂ ∧
      ∃ s, !max.dfn s s₁ s₂ ∧ ∃ r, !max.dfn r r₁ r₂ ∧ !pairDef y s r”
  or := .mkSigma
    “y param p₁ p₂ y₁ y₂.
      ∃ s₁, ∃ r₁, !pairDef y₁ s₁ r₁ ∧
      ∃ s₂, ∃ r₂, !pairDef y₂ s₂ r₂ ∧
      ∃ s, !max.dfn s s₁ s₂ ∧ ∃ r, !max.dfn r r₁ r₂ ∧ !pairDef y s r”
  all := .mkSigma
    “y param p₁ y₁.
      ∃ s₁, ∃ r₁, !pairDef y₁ s₁ r₁ ∧
      ∃ r, !max.dfn r 1 r₁ ∧ !pairDef y (r + 1) r”
  exs := .mkSigma
    “y param p₁ y₁.
      ∃ s₁, ∃ r₁, !pairDef y₁ s₁ r₁ ∧
      ∃ s, !max.dfn s 1 s₁ ∧ !pairDef y s (s + 1)”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun _ _ _ ↦ ⟪0, 0⟫
  nrel {_} := fun _ _ _ ↦ ⟪0, 0⟫
  verum {_} := ⟪0, 0⟫
  falsum {_} := ⟪0, 0⟫
  and {_} := fun _ _ y₁ y₂ ↦
    ⟪max (π₁ y₁) (π₁ y₂), max (π₂ y₁) (π₂ y₂)⟫
  or {_} := fun _ _ y₁ y₂ ↦
    ⟪max (π₁ y₁) (π₁ y₂), max (π₂ y₁) (π₂ y₂)⟫
  all {_} := fun _ y₁ ↦
    ⟪max 1 (π₂ y₁) + 1, max 1 (π₂ y₁)⟫
  exs {_} := fun _ y₁ ↦
    ⟪max 1 (π₁ y₁), max 1 (π₁ y₁) + 1⟫
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]; grind
  or_defined := .mk fun v ↦ by simp [blueprint]; grind
  all_defined := .mk fun v ↦ by
    simp [blueprint]
    constructor
    · rintro ⟨s, r, hpair, h⟩
      simpa [hpair] using h
    · intro h
      exact ⟨π₁ (v 3), π₂ (v 3), by simp, h⟩
  exs_defined := .mk fun v ↦ by
    simp [blueprint]
    constructor
    · rintro ⟨s, ⟨r, hpair⟩, h⟩
      simpa [hpair] using h
    · intro h
      exact ⟨π₁ (v 3), ⟨π₂ (v 3), by simp⟩, h⟩
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end RankPair

open RankPair

/-- The internally computed pair `(Sigma-rank, Pi-rank)` of a formula code. -/
noncomputable def rankPair (L : Language) [L.Encodable] [L.LORDefinable]
    (p : V) : V := construction.result L 0 p

/-- An explicit Sigma-one graph formula for `rankPair`. -/
noncomputable def rankPairGraph (L : Language) [L.Encodable]
    [L.LORDefinable] : HierarchySymbol.sigmaOne.Semisentence 2 :=
  (RankPair.blueprint.result L).rew (Rew.subst ![#0, ‘0’, #1])

instance rankPair.defined (L : Language) [L.Encodable] [L.LORDefinable] :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaOne
      (rankPair L) (rankPairGraph L) := .mk fun v ↦ by
  simpa [rankPair, rankPairGraph, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton] using!
      (RankPair.construction (V := V)).result_defined.defined ![v 0, 0, v 1]

instance rankPair.definable (L : Language) [L.Encodable] [L.LORDefinable] :
    HierarchySymbol.DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne
      (rankPair L) := (rankPair.defined L).to_definable

/-- Sigma-polarity component of `rankPair`. -/
noncomputable def sigmaRankCode (L : Language) [L.Encodable]
    [L.LORDefinable] (p : V) : V := π₁ (rankPair L p)

/-- Pi-polarity component of `rankPair`. -/
noncomputable def piRankCode (L : Language) [L.Encodable]
    [L.LORDefinable] (p : V) : V := π₂ (rankPair L p)

/-- Least hierarchy level at which the coded formula can be treated. -/
noncomputable def quantifierGroupsCode (L : Language) [L.Encodable]
    [L.LORDefinable] (p : V) : V :=
  min (sigmaRankCode L p) (piRankCode L p)

instance sigmaRankCode.definable (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne
      (sigmaRankCode L) := by
  unfold sigmaRankCode
  definability

instance piRankCode.definable (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne
      (piRankCode L) := by
  unfold piRankCode
  definability

instance quantifierGroupsCode.definable (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne
      (quantifierGroupsCode L) := by
  unfold quantifierGroupsCode
  definability

/-! ## Equations on coded formula constructors -/

@[simp] lemma rankPair_rel {L : Language} [L.Encodable] [L.LORDefinable]
    {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    rankPair L (^rel k R v) = ⟪0, 0⟫ := by
  simp [rankPair, hR, hv, RankPair.construction]

@[simp] lemma rankPair_nrel {L : Language} [L.Encodable] [L.LORDefinable]
    {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    rankPair L (^nrel k R v) = ⟪0, 0⟫ := by
  simp [rankPair, hR, hv, RankPair.construction]

@[simp] lemma rankPair_verum {L : Language} [L.Encodable]
    [L.LORDefinable] : rankPair (V := V) L ^⊤ = ⟪0, 0⟫ := by
  simp [rankPair, RankPair.construction]

@[simp] lemma rankPair_falsum {L : Language} [L.Encodable]
    [L.LORDefinable] : rankPair (V := V) L ^⊥ = ⟪0, 0⟫ := by
  simp [rankPair, RankPair.construction]

@[simp] lemma rankPair_and {L : Language} [L.Encodable] [L.LORDefinable]
    {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    rankPair L (p ^⋏ q) =
      ⟪max (sigmaRankCode L p) (sigmaRankCode L q),
        max (piRankCode L p) (piRankCode L q)⟫ := by
  simp [rankPair, sigmaRankCode, piRankCode, hp, hq,
    RankPair.construction]

@[simp] lemma rankPair_or {L : Language} [L.Encodable] [L.LORDefinable]
    {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    rankPair L (p ^⋎ q) =
      ⟪max (sigmaRankCode L p) (sigmaRankCode L q),
        max (piRankCode L p) (piRankCode L q)⟫ := by
  simp [rankPair, sigmaRankCode, piRankCode, hp, hq,
    RankPair.construction]

@[simp] lemma rankPair_all {L : Language} [L.Encodable] [L.LORDefinable]
    {p : V} (hp : IsUFormula L p) :
    rankPair L (^∀ p) =
      ⟪max 1 (piRankCode L p) + 1, max 1 (piRankCode L p)⟫ := by
  simp [rankPair, piRankCode, hp, RankPair.construction]

@[simp] lemma rankPair_exs {L : Language} [L.Encodable] [L.LORDefinable]
    {p : V} (hp : IsUFormula L p) :
    rankPair L (^∃ p) =
      ⟪max 1 (sigmaRankCode L p), max 1 (sigmaRankCode L p) + 1⟫ := by
  simp [rankPair, sigmaRankCode, hp, RankPair.construction]

@[simp] lemma sigmaRankCode_and {L : Language} [L.Encodable]
    [L.LORDefinable] {p q : V} (hp : IsUFormula L p)
    (hq : IsUFormula L q) :
    sigmaRankCode L (p ^⋏ q) =
      max (sigmaRankCode L p) (sigmaRankCode L q) := by
  simp [sigmaRankCode, hp, hq]

@[simp] lemma piRankCode_and {L : Language} [L.Encodable]
    [L.LORDefinable] {p q : V} (hp : IsUFormula L p)
    (hq : IsUFormula L q) :
    piRankCode L (p ^⋏ q) = max (piRankCode L p) (piRankCode L q) := by
  simp [piRankCode, hp, hq]

@[simp] lemma sigmaRankCode_or {L : Language} [L.Encodable]
    [L.LORDefinable] {p q : V} (hp : IsUFormula L p)
    (hq : IsUFormula L q) :
    sigmaRankCode L (p ^⋎ q) =
      max (sigmaRankCode L p) (sigmaRankCode L q) := by
  simp [sigmaRankCode, hp, hq]

@[simp] lemma piRankCode_or {L : Language} [L.Encodable]
    [L.LORDefinable] {p q : V} (hp : IsUFormula L p)
    (hq : IsUFormula L q) :
    piRankCode L (p ^⋎ q) = max (piRankCode L p) (piRankCode L q) := by
  simp [piRankCode, hp, hq]

@[simp] lemma sigmaRankCode_all {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    sigmaRankCode L (^∀ p) = max 1 (piRankCode L p) + 1 := by
  simp [sigmaRankCode, hp]

@[simp] lemma piRankCode_all {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    piRankCode L (^∀ p) = max 1 (piRankCode L p) := by
  simp [piRankCode, hp]

@[simp] lemma sigmaRankCode_exs {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    sigmaRankCode L (^∃ p) = max 1 (sigmaRankCode L p) := by
  simp [sigmaRankCode, hp]

@[simp] lemma piRankCode_exs {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    piRankCode L (^∃ p) = max 1 (sigmaRankCode L p) + 1 := by
  simp [piRankCode, hp]

/-! ## Invariance under proof-calculus syntax operations

The restricted derivation rules manipulate formula codes by negation,
renaming free variables, and substituting terms.  The following proofs use
Foundation's internal structural induction principles, so they apply to
well-formed nonstandard codes in arbitrary models of `I Sigma 1` as well as
to ordinary quoted formulae. -/

/-- Coded negation exchanges the two polarity ranks. -/
@[simp] lemma rankPair_neg {L : Language} [L.Encodable] [L.LORDefinable]
    {p : V} : IsUFormula L p →
      rankPair L (neg L p) = ⟪piRankCode L p, sigmaRankCode L p⟫ := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R terms hR hterms
    simp [hR, hterms, sigmaRankCode, piRankCode]
  · intro k R terms hR hterms
    simp [hR, hterms, sigmaRankCode, piRankCode]
  · simp [sigmaRankCode, piRankCode]
  · simp [sigmaRankCode, piRankCode]
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq, sigmaRankCode, piRankCode]
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq, sigmaRankCode, piRankCode]
  · intro p hp ihp
    simp [hp, ihp, sigmaRankCode, piRankCode]
  · intro p hp ihp
    simp [hp, ihp, sigmaRankCode, piRankCode]

@[simp] lemma sigmaRankCode_neg {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    sigmaRankCode L (neg L p) = piRankCode L p := by
  simpa [sigmaRankCode, piRankCode] using
    congrArg (fun x : V ↦ π₁ x) (rankPair_neg hp)

@[simp] lemma piRankCode_neg {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    piRankCode L (neg L p) = sigmaRankCode L p := by
  simpa [sigmaRankCode, piRankCode] using
    congrArg (fun x : V ↦ π₂ x) (rankPair_neg hp)

@[simp] lemma quantifierGroupsCode_neg {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    quantifierGroupsCode L (neg L p) = quantifierGroupsCode L p := by
  simp [quantifierGroupsCode, hp, min_comm]

/-- Shifting free-variable indices leaves both ranks unchanged. -/
@[simp] lemma rankPair_shift {L : Language} [L.Encodable] [L.LORDefinable]
    {p : V} : IsUFormula L p → rankPair L (shift L p) = rankPair L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R terms hR hterms
    simp [hR, hterms]
  · intro k R terms hR hterms
    simp [hR, hterms]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq, sigmaRankCode, piRankCode]
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq, sigmaRankCode, piRankCode]
  · intro p hp ihp
    simp [hp, ihp, piRankCode]
  · intro p hp ihp
    simp [hp, ihp, sigmaRankCode]

@[simp] lemma quantifierGroupsCode_shift {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsUFormula L p) :
    quantifierGroupsCode L (shift L p) = quantifierGroupsCode L p := by
  simp [quantifierGroupsCode, sigmaRankCode, piRankCode, hp]

/-- Substitution changes only coded terms, never the formula hierarchy. -/
lemma rankPair_subst {L : Language} [L.Encodable] [L.LORDefinable]
    {n m p w : V} (hp : IsSemiformula L n p)
    (hw : IsSemitermVec L n m w) :
    rankPair L (subst L w p) = rankPair L p := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R terms hR hterms m w hw
    simp [hR, hterms.isUTerm, (hw.termSubstVec hterms).isUTerm]
  · intro n k R terms hR hterms m w hw
    simp [hR, hterms.isUTerm, (hw.termSubstVec hterms).isUTerm]
  · intro n m w hw
    simp
  · intro n m w hw
    simp
  · intro n p q hp hq ihp ihq m w hw
    simp [hp.isUFormula, hq.isUFormula, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp hw, ihq hw,
      sigmaRankCode, piRankCode]
  · intro n p q hp hq ihp ihq m w hw
    simp [hp.isUFormula, hq.isUFormula, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp hw, ihq hw,
      sigmaRankCode, piRankCode]
  · intro n p hp ihp m w hw
    simp [hp.isUFormula, (hp.subst hw.qVec).isUFormula, ihp hw.qVec,
      piRankCode]
  · intro n p hp ihp m w hw
    simp [hp.isUFormula, (hp.subst hw.qVec).isUFormula, ihp hw.qVec,
      sigmaRankCode]

@[simp] lemma quantifierGroupsCode_subst {L : Language} [L.Encodable]
    [L.LORDefinable] {n m p w : V} (hp : IsSemiformula L n p)
    (hw : IsSemitermVec L n m w) :
    quantifierGroupsCode L (subst L w p) = quantifierGroupsCode L p := by
  simp [quantifierGroupsCode, sigmaRankCode, piRankCode, rankPair_subst hp hw]

@[simp] lemma quantifierGroupsCode_substs1 {L : Language} [L.Encodable]
    [L.LORDefinable] {m p t : V} (hp : IsSemiformula L 1 p)
    (ht : IsSemiterm L m t) :
    quantifierGroupsCode L (substs1 L t p) = quantifierGroupsCode L p := by
  unfold substs1
  exact quantifierGroupsCode_subst hp (IsSemitermVec.singleton.mpr ht)

@[simp] lemma quantifierGroupsCode_free {L : Language} [L.Encodable]
    [L.LORDefinable] {p : V} (hp : IsSemiformula L 1 p) :
    quantifierGroupsCode L (free L p) = quantifierGroupsCode L p := by
  unfold free
  rw [quantifierGroupsCode_substs1 hp.shift
      (show IsSemiterm (V := V) L 0 ^&0 by simp),
    quantifierGroupsCode_shift hp.isUFormula]

/-! ## A represented bounded-rank predicate -/

/-- A model element is a well-formed formula code whose hierarchy rank is at
most the supplied (possibly nonstandard) model element. -/
def QuantifierBoundedCode (L : Language) [L.Encodable] [L.LORDefinable]
    (n p : V) : Prop :=
  IsUFormula L p ∧ quantifierGroupsCode L p ≤ n

/-- A concrete Sigma-one formula representing `QuantifierBoundedCode`.

The projections are written through `pi₁Def` and `pi₂Def`, rather than by
existentially decomposing the pair, so simplification of the represented graph
does not depend on choosing a decomposition witness.
-/
noncomputable def quantifierBoundedCodeSigmaDef (L : Language) [L.Encodable]
    [L.LORDefinable] : HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “n p. !(isUFormula L).sigma p ∧
    ∃ y, !(rankPairGraph L) y p ∧
    ∃ s, !pi₁Def s y ∧ ∃ r, !pi₂Def r y ∧
    ∃ q, !min.dfn q s r ∧ q ≤ n”

instance QuantifierBoundedCode.definedSigma (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaOne
      (QuantifierBoundedCode L) (quantifierBoundedCodeSigmaDef L) :=
    .mk fun v ↦ by
  simp [quantifierBoundedCodeSigmaDef, QuantifierBoundedCode,
    quantifierGroupsCode, sigmaRankCode, piRankCode]

/-- A genuine Delta-one representation of the code-bound predicate.

The Sigma side chooses the unique recursive result and its projections.  The
Pi side says that *every* result and every represented choice of its two
projections and their minimum obeys the bound.  Totality and uniqueness of
`rankPairGraph`, `pi₁Def`, `pi₂Def`, and `min.dfn` make the presentations
equivalent in every model of `I Sigma 1`, including nonstandard models.
-/
noncomputable def quantifierBoundedCodeDef (L : Language) [L.Encodable]
    [L.LORDefinable] : HierarchySymbol.deltaOne.Semisentence 2 := .mkDelta
  (quantifierBoundedCodeSigmaDef L)
  (.mkPi “n p. !(isUFormula L).pi p ∧
    ∀ y, !(rankPairGraph L) y p →
    ∀ s, !pi₁Def s y → ∀ r, !pi₂Def r y →
    ∀ q, !min.dfn q s r → q ≤ n”)

instance QuantifierBoundedCode.defined (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.deltaOne
      (QuantifierBoundedCode L) (quantifierBoundedCodeDef L) := .mk <| by
  constructor
  · intro v
    simp [quantifierBoundedCodeDef, quantifierBoundedCodeSigmaDef,
      HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [quantifierBoundedCodeDef, quantifierBoundedCodeSigmaDef,
      HierarchySymbol.Semiformula.val_sigma, QuantifierBoundedCode,
      quantifierGroupsCode, sigmaRankCode, piRankCode]

instance QuantifierBoundedCode.definable (L : Language) [L.Encodable]
    [L.LORDefinable] :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.deltaOne
      (QuantifierBoundedCode L) :=
  (QuantifierBoundedCode.defined L).to_definable

/-- Specialization to an external standard bound.  The cast inserts the
standard numeral into the ambient (possibly nonstandard) model. -/
def QuantifierBoundedAt (L : Language) [L.Encodable] [L.LORDefinable]
    (n : Nat) (p : V) : Prop :=
  QuantifierBoundedCode L (n : V) p

instance QuantifierBoundedAt.definable (L : Language) [L.Encodable]
    [L.LORDefinable] (n : Nat) :
    HierarchySymbol.DefinablePred (V := V) HierarchySymbol.deltaOne
      (QuantifierBoundedAt L n) := by
  unfold QuantifierBoundedAt
  definability

lemma QuantifierBoundedCode.mono {L : Language} [L.Encodable]
    [L.LORDefinable] {m n p : V} (hmn : m ≤ n)
    (hp : QuantifierBoundedCode L m p) : QuantifierBoundedCode L n p :=
  ⟨hp.1, le_trans hp.2 hmn⟩

@[simp] lemma QuantifierBoundedCode.neg_iff {L : Language} [L.Encodable]
    [L.LORDefinable] {n p : V} (hp : IsUFormula L p) :
    QuantifierBoundedCode L n (neg L p) ↔ QuantifierBoundedCode L n p := by
  simp [QuantifierBoundedCode, hp]

@[simp] lemma QuantifierBoundedCode.shift_iff {L : Language} [L.Encodable]
    [L.LORDefinable] {n p : V} (hp : IsUFormula L p) :
    QuantifierBoundedCode L n (shift L p) ↔ QuantifierBoundedCode L n p := by
  simp [QuantifierBoundedCode, hp]

lemma QuantifierBoundedCode.subst {L : Language} [L.Encodable]
    [L.LORDefinable] {b n m p w : V} (hp : IsSemiformula L n p)
    (hw : IsSemitermVec L n m w) (hb : QuantifierBoundedCode L b p) :
    QuantifierBoundedCode L b (subst L w p) := by
  exact ⟨(hp.subst hw).isUFormula, by
    simpa only [quantifierGroupsCode_subst hp hw] using hb.2⟩

lemma QuantifierBoundedCode.substs1 {L : Language} [L.Encodable]
    [L.LORDefinable] {b m p t : V} (hp : IsSemiformula L 1 p)
    (ht : IsSemiterm L m t) (hb : QuantifierBoundedCode L b p) :
    QuantifierBoundedCode L b (substs1 L t p) := by
  unfold Bootstrapping.substs1
  exact hb.subst hp (IsSemitermVec.singleton.mpr ht)

lemma QuantifierBoundedCode.free {L : Language} [L.Encodable]
    [L.LORDefinable] {b p : V} (hp : IsSemiformula L 1 p)
    (hb : QuantifierBoundedCode L b p) :
    QuantifierBoundedCode L b (free L p) := by
  exact ⟨hp.free.isUFormula, by
    simpa only [quantifierGroupsCode_free hp] using hb.2⟩

/-! ## Correctness on standard quoted formulas -/

mutual
  /-- External Sigma-polarity rank for Foundation's negation-normal syntax. -/
  def sigmaRank {L : Language} {ξ : Type*} {n : Nat} :
      Semiformula L ξ n → Nat
    | .verum => 0
    | .falsum => 0
    | .rel _ _ => 0
    | .nrel _ _ => 0
    | .and φ ψ => Nat.max (sigmaRank φ) (sigmaRank ψ)
    | .or φ ψ => Nat.max (sigmaRank φ) (sigmaRank ψ)
    | .all φ => Nat.max 1 (piRank φ) + 1
    | .exs φ => Nat.max 1 (sigmaRank φ)

  /-- External Pi-polarity rank for Foundation's negation-normal syntax. -/
  def piRank {L : Language} {ξ : Type*} {n : Nat} :
      Semiformula L ξ n → Nat
    | .verum => 0
    | .falsum => 0
    | .rel _ _ => 0
    | .nrel _ _ => 0
    | .and φ ψ => Nat.max (piRank φ) (piRank ψ)
    | .or φ ψ => Nat.max (piRank φ) (piRank ψ)
    | .all φ => Nat.max 1 (piRank φ)
    | .exs φ => Nat.max 1 (sigmaRank φ) + 1
end

/-- External least hierarchy level, matching `quantifierGroupsCode`. -/
def quantifierGroups {L : Language} {ξ : Type*} {n : Nat}
    (φ : Semiformula L ξ n) : Nat :=
  Nat.min (sigmaRank φ) (piRank φ)

/- Foundation deliberately equips every arithmetic model with its own
order-derived lattice instances.  On the standard model these relations and
operations are extensionally the ordinary natural-number ones, but they are
not definitionally the same typeclass instances.  The following small bridge
lemmas make that distinction explicit instead of relying on instance-ordering
accidents. -/
private lemma foundationLe_iff_natLe (a b : Nat) :
    @LE.le Nat instLE_foundation a b ↔ @LE.le Nat instLENat a b := by
  rw [le_def]
  omega

private noncomputable abbrev foundationNatSup : SemilatticeSup Nat :=
  (@instDistribLatticeOfLinearOrder Nat
    instLinearOrder_foundation).toLattice.toSemilatticeSup

private noncomputable abbrev foundationNatInf : SemilatticeInf Nat :=
  (@instDistribLatticeOfLinearOrder Nat
    instLinearOrder_foundation).toLattice.toSemilatticeInf

private lemma foundationMax_eq_natMax (a b : Nat) :
    @max Nat foundationNatSup.toMax a b = Nat.max a b := by
  by_cases h : @LE.le Nat instLENat a b
  · have hf : @LE.le Nat foundationNatSup.toLE a b := by
      change a = b ∨ a < b
      omega
    calc
      @max Nat foundationNatSup.toMax a b = b :=
        (@sup_eq_right Nat foundationNatSup a b).2 hf
      _ = Nat.max a b := (Nat.max_eq_right h).symm
  · have hba : @LE.le Nat instLENat b a := Nat.le_of_not_ge h
    have hfb : @LE.le Nat foundationNatSup.toLE b a := by
      change b = a ∨ b < a
      omega
    calc
      @max Nat foundationNatSup.toMax a b = a :=
        (@sup_eq_left Nat foundationNatSup a b).2 hfb
      _ = Nat.max a b := (Nat.max_eq_left hba).symm

private lemma foundationMin_eq_natMin (a b : Nat) :
    @min Nat foundationNatInf.toMin a b = Nat.min a b := by
  by_cases h : @LE.le Nat instLENat a b
  · have hf : @LE.le Nat foundationNatInf.toLE a b := by
      change a = b ∨ a < b
      omega
    calc
      @min Nat foundationNatInf.toMin a b = a :=
        (@inf_eq_left Nat foundationNatInf a b).2 hf
      _ = Nat.min a b := (Nat.min_eq_left h).symm
  · have hba : @LE.le Nat instLENat b a := Nat.le_of_not_ge h
    have hfb : @LE.le Nat foundationNatInf.toLE b a := by
      change b = a ∨ b < a
      omega
    calc
      @min Nat foundationNatInf.toMin a b = b :=
        (@inf_eq_right Nat foundationNatInf a b).2 hfb
      _ = Nat.min a b := (Nat.min_eq_right hba).symm

/-- The internal recursion computes exactly the external pair of hierarchy
ranks on every standard quoted formula. -/
theorem rankPair_quote {L : Language} [L.Encodable] [L.LORDefinable]
    {n : Nat} (φ : Semiproposition L n) :
    rankPair L (⌜φ⌝ : Nat) = ⟪sigmaRank φ, piRank φ⟫ := by
  induction φ with
  | verum =>
      change rankPair L (^⊤ : Nat) = ⟪0, 0⟫
      exact rankPair_verum
  | falsum =>
      change rankPair L (^⊥ : Nat) = ⟪0, 0⟫
      exact rankPair_falsum
  | rel R v =>
      rw [Semiformula.quote_rel]
      apply rankPair_rel
      · have h := Semiformula.quote_isSemiformula (V := Nat)
            (Semiformula.rel R v)
        rw [Semiformula.quote_rel] at h
        exact (IsSemiformula.rel.mp h).1
      · have h := Semiformula.quote_isSemiformula (V := Nat)
            (Semiformula.rel R v)
        rw [Semiformula.quote_rel] at h
        exact (IsSemiformula.rel.mp h).2.isUTerm
  | nrel R v =>
      rw [Semiformula.quote_nrel]
      apply rankPair_nrel
      · have h := Semiformula.quote_isSemiformula (V := Nat)
            (Semiformula.nrel R v)
        rw [Semiformula.quote_nrel] at h
        exact (IsSemiformula.nrel.mp h).1
      · have h := Semiformula.quote_isSemiformula (V := Nat)
            (Semiformula.nrel R v)
        rw [Semiformula.quote_nrel] at h
        exact (IsSemiformula.nrel.mp h).2.isUTerm
  | and φ ψ ihφ ihψ =>
      change rankPair L ((⌜φ⌝ : Nat) ^⋏ (⌜ψ⌝ : Nat)) =
        ⟪Nat.max (sigmaRank φ) (sigmaRank ψ),
          Nat.max (piRank φ) (piRank ψ)⟫
      rw [rankPair_and
        (Semiformula.quote_isSemiformula φ).isUFormula
        (Semiformula.quote_isSemiformula ψ).isUFormula]
      simp [sigmaRankCode, piRankCode, ihφ, ihψ]
      exact ⟨foundationMax_eq_natMax _ _, foundationMax_eq_natMax _ _⟩
  | or φ ψ ihφ ihψ =>
      change rankPair L ((⌜φ⌝ : Nat) ^⋎ (⌜ψ⌝ : Nat)) =
        ⟪Nat.max (sigmaRank φ) (sigmaRank ψ),
          Nat.max (piRank φ) (piRank ψ)⟫
      rw [rankPair_or
        (Semiformula.quote_isSemiformula φ).isUFormula
        (Semiformula.quote_isSemiformula ψ).isUFormula]
      simp [sigmaRankCode, piRankCode, ihφ, ihψ]
      exact ⟨foundationMax_eq_natMax _ _, foundationMax_eq_natMax _ _⟩
  | all φ ih =>
      change rankPair L (^∀ (⌜φ⌝ : Nat)) =
        ⟪Nat.max 1 (piRank φ) + 1, Nat.max 1 (piRank φ)⟫
      rw [rankPair_all (Semiformula.quote_isSemiformula φ).isUFormula]
      simp [piRankCode, ih]
      exact foundationMax_eq_natMax _ _
  | exs φ ih =>
      change rankPair L (^∃ (⌜φ⌝ : Nat)) =
        ⟪Nat.max 1 (sigmaRank φ), Nat.max 1 (sigmaRank φ) + 1⟫
      rw [rankPair_exs (Semiformula.quote_isSemiformula φ).isUFormula]
      simp [sigmaRankCode, ih]
      exact foundationMax_eq_natMax _ _

@[simp] theorem sigmaRankCode_quote {L : Language} [L.Encodable]
    [L.LORDefinable] {n : Nat} (φ : Semiproposition L n) :
    sigmaRankCode L (⌜φ⌝ : Nat) = sigmaRank φ := by
  simp [sigmaRankCode, rankPair_quote]

@[simp] theorem piRankCode_quote {L : Language} [L.Encodable]
    [L.LORDefinable] {n : Nat} (φ : Semiproposition L n) :
    piRankCode L (⌜φ⌝ : Nat) = piRank φ := by
  simp [piRankCode, rankPair_quote]

@[simp] theorem quantifierGroupsCode_quote {L : Language} [L.Encodable]
    [L.LORDefinable] {n : Nat} (φ : Semiproposition L n) :
    quantifierGroupsCode L (⌜φ⌝ : Nat) = quantifierGroups φ := by
  simp only [quantifierGroupsCode, sigmaRankCode_quote, piRankCode_quote,
    quantifierGroups]
  exact foundationMin_eq_natMin _ _

theorem quantifierBoundedCode_quote_iff {L : Language} [L.Encodable]
    [L.LORDefinable] {n k : Nat} (φ : Semiproposition L k) :
    QuantifierBoundedCode L n (⌜φ⌝ : Nat) ↔
      @LE.le Nat instLENat (quantifierGroups φ) n := by
  constructor
  · intro h
    apply (foundationLe_iff_natLe (quantifierGroups φ) n).1
    simpa only [quantifierGroupsCode_quote] using h.2
  · intro h
    refine ⟨(Semiformula.quote_isSemiformula φ).isUFormula, ?_⟩
    simpa only [quantifierGroupsCode_quote] using
      (foundationLe_iff_natLe (quantifierGroups φ) n).2 h

end LeanProofs.BoundedPAConsistency.CodedHierarchy
