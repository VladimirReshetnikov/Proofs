import BoundedPAConsistency.CodedHierarchy

/-!
# Polarity-oriented domains for fixed-level partial truth

`QuantifierBoundedCode` records the smaller of the Sigma- and Pi-polarity
ranks.  A partial-truth construction must know *which* rank realizes that
minimum: existential and universal quantifier heads recurse differently.

This file exposes the two oriented domains separately.  Every theorem is
about Foundation formula codes inside an arbitrary model of `I Sigma 1`; in
particular, none of the constructor inversions decodes a model element into a
standard Lean formula.  The bounds below are model elements as well, so the
interface is also valid for nonstandard bounds even though the eventual truth
predicates will be indexed only by external standard naturals.
-/

namespace LeanProofs.BoundedPAConsistency.OrientedHierarchy

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Oriented domains -/

/-- `p` is a well-formed code whose Sigma-polarity rank is at most `n`. -/
def IsSigmaCode (L : Language) [L.Encodable] [L.LORDefinable]
    (n p : V) : Prop :=
  IsUFormula L p ∧ sigmaRankCode L p ≤ n

/-- `p` is a well-formed code whose Pi-polarity rank is at most `n`. -/
def IsPiCode (L : Language) [L.Encodable] [L.LORDefinable]
    (n p : V) : Prop :=
  IsUFormula L p ∧ piRankCode L p ≤ n

instance IsSigmaCode.definable :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.sigmaOne
      (IsSigmaCode L) := by
  unfold IsSigmaCode
  definability

instance IsPiCode.definable :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.sigmaOne
      (IsPiCode L) := by
  unfold IsPiCode
  definability

lemma IsSigmaCode.isUFormula {n p : V} (h : IsSigmaCode L n p) :
    IsUFormula L p := h.1

lemma IsPiCode.isUFormula {n p : V} (h : IsPiCode L n p) :
    IsUFormula L p := h.1

lemma IsSigmaCode.rank_le {n p : V} (h : IsSigmaCode L n p) :
    sigmaRankCode L p ≤ n := h.2

lemma IsPiCode.rank_le {n p : V} (h : IsPiCode L n p) :
    piRankCode L p ≤ n := h.2

/-- Resolving the minimum in `QuantifierBoundedCode` gives exactly one of the
two oriented domains (and possibly both). -/
@[simp] theorem quantifierBoundedCode_iff_sigma_or_pi {n p : V} :
    QuantifierBoundedCode L n p ↔
      IsSigmaCode L n p ∨ IsPiCode L n p := by
  simp only [QuantifierBoundedCode, quantifierGroupsCode, IsSigmaCode,
    IsPiCode, min_le_iff]
  aesop

lemma IsSigmaCode.quantifierBounded {n p : V} (h : IsSigmaCode L n p) :
    QuantifierBoundedCode L n p :=
  quantifierBoundedCode_iff_sigma_or_pi.mpr (Or.inl h)

lemma IsPiCode.quantifierBounded {n p : V} (h : IsPiCode L n p) :
    QuantifierBoundedCode L n p :=
  quantifierBoundedCode_iff_sigma_or_pi.mpr (Or.inr h)

lemma IsSigmaCode.mono {m n p : V} (hmn : m ≤ n)
    (h : IsSigmaCode L m p) : IsSigmaCode L n p :=
  ⟨h.1, le_trans h.2 hmn⟩

lemma IsPiCode.mono {m n p : V} (hmn : m ≤ n)
    (h : IsPiCode L m p) : IsPiCode L n p :=
  ⟨h.1, le_trans h.2 hmn⟩

/-! ## Formula constructors -/

@[simp] theorem isSigmaCode_rel {n k R terms : V}
    (hR : L.IsRel k R) (hterms : IsUTermVec L k terms) :
    IsSigmaCode L n (^rel k R terms) := by
  simp [IsSigmaCode, sigmaRankCode, hR, hterms]

@[simp] theorem isPiCode_rel {n k R terms : V}
    (hR : L.IsRel k R) (hterms : IsUTermVec L k terms) :
    IsPiCode L n (^rel k R terms) := by
  simp [IsPiCode, piRankCode, hR, hterms]

@[simp] theorem isSigmaCode_nrel {n k R terms : V}
    (hR : L.IsRel k R) (hterms : IsUTermVec L k terms) :
    IsSigmaCode L n (^nrel k R terms) := by
  simp [IsSigmaCode, sigmaRankCode, hR, hterms]

@[simp] theorem isPiCode_nrel {n k R terms : V}
    (hR : L.IsRel k R) (hterms : IsUTermVec L k terms) :
    IsPiCode L n (^nrel k R terms) := by
  simp [IsPiCode, piRankCode, hR, hterms]

@[simp] theorem isSigmaCode_verum {n : V} :
    IsSigmaCode (V := V) L n ^⊤ := by
  simp [IsSigmaCode, sigmaRankCode]

@[simp] theorem isPiCode_verum {n : V} :
    IsPiCode (V := V) L n ^⊤ := by
  simp [IsPiCode, piRankCode]

@[simp] theorem isSigmaCode_falsum {n : V} :
    IsSigmaCode (V := V) L n ^⊥ := by
  simp [IsSigmaCode, sigmaRankCode]

@[simp] theorem isPiCode_falsum {n : V} :
    IsPiCode (V := V) L n ^⊥ := by
  simp [IsPiCode, piRankCode]

@[simp] theorem isSigmaCode_and_iff {n p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    IsSigmaCode L n (p ^⋏ q) ↔
      IsSigmaCode L n p ∧ IsSigmaCode L n q := by
  simp [IsSigmaCode, hp, hq]

@[simp] theorem isPiCode_and_iff {n p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    IsPiCode L n (p ^⋏ q) ↔
      IsPiCode L n p ∧ IsPiCode L n q := by
  simp [IsPiCode, hp, hq]

@[simp] theorem isSigmaCode_or_iff {n p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    IsSigmaCode L n (p ^⋎ q) ↔
      IsSigmaCode L n p ∧ IsSigmaCode L n q := by
  simp [IsSigmaCode, hp, hq]

@[simp] theorem isPiCode_or_iff {n p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    IsPiCode L n (p ^⋎ q) ↔
      IsPiCode L n p ∧ IsPiCode L n q := by
  simp [IsPiCode, hp, hq]

/-! ## Quantifier constructors -/

/-- Existential quantification stays on the Sigma side, provided the level is
positive.  The positivity conjunct is intentionally explicit at an arbitrary
model bound. -/
@[simp] theorem isSigmaCode_exs_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L n (^∃ p) ↔
      IsSigmaCode L n p ∧ 1 ≤ n := by
  simp [IsSigmaCode, hp]
  aesop

/-- Universal quantification stays on the Pi side at every positive level. -/
@[simp] theorem isPiCode_all_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L n (^∀ p) ↔
      IsPiCode L n p ∧ 1 ≤ n := by
  simp [IsPiCode, hp]
  aesop

/-- A universal head on the Sigma side consumes one hierarchy level and
switches to the Pi rank of its body. -/
@[simp] theorem isSigmaCode_all_succ_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L (n + 1) (^∀ p) ↔
      IsPiCode L n p ∧ 1 ≤ n := by
  simp [IsSigmaCode, IsPiCode, hp]
  aesop

/-- An existential head on the Pi side consumes one hierarchy level and
switches to the Sigma rank of its body. -/
@[simp] theorem isPiCode_exs_succ_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L (n + 1) (^∃ p) ↔
      IsSigmaCode L n p ∧ 1 ≤ n := by
  simp [IsSigmaCode, IsPiCode, hp]
  aesop

/-- Successor levels are automatically positive, so same-polarity
quantification has no side condition in the form used by partial truth. -/
@[simp] theorem isSigmaCode_exs_succ_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L (n + 1) (^∃ p) ↔
      IsSigmaCode L (n + 1) p := by
  simp [isSigmaCode_exs_iff hp]

@[simp] theorem isPiCode_all_succ_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L (n + 1) (^∀ p) ↔
      IsPiCode L (n + 1) p := by
  simp [isPiCode_all_iff hp]

/-- At level `n + 2`, an opposite-polarity head switches cleanly to level
`n + 1`; this avoids carrying a positivity premise through the external
recursion on hierarchy levels. -/
@[simp] theorem isSigmaCode_all_add_two_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L (n + 1 + 1) (^∀ p) ↔
      IsPiCode L (n + 1) p := by
  simpa using isSigmaCode_all_succ_iff (L := L) (n := n + 1) hp

@[simp] theorem isPiCode_exs_add_two_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L (n + 1 + 1) (^∃ p) ↔
      IsSigmaCode L (n + 1) p := by
  simpa using isPiCode_exs_succ_iff (L := L) (n := n + 1) hp

@[simp] theorem not_isSigmaCode_all_zero {p : V}
    (hp : IsUFormula L p) :
    ¬IsSigmaCode L 0 (^∀ p) := by
  simp [IsSigmaCode, hp]

@[simp] theorem not_isPiCode_exs_zero {p : V}
    (hp : IsUFormula L p) :
    ¬IsPiCode L 0 (^∃ p) := by
  simp [IsPiCode, hp]

/-! ## Negation and syntax transport -/

/-- Coded negation exchanges the two oriented domains. -/
@[simp] theorem isSigmaCode_neg_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L n (neg L p) ↔ IsPiCode L n p := by
  simp [IsSigmaCode, IsPiCode, hp]

@[simp] theorem isPiCode_neg_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L n (neg L p) ↔ IsSigmaCode L n p := by
  simp [IsSigmaCode, IsPiCode, hp]

@[simp] theorem isSigmaCode_shift_iff {n p : V}
    (hp : IsUFormula L p) :
    IsSigmaCode L n (shift L p) ↔ IsSigmaCode L n p := by
  simp [IsSigmaCode, sigmaRankCode, hp]

@[simp] theorem isPiCode_shift_iff {n p : V}
    (hp : IsUFormula L p) :
    IsPiCode L n (shift L p) ↔ IsPiCode L n p := by
  simp [IsPiCode, piRankCode, hp]

lemma IsSigmaCode.subst {b n m p w : V}
    (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w)
    (h : IsSigmaCode L b p) :
    IsSigmaCode L b (subst L w p) := by
  exact ⟨(hp.subst hw).isUFormula, by
    simpa [sigmaRankCode, rankPair_subst hp hw] using h.2⟩

lemma IsPiCode.subst {b n m p w : V}
    (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w)
    (h : IsPiCode L b p) :
    IsPiCode L b (subst L w p) := by
  exact ⟨(hp.subst hw).isUFormula, by
    simpa [piRankCode, rankPair_subst hp hw] using h.2⟩

@[simp] theorem isSigmaCode_subst_iff {b n m p w : V}
    (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w) :
    IsSigmaCode L b (subst L w p) ↔ IsSigmaCode L b p := by
  constructor
  · intro h
    exact ⟨hp.isUFormula, by
      simpa [sigmaRankCode, rankPair_subst hp hw] using h.2⟩
  · exact IsSigmaCode.subst hp hw

@[simp] theorem isPiCode_subst_iff {b n m p w : V}
    (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w) :
    IsPiCode L b (subst L w p) ↔ IsPiCode L b p := by
  constructor
  · intro h
    exact ⟨hp.isUFormula, by
      simpa [piRankCode, rankPair_subst hp hw] using h.2⟩
  · exact IsPiCode.subst hp hw

@[simp] theorem isSigmaCode_substs1_iff {b m p t : V}
    (hp : IsSemiformula L 1 p) (ht : IsSemiterm L m t) :
    IsSigmaCode L b (substs1 L t p) ↔ IsSigmaCode L b p := by
  unfold substs1
  exact isSigmaCode_subst_iff hp (IsSemitermVec.singleton.mpr ht)

@[simp] theorem isPiCode_substs1_iff {b m p t : V}
    (hp : IsSemiformula L 1 p) (ht : IsSemiterm L m t) :
    IsPiCode L b (substs1 L t p) ↔ IsPiCode L b p := by
  unfold substs1
  exact isPiCode_subst_iff hp (IsSemitermVec.singleton.mpr ht)

/-- Opening the outer bound variable as free preserves each orientation.  This
is the domain fact used by the coded universal-introduction rule. -/
@[simp] theorem isSigmaCode_free_iff {b p : V}
    (hp : IsSemiformula L 1 p) :
    IsSigmaCode L b (free L p) ↔ IsSigmaCode L b p := by
  unfold free
  rw [isSigmaCode_substs1_iff hp.shift
      (show IsSemiterm (V := V) L 0 ^&0 by simp),
    isSigmaCode_shift_iff hp.isUFormula]

@[simp] theorem isPiCode_free_iff {b p : V}
    (hp : IsSemiformula L 1 p) :
    IsPiCode L b (free L p) ↔ IsPiCode L b p := by
  unfold free
  rw [isPiCode_substs1_iff hp.shift
      (show IsSemiterm (V := V) L 0 ^&0 by simp),
    isPiCode_shift_iff hp.isUFormula]

end LeanProofs.BoundedPAConsistency.OrientedHierarchy
