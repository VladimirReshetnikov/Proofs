import BoundedPAConsistency.QuantifierFreeTruth

/-!
# Structural Tarski interface for rank-zero coded truth

`QuantifierFreeTruth` constructs the represented Boolean evaluator.  This
module begins the rule-facing interface by proving that the level-zero rank
test has the expected structural consequences on arbitrary, possibly
nonstandard, formula codes.  In particular, a zero *least* polarity rank is
shown internally to force both polarity ranks to zero; this rules out a
spurious mixed-polarity reading of the minimum in later inversion proofs.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTarski

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.TermEvaluation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- For a well-formed code, hierarchy level zero is equivalent to both
polarity ranks being zero.  The nontrivial forward direction is proved by
internal structural induction and therefore includes nonstandard codes. -/
theorem quantifierGroupsCode_eq_zero_iff {p : V}
    (hp : IsUFormula ℒₒᵣ p) :
    quantifierGroupsCode ℒₒᵣ p = 0 ↔
      sigmaRankCode ℒₒᵣ p = 0 ∧ piRankCode ℒₒᵣ p = 0 := by
  constructor
  · revert p
    apply IsUFormula.ISigma1.pi1_succ_induction
        (P := fun p : V ↦ quantifierGroupsCode ℒₒᵣ p = 0 →
          sigmaRankCode ℒₒᵣ p = 0 ∧ piRankCode ℒₒᵣ p = 0)
    · definability
    · intro k R terms hR hterms
      simp [hR, hterms, quantifierGroupsCode, sigmaRankCode, piRankCode]
    · intro k R terms hR hterms
      simp [hR, hterms, quantifierGroupsCode, sigmaRankCode, piRankCode]
    · simp [quantifierGroupsCode, sigmaRankCode, piRankCode]
    · simp [quantifierGroupsCode, sigmaRankCode, piRankCode]
    · intro p q hp hq ihp ihq hzero
      simp [quantifierGroupsCode, hp, hq, sigmaRankCode, piRankCode] at hzero
      rcases hzero with ⟨hsp, hsq⟩ | ⟨hpp, hpq⟩
      · have hsp' : sigmaRankCode ℒₒᵣ p = 0 := by
          simpa [sigmaRankCode] using hsp
        have hsq' : sigmaRankCode ℒₒᵣ q = 0 := by
          simpa [sigmaRankCode] using hsq
        have ip := ihp (by simp [quantifierGroupsCode, hsp'])
        have iq := ihq (by simp [quantifierGroupsCode, hsq'])
        simp [hp, hq, ip.1, ip.2, iq.1, iq.2]
      · have hpp' : piRankCode ℒₒᵣ p = 0 := by
          simpa [piRankCode] using hpp
        have hpq' : piRankCode ℒₒᵣ q = 0 := by
          simpa [piRankCode] using hpq
        have ip := ihp (by simp [quantifierGroupsCode, hpp'])
        have iq := ihq (by simp [quantifierGroupsCode, hpq'])
        simp [hp, hq, ip.1, ip.2, iq.1, iq.2]
    · intro p q hp hq ihp ihq hzero
      simp [quantifierGroupsCode, hp, hq, sigmaRankCode, piRankCode] at hzero
      rcases hzero with ⟨hsp, hsq⟩ | ⟨hpp, hpq⟩
      · have hsp' : sigmaRankCode ℒₒᵣ p = 0 := by
          simpa [sigmaRankCode] using hsp
        have hsq' : sigmaRankCode ℒₒᵣ q = 0 := by
          simpa [sigmaRankCode] using hsq
        have ip := ihp (by simp [quantifierGroupsCode, hsp'])
        have iq := ihq (by simp [quantifierGroupsCode, hsq'])
        simp [hp, hq, ip.1, ip.2, iq.1, iq.2]
      · have hpp' : piRankCode ℒₒᵣ p = 0 := by
          simpa [piRankCode] using hpp
        have hpq' : piRankCode ℒₒᵣ q = 0 := by
          simpa [piRankCode] using hpq
        have ip := ihp (by simp [quantifierGroupsCode, hpp'])
        have iq := ihq (by simp [quantifierGroupsCode, hpq'])
        simp [hp, hq, ip.1, ip.2, iq.1, iq.2]
    · intro p hp ih hzero
      simp [quantifierGroupsCode, hp, sigmaRankCode, piRankCode] at hzero
    · intro p hp ih hzero
      simp [quantifierGroupsCode, hp, sigmaRankCode, piRankCode] at hzero
  · rintro ⟨hs, hp'⟩
    simp [quantifierGroupsCode, hs, hp']

/-! ## Structural characterization of the semantic domain -/

/-- The represented rank-zero predicate is exactly simultaneous zero in both
polarities.  Retaining the explicit well-formedness conjunct is useful when
the theorem is consumed by proof-rule inversion. -/
theorem isQuantifierFreeCode_iff {p : V} :
    IsQuantifierFreeCode p ↔
      IsUFormula ℒₒᵣ p ∧
      sigmaRankCode ℒₒᵣ p = 0 ∧ piRankCode ℒₒᵣ p = 0 := by
  constructor
  · intro hp
    exact ⟨hp.1, (quantifierGroupsCode_eq_zero_iff hp.1).mp
      (nonpos_iff_eq_zero.mp hp.2)⟩
  · rintro ⟨hp, hs, hpi⟩
    exact ⟨hp, by simp [quantifierGroupsCode, hs, hpi]⟩

@[simp] theorem isQuantifierFreeCode_rel {k R terms : V}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    IsQuantifierFreeCode (^rel k R terms) := by
  simp [isQuantifierFreeCode_iff, hR, hterms, sigmaRankCode, piRankCode]

@[simp] theorem isQuantifierFreeCode_nrel {k R terms : V}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    IsQuantifierFreeCode (^nrel k R terms) := by
  simp [isQuantifierFreeCode_iff, hR, hterms, sigmaRankCode, piRankCode]

@[simp] theorem isQuantifierFreeCode_verum :
    IsQuantifierFreeCode (V := V) ^⊤ := by
  simp [isQuantifierFreeCode_iff, sigmaRankCode, piRankCode]

@[simp] theorem isQuantifierFreeCode_falsum :
    IsQuantifierFreeCode (V := V) ^⊥ := by
  simp [isQuantifierFreeCode_iff, sigmaRankCode, piRankCode]

@[simp] theorem isQuantifierFreeCode_and_iff {p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    IsQuantifierFreeCode (p ^⋏ q) ↔
      IsQuantifierFreeCode p ∧ IsQuantifierFreeCode q := by
  simp only [isQuantifierFreeCode_iff]
  simp only [hp, hq, IsUFormula.and, and_self, sigmaRankCode_and,
    piRankCode_and, max_eq_zero]
  aesop

@[simp] theorem isQuantifierFreeCode_or_iff {p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    IsQuantifierFreeCode (p ^⋎ q) ↔
      IsQuantifierFreeCode p ∧ IsQuantifierFreeCode q := by
  simp only [isQuantifierFreeCode_iff]
  simp only [hp, hq, IsUFormula.or, and_self, sigmaRankCode_or,
    piRankCode_or, max_eq_zero]
  aesop

@[simp] theorem isQuantifierFreeCode_neg_iff {p : V}
    (hp : IsUFormula ℒₒᵣ p) :
    IsQuantifierFreeCode (neg ℒₒᵣ p) ↔ IsQuantifierFreeCode p := by
  exact QuantifierBoundedCode.neg_iff hp

theorem not_isQuantifierFreeCode_all {p : V} (hp : IsUFormula ℒₒᵣ p) :
    ¬IsQuantifierFreeCode (^∀ p) := by
  simp [isQuantifierFreeCode_iff, hp]

theorem not_isQuantifierFreeCode_exs {p : V} (hp : IsUFormula ℒₒᵣ p) :
    ¬IsQuantifierFreeCode (^∃ p) := by
  simp [isQuantifierFreeCode_iff, hp]

/-! ## Boolean and Tarski clauses -/

/-- On a well-formed code, zero is exactly failure to have Boolean value one.
This small bridge keeps subsequent falsity clauses independent of the
evaluator's totalization away from well-formed formula codes. -/
theorem qfValue_eq_zero_iff_not_eq_one {bound free p : V}
    (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound free p = 0 ↔ qfValue bound free p ≠ 1 := by
  rcases qfValue_isBit (bound := bound) (free := free) hp with h | h <;>
    simp [h]

@[simp] theorem qfValue_and_eq_zero_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋏ q) = 0 ↔
      qfValue bound free p = 0 ∨ qfValue bound free q = 0 := by
  rw [qfValue_and hp hq]
  rcases qfValue_isBit (bound := bound) (free := free) hp with h₁ | h₁ <;>
    rcases qfValue_isBit (bound := bound) (free := free) hq with h₂ | h₂ <;>
    simp [bitAnd, h₁, h₂]

@[simp] theorem qfValue_or_eq_zero_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    qfValue bound free (p ^⋎ q) = 0 ↔
      qfValue bound free p = 0 ∧ qfValue bound free q = 0 := by
  rw [qfValue_or hp hq]
  rcases qfValue_isBit (bound := bound) (free := free) hp with h₁ | h₁ <;>
    rcases qfValue_isBit (bound := bound) (free := free) hq with h₂ | h₂ <;>
    simp [bitOr, h₁, h₂]

@[simp] theorem qfTrue_verum {bound free : V} :
    QFTrue bound free ^⊤ := by
  simp [QFTrue]

@[simp] theorem not_qfTrue_falsum {bound free : V} :
    ¬QFTrue bound free ^⊥ := by
  simp [QFTrue]

@[simp] theorem not_qfFalse_verum {bound free : V} :
    ¬QFFalse bound free ^⊤ := by
  simp [QFFalse]

@[simp] theorem qfFalse_falsum {bound free : V} :
    QFFalse bound free ^⊥ := by
  simp [QFFalse]

@[simp] theorem qfTrue_and_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    QFTrue bound free (p ^⋏ q) ↔
      QFTrue bound free p ∧ QFTrue bound free q := by
  simp only [QFTrue, isQuantifierFreeCode_and_iff hp hq,
    qfValue_and_eq_one_iff hp hq]
  aesop

@[simp] theorem qfFalse_and_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hbp : IsQuantifierFreeCode p) (hbq : IsQuantifierFreeCode q) :
    QFFalse bound free (p ^⋏ q) ↔
      QFFalse bound free p ∨ QFFalse bound free q := by
  simp only [QFFalse, isQuantifierFreeCode_and_iff hp hq,
    qfValue_and_eq_zero_iff hp hq]
  simp [hbp, hbq]

@[simp] theorem qfTrue_or_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hbp : IsQuantifierFreeCode p) (hbq : IsQuantifierFreeCode q) :
    QFTrue bound free (p ^⋎ q) ↔
      QFTrue bound free p ∨ QFTrue bound free q := by
  simp only [QFTrue, isQuantifierFreeCode_or_iff hp hq,
    qfValue_or_eq_one_iff hp hq]
  simp [hbp, hbq]

@[simp] theorem qfFalse_or_iff {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    QFFalse bound free (p ^⋎ q) ↔
      QFFalse bound free p ∧ QFFalse bound free q := by
  simp only [QFFalse, isQuantifierFreeCode_or_iff hp hq,
    qfValue_or_eq_zero_iff hp hq]
  aesop

@[simp] theorem qfTrue_eq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFTrue bound free
        (^rel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ = termValue bound free t₁ := by
  simp [QFTrue, ht₀, ht₁]

@[simp] theorem qfTrue_neq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFTrue bound free
        (^nrel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ ≠ termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ = termValue bound free t₁ <;>
    simp [QFTrue, ht₀, ht₁, bitNot, h]

@[simp] theorem qfTrue_lt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFTrue bound free
        (^rel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ < termValue bound free t₁ := by
  simp [QFTrue, ht₀, ht₁]

@[simp] theorem qfTrue_nlt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFTrue bound free
        (^nrel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) ↔
      ¬termValue bound free t₀ < termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ < termValue bound free t₁ <;>
    simp [QFTrue, ht₀, ht₁, bitNot, h]

@[simp] theorem qfFalse_eq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFFalse bound free
        (^rel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ ≠ termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ = termValue bound free t₁ <;>
    simp [QFFalse, ht₀, ht₁, h]

@[simp] theorem qfFalse_neq_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFFalse bound free
        (^nrel 2 (Arithmetic.eqIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ = termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ = termValue bound free t₁ <;>
    simp [QFFalse, ht₀, ht₁, bitNot, h]

@[simp] theorem qfFalse_lt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFFalse bound free
        (^rel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) ↔
      ¬termValue bound free t₀ < termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ < termValue bound free t₁ <;>
    simp [QFFalse, ht₀, ht₁, h]

@[simp] theorem qfFalse_nlt_atom_iff {bound free t₀ t₁ : V}
    (ht₀ : IsUTerm ℒₒᵣ t₀) (ht₁ : IsUTerm ℒₒᵣ t₁) :
    QFFalse bound free
        (^nrel 2 (Arithmetic.ltIndex : V) ?[t₀, t₁]) ↔
      termValue bound free t₀ < termValue bound free t₁ := by
  by_cases h : termValue bound free t₀ < termValue bound free t₁ <;>
    simp [QFFalse, ht₀, ht₁, bitNot, h]

end LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
