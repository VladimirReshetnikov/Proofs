import BoundedPAConsistency.QuantifierFreeTarski
import BoundedPAConsistency.TermEvaluationTransport

/-!
# Semantic transport for coded rank-zero truth

The evaluator in `QuantifierFreeTruth` runs directly on formula codes in an
arbitrary model of `I Sigma 1`.  This file proves that its value is invariant
under the syntax operations used by the coded proof calculus.  All structural
arguments use Foundation's internal induction principles, so the statements
also cover nonstandard formula and term codes in nonstandard models.

Negation is deliberately restricted to `IsQuantifierFreeCode`: the total
rank-zero evaluator assigns the dummy value zero to both quantified
constructors, and hence cannot satisfy a complement law outside its advertised
semantic domain.  Shift and simultaneous substitution do preserve the total
value on every well-formed formula, since quantified constructors have the
same dummy value on both sides.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTransport

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## Boolean algebra used by negation -/

/-- A small represented graph for `bitNot`.  The rank-zero evaluator already
uses this function in its recursive construction, but exposing its graph here
lets the internal formula induction see the complement equation as a
Pi-one-definable property. -/
noncomputable def bitNotTransportGraph :
    HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “y x. (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y = 0)”

instance bitNot.defined_transport :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaOne
      (bitNot : V → V) bitNotTransportGraph := .mk fun v ↦ by
  simp [bitNotTransportGraph, bitNot]
  by_cases h : v 1 = 0 <;> simp [h]

instance bitNot.definable_transport :
    HierarchySymbol.DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne
      (bitNot : V → V) :=
  bitNot.defined_transport.to_definable

instance bitNot.definable_transport' :
    Γ-[k + 1]-Function₁ (bitNot : V → V) :=
  bitNot.definable_transport.of_sigmaOne

theorem bitNot_bitNot_of_isBit {x : V} (hx : x = 0 ∨ x = 1) :
    bitNot (bitNot x) = x := by
  rcases hx with rfl | rfl <;> simp [bitNot]

theorem bitOr_bitNot_eq_bitNot_bitAnd (x y : V) :
    bitOr (bitNot x) (bitNot y) = bitNot (bitAnd x y) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [bitNot, bitAnd, bitOr, hx, hy]

theorem bitAnd_bitNot_eq_bitNot_bitOr (x y : V) :
    bitAnd (bitNot x) (bitNot y) = bitNot (bitOr x y) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [bitNot, bitAnd, bitOr, hx, hy]

/-! ## Negation -/

/-- Coded negation complements the rank-zero evaluator on every internally
coded quantifier-free formula.  The proof does not decode `p`; in particular,
it applies to nonstandard well-founded syntax codes in nonstandard models. -/
@[simp] theorem qfValue_neg {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    qfValue bound free (neg ℒₒᵣ p) = bitNot (qfValue bound free p) := by
  have hmain : ∀ p : V, IsUFormula ℒₒᵣ p →
      IsQuantifierFreeCode p →
        qfValue bound free (neg ℒₒᵣ p) = bitNot (qfValue bound free p) := by
    apply IsUFormula.ISigma1.pi1_succ_induction
        (P := fun p : V ↦ IsQuantifierFreeCode p →
          qfValue bound free (neg ℒₒᵣ p) = bitNot (qfValue bound free p))
    · definability
    · intro k R terms hR hterms _
      simp [hR, hterms]
    · intro k R terms hR hterms _
      rw [neg_nrel hR hterms, qfValue_rel hR hterms,
        qfValue_nrel hR hterms]
      exact (bitNot_bitNot_of_isBit (atomicBit_isBit R
        (termValues bound free k terms))).symm
    · intro _
      simp [bitNot]
    · intro _
      simp [bitNot]
    · intro p q hp hq ihp ihq hpq
      have hparts := (isQuantifierFreeCode_and_iff hp hq).mp hpq
      rw [neg_and hp hq, qfValue_or hp.neg hq.neg,
        qfValue_and hp hq, ihp hparts.1, ihq hparts.2]
      exact bitOr_bitNot_eq_bitNot_bitAnd _ _
    · intro p q hp hq ihp ihq hpq
      have hparts := (isQuantifierFreeCode_or_iff hp hq).mp hpq
      rw [neg_or hp hq, qfValue_and hp.neg hq.neg,
        qfValue_or hp hq, ihp hparts.1, ihq hparts.2]
      exact bitAnd_bitNot_eq_bitNot_bitOr _ _
    · intro p hp ih hpq
      exact (not_isQuantifierFreeCode_all hp hpq).elim
    · intro p hp ih hpq
      exact (not_isQuantifierFreeCode_exs hp hpq).elim
  exact hmain p hp.1 hp

/-- Truth of a coded negation is falsity of its rank-zero operand. -/
@[simp] theorem qfTrue_neg_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    QFTrue bound free (neg ℒₒᵣ p) ↔ QFFalse bound free p := by
  have hneg : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
    (isQuantifierFreeCode_neg_iff hp.1).mpr hp
  unfold QFTrue QFFalse
  rw [qfValue_neg hp]
  rcases qfValue_isBit (bound := bound) (free := free) hp.1 with h | h <;>
    simp [hp, hneg, h, bitNot]

/-- Falsity of a coded negation is truth of its rank-zero operand. -/
@[simp] theorem qfFalse_neg_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    QFFalse bound free (neg ℒₒᵣ p) ↔ QFTrue bound free p := by
  have hneg : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
    (isQuantifierFreeCode_neg_iff hp.1).mpr hp
  unfold QFFalse QFTrue
  rw [qfValue_neg hp]
  rcases qfValue_isBit (bound := bound) (free := free) hp.1 with h | h <;>
    simp [hp, hneg, h, bitNot]

/-! ## Free-variable shift -/

/-- Evaluation commutes with coded free-variable shift when `shifted` has the
same tail lookups as `free`.  This is the exact semantic condition used by a
shifted free-variable code; no decoding to an external formula is involved. -/
theorem qfValue_shift_of_isFreeTail
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound shifted (shift ℒₒᵣ p) = qfValue bound free p := by
  have hmain : ∀ p : V, IsUFormula ℒₒᵣ p →
      qfValue bound shifted (shift ℒₒᵣ p) = qfValue bound free p := by
    apply IsUFormula.ISigma1.pi1_succ_induction
        (P := fun p : V ↦
          qfValue bound shifted (shift ℒₒᵣ p) = qfValue bound free p)
    · definability
    · intro k R terms hR hterms
      rw [shift_rel hR hterms,
        qfValue_rel hR hterms.termShiftVec,
        qfValue_rel hR hterms,
        termValues_termShiftVec_of_isFreeTail hfree hterms]
    · intro k R terms hR hterms
      rw [shift_nrel hR hterms,
        qfValue_nrel hR hterms.termShiftVec,
        qfValue_nrel hR hterms,
        termValues_termShiftVec_of_isFreeTail hfree hterms]
    · simp
    · simp
    · intro p q hp hq ihp ihq
      rw [shift_and hp hq, qfValue_and hp.shift hq.shift,
        qfValue_and hp hq, ihp, ihq]
    · intro p q hp hq ihp ihq
      rw [shift_or hp hq, qfValue_or hp.shift hq.shift,
        qfValue_or hp hq, ihp, ihq]
    · intro p hp ihp
      rw [shift_all hp, qfValue_all hp.shift, qfValue_all hp]
    · intro p hp ihp
      rw [shift_exs hp, qfValue_exs hp.shift, qfValue_exs hp]
  exact hmain p hp

/-- Fresh-head specialization of formula-shift transport. -/
theorem qfValue_shift_of_isFreeHead
    {bound fresh shifted free p : V}
    (hfree : IsFreeHead fresh shifted free)
    (hp : IsUFormula ℒₒᵣ p) :
    qfValue bound shifted (shift ℒₒᵣ p) = qfValue bound free p :=
  qfValue_shift_of_isFreeTail hfree.2.2.2.2 hp

/-- Rank-zero truth is invariant under the corresponding free-environment
tail shift. -/
theorem qfTrue_shift_iff_of_isFreeTail
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsQuantifierFreeCode p) :
    QFTrue bound shifted (shift ℒₒᵣ p) ↔ QFTrue bound free p := by
  have hshift : IsQuantifierFreeCode (shift ℒₒᵣ p) :=
    (QuantifierBoundedCode.shift_iff hp.1).mpr hp
  unfold QFTrue
  rw [qfValue_shift_of_isFreeTail hfree hp.1]
  simp [hp, hshift]

/-- Rank-zero falsity is invariant under the corresponding free-environment
tail shift. -/
theorem qfFalse_shift_iff_of_isFreeTail
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsQuantifierFreeCode p) :
    QFFalse bound shifted (shift ℒₒᵣ p) ↔ QFFalse bound free p := by
  have hshift : IsQuantifierFreeCode (shift ℒₒᵣ p) :=
    (QuantifierBoundedCode.shift_iff hp.1).mpr hp
  unfold QFFalse
  rw [qfValue_shift_of_isFreeTail hfree hp.1]
  simp [hp, hshift]

/-! ## Simultaneous bound-variable substitution -/

/-- Evaluation commutes with coded simultaneous substitution.  The
substituting terms are evaluated under `(bound, free)`, while `subBound`
records their values in the reverse de Bruijn order consumed by `termValue`.

The induction property carries an equality of arities rather than fixing the
arity silently.  This matters because internal structural induction changes
the arity under quantifiers, even though the rank-zero evaluator's quantified
clauses themselves are dummy zeroes. -/
theorem qfValue_subst_of_isSubstitutionBound
    {bound free n w subBound p : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (hp : IsSemiformula ℒₒᵣ n p) :
    qfValue bound free (subst ℒₒᵣ w p) = qfValue subBound free p := by
  apply IsSemiformula.pi1_structural_induction
      (P := fun n' p : V ↦ n' = n →
        qfValue bound free (subst ℒₒᵣ w p) = qfValue subBound free p)
      (L := ℒₒᵣ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp rfl
  · definability
  · intro n' k R terms hR hterms hn
    subst n'
    rw [substs_rel hR hterms.isUTerm,
      qfValue_rel hR (hw.isSemitermVec.termSubstVec hterms).isUTerm,
      qfValue_rel hR hterms.isUTerm,
      termValues_termSubstVec_of_isSubstitutionBound hw hsub hterms]
  · intro n' k R terms hR hterms hn
    subst n'
    rw [substs_nrel hR hterms.isUTerm,
      qfValue_nrel hR (hw.isSemitermVec.termSubstVec hterms).isUTerm,
      qfValue_nrel hR hterms.isUTerm,
      termValues_termSubstVec_of_isSubstitutionBound hw hsub hterms]
  · intro n' hn
    simp
  · intro n' hn
    simp
  · intro n' p q hp hq ihp ihq hn
    subst n'
    rw [substs_and hp.isUFormula hq.isUFormula,
      qfValue_and (hp.subst hw.isSemitermVec).isUFormula
        (hq.subst hw.isSemitermVec).isUFormula,
      qfValue_and hp.isUFormula hq.isUFormula, ihp rfl, ihq rfl]
  · intro n' p q hp hq ihp ihq hn
    subst n'
    rw [substs_or hp.isUFormula hq.isUFormula,
      qfValue_or (hp.subst hw.isSemitermVec).isUFormula
        (hq.subst hw.isSemitermVec).isUFormula,
      qfValue_or hp.isUFormula hq.isUFormula, ihp rfl, ihq rfl]
  · intro n' p hp ihp hn
    subst n'
    rw [substs_all hp.isUFormula,
      qfValue_all (hp.subst hw.isSemitermVec.qVec).isUFormula,
      qfValue_all hp.isUFormula]
  · intro n' p hp ihp hn
    subst n'
    rw [substs_ex hp.isUFormula,
      qfValue_exs (hp.subst hw.isSemitermVec.qVec).isUFormula,
      qfValue_exs hp.isUFormula]

/-- Specialization to a fully well-formed induced substitution environment. -/
theorem qfValue_subst_of_isSubstitutionEnvironment
    {bound free n w subBound p : V}
    (hsub : IsSubstitutionEnvironment bound free n w subBound)
    (hp : IsSemiformula ℒₒᵣ n p) :
    qfValue bound free (subst ℒₒᵣ w p) = qfValue subBound free p :=
  qfValue_subst_of_isSubstitutionBound hsub.1 hsub.2.2.2.2.2 hp

/-- Rank-zero truth is preserved and reflected by simultaneous substitution
and its induced semantic bound environment. -/
theorem qfTrue_subst_iff_of_isSubstitutionBound
    {bound free n w subBound p : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (hp : IsSemiformula ℒₒᵣ n p)
    (hqf : IsQuantifierFreeCode p) :
    QFTrue bound free (subst ℒₒᵣ w p) ↔ QFTrue subBound free p := by
  have hsubst : IsQuantifierFreeCode (subst ℒₒᵣ w p) :=
    hqf.subst hp hw.isSemitermVec
  unfold QFTrue
  rw [qfValue_subst_of_isSubstitutionBound hw hsub hp]
  simp [hqf, hsubst]

/-- Rank-zero falsity is preserved and reflected by simultaneous
substitution and its induced semantic bound environment. -/
theorem qfFalse_subst_iff_of_isSubstitutionBound
    {bound free n w subBound p : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (hp : IsSemiformula ℒₒᵣ n p)
    (hqf : IsQuantifierFreeCode p) :
    QFFalse bound free (subst ℒₒᵣ w p) ↔ QFFalse subBound free p := by
  have hsubst : IsQuantifierFreeCode (subst ℒₒᵣ w p) :=
    hqf.subst hp hw.isSemitermVec
  unfold QFFalse
  rw [qfValue_subst_of_isSubstitutionBound hw hsub hp]
  simp [hqf, hsubst]

end LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
