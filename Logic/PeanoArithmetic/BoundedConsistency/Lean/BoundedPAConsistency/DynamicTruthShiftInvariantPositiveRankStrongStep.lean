import BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

/-!
# Positive-rank strong step for dynamic shift invariance

This module is deliberately separate from the fixed-source interface.  It
develops the constructor-wise semantic theorem for the positive-rank branch,
using the generic `SuccessorTruth` laws already needed by cross-level
coherence.  Once complete, the theorem can be wrapped by fixed source syntax
without changing the reviewed source/audit modules.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

section GenericSuccessor

variable {M : Type*} [ORingStructure M]
variable [M↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Free-variable shift invariance of a ternary semantic relation, restricted
to formula codes at the displayed (possibly nonstandard) hierarchy bound. -/
def ShiftInvariantAt
    (relation : M → M → M → Prop) (level p : M) : Prop :=
  ∀ bound shifted free,
    IsFreeTail shifted free →
    QuantifierBoundedCode ℒₒᵣ level p →
    (relation bound shifted (shift ℒₒᵣ p) ↔
      relation bound free p)

private lemma quantifierBoundedCode_and_parts
    {level p q : M} (hp : IsUFormula ℒₒᵣ p)
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋏ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · have hparts := (isSigmaCode_and_iff hp hq).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_and_iff hp hq).mp hpi
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

private lemma quantifierBoundedCode_or_parts
    {level p q : M} (hp : IsUFormula ℒₒᵣ p)
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋎ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · have hparts := (isSigmaCode_or_iff hp hq).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_or_iff hp hq).mp hpi
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

/-- A bounded universal formula always belongs to the native Pi side at the
same level, even if boundedness was initially witnessed through Sigma rank. -/
private lemma quantifierBoundedCode_all_pi
    {level q : M} (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∀ q)) :
    IsPiCode ℒₒᵣ level (^∀ q) := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isSigmaCode_all_zero hq hs).elim
    · have hparts := (isSigmaCode_all_succ_iff hq).mp hs
      exact (isPiCode_all_iff hq).mpr
        ⟨hparts.1.mono (by simp), by simp⟩
  · exact hpi

/-- Dually, a bounded existential formula belongs to the native Sigma side
at the same level. -/
private lemma quantifierBoundedCode_exs_sigma
    {level q : M} (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∃ q)) :
    IsSigmaCode ℒₒᵣ level (^∃ q) := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · exact hs
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isPiCode_exs_zero hq hpi).elim
    · have hparts := (isPiCode_exs_succ_iff hq).mp hpi
      exact (isSigmaCode_exs_iff hq).mpr
        ⟨hparts.1.mono (by simp), by simp⟩

/-- Universal introduction needs only the advertised upper-domain fact.  The
successor-level equation used by the standard constructor lemma is one way to
derive this fact, but fixed source languages interpret named levels
arbitrarily; accepting the domain directly makes the shift step uniform in
those interpretations. -/
theorem SuccessorTruth.all_intro_of_domain
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (hdom : IsSigmaCode ℒₒᵣ upperLevel (^∀ q))
    (h : LowerPiTrue lower lowerLevel bound free (^∀ q)) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∀ q) := by
  let root : M := truthRecord bound free (^∀ q) 0
  let C : M := insert root ∅
  have hroot : root ∈ C := by simp [C]
  refine ⟨C, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    have hrr : r = root := by simpa [C] using hr
    subst r
    constructor
    · simpa [root] using hdom
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
        ⟨q, by simp [root], by simp [root], by simpa [root] using h⟩

@[simp] theorem SuccessorTruth.all_iff_of_domain
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (hdom : IsSigmaCode ℒₒᵣ upperLevel (^∀ q)) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∀ q) ↔
      LowerPiTrue lower lowerLevel bound free (^∀ q) :=
  ⟨SuccessorTruth.all_elim hq,
    SuccessorTruth.all_intro_of_domain hq hdom⟩

set_option maxHeartbeats 1600000 in
/-- One constructor-wise strong step for the represented successor truth
relation.  The cross-level laws are used only to pass the universal/Pi branch
through the represented negation; every recursive use is justified by a
strictly smaller numeric formula code. -/
theorem SuccessorTruth.shift_strongStep
    {current : M → M → M → Prop}
    {currentLevel nextLevel p : M}
    (hcross : ∀ q,
      SuccessorCrossLaws current currentLevel nextLevel q)
    (hprefix : ∀ q, q < p →
      ShiftInvariantAt
        (SuccessorTruth current currentLevel nextLevel)
        currentLevel q) :
    ShiftInvariantAt
      (SuccessorTruth current currentLevel nextLevel)
      currentLevel p := by
  intro bound shifted free hfree hp
  rcases hp.1.case with
      (⟨k, R, terms, hR, hterms, hcode⟩ |
       ⟨k, R, terms, hR, hterms, hcode⟩ |
       hcode | hcode | ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, hq, hcode⟩ | ⟨q, hq, hcode⟩)
  · subst p
    rw [shift_rel hR hterms,
      SuccessorTruth.rel_iff hR hterms.termShiftVec,
      SuccessorTruth.rel_iff hR hterms]
    have hqf : IsQuantifierFreeCode (^rel k R terms) := by
      simp [IsQuantifierFreeCode, hR, hterms]
    simpa only [shift_rel hR hterms] using
      (qfTrue_shift_iff_of_isFreeTail (bound := bound) hfree hqf)
  · subst p
    rw [shift_nrel hR hterms,
      SuccessorTruth.nrel_iff hR hterms.termShiftVec,
      SuccessorTruth.nrel_iff hR hterms]
    have hqf : IsQuantifierFreeCode (^nrel k R terms) := by
      simp [IsQuantifierFreeCode, hR, hterms]
    simpa only [shift_nrel hR hterms] using
      (qfTrue_shift_iff_of_isFreeTail (bound := bound) hfree hqf)
  · subst p
    rw [shift_verum, SuccessorTruth.verum_iff,
      SuccessorTruth.verum_iff]
    have hqf : IsQuantifierFreeCode (^⊤ : M) := by
      simp [IsQuantifierFreeCode]
    simpa only [shift_verum] using
      (qfTrue_shift_iff_of_isFreeTail (bound := bound) hfree hqf)
  · subst p
    rw [shift_falsum, SuccessorTruth.falsum_iff,
      SuccessorTruth.falsum_iff]
    have hqf : IsQuantifierFreeCode (^⊥ : M) := by
      simp [IsQuantifierFreeCode]
    simpa only [shift_falsum] using
      (qfTrue_shift_iff_of_isFreeTail (bound := bound) hfree hqf)
  · subst p
    have hparts := quantifierBoundedCode_and_parts hq hr hp
    rw [shift_and hq hr,
      SuccessorTruth.and_iff hq.shift hr.shift,
      SuccessorTruth.and_iff hq hr]
    exact and_congr
      (hprefix q (by simp) bound shifted free hfree hparts.1)
      (hprefix r (by simp) bound shifted free hfree hparts.2)
  · subst p
    have hparts := quantifierBoundedCode_or_parts hq hr hp
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (q ^⋎ r)
    · have hdomShift : IsSigmaCode ℒₒᵣ nextLevel
          (shift ℒₒᵣ (q ^⋎ r)) :=
        (isSigmaCode_shift_iff hdom.1).mpr hdom
      have hnextParts := (isSigmaCode_or_iff hq hr).mp hdom
      have hnextShiftParts :=
        (isSigmaCode_or_iff hq.shift hr.shift).mp (by
          simpa only [shift_or hq hr] using hdomShift)
      rw [shift_or hq hr,
        SuccessorTruth.or_iff hq.shift hr.shift
          hnextShiftParts.1 hnextShiftParts.2,
        SuccessorTruth.or_iff hq hr hnextParts.1 hnextParts.2]
      exact or_congr
        (hprefix q (by simp) bound shifted free hfree hparts.1)
        (hprefix r (by simp) bound shifted free hfree hparts.2)
    · have hdomShift : ¬IsSigmaCode ℒₒᵣ nextLevel
          (shift ℒₒᵣ (q ^⋎ r)) := by
        simpa only [isSigmaCode_shift_iff (show
          IsUFormula ℒₒᵣ (q ^⋎ r) by simp [hq, hr])] using hdom
      constructor
      · intro hs
        exact (hdomShift (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim
  · subst p
    have hpPi := quantifierBoundedCode_all_pi hq hp
    have hpPiShift :
        IsPiCode ℒₒᵣ currentLevel (shift ℒₒᵣ (^∀ q)) :=
      (isPiCode_shift_iff hpPi.1).mpr hpPi
    have hnegSigma :
        IsSigmaCode ℒₒᵣ currentLevel (neg ℒₒᵣ (^∀ q)) :=
      (isSigmaCode_neg_iff hpPi.1).mpr hpPi
    have hnegSigmaShift :
        IsSigmaCode ℒₒᵣ currentLevel
          (shift ℒₒᵣ (neg ℒₒᵣ (^∀ q))) :=
      (isSigmaCode_shift_iff hnegSigma.1).mpr hnegSigma
    have hpiParts := (isPiCode_all_iff hq).mp hpPi
    have hqPi : IsPiCode ℒₒᵣ currentLevel q := hpiParts.1
    have hnegBodySigma :
        IsSigmaCode ℒₒᵣ currentLevel (neg ℒₒᵣ q) :=
      (isSigmaCode_neg_iff hq).mpr hqPi
    have hqPiShift :
        IsPiCode ℒₒᵣ currentLevel (shift ℒₒᵣ q) :=
      (isPiCode_shift_iff hq).mpr hqPi
    have hnegBodySigmaShift :
        IsSigmaCode ℒₒᵣ currentLevel
          (shift ℒₒᵣ (neg ℒₒᵣ q)) :=
      (isSigmaCode_shift_iff hq.neg).mpr hnegBodySigma
    /- `neg q` need not itself be a smaller numeric code.  Instead, use the
    prefix theorem at the genuine child `q`; the Pi cross law turns that
    equivalence into an equivalence of the complements `current (neg q)`,
    and the Sigma cross law then transports it back to successor truth at
    `neg q`.  This is the key decrease in the universal branch. -/
    have hnegBodyInvariant (bodyBound : M) :
        SuccessorTruth current currentLevel nextLevel bodyBound shifted
            (shift ℒₒᵣ (neg ℒₒᵣ q)) ↔
          SuccessorTruth current currentLevel nextLevel bodyBound free
            (neg ℒₒᵣ q) := by
      have hqInvariant := hprefix q (by simp) bodyBound shifted free
        hfree hqPi.quantifierBounded
      have hcrossQShift :=
        (hcross (shift ℒₒᵣ q) bodyBound shifted).2 hqPiShift
      have hcrossQFree :=
        (hcross q bodyBound free).2 hqPi
      have hlowerQ :=
        hcrossQShift.symm.trans (hqInvariant.trans hcrossQFree)
      have hnotCurrentBody :
          (¬current bodyBound shifted (neg ℒₒᵣ (shift ℒₒᵣ q))) ↔
            ¬current bodyBound free (neg ℒₒᵣ q) := by
        simpa only [LowerPiTrue, hqPiShift, hqPi, true_and] using
          hlowerQ
      have hcurrentBody :
          current bodyBound shifted (shift ℒₒᵣ (neg ℒₒᵣ q)) ↔
            current bodyBound free (neg ℒₒᵣ q) := by
        rw [shift_neg hq.isSemiformula]
        simpa using not_congr hnotCurrentBody
      exact
        ((hcross (shift ℒₒᵣ (neg ℒₒᵣ q))
            bodyBound shifted).1 hnegBodySigmaShift).trans
          (hcurrentBody.trans
            ((hcross (neg ℒₒᵣ q) bodyBound free).1
              hnegBodySigma).symm)
    /- The represented negation of the universal is existential, so its
    invariance follows witness-by-witness from the derived body law. -/
    have hnegInvariant :
        SuccessorTruth current currentLevel nextLevel bound shifted
            (shift ℒₒᵣ (neg ℒₒᵣ (^∀ q))) ↔
          SuccessorTruth current currentLevel nextLevel bound free
            (neg ℒₒᵣ (^∀ q)) := by
      rw [neg_all hq, shift_exs hq.neg]
      by_cases hdomNeg :
          IsSigmaCode ℒₒᵣ nextLevel (^∃ (neg ℒₒᵣ q))
      · have hpositive := ((isSigmaCode_exs_iff hq.neg).mp hdomNeg).2
        rw [SuccessorTruth.exs_iff hq.neg.shift hpositive,
          SuccessorTruth.exs_iff hq.neg hpositive]
        constructor
        · rintro ⟨a, ha⟩
          exact ⟨a, (hnegBodyInvariant (bound ⁀' a)).mp ha⟩
        · rintro ⟨a, ha⟩
          exact ⟨a, (hnegBodyInvariant (bound ⁀' a)).mpr ha⟩
      · have hdomNegShift :
            ¬IsSigmaCode ℒₒᵣ nextLevel
              (shift ℒₒᵣ (^∃ (neg ℒₒᵣ q))) := by
          simpa only [isSigmaCode_shift_iff (show
            IsUFormula ℒₒᵣ (^∃ (neg ℒₒᵣ q)) by
              simpa using hq.neg)] using hdomNeg
        have hdomNegShiftEx :
            ¬IsSigmaCode ℒₒᵣ nextLevel
              (^∃ (shift ℒₒᵣ (neg ℒₒᵣ q))) := by
          simpa only [shift_exs hq.neg] using hdomNegShift
        constructor
        · intro hs
          have hsdom : IsSigmaCode ℒₒᵣ nextLevel
              (^∃ (shift ℒₒᵣ (neg ℒₒᵣ q))) :=
            SuccessorTruth.domain hs
          exact (hdomNegShiftEx hsdom).elim
        · intro hs
          have hsdom : IsSigmaCode ℒₒᵣ nextLevel
              (^∃ (neg ℒₒᵣ q)) :=
            SuccessorTruth.domain hs
          exact (hdomNeg hsdom).elim
    have hcrossShift :=
      (hcross (shift ℒₒᵣ (neg ℒₒᵣ (^∀ q)))
        bound shifted).1 hnegSigmaShift
    have hcrossFree :=
      (hcross (neg ℒₒᵣ (^∀ q)) bound free).1 hnegSigma
    have hcurrentNeg :=
      hcrossShift.symm.trans (hnegInvariant.trans hcrossFree)
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (^∀ q)
    · have hdomShift : IsSigmaCode ℒₒᵣ nextLevel
          (shift ℒₒᵣ (^∀ q)) :=
        (isSigmaCode_shift_iff hdom.1).mpr hdom
      rw [shift_all hq,
        SuccessorTruth.all_iff_of_domain hq.shift (by
          simpa only [shift_all hq] using hdomShift),
        SuccessorTruth.all_iff_of_domain hq hdom]
      have hpPiShiftAll :
          IsPiCode ℒₒᵣ currentLevel (^∀ (shift ℒₒᵣ q)) := by
        simpa only [shift_all hq] using hpPiShift
      simp only [LowerPiTrue, hpPiShiftAll, hpPi, true_and]
      simpa only [shift_neg hp.1.isSemiformula, shift_all hq] using
        not_congr hcurrentNeg
    · have hdomShift : ¬IsSigmaCode ℒₒᵣ nextLevel
          (shift ℒₒᵣ (^∀ q)) := by
        simpa only [isSigmaCode_shift_iff (show
          IsUFormula ℒₒᵣ (^∀ q) by simpa using hq)] using hdom
      constructor
      · intro hs
        exact (hdomShift (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim
  · subst p
    have hpSigma := quantifierBoundedCode_exs_sigma hq hp
    have hqBound : QuantifierBoundedCode ℒₒᵣ currentLevel q :=
      ((isSigmaCode_exs_iff hq).mp hpSigma).1.quantifierBounded
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (^∃ q)
    · have hpositive := ((isSigmaCode_exs_iff hq).mp hdom).2
      rw [shift_exs hq, SuccessorTruth.exs_iff hq.shift hpositive,
        SuccessorTruth.exs_iff hq hpositive]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, (hprefix q (by simp) (bound ⁀' a) shifted free
          hfree hqBound).mp ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, (hprefix q (by simp) (bound ⁀' a) shifted free
          hfree hqBound).mpr ha⟩
    · have hdomShift : ¬IsSigmaCode ℒₒᵣ nextLevel
          (shift ℒₒᵣ (^∃ q)) := by
        simpa only [isSigmaCode_shift_iff (show
          IsUFormula ℒₒᵣ (^∃ q) by simpa using hq)] using hdom
      constructor
      · intro hs
        exact (hdomShift (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim

end GenericSuccessor

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
