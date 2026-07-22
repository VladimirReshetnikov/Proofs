import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep

/-!
# Semantic laws for two adjacent dynamic truth successors

The final consistency stage must apply the abstract soundness theorem at a
possibly nonstandard hierarchy level.  The concrete truth relation at that
stage is a successor built over the preceding successor relation.  This file
proves, without decoding either level, that the cross-level, shift, and
substitution certificate fields give all of the Tarski and environment laws
required by `AbstractSoundness.Laws`.

The universal clause is the delicate case.  A universal root in the new
successor stores the Pi presentation of the preceding truth relation.  The
preceding relation is itself a successor, so its existential constructor
turns the represented negation into the expected pointwise universal law.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

private lemma bounded_and_parts {level p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋏ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · have hparts := (isSigmaCode_and_iff hp hq).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_and_iff hp hq).mp hpi
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

private lemma bounded_or_parts {level p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋎ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · have hparts := (isSigmaCode_or_iff hp hq).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_or_iff hp hq).mp hpi
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

private lemma bounded_all_pi {level q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∀ q)) :
    IsPiCode ℒₒᵣ level (^∀ q) := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isSigmaCode_all_zero hq hs).elim
    · have hparts := (isSigmaCode_all_succ_iff hq).mp hs
      exact (isPiCode_all_iff hq).mpr
        ⟨hparts.1.mono (by simp), by simp⟩
  · exact hpi

private lemma bounded_exs_sigma {level q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∃ q)) :
    IsSigmaCode ℒₒᵣ level (^∃ q) := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · exact hs
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isPiCode_exs_zero hq hpi).elim
    · have hparts := (isPiCode_exs_succ_iff hq).mp hpi
      exact (isSigmaCode_exs_iff hq).mpr
        ⟨hparts.1.mono (by simp), by simp⟩

private lemma bounded_all_body {level q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∀ q)) :
    QuantifierBoundedCode ℒₒᵣ level q := by
  exact ((isPiCode_all_iff hq).mp (bounded_all_pi hq h)).1.quantifierBounded

private lemma bounded_exs_body {level q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∃ q)) :
    QuantifierBoundedCode ℒₒᵣ level q := by
  exact ((isSigmaCode_exs_iff hq).mp (bounded_exs_sigma hq h)).1.quantifierBounded

private lemma bounded_shift {level : V} {p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ level p) :
    QuantifierBoundedCode ℒₒᵣ level (shift ℒₒᵣ p) := by
  exact (QuantifierBoundedCode.shift_iff hp.1).mpr hp

/-! ## Boolean and quantifier laws -/

theorem nextTruth_neg_iff
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel bound free p : V}
    (hcross : ∀ q,
      SuccessorCrossLaws
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel q)
    (hp : QuantifierBoundedCode ℒₒᵣ currentLevel p) :
    SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free (neg ℒₒᵣ p) ↔
      ¬SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free p := by
  classical
  let current := SuccessorTruth prior previousLevel currentLevel
  let next := SuccessorTruth current currentLevel nextLevel
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp hp with hs | hpi
  · have hnpi : IsPiCode ℒₒᵣ currentLevel (neg ℒₒᵣ p) :=
      (isPiCode_neg_iff hs.1).mpr hs
    rw [(hcross (neg ℒₒᵣ p) bound free).2 hnpi,
      (hcross p bound free).1 hs]
    simp [LowerPiTrue, hnpi, hs.1]
  · have hnsigma : IsSigmaCode ℒₒᵣ currentLevel (neg ℒₒᵣ p) :=
      (isSigmaCode_neg_iff hpi.1).mpr hpi
    rw [(hcross (neg ℒₒᵣ p) bound free).1 hnsigma,
      (hcross p bound free).2 hpi]
    simp [LowerPiTrue, hpi]

theorem nextTruth_and_iff
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel bound free p q : V}
    (hpq : QuantifierBoundedCode ℒₒᵣ currentLevel (p ^⋏ q)) :
    SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free (p ^⋏ q) ↔
      SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel bound free p ∧
        SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel bound free q := by
  have hparts : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using hpq.1
  exact SuccessorTruth.and_iff hparts.1 hparts.2

theorem nextTruth_or_iff
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel bound free p q : V}
    (hnext : nextLevel = currentLevel + 1)
    (hpq : QuantifierBoundedCode ℒₒᵣ currentLevel (p ^⋎ q)) :
    SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free (p ^⋎ q) ↔
      SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel bound free p ∨
        SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel bound free q := by
  have hu : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using hpq.1
  have hb := bounded_or_parts hu.1 hu.2 hpq
  have hsp : IsSigmaCode ℒₒᵣ nextLevel p := by
    rw [hnext]
    exact QuantifierBoundedCode.toSigmaSucc hb.1
  have hsq : IsSigmaCode ℒₒᵣ nextLevel q := by
    rw [hnext]
    exact QuantifierBoundedCode.toSigmaSucc hb.2
  exact SuccessorTruth.or_iff hu.1 hu.2 hsp hsq

theorem nextTruth_exs_iff
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel bound free q : V}
    (hnext : nextLevel = currentLevel + 1)
    (hq : QuantifierBoundedCode ℒₒᵣ currentLevel (^∃ q)) :
    SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free (^∃ q) ↔
      ∃ a, SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel (bound ⁀' a) free q := by
  have hqU : IsUFormula ℒₒᵣ q := by simpa using hq.1
  apply SuccessorTruth.exs_iff hqU
  rw [hnext]
  simp

theorem nextTruth_all_iff
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel bound free q : V}
    (hcurrent : currentLevel = previousLevel + 1)
    (hcross : ∀ r,
      SuccessorCrossLaws
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel r)
    (hq : QuantifierBoundedCode ℒₒᵣ currentLevel (^∀ q)) :
    SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel bound free (^∀ q) ↔
      ∀ a, SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel (bound ⁀' a) free q := by
  classical
  have hqU : IsUFormula ℒₒᵣ q := by simpa using hq.1
  have hallPi : IsPiCode ℒₒᵣ currentLevel (^∀ q) :=
    bounded_all_pi hqU hq
  have hqPi : IsPiCode ℒₒᵣ currentLevel q :=
    ((isPiCode_all_iff hqU).mp hallPi).1
  rw [(hcross (^∀ q) bound free).2 hallPi]
  change LowerPiTrue
      (SuccessorTruth prior previousLevel currentLevel)
      currentLevel bound free (^∀ q) ↔ _
  rw [LowerPiTrue, and_iff_right hallPi, neg_all hqU]
  have hpositive : (1 : V) ≤ currentLevel := by
    rw [hcurrent]
    simp
  rw [SuccessorTruth.exs_iff hqU.neg hpositive]
  constructor
  · intro h a
    apply ((hcross q (bound ⁀' a) free).2 hqPi).mpr
    exact ⟨hqPi, fun ha ↦ h ⟨a, ha⟩⟩
  · intro h hex
    rcases hex with ⟨a, ha⟩
    have hpi := ((hcross q (bound ⁀' a) free).2 hqPi).mp (h a)
    exact hpi.2 ha

/-! ## Environment laws -/

theorem nextTruth_substs1_iff
    {relation : V → V → V → Prop} {level free p t : V}
    (hsubstitution : ∀ q, SubstitutionInvariantAt relation level q)
    (hfree : Arithmetic.Seq free)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (ht : IsTerm ℒₒᵣ t)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level p) :
    relation 0 free (substs1 ℒₒᵣ t p) ↔
      relation (0 ⁀' termValue 0 free t) free p := by
  have hw : IsSemitermVec ℒₒᵣ (1 : V) (0 : V) (?[t] : V) := by
    simpa using ht
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hsub : IsSubstitutionEnvironment
      (0 : V) free (1 : V) (?[t] : V)
        (0 ⁀' termValue 0 free t) := by
    refine ⟨hw.isUTerm, hzeroSeq, hfree,
      hzeroSeq.seqCons (termValue 0 free t), ?_, ?_⟩
    · rw [Seq.lh_seqCons _ hzeroSeq, hlhZero]
      simp
    · intro z hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      simpa [termValue_bvar] using
        (termValue_bvar_zero_seqCons
          (free := free) (a := termValue 0 free t) hzeroSeq)
  simpa only [substs1] using
    hsubstitution p (0 ⁀' termValue 0 free t) (?[t] : V)
      0 free 0 1 hw hlhZero.symm hsub hp hbounded

theorem nextTruth_free_iff
    {relation : V → V → V → Prop} {level shifted free p a : V}
    (hshift : ∀ q, ShiftInvariantAt relation level q)
    (hsubstitution : ∀ q, SubstitutionInvariantAt relation level q)
    (hhead : IsFreeHead a shifted free)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level (^∀ p)) :
    relation 0 shifted (Bootstrapping.free ℒₒᵣ p) ↔
      relation (0 ⁀' a) free p := by
  have hpBounded := bounded_all_body hp.isUFormula hbounded
  have hshiftBounded := bounded_shift hpBounded
  unfold Bootstrapping.free
  rw [nextTruth_substs1_iff hsubstitution hhead.2.1 hp.shift
      (by simp) hshiftBounded,
    show termValue (0 : V) shifted ^&0 = a by
      simpa using hhead.2.2.2.1,
    hshift p (0 ⁀' a) shifted free hhead.2.2.2.2 hpBounded]

/-! ## Packaged abstract-soundness interface -/

/-- The complete law package for the next dynamic truth successor.

All quantified levels are carrier elements.  In particular, neither of the
two adjacent successors is required to be indexed by a standard numeral. -/
theorem nextTruth_laws
    {prior : V → V → V → Prop}
    {previousLevel currentLevel nextLevel : V}
    (hcurrent : currentLevel = previousLevel + 1)
    (hnext : nextLevel = currentLevel + 1)
    (hcross : ∀ q,
      SuccessorCrossLaws
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel q)
    (hshift : ∀ q,
      ShiftInvariantAt
        (SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel)
        currentLevel q)
    (hsubstitution : ∀ q,
      SubstitutionInvariantAt
        (SuccessorTruth
          (SuccessorTruth prior previousLevel currentLevel)
          currentLevel nextLevel)
        currentLevel q) :
    Laws currentLevel
      (SuccessorTruth
        (SuccessorTruth prior previousLevel currentLevel)
        currentLevel nextLevel) where
  verum bound free := by
    rw [SuccessorTruth.verum_iff]
    simp
  falsum bound free := by
    rw [SuccessorTruth.falsum_iff]
    simp
  neg_iff hp := nextTruth_neg_iff hcross hp
  and_iff hp := nextTruth_and_iff hp
  or_iff hp := nextTruth_or_iff hnext hp
  all_iff hp := nextTruth_all_iff hcurrent hcross hp
  exs_iff hp := nextTruth_exs_iff hnext hp
  shift_iff hfree hp := hshift _ _ _ _ hfree hp
  free_iff hhead hp hb :=
    nextTruth_free_iff hshift hsubstitution hhead hp hb
  substs1_iff hfree hp ht hb :=
    nextTruth_substs1_iff hsubstitution hfree hp ht
      (bounded_exs_body hp.isUFormula hb)

end LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws
