import BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource
import BoundedPAConsistency.FixedLevelTruthSubstitution

/-!
# Positive-rank strong step for dynamic substitution invariance

This module proves the semantic constructor step needed by the fixed-source
substitution certificate.  All hierarchy levels and formula codes remain
elements of an arbitrary model of PA: the proof never decodes a model code
as external syntax.  Recursive calls are obtained solely from the strict
numeric prefix of represented strong induction.

The universal constructor is the only subtle case.  A successor truth
certificate for a universal stores the predecessor Pi presentation, whose
negative half asks about the predecessor truth of the represented negation.
The induction prefix is used only at the genuine child `q`.  Cross-level
coherence identifies successor truth at `neg q` with the complement of
successor truth at `q`; `not_congr` then transports the child result through
the existential presentation of the negated universal.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

section GenericSuccessor

variable {M : Type*} [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Simultaneous-substitution invariance in the exact semantic order exposed
by `sourceSubstitutionInvariantBody` after the represented substitution graph
is evaluated.  The source formula states `termBound = lh bound`, hence that
orientation is retained here even though the environment-extension lemma
uses its symmetric form. -/
def SubstitutionInvariantAt
    (relation : M → M → M → Prop) (level p : M) : Prop :=
  ∀ subBound terms termBound free bound arity,
    IsSemitermVec ℒₒᵣ arity termBound terms →
    termBound = lh bound →
    IsSubstitutionEnvironment bound free arity terms subBound →
    IsSemiformula ℒₒᵣ arity p →
    QuantifierBoundedCode ℒₒᵣ level p →
    (relation bound free (subst ℒₒᵣ terms p) ↔
      relation subBound free p)

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

/-- A bounded universal lies on the native Pi side at the displayed level.
The impossible level-zero Sigma case is discharged internally. -/
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

/-- Dually, a bounded existential lies on the native Sigma side. -/
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

/-- Universal introduction from an explicitly supplied upper-domain fact.
This level-equation-free form is required because the named source levels
are interpreted by arbitrary model elements. -/
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

/-- On the current Pi domain, cross-level coherence makes represented
successor truth at the negated code the logical complement of successor truth
at the original code.  This polarity bridge is what lets the universal case
recurse at the genuine child `q`, rather than incorrectly assuming that the
recursively computed code `neg q` is numerically below `all q`. -/
theorem SuccessorTruth.neg_iff_not_of_pi
    {current : M → M → M → Prop}
    {currentLevel nextLevel bound free q : M}
    (hcross : ∀ r,
      SuccessorCrossLaws current currentLevel nextLevel r)
    (hq : IsPiCode ℒₒᵣ currentLevel q) :
    SuccessorTruth current currentLevel nextLevel bound free
        (neg ℒₒᵣ q) ↔
      ¬SuccessorTruth current currentLevel nextLevel bound free q := by
  have hneg : IsSigmaCode ℒₒᵣ currentLevel (neg ℒₒᵣ q) :=
    (isSigmaCode_neg_iff hq.1).mpr hq
  rw [(hcross (neg ℒₒᵣ q) bound free).1 hneg,
    (hcross q bound free).2 hq,
    LowerPiTrue, and_iff_right hq]
  simp

/-- One constructor-wise strong step for simultaneous substitution through
the represented successor truth relation. -/
theorem SuccessorTruth.substitution_strongStep
    {current : M → M → M → Prop}
    {currentLevel nextLevel p : M}
    (hcross : ∀ q,
      SuccessorCrossLaws current currentLevel nextLevel q)
    (hprefix : ∀ q, q < p →
      SubstitutionInvariantAt
        (SuccessorTruth current currentLevel nextLevel)
        currentLevel q) :
    SubstitutionInvariantAt
      (SuccessorTruth current currentLevel nextLevel)
      currentLevel p := by
  intro subBound terms termBound free bound arity hw hboundLen hsub hp hbounded
  rcases hbounded.1.case with
      (⟨k, R, termVec, hR, htermVec, hcode⟩ |
       ⟨k, R, termVec, hR, htermVec, hcode⟩ |
       hcode | hcode | ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, hq, hcode⟩ | ⟨q, hq, hcode⟩)
  · subst p
    have hqf : IsQuantifierFreeCode (^rel k R termVec) := by
      simp [IsQuantifierFreeCode, hR, htermVec]
    have hsemTerms := (IsSemiformula.rel.mp hp).2
    rw [substs_rel hR htermVec,
      SuccessorTruth.rel_iff hR (hw.termSubstVec hsemTerms).isUTerm,
      SuccessorTruth.rel_iff hR htermVec]
    simpa only [substs_rel hR htermVec] using
      (qfTrue_subst_iff_of_isSubstitutionBound
        hsub.1 hsub.2.2.2.2.2 hp hqf)
  · subst p
    have hqf : IsQuantifierFreeCode (^nrel k R termVec) := by
      simp [IsQuantifierFreeCode, hR, htermVec]
    have hsemTerms := (IsSemiformula.nrel.mp hp).2
    rw [substs_nrel hR htermVec,
      SuccessorTruth.nrel_iff hR (hw.termSubstVec hsemTerms).isUTerm,
      SuccessorTruth.nrel_iff hR htermVec]
    simpa only [substs_nrel hR htermVec] using
      (qfTrue_subst_iff_of_isSubstitutionBound
        hsub.1 hsub.2.2.2.2.2 hp hqf)
  · subst p
    rw [substs_verum, SuccessorTruth.verum_iff,
      SuccessorTruth.verum_iff]
    simpa only [substs_verum] using
      (qfTrue_subst_iff_of_isSubstitutionBound
        hsub.1 hsub.2.2.2.2.2 hp
        (by simp [IsQuantifierFreeCode]))
  · subst p
    rw [substs_falsum, SuccessorTruth.falsum_iff,
      SuccessorTruth.falsum_iff]
    simpa only [substs_falsum] using
      (qfTrue_subst_iff_of_isSubstitutionBound
        hsub.1 hsub.2.2.2.2.2 hp
        (by simp [IsQuantifierFreeCode]))
  · subst p
    have hsem := IsSemiformula.and.mp hp
    have hparts := quantifierBoundedCode_and_parts hq hr hbounded
    rw [substs_and hq hr,
      SuccessorTruth.and_iff (hsem.1.subst hw).isUFormula
        (hsem.2.subst hw).isUFormula,
      SuccessorTruth.and_iff hq hr]
    exact and_congr
      (hprefix q (by simp) subBound terms termBound free bound arity
        hw hboundLen hsub hsem.1 hparts.1)
      (hprefix r (by simp) subBound terms termBound free bound arity
        hw hboundLen hsub hsem.2 hparts.2)
  · subst p
    have hsem := IsSemiformula.or.mp hp
    have hparts := quantifierBoundedCode_or_parts hq hr hbounded
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (q ^⋎ r)
    · have hdomSub : IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (q ^⋎ r)) :=
        hdom.subst hp hw
      have hnextParts := (isSigmaCode_or_iff hq hr).mp hdom
      have hnextSubParts :=
        (isSigmaCode_or_iff (hsem.1.subst hw).isUFormula
          (hsem.2.subst hw).isUFormula).mp (by
            simpa only [substs_or hq hr] using hdomSub)
      rw [substs_or hq hr,
        SuccessorTruth.or_iff (hsem.1.subst hw).isUFormula
          (hsem.2.subst hw).isUFormula
          hnextSubParts.1 hnextSubParts.2,
        SuccessorTruth.or_iff hq hr hnextParts.1 hnextParts.2]
      exact or_congr
        (hprefix q (by simp) subBound terms termBound free bound arity
          hw hboundLen hsub hsem.1 hparts.1)
        (hprefix r (by simp) subBound terms termBound free bound arity
          hw hboundLen hsub hsem.2 hparts.2)
    · have hdomSub : ¬IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (q ^⋎ r)) := by
        simpa only [isSigmaCode_subst_iff hp hw] using hdom
      constructor
      · intro hs
        exact (hdomSub (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim
  · subst p
    have hsemQ := IsSemiformula.all.mp hp
    have hpPi := quantifierBoundedCode_all_pi hq hbounded
    have hpPiSub : IsPiCode ℒₒᵣ currentLevel
        (subst ℒₒᵣ terms (^∀ q)) :=
      hpPi.subst hp hw
    have hpiParts := (isPiCode_all_iff hq).mp hpPi
    have hqBound : QuantifierBoundedCode ℒₒᵣ currentLevel q :=
      hpiParts.1.quantifierBounded
    have hnegFormula : IsSemiformula ℒₒᵣ arity
        (^∃ (neg ℒₒᵣ q)) := by
      simpa only [neg_all hq] using hp.neg
    /- The negation of the universal is an existential with body `neg q`.
    We do not assume that this recursively computed negation code is below
    the universal code.  Instead the prefix is invoked at the actual child
    `q`, and the two cross-level polarity laws transport its equivalence
    through negation. -/
    have hnegInvariant :
        SuccessorTruth current currentLevel nextLevel bound free
            (neg ℒₒᵣ (subst ℒₒᵣ terms (^∀ q))) ↔
          SuccessorTruth current currentLevel nextLevel subBound free
            (neg ℒₒᵣ (^∀ q)) := by
      rw [← substs_neg hp hw, neg_all hq, substs_ex hq.neg]
      by_cases hdomNeg :
          IsSigmaCode ℒₒᵣ nextLevel (^∃ (neg ℒₒᵣ q))
      · have hpositive :=
          ((isSigmaCode_exs_iff hq.neg).mp hdomNeg).2
        rw [SuccessorTruth.exs_iff
              (hsemQ.neg.subst hw.qVec).isUFormula hpositive,
          SuccessorTruth.exs_iff hq.neg hpositive]
        constructor
        · rintro ⟨a, ha⟩
          have hsubQ := isSubstitutionEnvironment_qVec_seqCons
            (a := a) hw hboundLen.symm hsub
          have hlength : termBound + 1 = lh (bound ⁀' a) := by
            simp [hsub.2.1, hboundLen]
          have hqInvariant := hprefix q (by simp)
            (subBound ⁀' a) (qVec ℒₒᵣ terms) (termBound + 1)
            free (bound ⁀' a) (arity + 1)
            hw.qVec hlength hsubQ hsemQ hqBound
          have hqPiSub : IsPiCode ℒₒᵣ currentLevel
              (subst ℒₒᵣ (qVec ℒₒᵣ terms) q) :=
            hpiParts.1.subst hsemQ hw.qVec
          have hnegBodyInvariant :
              SuccessorTruth current currentLevel nextLevel
                  (bound ⁀' a) free
                  (subst ℒₒᵣ (qVec ℒₒᵣ terms)
                    (neg ℒₒᵣ q)) ↔
                SuccessorTruth current currentLevel nextLevel
                  (subBound ⁀' a) free (neg ℒₒᵣ q) := by
            rw [substs_neg hsemQ hw.qVec]
            exact (SuccessorTruth.neg_iff_not_of_pi hcross hqPiSub).trans
              ((not_congr hqInvariant).trans
                (SuccessorTruth.neg_iff_not_of_pi
                  hcross hpiParts.1).symm)
          exact ⟨a, hnegBodyInvariant.mp ha⟩
        · rintro ⟨a, ha⟩
          have hsubQ := isSubstitutionEnvironment_qVec_seqCons
            (a := a) hw hboundLen.symm hsub
          have hlength : termBound + 1 = lh (bound ⁀' a) := by
            simp [hsub.2.1, hboundLen]
          have hqInvariant := hprefix q (by simp)
            (subBound ⁀' a) (qVec ℒₒᵣ terms) (termBound + 1)
            free (bound ⁀' a) (arity + 1)
            hw.qVec hlength hsubQ hsemQ hqBound
          have hqPiSub : IsPiCode ℒₒᵣ currentLevel
              (subst ℒₒᵣ (qVec ℒₒᵣ terms) q) :=
            hpiParts.1.subst hsemQ hw.qVec
          have hnegBodyInvariant :
              SuccessorTruth current currentLevel nextLevel
                  (bound ⁀' a) free
                  (subst ℒₒᵣ (qVec ℒₒᵣ terms)
                    (neg ℒₒᵣ q)) ↔
                SuccessorTruth current currentLevel nextLevel
                  (subBound ⁀' a) free (neg ℒₒᵣ q) := by
            rw [substs_neg hsemQ hw.qVec]
            exact (SuccessorTruth.neg_iff_not_of_pi hcross hqPiSub).trans
              ((not_congr hqInvariant).trans
                (SuccessorTruth.neg_iff_not_of_pi
                  hcross hpiParts.1).symm)
          exact ⟨a, hnegBodyInvariant.mpr ha⟩
      · have hdomNegSub :
            ¬IsSigmaCode ℒₒᵣ nextLevel
              (subst ℒₒᵣ terms (^∃ (neg ℒₒᵣ q))) := by
          simpa only [isSigmaCode_subst_iff hnegFormula hw] using hdomNeg
        constructor
        · intro hs
          apply (hdomNegSub ?_).elim
          simpa only [substs_ex hq.neg] using SuccessorTruth.domain hs
        · intro hs
          exact (hdomNeg (SuccessorTruth.domain hs)).elim
    have hnegSigma :
        IsSigmaCode ℒₒᵣ currentLevel (neg ℒₒᵣ (^∀ q)) :=
      (isSigmaCode_neg_iff hpPi.1).mpr hpPi
    have hnegSigmaSub : IsSigmaCode ℒₒᵣ currentLevel
        (neg ℒₒᵣ (subst ℒₒᵣ terms (^∀ q))) :=
      (isSigmaCode_neg_iff (hp.subst hw).isUFormula).mpr hpPiSub
    have hcrossSub :=
      (hcross (neg ℒₒᵣ (subst ℒₒᵣ terms (^∀ q)))
        bound free).1 hnegSigmaSub
    have hcrossOriginal :=
      (hcross (neg ℒₒᵣ (^∀ q)) subBound free).1 hnegSigma
    have hcurrentNeg :
        current bound free
            (neg ℒₒᵣ (subst ℒₒᵣ terms (^∀ q))) ↔
          current subBound free (neg ℒₒᵣ (^∀ q)) :=
      hcrossSub.symm.trans (hnegInvariant.trans hcrossOriginal)
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (^∀ q)
    · have hdomSub : IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (^∀ q)) :=
        hdom.subst hp hw
      rw [substs_all hq,
        SuccessorTruth.all_iff_of_domain
          (hsemQ.subst hw.qVec).isUFormula (by
            simpa only [substs_all hq] using hdomSub),
        SuccessorTruth.all_iff_of_domain hq hdom]
      have hpPiSubAll : IsPiCode ℒₒᵣ currentLevel
          (^∀ (subst ℒₒᵣ (qVec ℒₒᵣ terms) q)) := by
        simpa only [substs_all hq] using hpPiSub
      simp only [LowerPiTrue, hpPiSubAll, hpPi, true_and]
      simpa only [substs_all hq] using not_congr hcurrentNeg
    · have hdomSub : ¬IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (^∀ q)) := by
        simpa only [isSigmaCode_subst_iff hp hw] using hdom
      constructor
      · intro hs
        exact (hdomSub (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim
  · subst p
    have hsemQ := IsSemiformula.exs.mp hp
    have hpSigma := quantifierBoundedCode_exs_sigma hq hbounded
    have hqBound : QuantifierBoundedCode ℒₒᵣ currentLevel q :=
      ((isSigmaCode_exs_iff hq).mp hpSigma).1.quantifierBounded
    by_cases hdom : IsSigmaCode ℒₒᵣ nextLevel (^∃ q)
    · have hpositive := ((isSigmaCode_exs_iff hq).mp hdom).2
      have hdomSub : IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (^∃ q)) :=
        hdom.subst hp hw
      rw [substs_ex hq,
        SuccessorTruth.exs_iff (hsemQ.subst hw.qVec).isUFormula
          (by
            have := ((isSigmaCode_exs_iff
              (hsemQ.subst hw.qVec).isUFormula).mp (by
                simpa only [substs_ex hq] using hdomSub)).2
            exact this),
        SuccessorTruth.exs_iff hq hpositive]
      constructor
      · rintro ⟨a, ha⟩
        have hsubQ := isSubstitutionEnvironment_qVec_seqCons
          (a := a) hw hboundLen.symm hsub
        refine ⟨a, (hprefix q (by simp)
          (subBound ⁀' a) (qVec ℒₒᵣ terms) (termBound + 1)
          free (bound ⁀' a) (arity + 1)
          hw.qVec ?_ hsubQ hsemQ hqBound).mp ha⟩
        simp [hsub.2.1, hboundLen]
      · rintro ⟨a, ha⟩
        have hsubQ := isSubstitutionEnvironment_qVec_seqCons
          (a := a) hw hboundLen.symm hsub
        refine ⟨a, (hprefix q (by simp)
          (subBound ⁀' a) (qVec ℒₒᵣ terms) (termBound + 1)
          free (bound ⁀' a) (arity + 1)
          hw.qVec ?_ hsubQ hsemQ hqBound).mpr ha⟩
        simp [hsub.2.1, hboundLen]
    · have hdomSub : ¬IsSigmaCode ℒₒᵣ nextLevel
          (subst ℒₒᵣ terms (^∃ q)) := by
        simpa only [isSigmaCode_subst_iff hp hw] using hdom
      constructor
      · intro hs
        exact (hdomSub (SuccessorTruth.domain hs)).elim
      · intro hs
        exact (hdom (SuccessorTruth.domain hs)).elim

end GenericSuccessor

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
