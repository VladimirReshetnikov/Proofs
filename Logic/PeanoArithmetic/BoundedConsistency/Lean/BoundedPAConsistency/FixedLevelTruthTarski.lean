import BoundedPAConsistency.FixedLevelTruthCertificate
import BoundedPAConsistency.FixedLevelTruthDefinability
import BoundedPAConsistency.ModelFormulaInduction

set_option maxHeartbeats 800000

/-!
# Tarski clauses for externally fixed partial truth

The positive clauses in `FixedLevelTruthCertificate` describe the Sigma
skeleton at a successor level.  This file packages those clauses uniformly
over the external level, derives the dual Pi clauses from coded negation, and
proves the two polarity-switching clauses at quantifier heads.

All formula codes below are elements of an arbitrary (possibly nonstandard)
model of arithmetic.  In particular, the universal clause is not proved by
decoding a code into a Lean formula.  It follows from complementing the
certificate clause for the coded existential negation.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

private lemma levelCode_succ (n : ℕ) :
    levelCode (V := V) (n + 1) = levelCode n + 1 := by
  exact (numeral_add_one n).symm

/-- The oriented domain carried by Sigma truth, uniformly over the external
level. -/
theorem SigmaTrue.domain {n : ℕ} {bound free p : V}
    (h : SigmaTrue n bound free p) :
    IsSigmaCode ℒₒᵣ (levelCode n) p := by
  cases n with
  | zero => exact sigmaTrue_zero_sigmaDomain h
  | succ n => exact FixedLevelTruth.SigmaTrue.domain_succ h

/-! ## Uniform positive clauses -/

@[simp] theorem sigmaTrue_and_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue n bound free (p ^⋏ q) ↔
      SigmaTrue n bound free p ∧ SigmaTrue n bound free q := by
  cases n with
  | zero => exact qfTrue_and_iff hp hq
  | succ n => exact sigmaTrue_succ_and_iff hp hq

@[simp] theorem sigmaTrue_or_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hpdom : IsSigmaCode ℒₒᵣ (levelCode n) p)
    (hqdom : IsSigmaCode ℒₒᵣ (levelCode n) q) :
    SigmaTrue n bound free (p ^⋎ q) ↔
      SigmaTrue n bound free p ∨ SigmaTrue n bound free q := by
  cases n with
  | zero =>
      have hpqf : IsQuantifierFreeCode p := by
        rcases hpdom with ⟨hpU, hs⟩
        have hs0 : sigmaRankCode ℒₒᵣ p = 0 := by
          simpa [levelCode] using hs
        have hgroups : quantifierGroupsCode ℒₒᵣ p = 0 := by
          simp [quantifierGroupsCode, hs0]
        exact ⟨hpU, by simp [hgroups]⟩
      have hqqf : IsQuantifierFreeCode q := by
        rcases hqdom with ⟨hqU, hs⟩
        have hs0 : sigmaRankCode ℒₒᵣ q = 0 := by
          simpa [levelCode] using hs
        have hgroups : quantifierGroupsCode ℒₒᵣ q = 0 := by
          simp [quantifierGroupsCode, hs0]
        exact ⟨hqU, by simp [hgroups]⟩
      exact qfTrue_or_iff hp hq hpqf hqqf
  | succ n => exact sigmaTrue_succ_or_iff hp hq hpdom hqdom

@[simp] theorem sigmaTrue_exs_iff {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (^∃ q) ↔
      ∃ a, SigmaTrue (n + 1) (bound ⁀' a) free q :=
  sigmaTrue_succ_exs_iff hq

/-! ## Dual Boolean clauses -/

@[simp] theorem piTrue_and_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    PiTrue n bound free (p ^⋏ q) ↔
      PiTrue n bound free p ∧ PiTrue n bound free q := by
  constructor
  · rintro ⟨hdom, hnot⟩
    have hparts := (isPiCode_and_iff hp hq).mp hdom
    have hsnegp : IsSigmaCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ p) :=
      (isSigmaCode_neg_iff hp).mpr hparts.1
    have hsnegq : IsSigmaCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ q) :=
      (isSigmaCode_neg_iff hq).mpr hparts.2
    rw [neg_and hp hq, sigmaTrue_or_iff hp.neg hq.neg
      hsnegp hsnegq] at hnot
    exact ⟨⟨hparts.1, fun h ↦ hnot (Or.inl h)⟩,
      ⟨hparts.2, fun h ↦ hnot (Or.inr h)⟩⟩
  · rintro ⟨⟨hdp, hnp⟩, ⟨hdq, hnq⟩⟩
    refine ⟨(isPiCode_and_iff hp hq).mpr ⟨hdp, hdq⟩, ?_⟩
    have hsnegp := (isSigmaCode_neg_iff hp).mpr hdp
    have hsnegq := (isSigmaCode_neg_iff hq).mpr hdq
    rw [neg_and hp hq, sigmaTrue_or_iff hp.neg hq.neg
      hsnegp hsnegq]
    tauto

@[simp] theorem piTrue_or_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hpdom : IsPiCode ℒₒᵣ (levelCode n) p)
    (hqdom : IsPiCode ℒₒᵣ (levelCode n) q) :
    PiTrue n bound free (p ^⋎ q) ↔
      PiTrue n bound free p ∨ PiTrue n bound free q := by
  constructor
  · rintro ⟨hdom, hnot⟩
    have hparts := (isPiCode_or_iff hp hq).mp hdom
    rw [neg_or hp hq, sigmaTrue_and_iff hp.neg hq.neg] at hnot
    rcases not_and_or.mp hnot with hnp | hnq
    · exact Or.inl ⟨hparts.1, hnp⟩
    · exact Or.inr ⟨hparts.2, hnq⟩
  · rintro (⟨hdp, hnp⟩ | ⟨hdq, hnq⟩)
    · exact ⟨(isPiCode_or_iff hp hq).mpr ⟨hdp, hqdom⟩, by
        rw [neg_or hp hq, sigmaTrue_and_iff hp.neg hq.neg]
        exact fun h ↦ hnp h.1⟩
    · exact ⟨(isPiCode_or_iff hp hq).mpr ⟨hpdom, hdq⟩, by
        rw [neg_or hp hq, sigmaTrue_and_iff hp.neg hq.neg]
        exact fun h ↦ hnq h.2⟩

/-! ## Quantifier clauses and polarity switches -/

/-- Pi truth of a universal formula is truth of its body at every element of
the ambient model.  The quantified element is a model element, not a Lean
natural, so this statement includes all nonstandard witnesses. -/
@[simp] theorem piTrue_all_iff {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q) :
    PiTrue (n + 1) bound free (^∀ q) ↔
      ∀ a, PiTrue (n + 1) (bound ⁀' a) free q := by
  constructor
  · rintro ⟨hdom, hnot⟩ a
    have hqdom : IsPiCode ℒₒᵣ (levelCode (n + 1)) q := by
      rw [levelCode_succ]
      exact (isPiCode_all_succ_iff (n := levelCode n) hq).mp
        (by simpa only [levelCode_succ] using hdom)
    refine ⟨hqdom, ?_⟩
    intro hneg
    apply hnot
    rw [neg_all hq, sigmaTrue_exs_iff hq.neg]
    exact ⟨a, hneg⟩
  · intro h
    have hqdom : IsPiCode ℒₒᵣ (levelCode (n + 1)) q :=
      (h 0).1
    have halldom : IsPiCode ℒₒᵣ (levelCode (n + 1)) (^∀ q) := by
      rw [levelCode_succ] at hqdom ⊢
      simpa only [levelCode_succ] using
        (isPiCode_all_succ_iff (n := levelCode n) hq).mpr hqdom
    refine ⟨halldom, ?_⟩
    rw [neg_all hq, sigmaTrue_exs_iff hq.neg]
    rintro ⟨a, ha⟩
    exact (h a).2 ha

/-- The lower-Pi leaf stored in a successor certificate is definitionally the
already constructed lower-level Pi truth predicate. -/
@[simp] theorem lowerPiTrue_iff_piTrue {n : ℕ} {bound free p : V} :
    LowerPiTrue (SigmaTrue n) (levelCode n) bound free p ↔
      PiTrue n bound free p := by
  rfl

/-- Reading an opposite-polarity universal leaf from a Sigma certificate. -/
theorem sigmaTrue_succ_all_elim {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : SigmaTrue (n + 1) bound free (^∀ q)) :
    PiTrue n bound free (^∀ q) := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (^∀ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · exact (not_isQuantifierFreeCode_all hq (by simpa using hqf.1)).elim
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqAll] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqOr, qqAll] at heq
  · rcases hexs with ⟨r, _, heq, _⟩
    simp [qqExs, qqAll] at heq
  · rcases hall with ⟨q', hq', heq, hlower⟩
    have heq' : q = q' := by
      apply (qqAll_inj q q').mp
      simpa using heq
    subst q'
    simpa using hlower

/-- Build the singleton successor certificate whose root is a lower-Pi
universal leaf. -/
theorem sigmaTrue_succ_all_intro {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : PiTrue n bound free (^∀ q)) :
    SigmaTrue (n + 1) bound free (^∀ q) := by
  let root : V := truthRecord bound free (^∀ q) 0
  let C : V := insert root ∅
  have hroot : root ∈ C := by simp [C]
  have hlower := (isPiCode_all_iff hq).mp h.1
  have hdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) (^∀ q) := by
    simpa only [levelCode_succ] using
      (isSigmaCode_all_succ_iff (n := levelCode n) hq).mpr hlower
  refine ⟨C, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    have hrr : r = root := by simpa [C] using hr
    subst r
    refine ⟨(by simpa [root] using hdom),
      Or.inr <| Or.inr <| Or.inr <| Or.inr ?_⟩
    exact ⟨q, by simp [root], by simp [root], by simpa [root] using h⟩

/-- At a universal head, successor Sigma truth is exactly lower Pi truth.
This is the alternation step of the externally indexed construction. -/
@[simp] theorem sigmaTrue_succ_all_iff {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (^∀ q) ↔
      PiTrue n bound free (^∀ q) :=
  ⟨sigmaTrue_succ_all_elim hq, sigmaTrue_succ_all_intro hq⟩

/-- At an existential head, successor Pi truth is exactly lower Sigma truth.
This is the De Morgan dual of `sigmaTrue_succ_all_iff`. -/
@[simp] theorem piTrue_succ_exs_iff {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q) :
    PiTrue (n + 1) bound free (^∃ q) ↔
      SigmaTrue n bound free (^∃ q) := by
  constructor
  · rintro ⟨hdom, hnotUpper⟩
    have hparts : IsSigmaCode ℒₒᵣ (levelCode n) q ∧
        (1 : V) ≤ levelCode (V := V) n := by
      have hdom' : IsPiCode ℒₒᵣ (levelCode n + 1) (^∃ q) := by
        simpa only [← levelCode_succ] using hdom
      exact (isPiCode_exs_succ_iff (n := levelCode n) hq).mp hdom'
    have hnqdom : IsPiCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ q) :=
      (isPiCode_neg_iff hq).mpr hparts.1
    have halldom : IsPiCode ℒₒᵣ (levelCode n) (^∀ (neg ℒₒᵣ q)) :=
      (isPiCode_all_iff hq.neg).mpr ⟨hnqdom, hparts.2⟩
    have hnotLower : ¬PiTrue n bound free (^∀ (neg ℒₒᵣ q)) := by
      intro hlower
      apply hnotUpper
      rw [neg_ex hq, sigmaTrue_succ_all_iff hq.neg]
      exact hlower
    have hs : SigmaTrue n bound free
        (neg ℒₒᵣ (^∀ (neg ℒₒᵣ q))) := by
      by_contra hs
      exact hnotLower ⟨halldom, hs⟩
    simpa [neg_all hq.neg, hq.neg_neg] using hs
  · intro hs
    have hdomLower := SigmaTrue.domain hs
    have hparts : IsSigmaCode ℒₒᵣ (levelCode n) q ∧
        (1 : V) ≤ levelCode (V := V) n :=
      (isSigmaCode_exs_iff hq).mp hdomLower
    have hdomUpper' : IsPiCode ℒₒᵣ (levelCode n + 1) (^∃ q) :=
      (isPiCode_exs_succ_iff (n := levelCode n) hq).mpr hparts
    have hdomUpper : IsPiCode ℒₒᵣ (levelCode (n + 1)) (^∃ q) := by
      simpa only [levelCode_succ] using hdomUpper'
    refine ⟨hdomUpper, ?_⟩
    rw [neg_ex hq, sigmaTrue_succ_all_iff hq.neg]
    intro hlower
    apply hlower.2
    simpa [neg_all hq.neg, hq.neg_neg] using hs

end LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
