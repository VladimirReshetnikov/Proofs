import BoundedPAConsistency.FixedLevelTruthTarski

set_option maxHeartbeats 800000

/-!
# Coherence of the two fixed-level truth polarities

The certificate predicate deliberately has separate Sigma and Pi
presentations.  This file starts their conservativity/coherence proof with
the rank-zero overlap: a positive-level certificate for a quantifier-free
formula has exactly the value of the represented quantifier-free evaluator.
The proof uses structural induction inside an arbitrary model of PA and thus
also covers nonstandard formula codes.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence

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
open LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
open LeanProofs.BoundedPAConsistency.ModelFormulaInduction

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

private def QFCertificateSound (p : V) : Prop :=
  ∀ bound free, IsQuantifierFreeCode p →
    SigmaTrue 1 bound free p → QFTrue bound free p

private lemma qfCertificateSound_definable :
    Polarity.pi-[2]-Predicate (QFCertificateSound (V := V)) := by
  unfold QFCertificateSound
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.DefinableRel₃.comp
          (sigmaTrue_definable (V := V) 1)
      · simp
      · simp
      · simp
    · exact HierarchySymbol.Definable.of_deltaOne (by definability)

private theorem sigmaTrue_succ_rel_elim {n : ℕ}
    {bound free k R terms : V}
    (h : SigmaTrue (n + 1) bound free (^rel k R terms)) :
    QFTrue bound free (^rel k R terms) := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (^rel k R terms) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · simpa using hqf
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqRel, qqAnd] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqRel, qqOr] at heq
  · rcases hexs with ⟨q, _, heq, _⟩
    simp [qqRel, qqExs] at heq
  · rcases hall with ⟨q, _, heq, _⟩
    simp [qqRel, qqAll] at heq

private theorem sigmaTrue_succ_nrel_elim {n : ℕ}
    {bound free k R terms : V}
    (h : SigmaTrue (n + 1) bound free (^nrel k R terms)) :
    QFTrue bound free (^nrel k R terms) := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (^nrel k R terms) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · simpa using hqf
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqNRel, qqAnd] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqNRel, qqOr] at heq
  · rcases hexs with ⟨q, _, heq, _⟩
    simp [qqNRel, qqExs] at heq
  · rcases hall with ⟨q, _, heq, _⟩
    simp [qqNRel, qqAll] at heq

private theorem sigmaTrue_succ_verum_elim {n : ℕ}
    {bound free : V} (h : SigmaTrue (n + 1) bound free ^⊤) :
    QFTrue bound free ^⊤ := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free ^⊤ w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · simpa using hqf
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqVerum, qqAnd] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqVerum, qqOr] at heq
  · rcases hexs with ⟨q, _, heq, _⟩
    simp [qqVerum, qqExs] at heq
  · rcases hall with ⟨q, _, heq, _⟩
    simp [qqVerum, qqAll] at heq

private theorem sigmaTrue_succ_falsum_elim {n : ℕ}
    {bound free : V} (h : SigmaTrue (n + 1) bound free ^⊥) :
    QFTrue bound free ^⊥ := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free ^⊥ w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · simpa using hqf
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqFalsum, qqAnd] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqFalsum, qqOr] at heq
  · rcases hexs with ⟨q, _, heq, _⟩
    simp [qqFalsum, qqExs] at heq
  · rcases hall with ⟨q, _, heq, _⟩
    simp [qqFalsum, qqAll] at heq

/-- A level-one certificate cannot assign a spurious value to a
quantifier-free formula.  The internal structural induction is what makes
this true for nonstandard Boolean formula trees as well as standard ones. -/
theorem sigmaTrue_one_qf_sound {bound free p : V}
    (hp : IsQuantifierFreeCode p)
    (h : SigmaTrue 1 bound free p) :
    QFTrue bound free p := by
  have hmain : ∀ p : V, IsUFormula ℒₒᵣ p →
      QFCertificateSound (V := V) p := by
    apply uformula_inductionInPeanoModel
        (L := ℒₒᵣ) qfCertificateSound_definable
    · intro k R terms hR hterms bound free hp h
      exact sigmaTrue_succ_rel_elim h
    · intro k R terms hR hterms bound free hp h
      exact sigmaTrue_succ_nrel_elim h
    · intro bound free hp h
      exact sigmaTrue_succ_verum_elim h
    · intro bound free hp h
      exact sigmaTrue_succ_falsum_elim h
    · intro p q hp hq ihp ihq bound free hpq htrue
      have hqf := (isQuantifierFreeCode_and_iff hp hq).mp hpq
      have hparts := (sigmaTrue_and_iff hp hq).mp htrue
      exact (qfTrue_and_iff hp hq).mpr
        ⟨ihp bound free hqf.1 hparts.1,
          ihq bound free hqf.2 hparts.2⟩
    · intro p q hp hq ihp ihq bound free hpq htrue
      have hqf := (isQuantifierFreeCode_or_iff hp hq).mp hpq
      have hdom := SigmaTrue.domain htrue
      have hdoms := (isSigmaCode_or_iff hp hq).mp hdom
      rcases (sigmaTrue_or_iff hp hq hdoms.1 hdoms.2).mp htrue with
          htrue | htrue
      · exact (qfTrue_or_iff hp hq hqf.1 hqf.2).mpr <|
          Or.inl (ihp bound free hqf.1 htrue)
      · exact (qfTrue_or_iff hp hq hqf.1 hqf.2).mpr <|
          Or.inr (ihq bound free hqf.2 htrue)
    · intro p hp ih bound free hpq
      exact (not_isQuantifierFreeCode_all hp hpq).elim
    · intro p hp ih bound free hpq
      exact (not_isQuantifierFreeCode_exs hp hpq).elim
  exact hmain p hp.1 bound free hp h

@[simp] theorem sigmaTrue_one_qf_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    SigmaTrue 1 bound free p ↔ QFTrue bound free p :=
  ⟨sigmaTrue_one_qf_sound hp, sigmaTrue_succ_of_qfTrue⟩

private lemma qf_isPiCode (n : ℕ) {p : V}
    (hp : IsQuantifierFreeCode p) :
    IsPiCode ℒₒᵣ (levelCode (V := V) n) p := by
  have hr := isQuantifierFreeCode_iff.mp hp
  exact ⟨hp.1, by simp [levelCode, hr.2.2]⟩

@[simp] theorem piTrue_zero_qf_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    PiTrue 0 bound free p ↔ QFTrue bound free p := by
  have hpPi := qf_isPiCode (V := V) 0 hp
  have hnqf : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
    (isQuantifierFreeCode_neg_iff hp.1).mpr hp
  rw [piTrue_iff, and_iff_right hpPi, sigmaTrue_zero,
    qfTrue_neg_iff hp, qfTrue_iff_not_qfFalse hp]

@[simp] theorem piTrue_one_qf_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    PiTrue 1 bound free p ↔ QFTrue bound free p := by
  have hpPi := qf_isPiCode (V := V) 1 hp
  have hnqf : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
    (isQuantifierFreeCode_neg_iff hp.1).mpr hp
  rw [piTrue_iff, and_iff_right hpPi, sigmaTrue_one_qf_iff hnqf,
    qfTrue_neg_iff hp, qfTrue_iff_not_qfFalse hp]

/-- Both oriented presentations agree at hierarchy zero. -/
theorem sigmaTrue_zero_iff_piTrue_zero {bound free p : V}
    (hs : IsSigmaCode ℒₒᵣ (levelCode (V := V) 0) p)
    (hpi : IsPiCode ℒₒᵣ (levelCode (V := V) 0) p) :
    SigmaTrue 0 bound free p ↔ PiTrue 0 bound free p := by
  have hp : IsQuantifierFreeCode p := by
    have hs0 : sigmaRankCode ℒₒᵣ p = 0 := by
      simpa [levelCode] using hs.2
    have hpi0 : piRankCode ℒₒᵣ p = 0 := by
      simpa [levelCode] using hpi.2
    exact isQuantifierFreeCode_iff.mpr ⟨hs.1, hs0, hpi0⟩
  rw [sigmaTrue_zero, piTrue_zero_qf_iff hp]

/-- Both oriented presentations agree on their rank-zero overlap when viewed
at the first positive certificate level. -/
theorem sigmaTrue_one_iff_piTrue_one_of_qf {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    SigmaTrue 1 bound free p ↔ PiTrue 1 bound free p := by
  rw [sigmaTrue_one_qf_iff hp, piTrue_one_qf_iff hp]

end LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
