import BoundedPAConsistency.FixedLevelTruthTarski

set_option maxHeartbeats 800000

/-!
# Coherence of the two fixed-level truth polarities

The certificate predicate deliberately has separate Sigma and Pi
presentations.  This file proves their conservativity and coherence at every
externally fixed hierarchy level.  Its base case identifies positive-level
certificates with the represented quantifier-free evaluator; the general
case combines external induction on the level with structural induction
inside an arbitrary model of PA.  It therefore covers nonstandard formula
codes as well as standard ones.
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

private def QFCertificateSound (n : ℕ) (p : V) : Prop :=
  ∀ bound free, IsQuantifierFreeCode p →
    SigmaTrue (n + 1) bound free p → QFTrue bound free p

private lemma qfCertificateSound_definable (n : ℕ) :
    Polarity.pi-[n + 2]-Predicate (QFCertificateSound (V := V) n) := by
  unfold QFCertificateSound
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.DefinableRel₃.comp
          (sigmaTrue_definable (V := V) (n + 1))
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
theorem sigmaTrue_succ_qf_sound (n : ℕ) {bound free p : V}
    (hp : IsQuantifierFreeCode p)
    (h : SigmaTrue (n + 1) bound free p) :
    QFTrue bound free p := by
  have hmain : ∀ p : V, IsUFormula ℒₒᵣ p →
      QFCertificateSound (V := V) n p := by
    apply uformula_inductionInPeanoModel
        (L := ℒₒᵣ) (qfCertificateSound_definable n)
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

@[simp] theorem sigmaTrue_succ_qf_iff (n : ℕ) {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    SigmaTrue (n + 1) bound free p ↔ QFTrue bound free p :=
  ⟨sigmaTrue_succ_qf_sound n hp, sigmaTrue_succ_of_qfTrue⟩

theorem sigmaTrue_one_qf_sound {bound free p : V}
    (hp : IsQuantifierFreeCode p)
    (h : SigmaTrue 1 bound free p) :
    QFTrue bound free p :=
  sigmaTrue_succ_qf_sound 0 hp h

@[simp] theorem sigmaTrue_one_qf_iff {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    SigmaTrue 1 bound free p ↔ QFTrue bound free p :=
  sigmaTrue_succ_qf_iff 0 hp

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

@[simp] theorem piTrue_succ_qf_iff (n : ℕ) {bound free p : V}
    (hp : IsQuantifierFreeCode p) :
    PiTrue (n + 1) bound free p ↔ QFTrue bound free p := by
  have hpPi := qf_isPiCode (V := V) (n + 1) hp
  have hnqf : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
    (isQuantifierFreeCode_neg_iff hp.1).mpr hp
  rw [piTrue_iff, and_iff_right hpPi, sigmaTrue_succ_qf_iff n hnqf,
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

/-! ## The mutual conservativity invariant -/

private lemma sigma_definable_succ
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.sigma-[m].Definable P) :
    Polarity.sigma-[m + 1].Definable P := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨HierarchySymbol.Semiformula.mkSigma φ.val
      (φ.sigma_prop.accum Polarity.sigma), by
    intro v
    simpa using hφ.iff (v := v)⟩

private lemma sigma_definable_add
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.sigma-[m].Definable P) :
    ∀ d : ℕ, Polarity.sigma-[m + d].Definable P := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
      simpa [Nat.add_assoc] using sigma_definable_succ ih

private lemma pi_definable_succ
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.pi-[m].Definable P) :
    Polarity.pi-[m + 1].Definable P := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨HierarchySymbol.Semiformula.mkPi φ.val
      (φ.pi_prop.accum Polarity.pi), by
    intro v
    simpa using hφ.iff (v := v)⟩

private lemma sigma_definable_delta_succ
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.sigma-[m].Definable P) :
    SigmaPiDelta.delta-[m + 1].Definable P := by
  rcases h with ⟨φ, hφ⟩
  apply HierarchySymbol.Definable.of_sigma_of_pi
      (Γ := SigmaPiDelta.delta)
  · exact ⟨HierarchySymbol.Semiformula.mkSigma φ.val
        (φ.sigma_prop.accum Polarity.sigma), by
      intro v
      simpa using hφ.iff (v := v)⟩
  · exact ⟨HierarchySymbol.Semiformula.mkPi φ.val
        (φ.sigma_prop.accum Polarity.pi), by
      intro v
      simpa using hφ.iff (v := v)⟩

private lemma pi_definable_delta_succ
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.pi-[m].Definable P) :
    SigmaPiDelta.delta-[m + 1].Definable P := by
  rcases h with ⟨φ, hφ⟩
  apply HierarchySymbol.Definable.of_sigma_of_pi
      (Γ := SigmaPiDelta.delta)
  · exact ⟨HierarchySymbol.Semiformula.mkSigma φ.val
        (φ.pi_prop.accum Polarity.sigma), by
      intro v
      simpa using hφ.iff (v := v)⟩
  · exact ⟨HierarchySymbol.Semiformula.mkPi φ.val
        (φ.pi_prop.accum Polarity.pi), by
      intro v
      simpa using hφ.iff (v := v)⟩

private def LevelLaws (n : ℕ) (p : V) : Prop :=
  ∀ bound free,
    (IsSigmaCode ℒₒᵣ (levelCode n) p →
      (SigmaTrue (n + 1) bound free p ↔ SigmaTrue n bound free p)) ∧
    (IsPiCode ℒₒᵣ (levelCode n) p →
      (SigmaTrue (n + 1) bound free p ↔ PiTrue n bound free p))

private lemma levelCode_succ (n : ℕ) :
    levelCode (V := V) (n + 1) = levelCode n + 1 :=
  (numeral_add_one n).symm

private lemma qf_of_isSigma_zero {p : V}
    (hp : IsSigmaCode ℒₒᵣ (levelCode (V := V) 0) p) :
    IsQuantifierFreeCode p := by
  simpa [IsQuantifierFreeCode, levelCode] using hp.quantifierBounded

private lemma qf_of_isPi_zero {p : V}
    (hp : IsPiCode ℒₒᵣ (levelCode (V := V) 0) p) :
    IsQuantifierFreeCode p := by
  simpa [IsQuantifierFreeCode, levelCode] using hp.quantifierBounded

private lemma levelLaws_definable (n : ℕ) :
    Polarity.pi-[n + 3 + 1]-Predicate (LevelLaws (V := V) n) := by
  letI : SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
      (SigmaTrue (V := V) (n + 1)) := by
    have h₀ : Polarity.sigma-[n + 2]-Relation₃
        (SigmaTrue (V := V) (n + 1)) := by
      have hraw := sigmaTrue_definable (V := V) (n + 1)
      change Polarity.sigma-[(n + 1) + 1]-Relation₃
        (SigmaTrue (V := V) (n + 1)) at hraw
      simpa [Nat.add_assoc] using hraw
    have h₁ : Polarity.sigma-[n + 3]-Relation₃
        (SigmaTrue (V := V) (n + 1)) := sigma_definable_succ h₀
    exact sigma_definable_delta_succ h₁
  letI : SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
      (SigmaTrue (V := V) n) := by
    have h₀ : Polarity.sigma-[n + 1]-Relation₃
        (SigmaTrue (V := V) n) := sigmaTrue_definable (V := V) n
    have h₁ : Polarity.sigma-[n + 2]-Relation₃
        (SigmaTrue (V := V) n) := sigma_definable_succ h₀
    have h₂ : Polarity.sigma-[n + 3]-Relation₃
        (SigmaTrue (V := V) n) := sigma_definable_succ h₁
    exact sigma_definable_delta_succ h₂
  letI : SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
      (PiTrue (V := V) n) := by
    have h₀ : Polarity.pi-[n + 1]-Relation₃
        (PiTrue (V := V) n) := piTrue_definable (V := V) n
    have h₁ : Polarity.pi-[n + 2]-Relation₃
        (PiTrue (V := V) n) := pi_definable_succ h₀
    have h₂ : Polarity.pi-[n + 3]-Relation₃
        (PiTrue (V := V) n) := pi_definable_succ h₁
    exact pi_definable_delta_succ h₂
  letI : Polarity.sigma-[n + 3 + 1]-Relation
      (IsSigmaCode (V := V) ℒₒᵣ) := by
    have hraw := IsSigmaCode.definable (V := V) (L := ℒₒᵣ)
    change HierarchySymbol.sigmaOne.DefinableRel
      (V := V) (IsSigmaCode ℒₒᵣ) at hraw
    have h₀ : Polarity.sigma-[1]-Relation
        (IsSigmaCode (V := V) ℒₒᵣ) := by simpa using hraw
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      sigma_definable_add h₀ (n + 3)
  letI : Polarity.sigma-[n + 3 + 1]-Relation
      (IsPiCode (V := V) ℒₒᵣ) := by
    have hraw := IsPiCode.definable (V := V) (L := ℒₒᵣ)
    change HierarchySymbol.sigmaOne.DefinableRel
      (V := V) (IsPiCode ℒₒᵣ) at hraw
    have h₀ : Polarity.sigma-[1]-Relation
        (IsPiCode (V := V) ℒₒᵣ) := by simpa using hraw
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      sigma_definable_add h₀ (n + 3)
  unfold LevelLaws
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.and
  · apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.DefinableRel.comp
          (show Polarity.sigma-[n + 3 + 1]-Relation
            (IsSigmaCode (V := V) ℒₒᵣ) from inferInstance)
      · simp
      · simp
    · apply HierarchySymbol.Definable.biconditional
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance) <;> simp
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
              (SigmaTrue (V := V) n) from inferInstance) <;> simp
  · apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.DefinableRel.comp
          (show Polarity.sigma-[n + 3 + 1]-Relation
            (IsPiCode (V := V) ℒₒᵣ) from inferInstance)
      · simp
      · simp
    · apply HierarchySymbol.Definable.biconditional
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance) <;> simp
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3 + 1]-Relation₃
              (PiTrue (V := V) n) from inferInstance) <;> simp

private theorem qf_levelLaws (n : ℕ) {p : V}
    (hp : IsQuantifierFreeCode p) :
    LevelLaws (V := V) n p := by
  intro bound free
  constructor <;> intro hdom
  · cases n with
    | zero =>
        rw [sigmaTrue_one_qf_iff hp, sigmaTrue_zero]
    | succ n =>
        rw [sigmaTrue_succ_qf_iff (n + 1) hp,
          sigmaTrue_succ_qf_iff n hp]
  · cases n with
    | zero =>
        rw [sigmaTrue_one_qf_iff hp, piTrue_zero_qf_iff hp]
    | succ n =>
        rw [sigmaTrue_succ_qf_iff (n + 1) hp,
          piTrue_succ_qf_iff n hp]

/-- Pi truth is conservative whenever the Sigma half of `LevelLaws` is
available for the coded negation. -/
private theorem pi_stable_of_neg_levelLaws {n : ℕ} {bound free p : V}
    (hp : IsPiCode ℒₒᵣ (levelCode n) p)
    (hneg : LevelLaws (V := V) n (neg ℒₒᵣ p)) :
    PiTrue (n + 1) bound free p ↔ PiTrue n bound free p := by
  have hpUpper : IsPiCode ℒₒᵣ (levelCode (n + 1)) p := by
    rw [levelCode_succ]
    exact hp.mono (by simp)
  have hnSigma : IsSigmaCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ p) :=
    (isSigmaCode_neg_iff hp.1).mpr hp
  have hstable := (hneg bound free).1 hnSigma
  rw [piTrue_iff, piTrue_iff, and_iff_right hpUpper,
    and_iff_right hp]
  exact not_congr hstable

/-!
The following is the key external/internal induction.  The hierarchy level is
an ordinary Lean natural, while the structural induction runs *inside* the
ambient PA model.  This distinction is essential: `p` may be a nonstandard
formula code, so ordinary recursion on a decoded Lean formula would not prove
the required statement.
-/

private theorem levelLaws_all : ∀ n : ℕ, ∀ p : V,
    IsUFormula ℒₒᵣ p → LevelLaws (V := V) n p := by
  intro n
  induction n with
  | zero =>
      intro p hp bound free
      constructor
      · intro hs
        exact (qf_levelLaws 0 (qf_of_isSigma_zero hs) bound free).1 hs
      · intro hpi
        exact (qf_levelLaws 0 (qf_of_isPi_zero hpi) bound free).2 hpi
  | succ n ihn =>
      intro p hp
      apply uformula_inductionInPeanoModel
          (L := ℒₒᵣ) (levelLaws_definable (n + 1))
      · intro k R terms hR hterms
        exact qf_levelLaws (n + 1) (by
          simp [IsQuantifierFreeCode, hR, hterms])
      · intro k R terms hR hterms
        exact qf_levelLaws (n + 1) (by
          simp [IsQuantifierFreeCode, hR, hterms])
      · exact qf_levelLaws (n + 1) (by simp)
      · exact qf_levelLaws (n + 1) (by simp)
      · intro p q hp hq ihp ihq bound free
        constructor
        · intro hs
          have hparts := (isSigmaCode_and_iff hp hq).mp hs
          simpa only [sigmaTrue_and_iff hp hq] using
            and_congr ((ihp bound free).1 hparts.1)
              ((ihq bound free).1 hparts.2)
        · intro hpi
          have hparts := (isPiCode_and_iff hp hq).mp hpi
          simpa only [sigmaTrue_and_iff hp hq, piTrue_and_iff hp hq] using
            and_congr ((ihp bound free).2 hparts.1)
              ((ihq bound free).2 hparts.2)
      · intro p q hp hq ihp ihq bound free
        constructor
        · intro hs
          have hparts := (isSigmaCode_or_iff hp hq).mp hs
          have hpUpper : IsSigmaCode ℒₒᵣ
              (levelCode (V := V) (n + 1 + 1)) p := by
            rw [levelCode_succ]
            exact hparts.1.mono (by simp)
          have hqUpper : IsSigmaCode ℒₒᵣ
              (levelCode (V := V) (n + 1 + 1)) q := by
            rw [levelCode_succ]
            exact hparts.2.mono (by simp)
          rw [sigmaTrue_or_iff hp hq hpUpper hqUpper,
            sigmaTrue_or_iff hp hq hparts.1 hparts.2]
          exact or_congr ((ihp bound free).1 hparts.1)
            ((ihq bound free).1 hparts.2)
        · intro hpi
          have hparts := (isPiCode_or_iff hp hq).mp hpi
          have hpUpper : IsSigmaCode ℒₒᵣ
              (levelCode (V := V) (n + 1 + 1)) p := by
            rw [levelCode_succ]
            exact hparts.1.toSigmaSucc
          have hqUpper : IsSigmaCode ℒₒᵣ
              (levelCode (V := V) (n + 1 + 1)) q := by
            rw [levelCode_succ]
            exact hparts.2.toSigmaSucc
          rw [sigmaTrue_or_iff hp hq hpUpper hqUpper,
            piTrue_or_iff hp hq hparts.1 hparts.2]
          exact or_congr ((ihp bound free).2 hparts.1)
            ((ihq bound free).2 hparts.2)
      · intro q hq ihq bound free
        constructor
        · intro hs
          have hparts : IsPiCode ℒₒᵣ (levelCode (V := V) n) q ∧
              (1 : V) ≤ levelCode (V := V) n := by
            apply (isSigmaCode_all_succ_iff
              (n := levelCode (V := V) n) hq).mp
            simpa only [levelCode_succ] using hs
          have hallPi : IsPiCode ℒₒᵣ (levelCode (V := V) n) (^∀ q) :=
            (isPiCode_all_iff hq).mpr hparts
          have hallU : IsUFormula ℒₒᵣ (^∀ q) := by simpa using hq
          rw [sigmaTrue_succ_all_iff hq, sigmaTrue_succ_all_iff hq]
          exact pi_stable_of_neg_levelLaws hallPi
            (ihn (neg ℒₒᵣ (^∀ q)) hallU.neg)
        · intro hpi
          exact sigmaTrue_succ_all_iff hq
      · intro q hq ihq bound free
        constructor
        · intro hs
          have hqSigma : IsSigmaCode ℒₒᵣ
              (levelCode (V := V) (n + 1)) q :=
            ((isSigmaCode_exs_iff hq).mp hs).1
          rw [sigmaTrue_exs_iff hq, sigmaTrue_exs_iff hq]
          constructor
          · rintro ⟨a, ha⟩
            exact ⟨a, ((ihq (bound ⁀' a) free).1 hqSigma).mp ha⟩
          · rintro ⟨a, ha⟩
            exact ⟨a, ((ihq (bound ⁀' a) free).1 hqSigma).mpr ha⟩
        · intro hpi
          have hpi' : IsPiCode ℒₒᵣ
              (levelCode (V := V) n + 1) (^∃ q) := by
            simpa only [levelCode_succ] using hpi
          have hparts := (isPiCode_exs_succ_iff
            (n := levelCode (V := V) n) hq).mp hpi'
          cases n with
          | zero =>
              have : ¬((1 : V) ≤ levelCode (V := V) 0) := by simp [levelCode]
              exact (this hparts.2).elim
          | succ n =>
              have hqMid : IsSigmaCode ℒₒᵣ
                  (levelCode (V := V) (n + 1 + 1)) q := by
                rw [levelCode_succ]
                exact hparts.1.mono (by simp)
              rw [sigmaTrue_exs_iff hq, piTrue_succ_exs_iff hq,
                sigmaTrue_exs_iff hq]
              constructor
              · rintro ⟨a, ha⟩
                exact ⟨a, (((ihq (bound ⁀' a) free).1 hqMid).trans
                  ((ihn q hq (bound ⁀' a) free).1 hparts.1)).mp ha⟩
              · rintro ⟨a, ha⟩
                exact ⟨a, (((ihq (bound ⁀' a) free).1 hqMid).trans
                  ((ihn q hq (bound ⁀' a) free).1 hparts.1)).mpr ha⟩
      · exact hp

/-- Successor Sigma truth is conservative on the Sigma-oriented domain at
the lower level. -/
theorem sigmaTrue_succ_iff_of_isSigmaCode (n : ℕ) {bound free p : V}
    (hp : IsSigmaCode ℒₒᵣ (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) bound free p ↔ SigmaTrue n bound free p :=
  ((levelLaws_all n p hp.1) bound free).1 hp

/-- At the alternation boundary, successor Sigma truth agrees with lower Pi
truth on the Pi-oriented domain. -/
theorem sigmaTrue_succ_iff_piTrue_of_isPiCode (n : ℕ)
    {bound free p : V}
    (hp : IsPiCode ℒₒᵣ (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) bound free p ↔ PiTrue n bound free p :=
  ((levelLaws_all n p hp.1) bound free).2 hp

/-- The two fixed-level polarity presentations coincide wherever both
oriented rank bounds hold. -/
theorem sigmaTrue_iff_piTrue_of_domains (n : ℕ) {bound free p : V}
    (hs : IsSigmaCode ℒₒᵣ (levelCode (V := V) n) p)
    (hp : IsPiCode ℒₒᵣ (levelCode (V := V) n) p) :
    SigmaTrue n bound free p ↔ PiTrue n bound free p :=
  (sigmaTrue_succ_iff_of_isSigmaCode n hs).symm.trans
    (sigmaTrue_succ_iff_piTrue_of_isPiCode n hp)

end LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
