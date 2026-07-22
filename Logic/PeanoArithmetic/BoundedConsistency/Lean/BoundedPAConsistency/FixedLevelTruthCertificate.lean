import BoundedPAConsistency.FixedLevelTruth

/-!
# Structural operations on fixed-level truth certificates

The successor truth predicate stores all recursive choices in one HFS set.
This file proves that states and local validity survive enlargement of that
set and constructs the one-record certificate for a quantifier-free leaf.
These small facts are the bookkeeping core used when Boolean and existential
certificates are joined.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- A state already present in a certificate remains present after enlarging
the underlying HFS set. -/
lemma HasTruthState.mono {C D bound free p : V}
    (hCD : C ⊆ D) (h : HasTruthState C bound free p) :
    HasTruthState D bound free p := by
  rcases h with ⟨w, hw, hr⟩
  refine ⟨w, lt_of_lt_of_le hw (le_of_subset hCD), hCD hr⟩

/-- The local certificate clause is positive in the certificate set. -/
lemma SigmaRecordValid.mono
    {lowerSigma : V → V → V → Prop}
    {lowerLevel upperLevel C D r : V}
    (hCD : C ⊆ D)
    (h : SigmaRecordValid lowerSigma lowerLevel upperLevel C r) :
    SigmaRecordValid lowerSigma lowerLevel upperLevel D r := by
  rcases h with ⟨hdom, hqf | hand | hor | hexs | hall⟩
  · exact ⟨hdom, Or.inl hqf⟩
  · rcases hand with ⟨p₁, hp₁, p₂, hp₂, hp, h₁, h₂⟩
    exact ⟨hdom, Or.inr <| Or.inl
      ⟨p₁, hp₁, p₂, hp₂, hp,
        HasTruthState.mono hCD h₁, HasTruthState.mono hCD h₂⟩⟩
  · rcases hor with ⟨p₁, hp₁, p₂, hp₂, hp, h₁ | h₂⟩
    · exact ⟨hdom, Or.inr <| Or.inr <| Or.inl
        ⟨p₁, hp₁, p₂, hp₂, hp,
          Or.inl (HasTruthState.mono hCD h₁)⟩⟩
    · exact ⟨hdom, Or.inr <| Or.inr <| Or.inl
        ⟨p₁, hp₁, p₂, hp₂, hp,
          Or.inr (HasTruthState.mono hCD h₂)⟩⟩
  · rcases hexs with ⟨q, hq, hp, hchild⟩
    exact ⟨hdom, Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨q, hq, hp, HasTruthState.mono hCD hchild⟩⟩
  · exact ⟨hdom, Or.inr <| Or.inr <| Or.inr <| Or.inr hall⟩

/-- A quantifier-free truth witness is a leaf at every positive Sigma level.

The singleton certificate is meaningful in a nonstandard model too: its sole
record is an HFS element, and the witness bound follows from projection of
that record rather than from a standard-natural calculation.
-/
theorem sigmaTrue_succ_of_qfTrue {n : ℕ} {bound free p : V}
    (h : QFTrue bound free p) :
    SigmaTrue (n + 1) bound free p := by
  let r : V := truthRecord bound free p 0
  let C : V := insert r ∅
  have hr : r ∈ C := by simp [C]
  refine ⟨C, ⟨0, ?_, hr⟩, ?_⟩
  · simpa [r, truthRecord] using (lt_of_mem_rng hr)
  · intro r' hr'
    have hrr : r' = r := by simpa [C] using hr'
    subst r'
    have hqf := isQuantifierFreeCode_iff.mp h.1
    have hdom :
        IsSigmaCode ℒₒᵣ (levelCode (n + 1)) (recordFormula r) := by
      simp only [r, recordFormula_truthRecord]
      exact ⟨hqf.1, by simp [levelCode, hqf.2.1]⟩
    exact ⟨hdom, Or.inl (by simpa [r] using h)⟩

/-- The base truth predicate carries both zero-oriented domains. -/
theorem sigmaTrue_zero_sigmaDomain {bound free p : V}
    (h : SigmaTrue 0 bound free p) :
    IsSigmaCode ℒₒᵣ (levelCode 0) p := by
  have hqf := isQuantifierFreeCode_iff.mp h.1
  exact ⟨hqf.1, by simp [levelCode, hqf.2.1]⟩

theorem sigmaTrue_zero_piDomain {bound free p : V}
    (h : SigmaTrue 0 bound free p) :
    IsPiCode ℒₒᵣ (levelCode 0) p := by
  have hqf := isQuantifierFreeCode_iff.mp h.1
  exact ⟨hqf.1, by simp [levelCode, hqf.2.2]⟩

/-! ## Joining successor certificates -/

/-- Join two certificates and add a conjunction record at their root. -/
theorem sigmaTrue_succ_and_intro {n : ℕ} {bound free p q : V}
    (hp : SigmaTrue (n + 1) bound free p)
    (hq : SigmaTrue (n + 1) bound free q) :
    SigmaTrue (n + 1) bound free (p ^⋏ q) := by
  rcases hp with ⟨C₁, hpC₁, hC₁⟩
  rcases hq with ⟨C₂, hqC₂, hC₂⟩
  let root : V := truthRecord bound free (p ^⋏ q) 0
  let D : V := insert root (C₁ ∪ C₂)
  have hC₁D : C₁ ⊆ D := by
    intro x hx
    simp [D, hx]
  have hC₂D : C₂ ⊆ D := by
    intro x hx
    simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr₁ | hr₂)
    · have hdp := SigmaTrue.domain_succ
          (show SigmaTrue (n + 1) bound free p from
            ⟨C₁, hpC₁, hC₁⟩)
      have hdq := SigmaTrue.domain_succ
          (show SigmaTrue (n + 1) bound free q from
            ⟨C₂, hqC₂, hC₂⟩)
      have hdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1))
          (recordFormula root) := by
        simp only [root, recordFormula_truthRecord]
        exact (isSigmaCode_and_iff hdp.1 hdq.1).2 ⟨hdp, hdq⟩
      refine ⟨hdom, Or.inr <| Or.inl
        ⟨p, ?_, q, ?_, by simp [root],
          (by simpa [root] using HasTruthState.mono hC₁D hpC₁),
          (by simpa [root] using HasTruthState.mono hC₂D hqC₂)⟩⟩
      · simp [root]
      · simp [root]
    · exact SigmaRecordValid.mono hC₁D (hC₁ r hr₁)
    · exact SigmaRecordValid.mono hC₂D (hC₂ r hr₂)

/-- Read the two child certificates from a conjunction root. -/
theorem sigmaTrue_succ_and_elim {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : SigmaTrue (n + 1) bound free (p ^⋏ q)) :
    SigmaTrue (n + 1) bound free p ∧
      SigmaTrue (n + 1) bound free q := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (p ^⋏ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · have hparts := (qfTrue_and_iff hp hq).mp (by simpa using hqf)
    exact ⟨sigmaTrue_succ_of_qfTrue hparts.1,
      sigmaTrue_succ_of_qfTrue hparts.2⟩
  · rcases hand with ⟨p₁, hp₁, p₂, hp₂, heq, h₁, h₂⟩
    have heq' : p = p₁ ∧ q = p₂ := by
      apply (qqAnd_inj p q p₁ p₂).mp
      simpa using heq
    rcases heq' with ⟨rfl, rfl⟩
    have h₁' : HasTruthState C bound free p := by
      simpa using h₁
    have h₂' : HasTruthState C bound free q := by
      simpa using h₂
    exact ⟨⟨C, h₁', hC⟩, ⟨C, h₂', hC⟩⟩
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqOr] at heq
  · rcases hexs with ⟨r, _, heq, _⟩
    simp [qqAnd, qqExs] at heq
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqAnd, qqAll] at heq

/-- Add a disjunction root selecting the left certificate. -/
theorem sigmaTrue_succ_or_intro_left {n : ℕ} {bound free p q : V}
    (hp : SigmaTrue (n + 1) bound free p)
    (hq : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) q) :
    SigmaTrue (n + 1) bound free (p ^⋎ q) := by
  rcases hp with ⟨C, hpC, hC⟩
  let root : V := truthRecord bound free (p ^⋎ q) 0
  let D : V := insert root C
  have hCD : C ⊆ D := by
    intro x hx
    simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdp := SigmaTrue.domain_succ
          (show SigmaTrue (n + 1) bound free p from ⟨C, hpC, hC⟩)
      have hdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1))
          (recordFormula root) := by
        simp only [root, recordFormula_truthRecord]
        exact (isSigmaCode_or_iff hdp.1 hq.1).2 ⟨hdp, hq⟩
      refine ⟨hdom, Or.inr <| Or.inr <| Or.inl
        ⟨p, ?_, q, ?_, by simp [root],
          Or.inl (by simpa [root] using HasTruthState.mono hCD hpC)⟩⟩
      · simp [root]
      · simp [root]
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- Add a disjunction root selecting the right certificate. -/
theorem sigmaTrue_succ_or_intro_right {n : ℕ} {bound free p q : V}
    (hp : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) p)
    (hq : SigmaTrue (n + 1) bound free q) :
    SigmaTrue (n + 1) bound free (p ^⋎ q) := by
  rcases hq with ⟨C, hqC, hC⟩
  let root : V := truthRecord bound free (p ^⋎ q) 0
  let D : V := insert root C
  have hCD : C ⊆ D := by
    intro x hx
    simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdq := SigmaTrue.domain_succ
          (show SigmaTrue (n + 1) bound free q from ⟨C, hqC, hC⟩)
      have hdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1))
          (recordFormula root) := by
        simp only [root, recordFormula_truthRecord]
        exact (isSigmaCode_or_iff hp.1 hdq.1).2 ⟨hp, hdq⟩
      refine ⟨hdom, Or.inr <| Or.inr <| Or.inl
        ⟨p, ?_, q, ?_, by simp [root],
          Or.inr (by simpa [root] using HasTruthState.mono hCD hqC)⟩⟩
      · simp [root]
      · simp [root]
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- A valid disjunction root contains a certificate for one of its children.

The quantifier-free leaf case is handled by the rank-zero Tarski clause;
otherwise constructor injectivity identifies the selected child state in the
same (possibly nonstandard) HFS certificate.
-/
theorem sigmaTrue_succ_or_elim {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : SigmaTrue (n + 1) bound free (p ^⋎ q)) :
    SigmaTrue (n + 1) bound free p ∨
      SigmaTrue (n + 1) bound free q := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (p ^⋎ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · have hqf' : QFTrue bound free (p ^⋎ q) := by simpa using hqf
    have hparts := (isQuantifierFreeCode_or_iff hp hq).mp hqf'.1
    rcases (qfTrue_or_iff hp hq hparts.1 hparts.2).mp
        hqf' with htrue | htrue
    · exact Or.inl (sigmaTrue_succ_of_qfTrue htrue)
    · exact Or.inr (sigmaTrue_succ_of_qfTrue htrue)
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqOr] at heq
  · rcases hor with ⟨p₁, hp₁, p₂, hp₂, heq, hchild⟩
    have heq' : p = p₁ ∧ q = p₂ := by
      apply (qqOr_inj p q p₁ p₂).mp
      simpa using heq
    rcases heq' with ⟨rfl, rfl⟩
    rcases hchild with h₁ | h₂
    · have h₁' : HasTruthState C bound free p := by simpa using h₁
      exact Or.inl ⟨C, h₁', hC⟩
    · have h₂' : HasTruthState C bound free q := by simpa using h₂
      exact Or.inr ⟨C, h₂', hC⟩
  · rcases hexs with ⟨r, _, heq, _⟩
    simp [qqOr, qqExs] at heq
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqOr, qqAll] at heq

/-- Add an existential root whose record stores the chosen witness. -/
theorem sigmaTrue_succ_exs_intro {n : ℕ} {bound free q a : V}
    (hq : SigmaTrue (n + 1) (bound ⁀' a) free q) :
    SigmaTrue (n + 1) bound free (^∃ q) := by
  rcases hq with ⟨C, hqC, hC⟩
  let root : V := truthRecord bound free (^∃ q) a
  let D : V := insert root C
  have hCD : C ⊆ D := by
    intro x hx
    simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨a, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdq := SigmaTrue.domain_succ
          (show SigmaTrue (n + 1) (bound ⁀' a) free q from
            ⟨C, hqC, hC⟩)
      have hdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1))
          (recordFormula root) := by
        simp only [root, recordFormula_truthRecord]
        exact (isSigmaCode_exs_iff hdq.1).2
          ⟨hdq, pos_iff_one_le.mp <| by
            simpa [levelCode] using
              (numeral_lt_of_lt (M := V) (n := 0) (m := n + 1)
                (Nat.zero_lt_succ n))⟩
      refine ⟨hdom, Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨q, ?_, by simp [root], ?_⟩⟩
      · simp [root]
      · simpa [root] using HasTruthState.mono hCD hqC
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- Read the stored witness and child certificate from an existential root. -/
theorem sigmaTrue_succ_exs_elim {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q)
    (h : SigmaTrue (n + 1) bound free (^∃ q)) :
    ∃ a, SigmaTrue (n + 1) (bound ⁀' a) free q := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (^∃ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · have hqf' : QFTrue bound free (^∃ q) := by simpa using hqf
    exact (not_isQuantifierFreeCode_exs hq hqf'.1).elim
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqExs] at heq
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqOr, qqExs] at heq
  · rcases hexs with ⟨q', hq', heq, hchild⟩
    have heq' : q = q' := by
      apply (qqExs_inj q q').mp
      simpa using heq
    subst q'
    have hchild' : HasTruthState C (bound ⁀' w) free q := by
      simpa using hchild
    exact ⟨w, ⟨C, hchild', hC⟩⟩
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqAll, qqExs] at heq

/-! ## Successor-level positive Tarski clauses -/

theorem sigmaTrue_succ_and_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (p ^⋏ q) ↔
      SigmaTrue (n + 1) bound free p ∧
        SigmaTrue (n + 1) bound free q :=
  ⟨sigmaTrue_succ_and_elim hp hq,
    fun h ↦ sigmaTrue_succ_and_intro h.1 h.2⟩

theorem sigmaTrue_succ_or_iff {n : ℕ} {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hpdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) p)
    (hqdom : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) q) :
    SigmaTrue (n + 1) bound free (p ^⋎ q) ↔
      SigmaTrue (n + 1) bound free p ∨
        SigmaTrue (n + 1) bound free q := by
  constructor
  · exact sigmaTrue_succ_or_elim hp hq
  · rintro (h | h)
    · exact sigmaTrue_succ_or_intro_left h hqdom
    · exact sigmaTrue_succ_or_intro_right hpdom h

theorem sigmaTrue_succ_exs_iff {n : ℕ} {bound free q : V}
    (hq : IsUFormula ℒₒᵣ q) :
    SigmaTrue (n + 1) bound free (^∃ q) ↔
      ∃ a, SigmaTrue (n + 1) (bound ⁀' a) free q :=
  ⟨sigmaTrue_succ_exs_elim hq,
    fun h ↦ by rcases h with ⟨a, ha⟩; exact sigmaTrue_succ_exs_intro ha⟩

end LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate
