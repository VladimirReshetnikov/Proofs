import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
import BoundedPAConsistency.ModelCodedStrongInduction

/-!
# Fixed-source strong step for dynamic cross-level coherence

The earlier two-predicate successor interface deliberately left its current
predicate arbitrary.  That interface is too weak: prior coherence does not
force an unrelated relation to have the Tarski clauses of the represented
truth successor.  The source context below therefore records the missing
literal fact that the current placeholder is the successor constructed from
the predecessor placeholder.  At production specialization this fact becomes
reflexivity by `successorTruthFormula_predecessor_eq`.

The mathematical proof is a strong step on the numeric formula code.  Every
proper child code is smaller than its constructor code, so the prefix
hypothesis supplies the two cross-level equivalences for the children.  The
certificate operations below are parameterized by an arbitrary lower
relation and arbitrary model levels; no source predicate is interpreted
semantically and no model element is decoded as standard syntax.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource

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
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-! ## Generic semantics of one represented successor -/

section GenericSuccessor

variable {M : Type*} [ORingStructure M]
variable [M↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Semantic contract of `successorTruthFormula`, separated from any
external natural-number index. -/
def SuccessorTruth
    (lower : M → M → M → Prop)
    (lowerLevel upperLevel bound free p : M) : Prop :=
  ∃ C,
    HasTruthState C bound free p ∧
      ∀ r ∈ C, SigmaRecordValid lower lowerLevel upperLevel C r

/-- Every accepted successor certificate advertises the upper oriented
domain at its root. -/
theorem SuccessorTruth.domain
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p : M}
    (h : SuccessorTruth lower lowerLevel upperLevel bound free p) :
    IsSigmaCode ℒₒᵣ upperLevel p := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hvalid⟩
  have hr := hvalid (truthRecord bound free p w) hroot
  simpa using hr.domain

/-- A true quantifier-free formula has a one-record successor certificate at
every upper level. -/
theorem SuccessorTruth.of_qfTrue
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p : M}
    (h : QFTrue bound free p) :
    SuccessorTruth lower lowerLevel upperLevel bound free p := by
  let r : M := truthRecord bound free p 0
  let C : M := insert r ∅
  have hr : r ∈ C := by simp [C]
  refine ⟨C, ⟨0, ?_, hr⟩, ?_⟩
  · simpa [r, truthRecord] using (lt_of_mem_rng hr)
  · intro r' hr'
    have hrr : r' = r := by simpa [C] using hr'
    subst r'
    have hqf := isQuantifierFreeCode_iff.mp h.1
    constructor
    · simp only [r, recordFormula_truthRecord]
      exact ⟨hqf.1, by simp [hqf.2.1]⟩
    · exact Or.inl (by simpa [r] using h)

/-- Join two certificates and add a conjunction root. -/
theorem SuccessorTruth.and_intro
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : SuccessorTruth lower lowerLevel upperLevel bound free p)
    (hq : SuccessorTruth lower lowerLevel upperLevel bound free q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋏ q) := by
  rcases hp with ⟨C₁, hpC₁, hC₁⟩
  rcases hq with ⟨C₂, hqC₂, hC₂⟩
  let root : M := truthRecord bound free (p ^⋏ q) 0
  let D : M := insert root (C₁ ∪ C₂)
  have hC₁D : C₁ ⊆ D := by intro x hx; simp [D, hx]
  have hC₂D : C₂ ⊆ D := by intro x hx; simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr₁ | hr₂)
    · have hdp := SuccessorTruth.domain
          (show SuccessorTruth lower lowerLevel upperLevel bound free p from
            ⟨C₁, hpC₁, hC₁⟩)
      have hdq := SuccessorTruth.domain
          (show SuccessorTruth lower lowerLevel upperLevel bound free q from
            ⟨C₂, hqC₂, hC₂⟩)
      constructor
      · simpa [root] using
          (isSigmaCode_and_iff hdp.1 hdq.1).2 ⟨hdp, hdq⟩
      · exact Or.inr <| Or.inl
          ⟨p, by simp [root], q, by simp [root], by simp [root],
            by simpa [root] using HasTruthState.mono hC₁D hpC₁,
            by simpa [root] using HasTruthState.mono hC₂D hqC₂⟩
    · exact SigmaRecordValid.mono hC₁D (hC₁ r hr₁)
    · exact SigmaRecordValid.mono hC₂D (hC₂ r hr₂)

/-- Read both child certificates from a conjunction root. -/
theorem SuccessorTruth.and_elim
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋏ q)) :
    SuccessorTruth lower lowerLevel upperLevel bound free p ∧
      SuccessorTruth lower lowerLevel upperLevel bound free q := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (p ^⋏ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · have hparts := (qfTrue_and_iff hp hq).mp (by simpa using hqf)
    exact ⟨SuccessorTruth.of_qfTrue hparts.1,
      SuccessorTruth.of_qfTrue hparts.2⟩
  · rcases hand with ⟨p₁, hp₁, p₂, hp₂, heq, h₁, h₂⟩
    have heq' : p = p₁ ∧ q = p₂ := by
      apply (qqAnd_inj p q p₁ p₂).mp
      simpa using heq
    rcases heq' with ⟨rfl, rfl⟩
    exact ⟨⟨C, by simpa using h₁, hC⟩,
      ⟨C, by simpa using h₂, hC⟩⟩
  · rcases hor with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqOr] at heq
  · rcases hexs with ⟨r, _, heq, _⟩
    simp [qqAnd, qqExs] at heq
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqAnd, qqAll] at heq

@[simp] theorem SuccessorTruth.and_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋏ q) ↔
      SuccessorTruth lower lowerLevel upperLevel bound free p ∧
        SuccessorTruth lower lowerLevel upperLevel bound free q :=
  ⟨SuccessorTruth.and_elim hp hq, fun h ↦
    SuccessorTruth.and_intro h.1 h.2⟩

/-- Add a disjunction root selecting the left certificate. -/
theorem SuccessorTruth.or_intro_left
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : SuccessorTruth lower lowerLevel upperLevel bound free p)
    (hq : IsSigmaCode ℒₒᵣ upperLevel q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋎ q) := by
  rcases hp with ⟨C, hpC, hC⟩
  let root : M := truthRecord bound free (p ^⋎ q) 0
  let D : M := insert root C
  have hCD : C ⊆ D := by intro x hx; simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdp := SuccessorTruth.domain
          (show SuccessorTruth lower lowerLevel upperLevel bound free p from
            ⟨C, hpC, hC⟩)
      constructor
      · simpa [root] using
          (isSigmaCode_or_iff hdp.1 hq.1).2 ⟨hdp, hq⟩
      · exact Or.inr <| Or.inr <| Or.inl
          ⟨p, by simp [root], q, by simp [root], by simp [root],
            Or.inl (by simpa [root] using HasTruthState.mono hCD hpC)⟩
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- Add a disjunction root selecting the right certificate. -/
theorem SuccessorTruth.or_intro_right
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsSigmaCode ℒₒᵣ upperLevel p)
    (hq : SuccessorTruth lower lowerLevel upperLevel bound free q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋎ q) := by
  rcases hq with ⟨C, hqC, hC⟩
  let root : M := truthRecord bound free (p ^⋎ q) 0
  let D : M := insert root C
  have hCD : C ⊆ D := by intro x hx; simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdq := SuccessorTruth.domain
          (show SuccessorTruth lower lowerLevel upperLevel bound free q from
            ⟨C, hqC, hC⟩)
      constructor
      · simpa [root] using
          (isSigmaCode_or_iff hp.1 hdq.1).2 ⟨hp, hdq⟩
      · exact Or.inr <| Or.inr <| Or.inl
          ⟨p, by simp [root], q, by simp [root], by simp [root],
            Or.inr (by simpa [root] using HasTruthState.mono hCD hqC)⟩
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- Read the selected child certificate from a disjunction root. -/
theorem SuccessorTruth.or_elim
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋎ q)) :
    SuccessorTruth lower lowerLevel upperLevel bound free p ∨
      SuccessorTruth lower lowerLevel upperLevel bound free q := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (p ^⋎ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · have hqf' : QFTrue bound free (p ^⋎ q) := by simpa using hqf
    have hparts := (isQuantifierFreeCode_or_iff hp hq).mp hqf'.1
    rcases (qfTrue_or_iff hp hq hparts.1 hparts.2).mp hqf' with
        htrue | htrue
    · exact Or.inl (SuccessorTruth.of_qfTrue htrue)
    · exact Or.inr (SuccessorTruth.of_qfTrue htrue)
  · rcases hand with ⟨p₁, _, p₂, _, heq, _⟩
    simp [qqAnd, qqOr] at heq
  · rcases hor with ⟨p₁, hp₁, p₂, hp₂, heq, hchild⟩
    have heq' : p = p₁ ∧ q = p₂ := by
      apply (qqOr_inj p q p₁ p₂).mp
      simpa using heq
    rcases heq' with ⟨rfl, rfl⟩
    rcases hchild with h₁ | h₂
    · exact Or.inl ⟨C, by simpa using h₁, hC⟩
    · exact Or.inr ⟨C, by simpa using h₂, hC⟩
  · rcases hexs with ⟨r, _, heq, _⟩
    simp [qqOr, qqExs] at heq
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqOr, qqAll] at heq

@[simp] theorem SuccessorTruth.or_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hpdom : IsSigmaCode ℒₒᵣ upperLevel p)
    (hqdom : IsSigmaCode ℒₒᵣ upperLevel q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (p ^⋎ q) ↔
      SuccessorTruth lower lowerLevel upperLevel bound free p ∨
        SuccessorTruth lower lowerLevel upperLevel bound free q := by
  constructor
  · exact SuccessorTruth.or_elim hp hq
  · rintro (h | h)
    · exact SuccessorTruth.or_intro_left h hqdom
    · exact SuccessorTruth.or_intro_right hpdom h

/-- Add an existential root carrying the chosen witness. -/
theorem SuccessorTruth.exs_intro
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q a : M}
    (hpositive : (1 : M) ≤ upperLevel)
    (hq : SuccessorTruth lower lowerLevel upperLevel
      (bound ⁀' a) free q) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∃ q) := by
  rcases hq with ⟨C, hqC, hC⟩
  let root : M := truthRecord bound free (^∃ q) a
  let D : M := insert root C
  have hCD : C ⊆ D := by intro x hx; simp [D, hx]
  have hroot : root ∈ D := by simp [D]
  refine ⟨D, ⟨a, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    rcases (by simpa [D] using hr) with (rfl | hr)
    · have hdq := SuccessorTruth.domain
          (show SuccessorTruth lower lowerLevel upperLevel
              (bound ⁀' a) free q from ⟨C, hqC, hC⟩)
      constructor
      · simpa [root] using
          (isSigmaCode_exs_iff hdq.1).2 ⟨hdq, hpositive⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨q, by simp [root], by simp [root],
            by simpa [root] using HasTruthState.mono hCD hqC⟩
    · exact SigmaRecordValid.mono hCD (hC r hr)

/-- Read the existential witness and its child certificate. -/
theorem SuccessorTruth.exs_elim
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (h : SuccessorTruth lower lowerLevel upperLevel bound free (^∃ q)) :
    ∃ a, SuccessorTruth lower lowerLevel upperLevel
      (bound ⁀' a) free q := by
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
    exact ⟨w, ⟨C, by simpa using hchild, hC⟩⟩
  · rcases hall with ⟨r, _, heq, _⟩
    simp [qqAll, qqExs] at heq

@[simp] theorem SuccessorTruth.exs_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q) (hpositive : (1 : M) ≤ upperLevel) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∃ q) ↔
      ∃ a, SuccessorTruth lower lowerLevel upperLevel
        (bound ⁀' a) free q :=
  ⟨SuccessorTruth.exs_elim hq,
    fun ⟨a, ha⟩ ↦ SuccessorTruth.exs_intro hpositive ha⟩

/-- A universal root of a successor certificate stores precisely the lower
Pi presentation. -/
theorem SuccessorTruth.all_elim
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (h : SuccessorTruth lower lowerLevel upperLevel bound free (^∀ q)) :
    LowerPiTrue lower lowerLevel bound free (^∀ q) := by
  rcases h with ⟨C, ⟨w, hw, hroot⟩, hC⟩
  have hv := hC (truthRecord bound free (^∀ q) w) hroot
  rcases hv.2 with (hqf | hand | hor | hexs | hall)
  · exact (not_isQuantifierFreeCode_all hq
      (by simpa using hqf.1)).elim
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

/-- Build the one-record successor certificate for a lower-Pi universal
leaf. -/
theorem SuccessorTruth.all_intro
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (hlevels : upperLevel = lowerLevel + 1)
    (h : LowerPiTrue lower lowerLevel bound free (^∀ q)) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∀ q) := by
  let root : M := truthRecord bound free (^∀ q) 0
  let C : M := insert root ∅
  have hroot : root ∈ C := by simp [C]
  have hlower := (isPiCode_all_iff hq).mp h.1
  have hdom : IsSigmaCode ℒₒᵣ upperLevel (^∀ q) := by
    rw [hlevels]
    exact (isSigmaCode_all_succ_iff (n := lowerLevel) hq).mpr hlower
  refine ⟨C, ⟨0, ?_, hroot⟩, ?_⟩
  · simpa [root, truthRecord] using (lt_of_mem_rng hroot)
  · intro r hr
    have hrr : r = root := by simpa [C] using hr
    subst r
    constructor
    · simpa [root] using hdom
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
        ⟨q, by simp [root], by simp [root], by simpa [root] using h⟩

@[simp] theorem SuccessorTruth.all_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (hlevels : upperLevel = lowerLevel + 1) :
    SuccessorTruth lower lowerLevel upperLevel bound free (^∀ q) ↔
      LowerPiTrue lower lowerLevel bound free (^∀ q) :=
  ⟨SuccessorTruth.all_elim hq,
    SuccessorTruth.all_intro hq hlevels⟩

/-- Atomic relation certificates can only use the quantifier-free branch. -/
theorem SuccessorTruth.rel_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free k R terms : M}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    SuccessorTruth lower lowerLevel upperLevel bound free
        (^rel k R terms) ↔
      QFTrue bound free (^rel k R terms) := by
  constructor
  · rintro ⟨C, ⟨w, hw, hroot⟩, hC⟩
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
  · exact SuccessorTruth.of_qfTrue

/-- Negated atomic relation certificates are likewise quantifier-free. -/
theorem SuccessorTruth.nrel_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free k R terms : M}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    SuccessorTruth lower lowerLevel upperLevel bound free
        (^nrel k R terms) ↔
      QFTrue bound free (^nrel k R terms) := by
  constructor
  · rintro ⟨C, ⟨w, hw, hroot⟩, hC⟩
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
  · exact SuccessorTruth.of_qfTrue

/-- The two nullary Boolean constants also reduce to the canonical
quantifier-free evaluator. -/
theorem SuccessorTruth.verum_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free : M} :
    SuccessorTruth lower lowerLevel upperLevel bound free ^⊤ ↔
      QFTrue bound free ^⊤ := by
  constructor
  · rintro ⟨C, ⟨w, hw, hroot⟩, hC⟩
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
  · exact SuccessorTruth.of_qfTrue

theorem SuccessorTruth.falsum_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free : M} :
    SuccessorTruth lower lowerLevel upperLevel bound free ^⊥ ↔
      QFTrue bound free ^⊥ := by
  constructor
  · rintro ⟨C, ⟨w, hw, hroot⟩, hC⟩
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
  · exact SuccessorTruth.of_qfTrue

/-- Pi presentation paired with one generic successor certificate. -/
def SuccessorPiTruth
    (lower : M → M → M → Prop)
    (lowerLevel upperLevel bound free p : M) : Prop :=
  LowerPiTrue
    (SuccessorTruth lower lowerLevel upperLevel)
    upperLevel bound free p

@[simp] theorem SuccessorPiTruth.and_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free (p ^⋏ q) ↔
      SuccessorPiTruth lower lowerLevel upperLevel bound free p ∧
        SuccessorPiTruth lower lowerLevel upperLevel bound free q := by
  constructor
  · rintro ⟨hdom, hnot⟩
    have hparts := (isPiCode_and_iff hp hq).mp hdom
    have hsnegp : IsSigmaCode ℒₒᵣ upperLevel (neg ℒₒᵣ p) :=
      (isSigmaCode_neg_iff hp).mpr hparts.1
    have hsnegq : IsSigmaCode ℒₒᵣ upperLevel (neg ℒₒᵣ q) :=
      (isSigmaCode_neg_iff hq).mpr hparts.2
    rw [neg_and hp hq,
      SuccessorTruth.or_iff hp.neg hq.neg hsnegp hsnegq] at hnot
    exact ⟨⟨hparts.1, fun h ↦ hnot (Or.inl h)⟩,
      ⟨hparts.2, fun h ↦ hnot (Or.inr h)⟩⟩
  · rintro ⟨⟨hdp, hnp⟩, ⟨hdq, hnq⟩⟩
    refine ⟨(isPiCode_and_iff hp hq).mpr ⟨hdp, hdq⟩, ?_⟩
    have hsnegp := (isSigmaCode_neg_iff hp).mpr hdp
    have hsnegq := (isSigmaCode_neg_iff hq).mpr hdq
    rw [neg_and hp hq,
      SuccessorTruth.or_iff hp.neg hq.neg hsnegp hsnegq]
    tauto

@[simp] theorem SuccessorPiTruth.or_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p q : M}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hpdom : IsPiCode ℒₒᵣ upperLevel p)
    (hqdom : IsPiCode ℒₒᵣ upperLevel q) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free (p ^⋎ q) ↔
      SuccessorPiTruth lower lowerLevel upperLevel bound free p ∨
        SuccessorPiTruth lower lowerLevel upperLevel bound free q := by
  constructor
  · rintro ⟨hdom, hnot⟩
    have hparts := (isPiCode_or_iff hp hq).mp hdom
    rw [neg_or hp hq, SuccessorTruth.and_iff hp.neg hq.neg] at hnot
    rcases not_and_or.mp hnot with hnp | hnq
    · exact Or.inl ⟨hparts.1, hnp⟩
    · exact Or.inr ⟨hparts.2, hnq⟩
  · rintro ( ⟨hdp, hnp⟩ | ⟨hdq, hnq⟩ )
    · exact ⟨(isPiCode_or_iff hp hq).mpr ⟨hdp, hqdom⟩, by
        rw [neg_or hp hq, SuccessorTruth.and_iff hp.neg hq.neg]
        exact fun h ↦ hnp h.1⟩
    · exact ⟨(isPiCode_or_iff hp hq).mpr ⟨hpdom, hdq⟩, by
        rw [neg_or hp hq, SuccessorTruth.and_iff hp.neg hq.neg]
        exact fun h ↦ hnq h.2⟩

/-- At an existential head, the Pi presentation of one successor reduces to
the lower Sigma relation, provided the lower oriented domain is known. -/
theorem SuccessorPiTruth.exs_iff_lower
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free q : M}
    (hq : IsUFormula ℒₒᵣ q)
    (hlevels : upperLevel = lowerLevel + 1)
    (hlowerDomain : IsSigmaCode ℒₒᵣ lowerLevel (^∃ q)) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free (^∃ q) ↔
      lower bound free (^∃ q) := by
  have hparts := (isSigmaCode_exs_iff hq).mp hlowerDomain
  have hnqdom : IsPiCode ℒₒᵣ lowerLevel (neg ℒₒᵣ q) :=
    (isPiCode_neg_iff hq).mpr hparts.1
  have halldom : IsPiCode ℒₒᵣ lowerLevel (^∀ (neg ℒₒᵣ q)) :=
    (isPiCode_all_iff hq.neg).mpr ⟨hnqdom, hparts.2⟩
  have hupperDomain : IsPiCode ℒₒᵣ upperLevel (^∃ q) := by
    rw [hlevels]
    exact (isPiCode_exs_succ_iff (n := lowerLevel) hq).mpr hparts
  rw [SuccessorPiTruth, LowerPiTrue, and_iff_right hupperDomain,
    neg_ex hq, SuccessorTruth.all_iff hq.neg hlevels,
    LowerPiTrue, and_iff_right halldom]
  rw [neg_all hq.neg, hq.neg_neg]
  exact not_not

/-- Quantifier-free formulas have the expected Pi presentation whenever the
successor predicate has the expected value on their represented negation.
This small factoring keeps the four atomic constructor cases below honest:
it does not assume a global quantifier-free Tarski theorem for an arbitrary
successor relation. -/
theorem SuccessorPiTruth.qf_iff_of_neg
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free p : M}
    (hp : IsQuantifierFreeCode p)
    (hneg : SuccessorTruth lower lowerLevel upperLevel bound free
        (neg ℒₒᵣ p) ↔ QFTrue bound free (neg ℒₒᵣ p)) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free p ↔
      QFTrue bound free p := by
  have hr := isQuantifierFreeCode_iff.mp hp
  have hpPi : IsPiCode ℒₒᵣ upperLevel p :=
    ⟨hp.1, by simp [hr.2.2]⟩
  rw [SuccessorPiTruth, LowerPiTrue, and_iff_right hpPi, hneg,
    qfTrue_neg_iff hp, qfTrue_iff_not_qfFalse hp]

@[simp] theorem SuccessorPiTruth.rel_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free k R terms : M}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free
        (^rel k R terms) ↔
      QFTrue bound free (^rel k R terms) := by
  apply SuccessorPiTruth.qf_iff_of_neg
      (by simp [IsQuantifierFreeCode, hR, hterms])
  rw [neg_rel hR hterms, SuccessorTruth.nrel_iff hR hterms]

@[simp] theorem SuccessorPiTruth.nrel_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free k R terms : M}
    (hR : (ℒₒᵣ).IsRel k R) (hterms : IsUTermVec ℒₒᵣ k terms) :
    SuccessorPiTruth lower lowerLevel upperLevel bound free
        (^nrel k R terms) ↔
      QFTrue bound free (^nrel k R terms) := by
  apply SuccessorPiTruth.qf_iff_of_neg
      (by simp [IsQuantifierFreeCode, hR, hterms])
  rw [neg_nrel hR hterms, SuccessorTruth.rel_iff hR hterms]

@[simp] theorem SuccessorPiTruth.verum_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free : M} :
    SuccessorPiTruth lower lowerLevel upperLevel bound free ^⊤ ↔
      QFTrue bound free ^⊤ := by
  apply SuccessorPiTruth.qf_iff_of_neg (by simp [IsQuantifierFreeCode])
  rw [neg_verum, SuccessorTruth.falsum_iff]

@[simp] theorem SuccessorPiTruth.falsum_iff
    {lower : M → M → M → Prop}
    {lowerLevel upperLevel bound free : M} :
    SuccessorPiTruth lower lowerLevel upperLevel bound free ^⊥ ↔
      QFTrue bound free ^⊥ := by
  apply SuccessorPiTruth.qf_iff_of_neg (by simp [IsQuantifierFreeCode])
  rw [neg_falsum, SuccessorTruth.verum_iff]

/-! ## The genuine strong step -/

/-- The already established cross-level laws between an arbitrary lower
relation and the current relation. -/
def PriorCrossLaws
    (lower current : M → M → M → Prop)
    (lowerLevel : M) (p : M) : Prop :=
  ∀ bound free,
    (IsSigmaCode ℒₒᵣ lowerLevel p →
      (current bound free p ↔ lower bound free p)) ∧
    (IsPiCode ℒₒᵣ lowerLevel p →
      (current bound free p ↔
        LowerPiTrue lower lowerLevel bound free p))

/-- The next cross-level laws whose universal closure is the requested
successor field. -/
def SuccessorCrossLaws
    (current : M → M → M → Prop)
    (currentLevel nextLevel : M) (p : M) : Prop :=
  ∀ bound free,
    (IsSigmaCode ℒₒᵣ currentLevel p →
      (SuccessorTruth current currentLevel nextLevel bound free p ↔
        current bound free p)) ∧
    (IsPiCode ℒₒᵣ currentLevel p →
      (SuccessorTruth current currentLevel nextLevel bound free p ↔
        LowerPiTrue current currentLevel bound free p))

/-- The Pi presentation of the represented current successor is stable if
the prior Sigma law is known for the represented negation code. -/
theorem successorPi_stable_of_prior_neg
    {lower : M → M → M → Prop}
    {lowerLevel currentLevel bound free p : M}
    (hlevels : currentLevel = lowerLevel + 1)
    (hp : IsPiCode ℒₒᵣ lowerLevel p)
    (hprior : PriorCrossLaws lower
      (SuccessorTruth lower lowerLevel currentLevel)
      lowerLevel (neg ℒₒᵣ p)) :
    SuccessorPiTruth lower lowerLevel currentLevel bound free p ↔
      LowerPiTrue lower lowerLevel bound free p := by
  have hpCurrent : IsPiCode ℒₒᵣ currentLevel p := by
    rw [hlevels]
    exact hp.mono (by simp)
  have hnSigma : IsSigmaCode ℒₒᵣ lowerLevel (neg ℒₒᵣ p) :=
    (isSigmaCode_neg_iff hp.1).mpr hp
  have hstable := (hprior bound free).1 hnSigma
  rw [SuccessorPiTruth, LowerPiTrue, and_iff_right hpCurrent,
    LowerPiTrue, and_iff_right hp]
  exact not_congr hstable

/-- One represented strong-induction step.  The `currentDefinition` premise
is the crucial hypothesis absent from the old two-arbitrary-predicate
interface.  The quantifier-free premise is also consumed literally in every
atomic introduction into the next successor relation. -/
theorem successorCrossLaws_strongStep
    {lower current : M → M → M → Prop}
    {lowerLevel currentLevel nextLevel p : M}
    (hcurrentLevel : currentLevel = lowerLevel + 1)
    (hnextLevel : nextLevel = currentLevel + 1)
    (hprior : ∀ q, PriorCrossLaws lower current lowerLevel q)
    (hcurrentDefinition : ∀ bound free q,
      current bound free q ↔
        SuccessorTruth lower lowerLevel currentLevel bound free q)
    (hnextQF : ∀ bound free q, QFTrue bound free q →
      SuccessorTruth current currentLevel nextLevel bound free q)
    (hprefix : ∀ q, q < p →
      SuccessorCrossLaws current currentLevel nextLevel q) :
    SuccessorCrossLaws current currentLevel nextLevel p := by
  have hcurrentEq : current =
      SuccessorTruth lower lowerLevel currentLevel := by
    funext bound free q
    exact propext (hcurrentDefinition bound free q)
  subst current
  by_cases hp : IsUFormula ℒₒᵣ p
  · rcases hp.case with
      (⟨k, R, terms, hR, hterms, hcode⟩ |
       ⟨k, R, terms, hR, hterms, hcode⟩ |
       hcode | hcode | ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, r, hq, hr, hcode⟩ |
       ⟨q, hq, hcode⟩ | ⟨q, hq, hcode⟩)
    · subst p
      intro bound free
      constructor
      · intro _hdom
        constructor
        · intro hnext
          exact (SuccessorTruth.rel_iff hR hterms).mpr
            ((SuccessorTruth.rel_iff hR hterms).mp hnext)
        · intro hcurrent
          exact hnextQF bound free _
            ((SuccessorTruth.rel_iff hR hterms).mp hcurrent)
      · intro _hdom
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free (^rel k R terms) ↔
          SuccessorPiTruth lower lowerLevel currentLevel
            bound free (^rel k R terms)
        rw [SuccessorPiTruth.rel_iff hR hterms]
        constructor
        · exact (SuccessorTruth.rel_iff hR hterms).mp
        · exact hnextQF bound free _
    · subst p
      intro bound free
      constructor
      · intro _hdom
        constructor
        · intro hnext
          exact (SuccessorTruth.nrel_iff hR hterms).mpr
            ((SuccessorTruth.nrel_iff hR hterms).mp hnext)
        · intro hcurrent
          exact hnextQF bound free _
            ((SuccessorTruth.nrel_iff hR hterms).mp hcurrent)
      · intro _hdom
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free (^nrel k R terms) ↔
          SuccessorPiTruth lower lowerLevel currentLevel
            bound free (^nrel k R terms)
        rw [SuccessorPiTruth.nrel_iff hR hterms]
        constructor
        · exact (SuccessorTruth.nrel_iff hR hterms).mp
        · exact hnextQF bound free _
    · subst p
      intro bound free
      constructor
      · intro _hdom
        constructor
        · intro hnext
          exact SuccessorTruth.verum_iff.mpr
            (SuccessorTruth.verum_iff.mp hnext)
        · intro hcurrent
          exact hnextQF bound free _
            (SuccessorTruth.verum_iff.mp hcurrent)
      · intro _hdom
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free ^⊤ ↔
          SuccessorPiTruth lower lowerLevel currentLevel bound free ^⊤
        rw [SuccessorPiTruth.verum_iff]
        constructor
        · exact SuccessorTruth.verum_iff.mp
        · exact hnextQF bound free _
    · subst p
      intro bound free
      constructor
      · intro _hdom
        constructor
        · intro hnext
          exact SuccessorTruth.falsum_iff.mpr
            (SuccessorTruth.falsum_iff.mp hnext)
        · intro hcurrent
          exact hnextQF bound free _
            (SuccessorTruth.falsum_iff.mp hcurrent)
      · intro _hdom
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free ^⊥ ↔
          SuccessorPiTruth lower lowerLevel currentLevel bound free ^⊥
        rw [SuccessorPiTruth.falsum_iff]
        constructor
        · exact SuccessorTruth.falsum_iff.mp
        · exact hnextQF bound free _
    · subst p
      have ihq := hprefix q (by simp)
      have ihr := hprefix r (by simp)
      intro bound free
      constructor
      · intro hs
        have hparts := (isSigmaCode_and_iff hq hr).mp hs
        simpa only [SuccessorTruth.and_iff hq hr] using
          and_congr ((ihq bound free).1 hparts.1)
            ((ihr bound free).1 hparts.2)
      · intro hpi
        have hparts := (isPiCode_and_iff hq hr).mp hpi
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free (q ^⋏ r) ↔
          SuccessorPiTruth lower lowerLevel currentLevel
            bound free (q ^⋏ r)
        rw [SuccessorTruth.and_iff hq hr,
          SuccessorPiTruth.and_iff hq hr]
        change
          (SuccessorTruth (SuccessorTruth lower lowerLevel currentLevel)
              currentLevel nextLevel bound free q ∧
            SuccessorTruth (SuccessorTruth lower lowerLevel currentLevel)
              currentLevel nextLevel bound free r) ↔
          (LowerPiTrue (SuccessorTruth lower lowerLevel currentLevel)
              currentLevel bound free q ∧
            LowerPiTrue (SuccessorTruth lower lowerLevel currentLevel)
              currentLevel bound free r)
        exact and_congr ((ihq bound free).2 hparts.1)
          ((ihr bound free).2 hparts.2)
    · subst p
      have ihq := hprefix q (by simp)
      have ihr := hprefix r (by simp)
      intro bound free
      constructor
      · intro hs
        have hparts := (isSigmaCode_or_iff hq hr).mp hs
        have hqNext : IsSigmaCode ℒₒᵣ nextLevel q := by
          rw [hnextLevel]
          exact hparts.1.mono (by simp)
        have hrNext : IsSigmaCode ℒₒᵣ nextLevel r := by
          rw [hnextLevel]
          exact hparts.2.mono (by simp)
        rw [SuccessorTruth.or_iff hq hr hqNext hrNext,
          SuccessorTruth.or_iff hq hr hparts.1 hparts.2]
        exact or_congr ((ihq bound free).1 hparts.1)
          ((ihr bound free).1 hparts.2)
      · intro hpi
        have hparts := (isPiCode_or_iff hq hr).mp hpi
        have hqNext : IsSigmaCode ℒₒᵣ nextLevel q := by
          rw [hnextLevel]
          exact hparts.1.toSigmaSucc
        have hrNext : IsSigmaCode ℒₒᵣ nextLevel r := by
          rw [hnextLevel]
          exact hparts.2.toSigmaSucc
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free (q ^⋎ r) ↔
          SuccessorPiTruth lower lowerLevel currentLevel
            bound free (q ^⋎ r)
        rw [SuccessorTruth.or_iff hq hr hqNext hrNext,
          SuccessorPiTruth.or_iff hq hr hparts.1 hparts.2]
        exact or_congr ((ihq bound free).2 hparts.1)
          ((ihr bound free).2 hparts.2)
    · subst p
      intro bound free
      constructor
      · intro hs
        have hparts : IsPiCode ℒₒᵣ lowerLevel q ∧
            (1 : M) ≤ lowerLevel := by
          apply (isSigmaCode_all_succ_iff
            (n := lowerLevel) hq).mp
          simpa only [hcurrentLevel] using hs
        have hallPi : IsPiCode ℒₒᵣ lowerLevel (^∀ q) :=
          (isPiCode_all_iff hq).mpr hparts
        have hallU : IsUFormula ℒₒᵣ (^∀ q) := by simpa using hq
        rw [SuccessorTruth.all_iff hq hnextLevel,
          SuccessorTruth.all_iff hq hcurrentLevel]
        exact successorPi_stable_of_prior_neg hcurrentLevel hallPi
          (hprior (neg ℒₒᵣ (^∀ q)))
      · intro _hpi
        exact SuccessorTruth.all_iff hq hnextLevel
    · subst p
      have ihq := hprefix q (by simp)
      intro bound free
      constructor
      · intro hs
        have hqCurrent : IsSigmaCode ℒₒᵣ currentLevel q :=
          ((isSigmaCode_exs_iff hq).mp hs).1
        have hpositive := ((isSigmaCode_exs_iff hq).mp hs).2
        rw [SuccessorTruth.exs_iff hq (by
              rw [hnextLevel]
              exact le_trans hpositive (by simp)),
          SuccessorTruth.exs_iff hq hpositive]
        constructor
        · rintro ⟨a, ha⟩
          exact ⟨a, ((ihq (bound ⁀' a) free).1 hqCurrent).mp ha⟩
        · rintro ⟨a, ha⟩
          exact ⟨a, ((ihq (bound ⁀' a) free).1 hqCurrent).mpr ha⟩
      · intro hpi
        have hpi' : IsPiCode ℒₒᵣ (lowerLevel + 1) (^∃ q) := by
          simpa only [hcurrentLevel] using hpi
        have hparts :=
          (isPiCode_exs_succ_iff (n := lowerLevel) hq).mp hpi'
        have hqCurrent : IsSigmaCode ℒₒᵣ currentLevel q := by
          rw [hcurrentLevel]
          exact hparts.1.mono (by simp)
        have hqNext : IsSigmaCode ℒₒᵣ nextLevel q := by
          rw [hnextLevel]
          exact hqCurrent.mono (by simp)
        have hnextPositive : (1 : M) ≤ nextLevel := by
          rw [hnextLevel, hcurrentLevel]
          exact le_trans hparts.2 (by simp)
        have hcurrentPositive : (1 : M) ≤ currentLevel := by
          rw [hcurrentLevel]
          exact le_trans hparts.2 (by simp)
        have hexSigma : IsSigmaCode ℒₒᵣ lowerLevel (^∃ q) :=
          (isSigmaCode_exs_iff hq).mpr hparts
        change SuccessorTruth
            (SuccessorTruth lower lowerLevel currentLevel)
            currentLevel nextLevel bound free (^∃ q) ↔
          SuccessorPiTruth lower lowerLevel currentLevel
            bound free (^∃ q)
        rw [SuccessorTruth.exs_iff hq hnextPositive,
          SuccessorPiTruth.exs_iff_lower hq hcurrentLevel
            hexSigma,
          ← (hprior (^∃ q) bound free).1 hexSigma,
          SuccessorTruth.exs_iff hq hcurrentPositive]
        constructor
        · rintro ⟨a, ha⟩
          exact ⟨a, ((ihq (bound ⁀' a) free).1 hqCurrent).mp ha⟩
        · rintro ⟨a, ha⟩
          exact ⟨a, ((ihq (bound ⁀' a) free).1 hqCurrent).mpr ha⟩
  · intro bound free
    constructor
    · intro hs
      exact (hp hs.1).elim
    · intro hpi
      exact (hp hpi.1).elim

end GenericSuccessor

/-! ## Literal fixed-source statement -/

/-- The predecessor analogue of `sourceCurrentUniversalRecordBranch`.  It
is kept as source syntax so that the current-definition premise survives
template compilation rather than becoming a meta-level equality. -/
noncomputable def sourcePredecessorUniversalRecordBranch :
    Semisentence SourceLanguage 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    (liftArithmeticFormula universalRecordPrefixDef.val ⋏
      ∼(predecessorAtom (#4) (#3) (#0)))

noncomputable def sourcePredecessorSuccessorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      (levelTerm 1) (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ sourcePredecessorUniversalRecordBranch
        (levelTerm 0) (#0) (#1))

/-- The represented successor built from the predecessor placeholder. -/
noncomputable def sourcePredecessorSuccessorTruth :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ sourcePredecessorSuccessorRecordValid (#1) (#0))))

/-- Pointwise assertion that the otherwise arbitrary current placeholder is
exactly the represented successor of the predecessor placeholder. -/
noncomputable def sourceCurrentDefinitionBody :
    Semisentence SourceLanguage 3 :=
  currentAtom (#0) (#1) (#2) 🡘 sourcePredecessorSuccessorTruth

noncomputable def sourceCurrentDefinition : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceCurrentDefinitionBody

/-- The target-level positive quantifier-free constructor, copied literally
from the augmented local bundle. -/
noncomputable def sourceTargetQuantifierFreeIntroductionBody :
    Semisentence SourceLanguage 3 :=
  sourceQuantifierFreeTruth 🡒 sourceCurrentSuccessorTruth

noncomputable def sourceTargetQuantifierFreeIntroduction :
    Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceTargetQuantifierFreeIntroductionBody

/-- Arithmetic graph saying that the second argument is the successor of
the first. -/
noncomputable def sourceLevelSuccessorEquation
    (lower upper : Fin 3) : Sentence SourceLanguage :=
  .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
    ![levelTerm upper,
      .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
        ![levelTerm lower,
          .func (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![]]]

/-- Both named-level successor equations needed by the certificate
constructors.  They become reflexive arithmetic equalities at production
specialization. -/
noncomputable def sourceLevelEquations : Sentence SourceLanguage :=
  sourceLevelSuccessorEquation 0 1 ⋏
    sourceLevelSuccessorEquation 1 2

/-- Every premise used by the strong step is an ordinary source formula.
The association makes the two production projections visible: the previous
cross field is first, and the target quantifier-free anchor is second. -/
noncomputable def sourceStrongStepPremises : Sentence SourceLanguage :=
  ((sourcePriorCrossLevelContext ⋏
      sourceTargetQuantifierFreeIntroduction) ⋏
    sourceCurrentDefinition) ⋏ sourceLevelEquations

noncomputable def sourceStrongPrefixGuard :
    Semisentence SourceLanguage 2 :=
  .rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2))
    ![(#0 : ClosedSemiterm SourceLanguage 2),
      (#1 : ClosedSemiterm SourceLanguage 2)]

/-- `forall q < p, NextCrossLevel(q)` in the fixed source language. -/
noncomputable def sourceStrongPrefix : Semisentence SourceLanguage 1 :=
  ∀⁰[sourceStrongPrefixGuard]
    (sourceNextCrossLevelInvariant/[
      (#0 : ClosedSemiterm SourceLanguage 2)])

/-- The exact source theorem compiled into the generic represented
strong-induction adapter. -/
noncomputable def sourceStrongStepSentence : Sentence SourceLanguage :=
  Arrow.arrow sourceStrongStepPremises
    (∀⁰ Arrow.arrow sourceStrongPrefix
      sourceNextCrossLevelInvariant)

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
