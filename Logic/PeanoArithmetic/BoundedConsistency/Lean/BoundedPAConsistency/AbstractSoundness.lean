import BoundedPAConsistency.RestrictedConsistency
import BoundedPAConsistency.TermEvaluationTransport

set_option maxHeartbeats 800000

/-!
# Abstract soundness of the all-occurrences restricted calculus

This module proves the proof-calculus part of bounded reflection once and for
all, independently of the concrete partial-truth certificates.  The semantic
relation `Sat` is required to satisfy exactly the clauses used by the coded
one-sided calculus.  A later module instantiates these laws with the
externally fixed truth predicate.

The sequent invariant quantifies over every well-formed coded free-variable
environment.  This is essential at positive hierarchy levels.  Universal
introduction evaluates its premise under a fresh-head extension, while the
shift rule removes an arbitrary head from the conclusion assignment.  Both
operations work for nonstandard HFS sequences and nonstandard formula codes.
-/

namespace LeanProofs.BoundedPAConsistency.AbstractSoundness

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.Internal
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## The semantic interface -/

/-- The exact semantic laws used by the coded sequent calculus at one fixed
model-internal hierarchy bound.

The opening and singleton-substitution laws are stated separately from the
generic Tarski clauses.  This keeps the delicate convention visible:
de Bruijn variable zero is read from the right-hand end of `bound`, whereas a
fresh free variable is inserted at the left-hand end of the lookup sequence.
-/
structure Laws (level : V) (Sat : V → V → V → Prop) : Prop where
  verum : ∀ bound free, Sat bound free ^⊤
  falsum : ∀ bound free, ¬Sat bound free ^⊥
  neg_iff : ∀ {bound free p},
    QuantifierBoundedCode ℒₒᵣ level p →
      (Sat bound free (neg ℒₒᵣ p) ↔ ¬Sat bound free p)
  and_iff : ∀ {bound free p q},
    QuantifierBoundedCode ℒₒᵣ level (p ^⋏ q) →
      (Sat bound free (p ^⋏ q) ↔
        Sat bound free p ∧ Sat bound free q)
  or_iff : ∀ {bound free p q},
    QuantifierBoundedCode ℒₒᵣ level (p ^⋎ q) →
      (Sat bound free (p ^⋎ q) ↔
        Sat bound free p ∨ Sat bound free q)
  all_iff : ∀ {bound free p},
    QuantifierBoundedCode ℒₒᵣ level (^∀ p) →
      (Sat bound free (^∀ p) ↔
        ∀ a, Sat (bound ⁀' a) free p)
  exs_iff : ∀ {bound free p},
    QuantifierBoundedCode ℒₒᵣ level (^∃ p) →
      (Sat bound free (^∃ p) ↔
        ∃ a, Sat (bound ⁀' a) free p)
  shift_iff : ∀ {bound shifted free p},
    IsFreeTail shifted free →
    QuantifierBoundedCode ℒₒᵣ level p →
      (Sat bound shifted (shift ℒₒᵣ p) ↔ Sat bound free p)
  free_iff : ∀ {shifted free p a},
    IsFreeHead a shifted free →
    IsSemiformula ℒₒᵣ 1 p →
    QuantifierBoundedCode ℒₒᵣ level (^∀ p) →
      (Sat 0 shifted (Bootstrapping.free ℒₒᵣ p) ↔
        Sat (0 ⁀' a) free p)
  substs1_iff : ∀ {free p t},
    Arithmetic.Seq free →
    IsSemiformula ℒₒᵣ 1 p →
    IsTerm ℒₒᵣ t →
    QuantifierBoundedCode ℒₒᵣ level (^∃ p) →
      (Sat 0 free (substs1 ℒₒᵣ t p) ↔
        Sat (0 ⁀' termValue 0 free t) free p)

/-- A one-sided sequent is true when it has a true member under every genuine
HFS-coded free-variable assignment.  Quantifying over assignments here,
rather than fixing the zero environment, is what validates the eigenvariable
rule for universal quantification. -/
def SequentTrue (Sat : V → V → V → Prop) (s : V) : Prop :=
  ∀ free : V, Arithmetic.Seq free → ∃ p ∈ s, Sat 0 free p

private lemma sequentTrue_mono {Sat : V → V → V → Prop}
    {s t : V} (hst : s ⊆ t) :
    SequentTrue Sat s → SequentTrue Sat t := by
  intro hs free hfree
  rcases hs free hfree with ⟨p, hp, htrue⟩
  exact ⟨p, hst hp, htrue⟩

/-! ## Rule soundness -/

/-- Every inference of the all-occurrences restricted calculus is sound for
any semantic relation satisfying `Laws`.

`hDef` is deliberately explicit.  The concrete fixed-level truth predicate
will supply a formula defining this invariant at one finite external
hierarchy level, after which full PA supplies the corresponding induction.
-/
theorem restrictedDerivation_sound
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    {Γ : SigmaPiDelta} {m : Nat}
    (hDef : Γ-[m + 1]-Predicate
      (fun d : V ↦ SequentTrue Sat (fstIdx d)))
    {d : V} (hd : RestrictedDerivation T level d) :
    SequentTrue Sat (fstIdx d) := by
  apply inductionInPeanoModel
      (construction (V := V) T) ![level]
      (P := fun d : V ↦ SequentTrue Sat (fstIdx d))
      hDef ?_ d hd
  intro C hC x hx
  rcases hx with ⟨⟨hformulas, hrule⟩, hbounded⟩
  simp only [Matrix.cons_val_zero] at hbounded
  rcases hrule with
      (⟨s, p, rfl, hp, hnp⟩ |
       ⟨s, rfl, hverum⟩ |
       ⟨s, p, q, dp, dq, rfl, hpq, ⟨hdp, hdpC⟩, ⟨hdq, hdqC⟩⟩ |
       ⟨s, p, q, dpq, rfl, hpq, hdpq, hdpqC⟩ |
       ⟨s, p, dp, rfl, hp, hdp, hdpC⟩ |
       ⟨s, p, t, dp, rfl, hp, ht, hdp, hdpC⟩ |
       ⟨s, d', rfl, hss, hd'C⟩ |
       ⟨s, d', rfl, hs, hd'C⟩ |
       ⟨s, p, d₁, d₂, rfl, ⟨hd₁, hd₁C⟩, ⟨hd₂, hd₂C⟩⟩ |
       ⟨s, p, rfl, hp, hpT⟩)
  · -- Initial sequent: `p` and its coded negation are complementary.
    simp only [fstIdx_axL] at hbounded ⊢
    intro free hfree
    have hbp : QuantifierBoundedCode ℒₒᵣ level p := hbounded p hp
    by_cases htrue : Sat 0 free p
    · exact ⟨p, hp, htrue⟩
    · exact ⟨neg ℒₒᵣ p, hnp, (laws.neg_iff hbp).mpr htrue⟩
  · simp only [fstIdx_verumIntro] at hbounded ⊢
    intro free hfree
    exact ⟨^⊤, hverum, laws.verum 0 free⟩
  · -- Conjunction: unless the side sequent is already true, each
    -- premise forces its displayed conjunct.
    simp only [fstIdx_andIntro] at hbounded ⊢
    intro free hfree
    by_cases hside : ∃ r ∈ s, Sat 0 free r
    · exact hside
    · have ihp := (hC dp hdpC).2 free hfree
      have ihq := (hC dq hdqC).2 free hfree
      rw [hdp] at ihp
      rw [hdq] at ihq
      have htp : Sat 0 free p := by
        rcases ihp with ⟨r, hr, htr⟩
        rcases by simpa using hr with (rfl | hrs)
        · exact htr
        · exact (hside ⟨r, hrs, htr⟩).elim
      have htq : Sat 0 free q := by
        rcases ihq with ⟨r, hr, htr⟩
        rcases by simpa using hr with (rfl | hrs)
        · exact htr
        · exact (hside ⟨r, hrs, htr⟩).elim
      exact ⟨p ^⋏ q, hpq,
        (laws.and_iff (hbounded _ hpq)).mpr ⟨htp, htq⟩⟩
  · -- Disjunction: the premise exposes one true disjunct unless its
    -- side sequent already supplies the conclusion witness.
    simp only [fstIdx_orIntro] at hbounded ⊢
    intro free hfree
    by_cases hside : ∃ r ∈ s, Sat 0 free r
    · exact hside
    · have ih := (hC dpq hdpqC).2 free hfree
      rw [hdpq] at ih
      rcases ih with ⟨r, hr, htr⟩
      rcases by simpa using hr with (hrp | hrq | hrs)
      · subst r
        exact ⟨p ^⋎ q, hpq,
          (laws.or_iff (hbounded _ hpq)).mpr (Or.inl htr)⟩
      · subst r
        exact ⟨p ^⋎ q, hpq,
          (laws.or_iff (hbounded _ hpq)).mpr (Or.inr htr)⟩
      · exact (hside ⟨r, hrs, htr⟩).elim
  · -- Universal introduction uses a genuine fresh-head assignment.
    -- If no side formula is true, the premise forces the opened body for
    -- every possible value of the fresh variable.
    simp only [fstIdx_allIntro] at hbounded hformulas ⊢
    intro free hfree
    by_cases hside : ∃ r ∈ s, Sat 0 free r
    · exact hside
    · have hball : QuantifierBoundedCode ℒₒᵣ level (^∀ p) :=
          hbounded _ hp
      have hpsem : IsSemiformula ℒₒᵣ 1 p := by
        have hallFormula := hformulas (^∀ p) hp
        simpa using hallFormula
      refine ⟨^∀ p, hp, (laws.all_iff hball).mpr ?_⟩
      intro a
      rcases exists_isFreeHead a hfree with ⟨shifted, hhead⟩
      have ih := (hC dp hdpC).2 shifted hhead.2.1
      rw [hdp] at ih
      rcases ih with ⟨r, hr, htr⟩
      rcases by simpa using hr with (rfl | hrshift)
      · exact (laws.free_iff hhead hpsem hball).mp htr
      · rcases mem_setShift_iff.mp hrshift with ⟨q, hqs, rfl⟩
        have hbq : QuantifierBoundedCode ℒₒᵣ level q :=
          hbounded q hqs
        have htq : Sat 0 free q :=
          (laws.shift_iff hhead.2.2.2.2 hbq).mp htr
        exact (hside ⟨q, hqs, htq⟩).elim
  · -- Existential introduction evaluates the coded witness term and
    -- transports the singleton substitution to a one-element bound
    -- environment.
    simp only [fstIdx_exsIntro] at hbounded hformulas ⊢
    intro free hfree
    by_cases hside : ∃ r ∈ s, Sat 0 free r
    · exact hside
    · have hbex : QuantifierBoundedCode ℒₒᵣ level (^∃ p) :=
          hbounded _ hp
      have hpsem : IsSemiformula ℒₒᵣ 1 p := by
        have hexFormula := hformulas (^∃ p) hp
        simpa using hexFormula
      have ih := (hC dp hdpC).2 free hfree
      rw [hdp] at ih
      rcases ih with ⟨r, hr, htr⟩
      rcases by simpa using hr with (rfl | hrs)
      · have hbody : Sat (0 ⁀' termValue 0 free t) free p :=
          (laws.substs1_iff hfree hpsem ht hbex).mp htr
        exact ⟨^∃ p, hp,
          (laws.exs_iff hbex).mpr ⟨termValue 0 free t, hbody⟩⟩
      · exact (hside ⟨r, hrs, htr⟩).elim
  · -- Weakening only enlarges the side sequent.
    simp only [fstIdx_wkRule] at hbounded ⊢
    exact sequentTrue_mono hss (hC d' hd'C).2
  · -- The shift rule removes the arbitrary head of the conclusion's
    -- assignment and evaluates the premise in the resulting tail.
    simp only [fstIdx_shiftRule] at hbounded ⊢
    rw [hs]
    intro shifted hshifted
    rcases exists_isFreeTail hshifted with ⟨free, hfree, _, htail⟩
    rcases (hC d' hd'C).2 free hfree with ⟨p, hp, htp⟩
    have hbd := allBounded_of_restricted (T := T) (hC d' hd'C).1
    have hbp : QuantifierBoundedCode ℒₒᵣ level p := hbd p hp
    exact ⟨shift ℒₒᵣ p, shift_mem_setShift hp,
      (laws.shift_iff htail hbp).mpr htp⟩
  · -- Cut: if the side sequent is false, the two premises force both a
    -- formula and its coded negation, contradicting complementarity.
    simp only [fstIdx_cutRule] at hbounded ⊢
    intro free hfree
    by_cases hside : ∃ r ∈ s, Sat 0 free r
    · exact hside
    · have ih₁ := (hC d₁ hd₁C).2 free hfree
      have ih₂ := (hC d₂ hd₂C).2 free hfree
      rw [hd₁] at ih₁
      rw [hd₂] at ih₂
      have htp : Sat 0 free p := by
        rcases ih₁ with ⟨r, hr, htr⟩
        rcases by simpa using hr with (rfl | hrs)
        · exact htr
        · exact (hside ⟨r, hrs, htr⟩).elim
      have htnp : Sat 0 free (neg ℒₒᵣ p) := by
        rcases ih₂ with ⟨r, hr, htr⟩
        rcases by simpa using hr with (rfl | hrs)
        · exact htr
        · exact (hside ⟨r, hrs, htr⟩).elim
      have hb₁ := allBounded_of_restricted (T := T) (hC d₁ hd₁C).1
      have hbp : QuantifierBoundedCode ℒₒᵣ level p := by
        exact hb₁ p (by simp [hd₁])
      exact ((laws.neg_iff hbp).mp htnp htp).elim
  · simp only [fstIdx_axm] at hbounded ⊢
    intro free hfree
    exact ⟨p, hp, hAx p hpT (hbounded p hp) free hfree⟩

/-- Soundness excludes a restricted derivation of the singleton false
sequent.  The statement is kept abstract so the final fixed-level module only
has to provide the definability and PA-axiom instances of `Laws`. -/
theorem restrictedConsistent_of_laws
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    {Γ : SigmaPiDelta} {m : Nat}
    (hDef : Γ-[m + 1]-Predicate
      (fun d : V ↦ SequentTrue Sat (fstIdx d))) :
    RestrictedConsistent T level := by
  rintro ⟨d, hroot, hd⟩
  have hs := restrictedDerivation_sound T laws hAx hDef hd
  rw [hroot] at hs
  rcases hs (∅ : V) seq_empty with ⟨p, hp, htrue⟩
  have hpbot : p = (qqFalsum : V) := by simpa using hp
  subst p
  exact laws.falsum 0 (∅ : V) htrue

end LeanProofs.BoundedPAConsistency.AbstractSoundness
