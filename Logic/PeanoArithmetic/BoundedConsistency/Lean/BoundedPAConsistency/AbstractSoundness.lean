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

/-- The exact fixed-point induction interface used by restricted-derivation
soundness.

For a predicate that is externally definable at some fixed hierarchy level,
full PA supplies this interface through `inductionInPeanoModel`.  Keeping the
interface explicit is also essential for a genuinely model-coded truth
predicate: a later source proof can establish the corresponding closed
induction instance after substituting the represented arithmetic formula,
without pretending that a nonstandard formula code has a fixed external
definability level. -/
def RestrictedDerivationInduction
    (T : Theory ℒₒᵣ) [T.Δ₁] (level : V) (P : V → Prop) : Prop :=
  (∀ C : Set V,
      (∀ x ∈ C, RestrictedDerivation T level x ∧ P x) →
      ∀ x, (construction (V := V) T).Φ ![level] C x → P x) →
    ∀ x, RestrictedDerivation T level x → P x

private lemma sequentTrue_mono {Sat : V → V → V → Prop}
    {s t : V} (hst : s ⊆ t) :
    SequentTrue Sat s → SequentTrue Sat t := by
  intro hs free hfree
  rcases hs free hfree with ⟨p, hp, htrue⟩
  exact ⟨p, hst hp, htrue⟩

/-! ## Rule soundness -/

/-- One local inference of the all-occurrences restricted calculus preserves
sequent truth.

This theorem contains all rule-specific mathematics, but no induction.  Its
explicit predecessor set is useful both for the ordinary least-fixed-point
induction below and for the fixed source strong-step theorem used with a
model-coded truth predicate. -/
theorem restrictedDerivation_sequent_step
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    (C : Set V)
    (hC : ∀ x ∈ C,
      RestrictedDerivation T level x ∧ SequentTrue Sat (fstIdx x))
    (x : V)
    (hx : (construction (V := V) T).Φ ![level] C x) :
    SequentTrue Sat (fstIdx x) := by
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

/-- Every inference of the all-occurrences restricted calculus is sound for
any semantic relation satisfying `Laws`, assuming only the exact induction
interface for the resulting sequent invariant.

This form is independent of how the induction interface is obtained: fixed
external truth predicates use a definability theorem, while a model-coded
truth predicate can use a compiled closed induction instance. -/
theorem restrictedDerivation_sound_of_induction
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    (hinduction : RestrictedDerivationInduction T level
      (fun d : V ↦ SequentTrue Sat (fstIdx d)))
    {d : V} (hd : RestrictedDerivation T level d) :
    SequentTrue Sat (fstIdx d) := by
  apply hinduction _ d hd
  exact restrictedDerivation_sequent_step T laws hAx

/-- The local rule theorem in the strong-step shape used by represented
strong induction on derivation codes.

Strong finiteness of the restricted derivation construction replaces the
arbitrary predecessor set by the genuinely smaller restricted derivations.
Consequently this statement can be expressed by one fixed source formula and
specialized to a nonstandard coded truth predicate. -/
theorem restrictedDerivation_sequent_strongStep
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    (d : V)
    (ih : ∀ e < d,
      RestrictedDerivation T level e → SequentTrue Sat (fstIdx e))
    (hd : RestrictedDerivation T level d) :
    SequentTrue Sat (fstIdx d) := by
  have hstep : (construction (V := V) T).Φ ![level]
      {e | RestrictedDerivation T level e ∧ e < d} d :=
    Fixpoint.Construction.StrongFinite.strong_finite
      ((construction (V := V) T).case.mp hd)
  apply restrictedDerivation_sequent_step T laws hAx
      {e | RestrictedDerivation T level e ∧ e < d} _ d hstep
  intro e he
  exact ⟨he.1, ih e he.2 he.1⟩

/-- Definability-based compatibility wrapper for
`restrictedDerivation_sound_of_induction`.

This retains the original fixed-level API: full PA turns any invariant at a
fixed positive arithmetical-hierarchy level into the explicit induction
interface above. -/
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
  apply restrictedDerivation_sound_of_induction T laws hAx _ hd
  intro step
  exact inductionInPeanoModel
    (construction (V := V) T) ![level] hDef step

/-- Universal soundness of restricted derivations excludes a restricted
derivation of the singleton false sequent.

Separating this final propositional step from both rule soundness and the
choice of induction principle makes it directly reusable after a represented
strong-induction compiler has produced the universal soundness assertion. -/
theorem restrictedConsistent_of_soundness
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hsound : ∀ d : V,
      RestrictedDerivation T level d → SequentTrue Sat (fstIdx d)) :
    RestrictedConsistent T level := by
  rintro ⟨d, hroot, hd⟩
  have hs := hsound d hd
  rw [hroot] at hs
  rcases hs (∅ : V) seq_empty with ⟨p, hp, htrue⟩
  have hpbot : p = (qqFalsum : V) := by simpa using hp
  subst p
  exact laws.falsum 0 (∅ : V) htrue

/-- Soundness excludes a restricted derivation of falsity once the exact
restricted-derivation induction interface is available.  This is the form
used by model-coded truth, whose defining formula may have nonstandard code
and therefore need not lie at any externally fixed hierarchy level. -/
theorem restrictedConsistent_of_laws_of_induction
    (T : Theory ℒₒᵣ) [T.Δ₁]
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      ∀ free : V, Arithmetic.Seq free → Sat 0 free p)
    (hinduction : RestrictedDerivationInduction T level
      (fun d : V ↦ SequentTrue Sat (fstIdx d))) :
    RestrictedConsistent T level := by
  apply restrictedConsistent_of_soundness T laws
  intro d hd
  exact restrictedDerivation_sound_of_induction
    T laws hAx hinduction hd

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
  apply restrictedConsistent_of_laws_of_induction T laws hAx
  intro step
  exact inductionInPeanoModel
    (construction (V := V) T) ![level] hDef step

end LeanProofs.BoundedPAConsistency.AbstractSoundness
