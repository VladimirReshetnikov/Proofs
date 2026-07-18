import BoundedPAConsistency.QuantifierFreeTransport
import BoundedPAConsistency.RestrictedConsistency

set_option maxHeartbeats 800000

/-!
# Logical soundness of the rank-zero restricted calculus

This module isolates the proof-rule part of bounded reflection at the base
hierarchy level.  It deliberately leaves theory axioms behind one explicit
hypothesis: an internally recognized rank-zero axiom must satisfy the coded
rank-zero truth predicate.  The logical rules themselves are then verified by
induction over the *nonstandard* restricted-derivation fixed point in an
arbitrary model of PA.

Quantifier rules cannot occur at level zero because their principal formula
is not in the represented rank-zero domain.  The remaining rules use only the
Boolean Tarski clauses and semantic transport under negation and shift.  This
separation makes the outstanding PA-axiom obligation exact rather than hiding
it inside a standard-code soundness theorem.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeSoundness

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.Internal
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- A coded one-sided sequent is rank-zero true when one of its members has
Boolean value one under the all-zero bound and free environments.  A fixed
environment is sufficient for excluding the empty/false root at level zero;
the shift rule is sound because zero is its own free-variable tail. -/
def QFSequentTrue (s : V) : Prop :=
  ∃ p ∈ s, QFTrue 0 0 p

instance QFSequentTrue.definable :
    HierarchySymbol.DefinablePred (V := V) HierarchySymbol.sigmaOne
      QFSequentTrue := by
  unfold QFSequentTrue
  definability

private lemma qfSequentTrue_mono {s t : V} (hst : s ⊆ t) :
    QFSequentTrue s → QFSequentTrue t := by
  rintro ⟨p, hp, htrue⟩
  exact ⟨p, hst hp, htrue⟩

private lemma zero_isFreeTail : IsFreeTail (0 : V) 0 := by
  change IsFreeTail (∅ : V) ∅
  intro x
  rw [znth_prop_not (Or.inr (by simp)),
    znth_prop_not (Or.inr (by simp))]

/-- Soundness of every rank-zero logical inference, parameterized only by
truth of internally recognized rank-zero theory axioms. -/
theorem restrictedDerivation_qf_sound
    (T : Theory ℒₒᵣ) [T.Δ₁]
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      IsQuantifierFreeCode p → QFTrue 0 0 p)
    {d : V} (hd : RestrictedDerivation T 0 d) :
    QFSequentTrue (fstIdx d) := by
  have hP : HierarchySymbol.DefinablePred (V := V)
      HierarchySymbol.sigmaOne
      (fun d : V ↦ QFSequentTrue (fstIdx d)) := by
    definability
  apply inductionInPeanoModel
      (construction (V := V) T) ![0]
      (P := fun d : V ↦ QFSequentTrue (fstIdx d))
      (m := 0) hP ?_ d hd
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
  · -- Initial sequent: one of `p` and its coded negation is true.
    simp only [fstIdx_axL] at hbounded ⊢
    have hb : AllBounded (L := ℒₒᵣ) 0 s := hbounded
    have hbp : IsQuantifierFreeCode p := hb p hp
    rcases qfValue_isBit (bound := (0 : V)) (free := 0) hbp.1 with hz | ho
    · refine ⟨neg ℒₒᵣ p, hnp, ?_⟩
      have hbneg : IsQuantifierFreeCode (neg ℒₒᵣ p) :=
        (isQuantifierFreeCode_neg_iff hbp.1).mpr hbp
      simp [QFTrue, hbneg, qfValue_neg hbp, hz, bitNot]
    · exact ⟨p, hp, hbp, ho⟩
  · simp only [fstIdx_verumIntro] at hbounded ⊢
    exact ⟨^⊤, hverum, qfTrue_verum⟩
  · -- Conjunction: if neither premise is already true in the side
    -- sequent, their principal formulae are both true.
    simp only [fstIdx_andIntro] at hbounded ⊢
    have hb : AllBounded (L := ℒₒᵣ) 0 s := hbounded
    rcases hC dp hdpC with ⟨_, ihp⟩
    rcases hC dq hdqC with ⟨_, ihq⟩
    rw [hdp] at ihp
    rw [hdq] at ihq
    rcases ihp with ⟨r, hr, htr⟩
    rcases by simpa using hr with (hrp | hrs)
    · subst r
      rcases ihq with ⟨r, hr, htrq⟩
      rcases by simpa using hr with (hrq | hrs)
      · subst r
        have hbpq : IsQuantifierFreeCode (p ^⋏ q) := hb _ hpq
        have hpqU : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
          simpa using hbpq.1
        have hparts := (isQuantifierFreeCode_and_iff hpqU.1 hpqU.2).mp hbpq
        exact ⟨p ^⋏ q, hpq,
          (qfTrue_and_iff hpqU.1 hpqU.2).2 ⟨htr, htrq⟩⟩
      · exact ⟨r, hrs, htrq⟩
    · exact ⟨r, hrs, htr⟩
  · -- Disjunction: the single premise exposes both disjuncts.
    simp only [fstIdx_orIntro] at hbounded ⊢
    have hb : AllBounded (L := ℒₒᵣ) 0 s := hbounded
    rcases hC dpq hdpqC with ⟨_, ih⟩
    rw [hdpq] at ih
    rcases ih with ⟨r, hr, htr⟩
    rcases by simpa using hr with (hrp | hrq | hrs)
    · subst r
      have hbpq : IsQuantifierFreeCode (p ^⋎ q) := hb _ hpq
      have hpqU : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
        simpa using hbpq.1
      have hparts := (isQuantifierFreeCode_or_iff hpqU.1 hpqU.2).mp hbpq
      exact ⟨p ^⋎ q, hpq,
        (qfTrue_or_iff hpqU.1 hpqU.2 hparts.1 hparts.2).2 (Or.inl htr)⟩
    · subst r
      have hbpq : IsQuantifierFreeCode (p ^⋎ q) := hb _ hpq
      have hpqU : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
        simpa using hbpq.1
      have hparts := (isQuantifierFreeCode_or_iff hpqU.1 hpqU.2).mp hbpq
      exact ⟨p ^⋎ q, hpq,
        (qfTrue_or_iff hpqU.1 hpqU.2 hparts.1 hparts.2).2 (Or.inr htr)⟩
    · exact ⟨r, hrs, htr⟩
  · -- A quantified principal formula contradicts the node's zero bound.
    have hb : AllBounded (L := ℒₒᵣ) 0 s := by
      simpa only [fstIdx_allIntro] using hbounded
    have hbq : IsQuantifierFreeCode (^∀ p) := hb _ hp
    have hpU : IsUFormula ℒₒᵣ p := by simpa using hbq.1
    exact (not_isQuantifierFreeCode_all hpU hbq).elim
  · have hb : AllBounded (L := ℒₒᵣ) 0 s := by
      simpa only [fstIdx_exsIntro] using hbounded
    have hbq : IsQuantifierFreeCode (^∃ p) := hb _ hp
    have hpU : IsUFormula ℒₒᵣ p := by simpa using hbq.1
    exact (not_isQuantifierFreeCode_exs hpU hbq).elim
  · rcases hC d' hd'C with ⟨_, ih⟩
    simp only [fstIdx_wkRule] at hbounded ⊢
    exact qfSequentTrue_mono hss (by simpa using ih)
  · -- Shifting every free variable preserves value in the zero
    -- environment because that environment is its own tail.
    simp only [fstIdx_shiftRule] at hbounded ⊢
    rcases hC d' hd'C with ⟨_, ih⟩
    rw [hs]
    rcases ih with ⟨p, hp, htp⟩
    refine ⟨shift ℒₒᵣ p, shift_mem_setShift hp, ?_⟩
    exact (qfTrue_shift_iff_of_isFreeTail zero_isFreeTail htp.1).2 htp
  · -- Cut: if the side sequent is false, the two premises make both a
    -- formula and its coded negation true, contradicting complementarity.
    simp only [fstIdx_cutRule] at hbounded ⊢
    rcases hC d₁ hd₁C with ⟨hd₁r, ih₁⟩
    rcases hC d₂ hd₂C with ⟨hd₂r, ih₂⟩
    rw [hd₁] at ih₁
    rw [hd₂] at ih₂
    rcases ih₁ with ⟨r, hr, htr⟩
    rcases by simpa using hr with (hrp | hrs)
    · subst r
      rcases ih₂ with ⟨r, hr, htrn⟩
      rcases by simpa using hr with (hrnp | hrs)
      · subst r
        have hbp : IsQuantifierFreeCode p := by
          have hb := allBounded_of_restricted (T := T) hd₁r
          exact hb p (by simp [hd₁])
        exact False.elim <| ((qfTrue_iff_not_qfFalse hbp).mp htr)
          ((qfTrue_neg_iff hbp).mp htrn)
      · exact ⟨r, hrs, htrn⟩
    · exact ⟨r, hrs, htr⟩
  · simp only [fstIdx_axm] at hbounded ⊢
    exact ⟨p, hp, hAx p hpT (hbounded p hp)⟩

/-- The rule-soundness theorem excludes a rank-zero proof of falsity.  The
only remaining theory-specific premise is the truth of internally recognized
rank-zero axioms. -/
theorem restrictedConsistent_zero_of_qf_axioms
    (T : Theory ℒₒᵣ) [T.Δ₁]
    (hAx : ∀ p : V, p ∈ T.Δ₁Class →
      IsQuantifierFreeCode p → QFTrue 0 0 p) :
    RestrictedConsistent T (0 : V) := by
  rintro ⟨d, hroot, hd⟩
  have hs := restrictedDerivation_qf_sound T hAx hd
  rw [hroot] at hs
  rcases hs with ⟨p, hp, htrue⟩
  have hpbot : p = (qqFalsum : V) := by simpa using hp
  subst p
  exact not_qfTrue_falsum htrue

end LeanProofs.BoundedPAConsistency.QuantifierFreeSoundness
