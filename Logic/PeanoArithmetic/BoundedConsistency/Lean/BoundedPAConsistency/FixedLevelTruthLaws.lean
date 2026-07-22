import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.FixedLevelTruthSubstitution

/-!
# The unified bounded partial-truth laws

For formulas with at most the model numeral `n` quantifier groups we use
`SigmaTrue (n + 1)` as a single satisfaction relation.  The spare hierarchy
level puts every bounded formula in both oriented domains.  Coherence then
turns the Sigma certificate predicate into a genuinely classical truth
predicate, including complement and the universal clause.

The final theorem in this file packages exactly the interface consumed by the
abstract soundness proof.  All arguments continue to range over arbitrary
codes and environments in an arbitrary (possibly nonstandard) model of PA.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthLaws

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

private lemma levelCode_succ (n : ℕ) :
    levelCode (V := V) (n + 1) = levelCode n + 1 :=
  (numeral_add_one n).symm

private lemma sigmaDomain_of_bounded (n : ℕ) {p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p) :
    IsSigmaCode ℒₒᵣ (levelCode (V := V) (n + 1)) p := by
  rw [levelCode_succ]
  exact LeanProofs.BoundedPAConsistency.OrientedHierarchy.QuantifierBoundedCode.toSigmaSucc hp

private lemma piDomain_of_bounded (n : ℕ) {p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p) :
    IsPiCode ℒₒᵣ (levelCode (V := V) (n + 1)) p := by
  rw [levelCode_succ]
  exact LeanProofs.BoundedPAConsistency.OrientedHierarchy.QuantifierBoundedCode.toPiSucc hp

/-! ## Boolean and quantifier clauses on the bounded domain -/

/-- Coded negation is genuine complement for the unified truth predicate. -/
theorem sigmaTrue_succ_neg_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) bound free (neg ℒₒᵣ p) ↔
      ¬SigmaTrue (n + 1) bound free p := by
  have hs := sigmaDomain_of_bounded n hp
  have hpi := piDomain_of_bounded n hp
  have hcoh := sigmaTrue_iff_piTrue_of_domains (n + 1)
    (bound := bound) (free := free) hs hpi
  rw [piTrue_iff, and_iff_right hpi] at hcoh
  constructor
  · intro hneg htrue
    exact (hcoh.mp htrue) hneg
  · intro hfalse
    by_contra hneg
    exact hfalse (hcoh.mpr hneg)

/-- Conjunction has its usual Tarski clause on the bounded domain. -/
theorem sigmaTrue_succ_and_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p q : V}
    (hpq : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (p ^⋏ q)) :
    SigmaTrue (n + 1) bound free (p ^⋏ q) ↔
      SigmaTrue (n + 1) bound free p ∧
        SigmaTrue (n + 1) bound free q := by
  have hparts : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using hpq.1
  exact sigmaTrue_and_iff hparts.1 hparts.2

/-- Disjunction has its usual Tarski clause on the bounded domain. -/
theorem sigmaTrue_succ_or_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p q : V}
    (hpq : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (p ^⋎ q)) :
    SigmaTrue (n + 1) bound free (p ^⋎ q) ↔
      SigmaTrue (n + 1) bound free p ∨
        SigmaTrue (n + 1) bound free q := by
  have hu : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using hpq.1
  have hparts := (isSigmaCode_or_iff hu.1 hu.2).mp
    (sigmaDomain_of_bounded n hpq)
  exact sigmaTrue_or_iff hu.1 hu.2 hparts.1 hparts.2

/-- Existential quantification has its usual witness clause. -/
theorem sigmaTrue_succ_exs_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (^∃ p)) :
    SigmaTrue (n + 1) bound free (^∃ p) ↔
      ∃ a, SigmaTrue (n + 1) (bound ⁀' a) free p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using hp.1
  exact sigmaTrue_exs_iff hpU

/-- Universal quantification is obtained from Pi's direct universal clause
and same-level Sigma/Pi coherence for the quantified formula and its body. -/
theorem sigmaTrue_succ_all_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (^∀ p)) :
    SigmaTrue (n + 1) bound free (^∀ p) ↔
      ∀ a, SigmaTrue (n + 1) (bound ⁀' a) free p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using hp.1
  have hsAll := sigmaDomain_of_bounded n hp
  have hpiAll := piDomain_of_bounded n hp
  have hpiBody : IsPiCode ℒₒᵣ (levelCode (V := V) (n + 1)) p :=
    ((isPiCode_all_iff hpU).mp hpiAll).1
  have hsAll' : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) n + 1) (^∀ p) := by
    simpa only [← levelCode_succ] using hsAll
  have hpiBodyLower : IsPiCode ℒₒᵣ (levelCode (V := V) n) p :=
    ((isSigmaCode_all_succ_iff
      (n := levelCode (V := V) n) hpU).mp hsAll').1
  have hsBody : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) (n + 1)) p := by
    rw [levelCode_succ]
    exact hpiBodyLower.toSigmaSucc
  rw [sigmaTrue_iff_piTrue_of_domains (n + 1) hsAll hpiAll,
    piTrue_all_iff hpU]
  constructor
  · intro h a
    exact (sigmaTrue_iff_piTrue_of_domains (n + 1)
      hsBody hpiBody).mpr (h a)
  · intro h a
    exact (sigmaTrue_iff_piTrue_of_domains (n + 1)
      hsBody hpiBody).mp (h a)

/-! ## Environment transport -/

/-- Free-variable shifting preserves unified truth. -/
theorem sigmaTrue_succ_shift_iff_of_quantifierBoundedCode (n : ℕ)
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) bound shifted (shift ℒₒᵣ p) ↔
      SigmaTrue (n + 1) bound free p :=
  sigmaTrue_shift_iff_of_isFreeTail (n + 1) hfree
    (sigmaDomain_of_bounded n hp)

/-- Singleton substitution evaluates its term and installs the result as the
sole bound-variable value.  This raw form records precisely the oriented
domain needed by substitution; the bounded-domain adapter follows below. -/
theorem sigmaTrue_substs1_iff_of_isSigmaCode (level : ℕ)
    {free p t : V}
    (hfree : Arithmetic.Seq free)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (ht : IsTerm ℒₒᵣ t)
    (hdom : IsSigmaCode ℒₒᵣ (levelCode (V := V) level) p) :
    SigmaTrue level 0 free (substs1 ℒₒᵣ t p) ↔
      SigmaTrue level (0 ⁀' termValue 0 free t) free p := by
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
    intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    simpa [termValue_bvar] using
      (termValue_bvar_zero_seqCons
        (free := free) (a := termValue 0 free t) hzeroSeq)
  simpa only [substs1] using
    sigmaTrue_subst_iff_of_isSubstitutionEnvironment level
      hw hlhZero hsub hp hdom

/-- Bounded-domain specialization of singleton substitution. -/
theorem sigmaTrue_succ_substs1_iff_of_quantifierBoundedCode (n : ℕ)
    {free p t : V}
    (hfree : Arithmetic.Seq free)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (ht : IsTerm ℒₒᵣ t)
    (hb : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (^∃ p)) :
    SigmaTrue (n + 1) 0 free (substs1 ℒₒᵣ t p) ↔
      SigmaTrue (n + 1) (0 ⁀' termValue 0 free t) free p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using hb.1
  have hpSigma : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) (n + 1)) p := by
    have hsEx := sigmaDomain_of_bounded n hb
    exact ((isSigmaCode_exs_iff hpU).mp hsEx).1
  exact sigmaTrue_substs1_iff_of_isSigmaCode (n + 1)
    hfree hp ht hpSigma

/-- Opening a unary formula is singleton substitution after free-variable
shift.  `IsFreeHead` supplies both the head value and the tail lookup law. -/
theorem sigmaTrue_succ_free_iff_of_quantifierBoundedCode (n : ℕ)
    {shifted free p a : V}
    (hhead : IsFreeHead a shifted free)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (hb : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (^∀ p)) :
    SigmaTrue (n + 1) 0 shifted (Bootstrapping.free ℒₒᵣ p) ↔
      SigmaTrue (n + 1) (0 ⁀' a) free p := by
  have hpBounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) p := by
    have hpU : IsUFormula ℒₒᵣ p := by simpa using hb.1
    have hsAll := sigmaDomain_of_bounded n hb
    have hsAll' : IsSigmaCode ℒₒᵣ
        (levelCode (V := V) n + 1) (^∀ p) := by
      simpa only [← levelCode_succ] using hsAll
    have hpiLower := ((isSigmaCode_all_succ_iff
      (n := levelCode (V := V) n) hpU).mp hsAll').1
    exact hpiLower.quantifierBounded
  have hsBody : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) (n + 1)) p :=
    sigmaDomain_of_bounded n hpBounded
  have hsShift : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) (n + 1)) (shift ℒₒᵣ p) :=
    (isSigmaCode_shift_iff hp.isUFormula).mpr hsBody
  unfold Bootstrapping.free
  rw [sigmaTrue_substs1_iff_of_isSigmaCode (n + 1)
      hhead.2.1 hp.shift (by simp) hsShift,
    show termValue (0 : V) shifted ^&0 = a by
      simpa using hhead.2.2.2.1,
    sigmaTrue_succ_shift_iff_of_quantifierBoundedCode n
      hhead.2.2.2.2 hpBounded]

/-! ## Packaged calculus interface -/

/-- `SigmaTrue (n + 1)` satisfies every semantic law required by the
all-occurrences restricted sequent calculus at model bound `levelCode n`. -/
theorem sigmaTrue_succ_laws (n : ℕ) :
    Laws (V := V) (levelCode n) (SigmaTrue (V := V) (n + 1)) where
  verum bound free := by
    rw [sigmaTrue_succ_qf_iff n (by simp)]
    simp
  falsum bound free := by
    rw [sigmaTrue_succ_qf_iff n (by simp)]
    simp
  neg_iff hp := sigmaTrue_succ_neg_iff_of_quantifierBoundedCode n hp
  and_iff hp := sigmaTrue_succ_and_iff_of_quantifierBoundedCode n hp
  or_iff hp := sigmaTrue_succ_or_iff_of_quantifierBoundedCode n hp
  all_iff hp := sigmaTrue_succ_all_iff_of_quantifierBoundedCode n hp
  exs_iff hp := sigmaTrue_succ_exs_iff_of_quantifierBoundedCode n hp
  shift_iff hfree hp :=
    sigmaTrue_succ_shift_iff_of_quantifierBoundedCode n hfree hp
  free_iff hhead hp hb :=
    sigmaTrue_succ_free_iff_of_quantifierBoundedCode n hhead hp hb
  substs1_iff hfree hp ht hb :=
    sigmaTrue_succ_substs1_iff_of_quantifierBoundedCode n hfree hp ht hb

end LeanProofs.BoundedPAConsistency.FixedLevelTruthLaws
