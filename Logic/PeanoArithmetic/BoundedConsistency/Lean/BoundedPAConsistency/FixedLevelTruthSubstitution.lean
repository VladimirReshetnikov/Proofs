import BoundedPAConsistency.FixedLevelTruthCoherence
import BoundedPAConsistency.ModelFormulaInduction
import BoundedPAConsistency.TermEvaluationTransport

set_option maxHeartbeats 1000000
set_option maxRecDepth 5000

/-!
# Substitution and free-variable transport for fixed-level truth

This module proves semantic transport directly on coded formulas in an
arbitrary model of PA.  Formula codes, term vectors, and environments may all
be nonstandard.  Consequently the structural arguments use model-internal
formula and term induction rather than decoding codes into Lean syntax.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.ModelFormulaInduction

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Extending semantic bound environments -/

/-- Bound-variable shift is evaluated by dropping the newly appended
de Bruijn head.  This is the bound-variable analogue of
`termValue_termShift_of_isFreeTail`. -/
theorem termValue_termBShift_seqCons {bound free a t : V}
    (hbound : Seq bound) (ht : IsSemiterm ℒₒᵣ (lh bound) t) :
    termValue (bound ⁀' a) free (termBShift ℒₒᵣ t) =
      termValue bound free t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termBShift_bvar, termValue_bvar, termValue_bvar]
    have hi : boundPosition bound z < lh bound := by
      simp only [boundPosition]
      exact tsub_lt_self (lt_of_le_of_lt (by simp) hz) (by simp)
    have hmem : ⟪boundPosition bound z, znth bound (boundPosition bound z)⟫ ∈
        bound ⁀' a :=
      Seq.subset_seqCons bound a (hbound.znth hi)
    have heq := (hbound.seqCons a).znth_eq_of_mem hmem
    simpa [boundPosition, hbound, Arithmetic.sub_sub] using heq
  · intro x
    simp
  · intro k f terms hf hterms ih
    rw [termBShift_func hf hterms.isUTerm,
      termValue_func hf hterms.termBShiftVec.isUTerm,
      termValue_func hf hterms.isUTerm]
    congr 1
    apply nth_ext' k
      (by rw [length_termValues hterms.termBShiftVec.isUTerm])
      (by rw [length_termValues hterms.isUTerm])
    intro i hi
    rw [nth_termValues hterms.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hterms.isUTerm hi,
      nth_termValues hterms.isUTerm hi,
      ih i hi]

/-- Appending a sequence entry leaves every earlier lookup unchanged. -/
theorem znth_seqCons_of_lt {s a i : V} (hs : Seq s) (hi : i < lh s) :
    znth (s ⁀' a) i = znth s i := by
  exact (hs.seqCons a).znth_eq_of_mem
    (Seq.subset_seqCons s a (hs.znth hi))

/-- A semantic substitution environment extends through one object-language
quantifier.  The new `qVec` head denotes the freshly bound variable, while
every old substituting term is bound-shifted and therefore continues to have
the same value below the appended environment entry.

The source environment length is explicit.  Without it the claim is false
for a term containing a bound variable evaluated in an undersized totalized
environment.
-/
theorem isSubstitutionEnvironment_qVec_seqCons
    {bound free n m w subBound a : V}
    (hw : IsSemitermVec ℒₒᵣ n m w)
    (hboundLen : lh bound = m)
    (hsub : IsSubstitutionEnvironment bound free n w subBound) :
    IsSubstitutionEnvironment
      (bound ⁀' a) free (n + 1) (qVec ℒₒᵣ w) (subBound ⁀' a) := by
  rcases hsub with ⟨_, hbound, hfree, hsubBound, hlen, hrel⟩
  refine ⟨hw.qVec.isUTerm, hbound.seqCons a, hfree,
    hsubBound.seqCons a, ?_, ?_⟩
  · simp [hsubBound, hlen]
  · intro z hz
    rcases zero_or_succ z with rfl | ⟨i, rfl⟩
    · calc
        znth (subBound ⁀' a) (boundPosition (subBound ⁀' a) 0) = a := by
          simpa [termValue_bvar] using
            (termValue_bvar_zero_seqCons (free := free) hsubBound)
        _ = termValue (bound ⁀' a) free (qVec ℒₒᵣ w).[0] := by
          rw [show (qVec ℒₒᵣ w).[0] = ^#(0 : V) by simp [qVec]]
          simpa using
            (termValue_bvar_zero_seqCons (free := free) hbound).symm
    · have hi : i < n := by simpa using hz
      have hold := hrel i hi
      have hterm : IsSemiterm ℒₒᵣ (lh bound) w.[i] := by
        rw [hboundLen]
        exact hw.nth hi
      have hiw : i < len w := by simpa [hw.lh] using hi
      have hwLen : IsUTermVec ℒₒᵣ (len w) w := by
        simpa [hw.lh] using hw.isUTerm
      rw [show (qVec ℒₒᵣ w).[i + 1] =
          (termBShiftVec ℒₒᵣ (len w) w).[i] by simp [qVec],
        nth_termBShiftVec hwLen hiw,
        termValue_termBShift_seqCons hbound hterm]
      have hpos : boundPosition subBound i < lh subBound := by
        simp only [boundPosition, hlen]
        exact tsub_lt_self (lt_of_le_of_lt (by simp) hi) (by simp)
      rw [show boundPosition (subBound ⁀' a) (i + 1) =
          boundPosition subBound i by
        simp [boundPosition, hsubBound],
        znth_seqCons_of_lt hsubBound hpos]
      exact hold

/-! ## Free-variable shift -/

private def SigmaShiftInvariant
    (n : ℕ) (shifted free p : V) : Prop :=
  ∀ bound,
    IsSigmaCode ℒₒᵣ (levelCode n) p →
      (SigmaTrue n bound shifted (shift ℒₒᵣ p) ↔
        SigmaTrue n bound free p)

/-- Raising a Sigma definition by one level gives both polarities.  We use
this small definability bridge only to make the biconditional in the
structural-induction invariant available as a Delta predicate. -/
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

private lemma sigmaShiftInvariant_definable
    (n : ℕ) (shifted free : V) :
    Polarity.pi-[n + 2]-Predicate
      (SigmaShiftInvariant (V := V) n shifted free) := by
  letI : SigmaPiDelta.delta-[n + 2]-Relation₃
      (SigmaTrue n : V → V → V → Prop) := by
    exact sigma_definable_delta_succ (sigmaTrue_definable n)
  unfold SigmaShiftInvariant
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.biconditional
    · definability
    · definability

private lemma levelCode_succ (n : ℕ) :
    levelCode (V := V) (n + 1) = levelCode n + 1 := by
  exact (numeral_add_one n).symm

private lemma quantifierFree_of_isSigmaCode_zero {p : V}
    (hp : IsSigmaCode ℒₒᵣ (levelCode (V := V) 0) p) :
    IsQuantifierFreeCode p := by
  have hs0 : sigmaRankCode ℒₒᵣ p = 0 := by
    simpa [levelCode] using hp.2
  have hgroups : quantifierGroupsCode ℒₒᵣ p = 0 := by
    simp [quantifierGroupsCode, hs0]
  exact ⟨hp.1, by simp [hgroups]⟩

/-- Fixed-level Sigma truth commutes with free-variable shift for arbitrary
codes in the model.  The hierarchy level is external, while `p` may be a
nonstandard formula code. -/
theorem sigmaTrue_shift_iff_of_isFreeTail (n : ℕ)
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsSigmaCode ℒₒᵣ (levelCode n) p) :
    SigmaTrue n bound shifted (shift ℒₒᵣ p) ↔
      SigmaTrue n bound free p := by
  induction n generalizing bound shifted free p with
  | zero =>
      have hqf := quantifierFree_of_isSigmaCode_zero hp
      simpa only [sigmaTrue_zero] using
        qfTrue_shift_iff_of_isFreeTail hfree hqf
  | succ n ih =>
      have piShift : ∀ {bound p : V},
          IsPiCode ℒₒᵣ (levelCode n) p →
          (PiTrue n bound shifted (shift ℒₒᵣ p) ↔
            PiTrue n bound free p) := by
        intro bound p hpPi
        have hpShift : IsPiCode ℒₒᵣ (levelCode n) (shift ℒₒᵣ p) :=
          (isPiCode_shift_iff hpPi.1).mpr hpPi
        have hneg : IsSigmaCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ p) :=
          (isSigmaCode_neg_iff hpPi.1).mpr hpPi
        rw [piTrue_iff, and_iff_right hpShift,
          piTrue_iff, and_iff_right hpPi,
          ← shift_neg hpPi.1.isSemiformula]
        exact not_congr (ih hfree hneg)
      have hmain : ∀ q : V, IsUFormula ℒₒᵣ q →
          SigmaShiftInvariant (V := V) (n + 1) shifted free q := by
        apply uformula_inductionInPeanoModel
            (L := ℒₒᵣ) (sigmaShiftInvariant_definable (n + 1) shifted free)
        · intro k R terms hR hterms bound hdom
          have hqf : IsQuantifierFreeCode (^rel k R terms) := by
            simp [IsQuantifierFreeCode, hR, hterms]
          have hqfShift : IsQuantifierFreeCode
              (shift ℒₒᵣ (^rel k R terms)) :=
            (QuantifierBoundedCode.shift_iff hqf.1).mpr hqf
          rw [sigmaTrue_succ_qf_iff n hqfShift,
            sigmaTrue_succ_qf_iff n hqf,
            qfTrue_shift_iff_of_isFreeTail hfree hqf]
        · intro k R terms hR hterms bound hdom
          have hqf : IsQuantifierFreeCode (^nrel k R terms) := by
            simp [IsQuantifierFreeCode, hR, hterms]
          have hqfShift : IsQuantifierFreeCode
              (shift ℒₒᵣ (^nrel k R terms)) :=
            (QuantifierBoundedCode.shift_iff hqf.1).mpr hqf
          rw [sigmaTrue_succ_qf_iff n hqfShift,
            sigmaTrue_succ_qf_iff n hqf,
            qfTrue_shift_iff_of_isFreeTail hfree hqf]
        · intro bound hdom
          have hqf : IsQuantifierFreeCode (^⊤ : V) := by simp
          simpa using
            ((sigmaTrue_succ_qf_iff n
                ((QuantifierBoundedCode.shift_iff hqf.1).mpr hqf)).trans
              ((qfTrue_shift_iff_of_isFreeTail hfree hqf).trans
                (sigmaTrue_succ_qf_iff n hqf).symm))
        · intro bound hdom
          have hqf : IsQuantifierFreeCode (^⊥ : V) := by simp
          simpa using
            ((sigmaTrue_succ_qf_iff n
                ((QuantifierBoundedCode.shift_iff hqf.1).mpr hqf)).trans
              ((qfTrue_shift_iff_of_isFreeTail hfree hqf).trans
                (sigmaTrue_succ_qf_iff n hqf).symm))
        · intro p q hpU hqU ihp ihq bound hdom
          have hparts := (isSigmaCode_and_iff hpU hqU).mp hdom
          rw [shift_and hpU hqU,
            sigmaTrue_and_iff hpU.shift hqU.shift,
            sigmaTrue_and_iff hpU hqU,
            ihp bound hparts.1, ihq bound hparts.2]
        · intro p q hpU hqU ihp ihq bound hdom
          have hparts := (isSigmaCode_or_iff hpU hqU).mp hdom
          have hpShift := (isSigmaCode_shift_iff hpU).mpr hparts.1
          have hqShift := (isSigmaCode_shift_iff hqU).mpr hparts.2
          rw [shift_or hpU hqU,
            sigmaTrue_or_iff hpU.shift hqU.shift hpShift hqShift,
            sigmaTrue_or_iff hpU hqU hparts.1 hparts.2,
            ihp bound hparts.1, ihq bound hparts.2]
        · intro q hqU ihq bound hdom
          have hdom' : IsSigmaCode ℒₒᵣ (levelCode n + 1) (^∀ q) := by
            simpa only [levelCode_succ] using hdom
          have hparts :=
            (isSigmaCode_all_succ_iff (n := levelCode n) hqU).mp hdom'
          have hpiall : IsPiCode ℒₒᵣ (levelCode n) (^∀ q) :=
            (isPiCode_all_iff hqU).mpr hparts
          rw [shift_all hqU,
            sigmaTrue_succ_all_iff hqU.shift,
            sigmaTrue_succ_all_iff hqU]
          simpa only [shift_all hqU] using
            (piShift (bound := bound) hpiall)
        · intro q hqU ihq bound hdom
          have hbody :=
            (isSigmaCode_exs_succ_iff (n := levelCode n) hqU).mp
              (by simpa only [levelCode_succ] using hdom)
          have hbody' : IsSigmaCode ℒₒᵣ (levelCode (n + 1)) q := by
            simpa only [levelCode_succ] using hbody
          rw [shift_exs hqU, sigmaTrue_exs_iff hqU.shift,
            sigmaTrue_exs_iff hqU]
          constructor
          · rintro ⟨a, ha⟩
            exact ⟨a, (ihq (bound ⁀' a) hbody').mp ha⟩
          · rintro ⟨a, ha⟩
            exact ⟨a, (ihq (bound ⁀' a) hbody').mpr ha⟩
      exact hmain p hp.1 bound hp

/-- The dual fixed-level truth presentation obeys the same free-variable
shift law. -/
theorem piTrue_shift_iff_of_isFreeTail (n : ℕ)
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hp : IsPiCode ℒₒᵣ (levelCode n) p) :
    PiTrue n bound shifted (shift ℒₒᵣ p) ↔
      PiTrue n bound free p := by
  have hpShift : IsPiCode ℒₒᵣ (levelCode n) (shift ℒₒᵣ p) :=
    (isPiCode_shift_iff hp.1).mpr hp
  have hneg : IsSigmaCode ℒₒᵣ (levelCode n) (neg ℒₒᵣ p) :=
    (isSigmaCode_neg_iff hp.1).mpr hp
  rw [piTrue_iff, and_iff_right hpShift,
    piTrue_iff, and_iff_right hp,
    ← shift_neg hp.1.isSemiformula]
  exact not_congr (sigmaTrue_shift_iff_of_isFreeTail n hfree hneg)

/-! ## Simultaneous bound-variable substitution -/

private def SigmaSubstitutionInvariant (level : ℕ) (p : V) : Prop :=
  ∀ arity bound free m w subBound,
    IsSemiformula ℒₒᵣ arity p →
    IsSemitermVec ℒₒᵣ arity m w →
    lh bound = m →
    IsSubstitutionEnvironment bound free arity w subBound →
    IsSigmaCode ℒₒᵣ (levelCode level) p →
      (SigmaTrue level bound free (subst ℒₒᵣ w p) ↔
        SigmaTrue level subBound free p)

private lemma isSubstitutionBound_definable :
    SigmaPiDelta.delta-[1]-Relation₅
      (IsSubstitutionBound (V := V)) := by
  unfold IsSubstitutionBound boundPosition
  definability

private lemma isSubstitutionEnvironment_definable :
    SigmaPiDelta.delta-[1]-Relation₅
      (IsSubstitutionEnvironment (V := V)) := by
  letI : SigmaPiDelta.delta-[1]-Relation₅
      (IsSubstitutionBound (V := V)) :=
    isSubstitutionBound_definable
  unfold IsSubstitutionEnvironment
  definability

private lemma sigmaSubstitutionInvariant_definable (level : ℕ) :
    Polarity.pi-[level + 2]-Predicate
      (SigmaSubstitutionInvariant (V := V) level) := by
  letI : SigmaPiDelta.delta-[level + 2]-Relation₃
      (SigmaTrue level : V → V → V → Prop) := by
    exact sigma_definable_delta_succ (sigmaTrue_definable level)
  letI : SigmaPiDelta.delta-[1]-Relation₅
      (IsSubstitutionEnvironment (V := V)) :=
    isSubstitutionEnvironment_definable
  unfold SigmaSubstitutionInvariant
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.imp
    · exact HierarchySymbol.Definable.of_deltaOne (by definability)
    · apply HierarchySymbol.Definable.imp
      · exact HierarchySymbol.Definable.of_deltaOne (by definability)
      · apply HierarchySymbol.Definable.imp
        · exact HierarchySymbol.Definable.of_deltaOne (by definability)
        · apply HierarchySymbol.Definable.imp
          · exact HierarchySymbol.Definable.of_deltaOne (by definability)
          · apply HierarchySymbol.Definable.biconditional
            · definability
            · definability

/-- Simultaneous coded substitution is interpreted by the induced semantic
bound environment.  `lh bound = m` is essential: below a quantifier it is
what makes bound-shifting of substituting terms semantically sound. -/
theorem sigmaTrue_subst_iff_of_isSubstitutionEnvironment (level : ℕ)
    {arity bound free m w subBound p : V}
    (hw : IsSemitermVec ℒₒᵣ arity m w)
    (hboundLen : lh bound = m)
    (hsub : IsSubstitutionEnvironment bound free arity w subBound)
    (hp : IsSemiformula ℒₒᵣ arity p)
    (hdom : IsSigmaCode ℒₒᵣ (levelCode level) p) :
    SigmaTrue level bound free (subst ℒₒᵣ w p) ↔
      SigmaTrue level subBound free p := by
  induction level generalizing arity bound free m w subBound p with
  | zero =>
      have hqf := quantifierFree_of_isSigmaCode_zero hdom
      simpa only [sigmaTrue_zero] using
        qfTrue_subst_iff_of_isSubstitutionBound
          hsub.1 hsub.2.2.2.2.2 hp hqf
  | succ level ih =>
      have piSub : ∀ {arity bound free m w subBound p : V},
          IsSemitermVec ℒₒᵣ arity m w →
          lh bound = m →
          IsSubstitutionEnvironment bound free arity w subBound →
          IsSemiformula ℒₒᵣ arity p →
          IsPiCode ℒₒᵣ (levelCode level) p →
          (PiTrue level bound free (subst ℒₒᵣ w p) ↔
            PiTrue level subBound free p) := by
        intro arity bound free m w subBound p hw hboundLen hsub hp hpPi
        have hpSub : IsPiCode ℒₒᵣ (levelCode level) (subst ℒₒᵣ w p) :=
          hpPi.subst hp hw
        have hneg : IsSigmaCode ℒₒᵣ (levelCode level) (neg ℒₒᵣ p) :=
          (isSigmaCode_neg_iff hpPi.1).mpr hpPi
        rw [piTrue_iff, and_iff_right hpSub,
          piTrue_iff, and_iff_right hpPi,
          ← substs_neg hp hw]
        exact not_congr (ih hw hboundLen hsub hp.neg hneg)
      have hmain : ∀ q : V, IsUFormula ℒₒᵣ q →
          SigmaSubstitutionInvariant (V := V) (level + 1) q := by
        apply uformula_inductionInPeanoModel
            (L := ℒₒᵣ) (sigmaSubstitutionInvariant_definable (level + 1))
        · intro k R terms hR hterms arity bound free m w subBound
            hp hw hboundLen hsub hdom
          have hqf : IsQuantifierFreeCode (^rel k R terms) := by
            simp [IsQuantifierFreeCode, hR, hterms]
          have hqfSub := hqf.subst hp hw
          rw [sigmaTrue_succ_qf_iff level hqfSub,
            sigmaTrue_succ_qf_iff level hqf]
          exact qfTrue_subst_iff_of_isSubstitutionBound
            hsub.1 hsub.2.2.2.2.2 hp hqf
        · intro k R terms hR hterms arity bound free m w subBound
            hp hw hboundLen hsub hdom
          have hqf : IsQuantifierFreeCode (^nrel k R terms) := by
            simp [IsQuantifierFreeCode, hR, hterms]
          have hqfSub := hqf.subst hp hw
          rw [sigmaTrue_succ_qf_iff level hqfSub,
            sigmaTrue_succ_qf_iff level hqf]
          exact qfTrue_subst_iff_of_isSubstitutionBound
            hsub.1 hsub.2.2.2.2.2 hp hqf
        · intro arity bound free m w subBound hp hw hboundLen hsub hdom
          have hqf : IsQuantifierFreeCode (^⊤ : V) := by simp
          have hqfSub := hqf.subst hp hw
          rw [sigmaTrue_succ_qf_iff level hqfSub,
            sigmaTrue_succ_qf_iff level hqf]
          exact qfTrue_subst_iff_of_isSubstitutionBound
            hsub.1 hsub.2.2.2.2.2 hp hqf
        · intro arity bound free m w subBound hp hw hboundLen hsub hdom
          have hqf : IsQuantifierFreeCode (^⊥ : V) := by simp
          have hqfSub := hqf.subst hp hw
          rw [sigmaTrue_succ_qf_iff level hqfSub,
            sigmaTrue_succ_qf_iff level hqf]
          exact qfTrue_subst_iff_of_isSubstitutionBound
            hsub.1 hsub.2.2.2.2.2 hp hqf
        · intro p q hpU hqU ihp ihq arity bound free m w subBound
            hpq hw hboundLen hsub hdom
          have hpqSem := IsSemiformula.and.mp hpq
          have hparts := (isSigmaCode_and_iff hpU hqU).mp hdom
          rw [substs_and hpU hqU,
            sigmaTrue_and_iff (hpqSem.1.subst hw).isUFormula
              (hpqSem.2.subst hw).isUFormula,
            sigmaTrue_and_iff hpU hqU,
            ihp arity bound free m w subBound hpqSem.1 hw hboundLen hsub
              hparts.1,
            ihq arity bound free m w subBound hpqSem.2 hw hboundLen hsub
              hparts.2]
        · intro p q hpU hqU ihp ihq arity bound free m w subBound
            hpq hw hboundLen hsub hdom
          have hpqSem := IsSemiformula.or.mp hpq
          have hparts := (isSigmaCode_or_iff hpU hqU).mp hdom
          have hpSub := hparts.1.subst hpqSem.1 hw
          have hqSub := hparts.2.subst hpqSem.2 hw
          rw [substs_or hpU hqU,
            sigmaTrue_or_iff (hpqSem.1.subst hw).isUFormula
              (hpqSem.2.subst hw).isUFormula hpSub hqSub,
            sigmaTrue_or_iff hpU hqU hparts.1 hparts.2,
            ihp arity bound free m w subBound hpqSem.1 hw hboundLen hsub
              hparts.1,
            ihq arity bound free m w subBound hpqSem.2 hw hboundLen hsub
              hparts.2]
        · intro q hqU ihq arity bound free m w subBound hpall hw
            hboundLen hsub hdom
          have hqSem := IsSemiformula.all.mp hpall
          have hdom' : IsSigmaCode ℒₒᵣ
              (levelCode level + 1) (^∀ q) := by
            simpa only [levelCode_succ] using hdom
          have hparts :=
            (isSigmaCode_all_succ_iff (n := levelCode level) hqU).mp hdom'
          have hpiall : IsPiCode ℒₒᵣ (levelCode level) (^∀ q) :=
            (isPiCode_all_iff hqU).mpr hparts
          rw [substs_all hqU,
            sigmaTrue_succ_all_iff (hqSem.subst hw.qVec).isUFormula,
            sigmaTrue_succ_all_iff hqU]
          simpa only [substs_all hqU] using
            (piSub hw hboundLen hsub hpall hpiall)
        · intro q hqU ihq arity bound free m w subBound hpex hw
            hboundLen hsub hdom
          have hqSem := IsSemiformula.exs.mp hpex
          have hbodyRaw : IsSigmaCode ℒₒᵣ (levelCode level + 1) q :=
            (isSigmaCode_exs_succ_iff hqU).mp
              (by simpa only [levelCode_succ] using hdom)
          have hbody : IsSigmaCode ℒₒᵣ (levelCode (level + 1)) q := by
            simpa only [levelCode_succ] using hbodyRaw
          rw [substs_ex hqU,
            sigmaTrue_exs_iff (hqSem.subst hw.qVec).isUFormula,
            sigmaTrue_exs_iff hqU]
          constructor
          · rintro ⟨a, ha⟩
            have hsubQ := isSubstitutionEnvironment_qVec_seqCons
              (a := a) hw hboundLen hsub
            refine ⟨a, (ihq (arity + 1) (bound ⁀' a) free (m + 1)
              (qVec ℒₒᵣ w) (subBound ⁀' a) hqSem hw.qVec ?_ hsubQ
              hbody).mp ha⟩
            simp [hsub.2.1, hboundLen]
          · rintro ⟨a, ha⟩
            have hsubQ := isSubstitutionEnvironment_qVec_seqCons
              (a := a) hw hboundLen hsub
            refine ⟨a, (ihq (arity + 1) (bound ⁀' a) free (m + 1)
              (qVec ℒₒᵣ w) (subBound ⁀' a) hqSem hw.qVec ?_ hsubQ
              hbody).mpr ha⟩
            simp [hsub.2.1, hboundLen]
      exact hmain p hp.isUFormula arity bound free m w subBound hp hw
        hboundLen hsub hdom

/-- Dual version of simultaneous substitution transport. -/
theorem piTrue_subst_iff_of_isSubstitutionEnvironment (level : ℕ)
    {arity bound free m w subBound p : V}
    (hw : IsSemitermVec ℒₒᵣ arity m w)
    (hboundLen : lh bound = m)
    (hsub : IsSubstitutionEnvironment bound free arity w subBound)
    (hp : IsSemiformula ℒₒᵣ arity p)
    (hdom : IsPiCode ℒₒᵣ (levelCode level) p) :
    PiTrue level bound free (subst ℒₒᵣ w p) ↔
      PiTrue level subBound free p := by
  have hpSub := hdom.subst hp hw
  have hneg := (isSigmaCode_neg_iff hdom.1).mpr hdom
  rw [piTrue_iff, and_iff_right hpSub,
    piTrue_iff, and_iff_right hdom,
    ← substs_neg hp hw]
  exact not_congr
    (sigmaTrue_subst_iff_of_isSubstitutionEnvironment level
      hw hboundLen hsub hp.neg hneg)

/-! ## Uniform successor truth on the quantifier-group-bounded domain -/

/-- The shift law in the exact orientation-independent form consumed by the
abstract soundness interface.  Successor Sigma truth is reduced to the
appropriate lower Sigma or Pi presentation using fixed-level coherence. -/
theorem sigmaTrue_succ_shift_iff (n : ℕ)
    {bound shifted free p : V}
    (hfree : IsFreeTail shifted free)
    (hbounded : QuantifierBoundedCode ℒₒᵣ (levelCode n) p) :
    SigmaTrue (n + 1) bound shifted (shift ℒₒᵣ p) ↔
      SigmaTrue (n + 1) bound free p := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp hbounded with hs | hp
  · have hsShift := (isSigmaCode_shift_iff hs.1).mpr hs
    exact (sigmaTrue_succ_iff_of_isSigmaCode n hsShift).trans <|
      (sigmaTrue_shift_iff_of_isFreeTail n hfree hs).trans <|
        (sigmaTrue_succ_iff_of_isSigmaCode n hs).symm
  · have hpShift := (isPiCode_shift_iff hp.1).mpr hp
    exact (sigmaTrue_succ_iff_piTrue_of_isPiCode n hpShift).trans <|
      (piTrue_shift_iff_of_isFreeTail n hfree hp).trans <|
        (sigmaTrue_succ_iff_piTrue_of_isPiCode n hp).symm

/-- Simultaneous substitution transport for the uniform successor truth
predicate, independent of which oriented rank realizes the quantifier-group
bound. -/
theorem sigmaTrue_succ_subst_iff_of_isSubstitutionEnvironment (n : ℕ)
    {arity bound free m w subBound p : V}
    (hw : IsSemitermVec ℒₒᵣ arity m w)
    (hboundLen : lh bound = m)
    (hsub : IsSubstitutionEnvironment bound free arity w subBound)
    (hp : IsSemiformula ℒₒᵣ arity p)
    (hbounded : QuantifierBoundedCode ℒₒᵣ (levelCode n) p) :
    SigmaTrue (n + 1) bound free (subst ℒₒᵣ w p) ↔
      SigmaTrue (n + 1) subBound free p := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp hbounded with hs | hpi
  · have hsSub := hs.subst hp hw
    exact (sigmaTrue_succ_iff_of_isSigmaCode n hsSub).trans <|
      (sigmaTrue_subst_iff_of_isSubstitutionEnvironment n
        hw hboundLen hsub hp hs).trans <|
          (sigmaTrue_succ_iff_of_isSigmaCode n hs).symm
  · have hpiSub := hpi.subst hp hw
    exact (sigmaTrue_succ_iff_piTrue_of_isPiCode n hpiSub).trans <|
      (piTrue_subst_iff_of_isSubstitutionEnvironment n
        hw hboundLen hsub hp hpi).trans <|
          (sigmaTrue_succ_iff_piTrue_of_isPiCode n hpi).symm

end LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution
