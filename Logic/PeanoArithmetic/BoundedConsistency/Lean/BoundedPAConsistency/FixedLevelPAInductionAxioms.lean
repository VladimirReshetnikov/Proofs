import BoundedPAConsistency.FixedLevelPAInduction
import BoundedPAConsistency.FixedLevelTruthLaws

set_option maxHeartbeats 1000000
set_option maxRecDepth 5000

/-!
# Truth of internally recognized PA induction axioms

The induction recognizer may return a nonstandard universal-closure length
and nonstandard formula codes.  This file never decodes them.  It first proves
truth of the recovered raw induction body using fixed-level substitution and
PA induction, then introduces the internally iterated universal closure by a
second represented induction invariant.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxioms

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution
open LeanProofs.BoundedPAConsistency.FixedLevelTruthLaws
open LeanProofs.BoundedPAConsistency.FixedLevelPAInduction

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

/-! The two standard substitution terms are evaluated directly below.  These
small quotation lemmas are local so this induction-axiom layer does not
depend on the separate finite-PA-minus axiom module. -/

private noncomputable def quotedBoundAssignment {k : ℕ}
    (bound : V) (i : Fin k) : V :=
  znth bound (boundPosition bound (↑(i : ℕ) : V))

private noncomputable def quotedFreeAssignment (free : V) (x : ℕ) : V :=
  znth free (x : V)

private theorem termValue_quote_iff_val {k : ℕ} (bound free : V)
    (t : SyntacticSemiterm ℒₒᵣ k) :
    termValue bound free
        (⌜t⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val =
      t.val (quotedBoundAssignment bound) (quotedFreeAssignment free) := by
  induction t with
  | bvar i => simp [quotedBoundAssignment]
  | fvar x => simp [quotedFreeAssignment]
  | func f v ih =>
      cases f with
      | zero =>
          change termValue bound free
              (^func 0 (Arithmetic.zeroIndex : V) 0) = 0
          simp
      | one =>
          change termValue bound free
              (^func 0 (Arithmetic.oneIndex : V) 0) = 1
          simp
      | add =>
          have hv0 : IsUTerm ℒₒᵣ
              (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ
              (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.addIndex : V)
                ?[(⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val,
                  (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) +
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_add hv0 hv1, ih 0, ih 1]
      | mul =>
          have hv0 : IsUTerm ℒₒᵣ
              (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ
              (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.mulIndex : V)
                ?[(⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val,
                  (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) *
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_mul hv0 hv1, ih 0, ih 1]

private theorem quotedBoundAssignment_seqCons {k : ℕ} {bound : V}
    (hbound : Arithmetic.Seq bound) (hlen : lh bound = (k : V)) (a : V) :
    quotedBoundAssignment (k := k + 1) (bound ⁀' a) =
      (a :> quotedBoundAssignment (k := k) bound) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      change znth (bound ⁀' a)
          (boundPosition (bound ⁀' a) (0 : V)) = a
      simpa [termValue_bvar] using
        (termValue_bvar_zero_seqCons (free := (0 : V)) (a := a) hbound)
  | succ i =>
      have hi : (↑(i : ℕ) : V) < (k : V) := by
        simpa [← numeral_eq_natCast_app] using
          (Arithmetic.numeral_lt_numeral_iff (M := V)).mpr i.isLt
      have hpos : boundPosition bound (↑(i : ℕ) : V) < lh bound := by
        simp only [boundPosition, hlen]
        exact tsub_lt_self (lt_of_le_of_lt (by simp) hi) (by simp)
      change znth (bound ⁀' a)
          (boundPosition (bound ⁀' a) (↑(i.succ : ℕ) : V)) =
        znth bound (boundPosition bound (↑(i : ℕ) : V))
      rw [show boundPosition (bound ⁀' a) (↑(i.succ : ℕ) : V) =
          boundPosition bound (↑(i : ℕ) : V) by
        simp [boundPosition, hbound],
        znth_seqCons_of_lt hbound hpos]

/-! ## Rank inversion for the exact induction-body constructors -/

private lemma quantifierBoundedCode_imp_parts {bound p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ bound (imp ℒₒᵣ p q)) :
    QuantifierBoundedCode ℒₒᵣ bound p ∧
      QuantifierBoundedCode ℒₒᵣ bound q := by
  have hshape : imp ℒₒᵣ p q = neg ℒₒᵣ p ^⋎ q := rfl
  rw [hshape] at h
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · have hparts := (isSigmaCode_or_iff hp.neg hq).mp hs
    exact ⟨(QuantifierBoundedCode.neg_iff hp).mp
        hparts.1.quantifierBounded,
      hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_or_iff hp.neg hq).mp hpi
    exact ⟨(QuantifierBoundedCode.neg_iff hp).mp
        hparts.1.quantifierBounded,
      hparts.2.quantifierBounded⟩

private lemma quantifierBoundedCode_all_body {bound p : V}
    (hp : IsUFormula ℒₒᵣ p)
    (h : QuantifierBoundedCode ℒₒᵣ bound (^∀ p)) :
    QuantifierBoundedCode ℒₒᵣ bound p := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · rcases zero_or_succ bound with rfl | ⟨level, rfl⟩
    · exact (not_isSigmaCode_all_zero hp hs).elim
    · have hpPi : IsPiCode ℒₒᵣ level p :=
        ((isSigmaCode_all_succ_iff hp).mp hs).1
      exact (hpPi.mono (by simp)).quantifierBounded
  · exact ((isPiCode_all_iff hp).mp hpi).1.quantifierBounded

private theorem sigmaTrue_succ_imp_iff_of_quantifierBoundedCode (n : ℕ)
    {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (imp ℒₒᵣ p q)) :
    SigmaTrue (n + 1) bound free (imp ℒₒᵣ p q) ↔
      (SigmaTrue (n + 1) bound free p →
        SigmaTrue (n + 1) bound free q) := by
  have hparts := quantifierBoundedCode_imp_parts hp hq h
  have hshape : imp ℒₒᵣ p q = neg ℒₒᵣ p ^⋎ q := rfl
  rw [hshape,
    sigmaTrue_succ_or_iff_of_quantifierBoundedCode n (by simpa [hshape] using h),
    sigmaTrue_succ_neg_iff_of_quantifierBoundedCode n hparts.1]
  tauto

/-! ## Singleton simultaneous substitution -/

/-- A one-entry substitution vector installs its evaluated entry as the sole
de Bruijn value.  Unlike the calculus adapter, the term may itself contain
bound variables; this is needed for the successor term `#0 + 1`. -/
private theorem sigmaTrue_subst_one (level : ℕ)
    {bound free m w p value : V}
    (hbound : Arithmetic.Seq bound) (hfree : Arithmetic.Seq free)
    (hw : IsSemitermVec ℒₒᵣ 1 m w) (hlen : lh bound = m)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (hvalue : termValue bound free w.[0] = value)
    (hdom : IsSigmaCode ℒₒᵣ (levelCode (V := V) level) p) :
    SigmaTrue level bound free (subst ℒₒᵣ w p) ↔
      SigmaTrue level (0 ⁀' value) free p := by
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hsub : IsSubstitutionEnvironment
      bound free (1 : V) w (0 ⁀' value) := by
    refine ⟨hw.isUTerm, hbound, hfree, hzeroSeq.seqCons value, ?_, ?_⟩
    · rw [Seq.lh_seqCons _ hzeroSeq, hlhZero]
      simp
    · intro z hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      have hlookup : znth (0 ⁀' value)
          (boundPosition (0 ⁀' value) 0) = value := by
        simpa [termValue_bvar] using
          (termValue_bvar_zero_seqCons (free := free) (a := value) hzeroSeq)
      simpa [hvalue] using hlookup
  exact sigmaTrue_subst_iff_of_isSubstitutionEnvironment level
    hw hlen hsub hp hdom

/-! ## Truth of the recovered raw induction body -/

/-- Every bounded raw induction body recovered by the internal recognizer is
true under every genuine free-variable environment. -/
theorem sigmaTrue_succ_indBodyVal (n : ℕ) {K free : V}
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hbody : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (indBodyVal K))
    (hfree : Arithmetic.Seq free) :
    SigmaTrue (n + 1) 0 free (indBodyVal K) := by
  let baseCode : V := subst ℒₒᵣ (inductionZeroVec (V := V)) K
  let nextCode : V := subst ℒₒᵣ (inductionSuccVec (V := V)) K
  let stepCode : V := imp ℒₒᵣ K nextCode
  let stepAll : V := ^∀ stepCode
  let conclusion : V := ^∀ K
  let tail : V := imp ℒₒᵣ stepAll conclusion
  have hzeroVec : IsSemitermVec ℒₒᵣ 1 0
      (inductionZeroVec (V := V)) := by
    dsimp [inductionZeroVec]
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)
  have hsuccVec : IsSemitermVec ℒₒᵣ 1 1
      (inductionSuccVec (V := V)) := by
    dsimp [inductionSuccVec]
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)
  have hbaseU : IsUFormula ℒₒᵣ baseCode :=
    (hK.subst hzeroVec).isUFormula
  have hnextU : IsUFormula ℒₒᵣ nextCode :=
    (hK.subst hsuccVec).isUFormula
  have hstepU : IsUFormula ℒₒᵣ stepCode := by
    simp [stepCode, hK.isUFormula, hnextU]
  have hstepAllU : IsUFormula ℒₒᵣ stepAll := by
    simp [stepAll, hstepU]
  have hconclusionU : IsUFormula ℒₒᵣ conclusion := by
    simp [conclusion, hK.isUFormula]
  have htailU : IsUFormula ℒₒᵣ tail := by
    simp [tail, hstepAllU, hconclusionU]
  have hshape : indBodyVal K = imp ℒₒᵣ baseCode tail := rfl
  have hrootBound : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (imp ℒₒᵣ baseCode tail) := by
    simpa only [hshape] using hbody
  have hrootParts := quantifierBoundedCode_imp_parts hbaseU htailU hrootBound
  have htailParts := quantifierBoundedCode_imp_parts
    hstepAllU hconclusionU hrootParts.2
  have hstepBound := quantifierBoundedCode_all_body hstepU htailParts.1
  have hstepParts := quantifierBoundedCode_imp_parts
    hK.isUFormula hnextU hstepBound
  have hconclusionBodyBound := quantifierBoundedCode_all_body
    hK.isUFormula htailParts.2
  have hKBound : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) K := hconclusionBodyBound
  have hKDom := sigmaDomain_of_bounded n hKBound
  have hzeroValue : termValue (0 : V) free
      (inductionZeroVec (V := V)).[0] = 0 := by
    simpa [inductionZeroVec] using
      (termValue_quote_iff_val (V := V) (0 : V) free
        (‘0’ : ArithmeticSemiterm ℕ 0))
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hzeroSub := sigmaTrue_subst_one (n + 1)
    hzeroSeq hfree hzeroVec hlhZero hK hzeroValue hKDom
  rw [hshape,
    sigmaTrue_succ_imp_iff_of_quantifierBoundedCode n hbaseU htailU hrootBound]
  intro hbase
  rw [sigmaTrue_succ_imp_iff_of_quantifierBoundedCode n
    hstepAllU hconclusionU hrootParts.2]
  intro hstep
  rw [sigmaTrue_succ_all_iff_of_quantifierBoundedCode n htailParts.2]
  apply sigmaTrue_succ_induction (n + 1)
  · exact hzeroSub.mp (by simpa [baseCode] using hbase)
  · intro x hx
    have hstepAt : SigmaTrue (n + 1) (0 ⁀' x) free stepCode :=
      (sigmaTrue_succ_all_iff_of_quantifierBoundedCode n
        htailParts.1).mp hstep x
    have hnext : SigmaTrue (n + 1) (0 ⁀' x) free nextCode :=
      (sigmaTrue_succ_imp_iff_of_quantifierBoundedCode n
        hK.isUFormula hnextU hstepBound).mp hstepAt hx
    have hboundX : Arithmetic.Seq (0 ⁀' x) := hzeroSeq.seqCons x
    have hlenX : lh (0 ⁀' x) = 1 := by
      rw [Seq.lh_seqCons _ hzeroSeq, hlhZero]
      simp
    have hsuccValue : termValue (0 ⁀' x) free
        (inductionSuccVec (V := V)).[0] = x + 1 := by
      have hval := termValue_quote_iff_val (V := V)
        (0 ⁀' x) free (‘#0 + 1’ : ArithmeticSemiterm ℕ 1)
      simpa [inductionSuccVec,
        quotedBoundAssignment_seqCons (k := 0) hzeroSeq hlhZero x] using hval
    have hsuccSub := sigmaTrue_subst_one (n + 1)
      hboundX hfree hsuccVec hlenX hK hsuccValue hKDom
    exact hsuccSub.mp (by simpa [nextCode] using hnext)

/-! ## Independence from free environments for closed codes -/

private lemma sigma_definable_delta_succ
    {P : (Fin k → V) → Prop} {level : ℕ}
    (h : Polarity.sigma-[level].Definable P) :
    SigmaPiDelta.delta-[level + 1].Definable P := by
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

private def FreeEnvironmentInvariant
    (n : ℕ) (bound p k : V) : Prop :=
  ∀ free, Arithmetic.Seq free → lh free = k →
    (SigmaTrue (n + 1) bound free p ↔
      SigmaTrue (n + 1) bound 0 p)

private lemma freeEnvironmentInvariant_definable
    (n : ℕ) (bound p : V) :
    Polarity.pi-[n + 3]-Predicate
      (FreeEnvironmentInvariant (V := V) n bound p) := by
  letI : SigmaPiDelta.delta-[n + 3]-Relation₃
      (SigmaTrue (V := V) (n + 1)) := by
    have h : Polarity.sigma-[n + 2]-Relation₃
        (SigmaTrue (V := V) (n + 1)) :=
      sigmaTrue_definable (n + 1)
    exact sigma_definable_delta_succ h
  unfold FreeEnvironmentInvariant
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.imp
    · exact HierarchySymbol.Definable.of_deltaOne (by definability)
    · apply HierarchySymbol.Definable.biconditional
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance) <;> simp
      · apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance) <;> simp

/-- A shift-fixed bounded code has the same truth value under any two genuine
free-variable environments.  The environments may have nonstandard length;
the proof peels their semantic heads by represented PA induction. -/
theorem sigmaTrue_succ_free_independent (n : ℕ)
    {bound p free₁ free₂ : V}
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p)
    (hshift : shift ℒₒᵣ p = p)
    (hfree₁ : Arithmetic.Seq free₁) (hfree₂ : Arithmetic.Seq free₂) :
    SigmaTrue (n + 1) bound free₁ p ↔
      SigmaTrue (n + 1) bound free₂ p := by
  have hmain : ∀ k : V,
      FreeEnvironmentInvariant (V := V) n bound p k := by
    letI : V↓[ℒₒᵣ] ⊧* ISigma (n + 3) := models_of_subtheory hPA
    apply InductionOnHierarchy.succ_induction (V := V)
      (P := FreeEnvironmentInvariant (V := V) n bound p)
      Polarity.pi (n + 3)
    · exact freeEnvironmentInvariant_definable n bound p
    · intro free hfree hlen
      have hzero : free = (∅ : V) := hfree.isempty_of_lh_eq_zero hlen
      have hempty : (∅ : V) = 0 := emptyset_def
      subst free
      simpa [hempty]
    · intro k ih free hfree hlen
      rcases exists_isFreeTail hfree with ⟨tail, htail, htailLen, hfreeTail⟩
      have htailLen' : lh tail = k := by
        simpa [hlen] using htailLen
      calc
        SigmaTrue (n + 1) bound free p ↔
            SigmaTrue (n + 1) bound free (shift ℒₒᵣ p) := by
              rw [hshift]
        _ ↔ SigmaTrue (n + 1) bound tail p :=
          sigmaTrue_succ_shift_iff_of_quantifierBoundedCode
            n hfreeTail hp
        _ ↔ SigmaTrue (n + 1) bound 0 p := ih tail htail htailLen'
  exact (hmain (lh free₁) free₁ hfree₁ rfl).trans
    (hmain (lh free₂) free₂ hfree₂ rfl).symm

/-! ## Reversing a bound tuple into the recognizer's free variables -/

/-- For every genuine length-`m` de Bruijn environment, there is a genuine
free environment whose first `m` entries make `fvarVec m` induce exactly that
bound environment.  The reversal is forced by `boundPosition`; the Skolem
sequence construction works equally for nonstandard `m`. -/
theorem exists_fvarVec_substitutionEnvironment {m base : V}
    (hbase : Arithmetic.Seq base) (hlen : lh base = m) :
    ∃ free, Arithmetic.Seq free ∧
      IsSubstitutionEnvironment
        (0 : V) free m (fvarVec m) base := by
  let R : V → V → Prop := fun i y ↦
    y = znth base (boundPosition base i)
  have hR : 𝚺₁-Relation R := by
    dsimp [R, boundPosition]
    definability
  have htotal : ∀ i < m, ∃ y, R i y := by
    intro i hi
    exact ⟨znth base (boundPosition base i), rfl⟩
  rcases sigmaOne_skolem_seq hR htotal with
    ⟨free, hfree, hfreeLen, hmem⟩
  have hfvar : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
    isSemitermVec_fvarVec m
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  refine ⟨free, hfree, hfvar.isUTerm, hzeroSeq, hfree, hbase,
    hlen, ?_⟩
  intro z hz
  have hzfree : z < lh free := by simpa [hfreeLen] using hz
  have hy := hmem z (znth free z) (hfree.znth hzfree)
  rw [nth_fvarVec m z hz, termValue_fvar]
  simpa [R] using hy.symm

/-- Truth of the recovered `indBodyVal` transfers back through `fvarVec` to
the nonstandard closure body `b`, under every length-`m` bound environment. -/
theorem sigmaTrue_succ_inductionClosureBody (n : ℕ)
    {m b K free base : V}
    (hbU : IsUFormula ℒₒᵣ b) (hshift : shift ℒₒᵣ b = b)
    (hbv : bv ℒₒᵣ b = m)
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hsubst : subst ℒₒᵣ (fvarVec m) b = indBodyVal K)
    (hbBound : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) b)
    (hbodyBound : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (indBodyVal K))
    (hfree : Arithmetic.Seq free) (hbase : Arithmetic.Seq base)
    (hlen : lh base = m) :
    SigmaTrue (n + 1) base free b := by
  rcases exists_fvarVec_substitutionEnvironment hbase hlen with
    ⟨codedFree, hcodedFree, hsub⟩
  have hbSemi : IsSemiformula ℒₒᵣ m b :=
    ⟨hbU, by simp [hbv]⟩
  have hfvar : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
    isSemitermVec_fvarVec m
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have htransport :=
    sigmaTrue_subst_iff_of_isSubstitutionEnvironment (n + 1)
      hfvar hlhZero hsub hbSemi (sigmaDomain_of_bounded n hbBound)
  have hindBody : SigmaTrue (n + 1) 0 codedFree (indBodyVal K) :=
    sigmaTrue_succ_indBodyVal n hK hbodyBound hcodedFree
  have hbCoded : SigmaTrue (n + 1) base codedFree b :=
    htransport.mp (by simpa only [hsubst] using hindBody)
  exact (sigmaTrue_succ_free_independent n hbBound hshift
    hcodedFree hfree).mp hbCoded

/-! ## Internally iterated universal closure -/

/-- At stage `k`, the remaining `k` quantifiers are true under every genuine
bound environment whose length, together with `k`, is the original closure
length `m`.  Carrying the rank hypothesis in the invariant supplies the
premise required by the fixed-level universal Tarski clause at successor
stages. -/
private def UniversalClosureInvariant
    (n : ℕ) (m b free k : V) : Prop :=
  QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) (qqAlls b k) →
    ∀ base, Arithmetic.Seq base → lh base + k = m →
      SigmaTrue (n + 1) base free (qqAlls b k)

private lemma universalClosureInvariant_definable
    (n : ℕ) (m b free : V) :
    Polarity.pi-[n + 3]-Predicate
      (UniversalClosureInvariant (V := V) n m b free) := by
  letI : SigmaPiDelta.delta-[n + 3]-Relation₃
      (SigmaTrue (V := V) (n + 1)) := by
    have h : Polarity.sigma-[n + 2]-Relation₃
        (SigmaTrue (V := V) (n + 1)) :=
      sigmaTrue_definable (n + 1)
    exact sigma_definable_delta_succ h
  unfold UniversalClosureInvariant
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.imp
    · exact HierarchySymbol.Definable.of_deltaOne (by definability)
    · apply HierarchySymbol.Definable.imp
      · exact HierarchySymbol.Definable.of_deltaOne (by definability)
      · exact HierarchySymbol.Definable.of_delta (by
          apply HierarchySymbol.DefinableRel₃.comp
            (show SigmaPiDelta.delta-[n + 3]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance)
          · simp
          · simp
          · exact HierarchySymbol.DefinableFunction₂.comp
              (HierarchySymbol.DefinableFunction.const b)
              (HierarchySymbol.DefinableFunction.var 1))

/-- Fixed-level truth introduces an internally finite, possibly nonstandard,
block of leading universal quantifiers.  The body premise ranges over every
genuine bound environment of the internally specified length. -/
theorem sigmaTrue_succ_qqAlls_intro (n : ℕ) {m b free : V}
    (hclosure : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (qqAlls b m))
    (_hfree : Arithmetic.Seq free)
    (hbody : ∀ base, Arithmetic.Seq base → lh base = m →
      SigmaTrue (n + 1) base free b) :
    SigmaTrue (n + 1) 0 free (qqAlls b m) := by
  have hmain : ∀ k : V,
      UniversalClosureInvariant (V := V) n m b free k := by
    letI : V↓[ℒₒᵣ] ⊧* ISigma (n + 3) := models_of_subtheory hPA
    apply InductionOnHierarchy.succ_induction (V := V)
      (P := UniversalClosureInvariant (V := V) n m b free)
      Polarity.pi (n + 3)
    · exact universalClosureInvariant_definable n m b free
    · intro _hbounded base hbase hlen
      simpa using hbody base hbase (by simpa using hlen)
    · intro k ih hbounded base hbase hlen
      rw [qqAlls_succ] at hbounded ⊢
      have hchildU : IsUFormula ℒₒᵣ (qqAlls b k) := by
        simpa using hbounded.1
      have hchildBound : QuantifierBoundedCode ℒₒᵣ
          (levelCode (V := V) n) (qqAlls b k) :=
        quantifierBoundedCode_all_body hchildU hbounded
      apply (sigmaTrue_succ_all_iff_of_quantifierBoundedCode
        n hbounded).mpr
      intro a
      apply ih hchildBound (base ⁀' a) (hbase.seqCons a)
      rw [Seq.lh_seqCons _ hbase]
      simpa [add_assoc, add_comm, add_left_comm] using hlen
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  exact hmain m hclosure 0 hzeroSeq (by simp [hlhZero])

/-! ## Soundness of the internal induction-axiom recognizer -/

/-- Every internally recognized PA induction axiom whose quantifier rank is
bounded by the external level `n` is true for fixed-level Sigma truth.  Both
the recovered formula and the number of closing quantifiers may be
nonstandard elements of the ambient model. -/
theorem sigmaTrue_succ_of_inductionUnivR (n : ℕ) {p free : V}
    (hind : InductionUnivR p)
    (hp : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p)
    (hfree : Arithmetic.Seq free) :
    SigmaTrue (n + 1) 0 free p := by
  rcases bounded_inductionUnivR_data hind hp with
    ⟨m, b, K, hpcode, hbU, hshift, hbv, hK, hsubst,
      hbBound, hbodyBound, _hKBound⟩
  have hclosure : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (qqAlls b m) := by
    simpa only [← hpcode] using hp
  rw [hpcode]
  apply sigmaTrue_succ_qqAlls_intro n hclosure hfree
  intro base hbase hlen
  exact sigmaTrue_succ_inductionClosureBody n hbU hshift hbv hK hsubst
    hbBound hbodyBound hfree hbase hlen

end LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxioms
