import BoundedPAConsistency.DynamicTruthSuccessorLaws
import BoundedPAConsistency.FixedLevelPAInductionAxioms
import BoundedPAConsistency.FixedLevelPAMinusAxioms

set_option maxHeartbeats 1000000
set_option maxRecDepth 5000

/-!
# Semantic PA-axiom soundness for a model-coded truth relation

The fixed-level development proves PA-axiom soundness for `SigmaTrue n`.
At a nonstandard hierarchy index the truth predicate is instead supplied by
a represented arithmetic formula.  This file separates the part of the old
argument that is independent of the concrete truth implementation.

The three interfaces below are precisely the uses of full PA induction in
the proof:

* induction of the semantic predicate recovered from an induction axiom;
* removal of an internally long free-variable environment from a closed
  formula code;
* introduction of an internally long block of universal quantifiers.

Everything else follows from the dynamic Tarski laws and the represented
simultaneous-substitution field.  Keeping these obligations explicit is
useful for the fixed-source compiler: each interface can be realized by one
closed source induction axiom and then discharged after specialization by
`ModelCodedInductionAxiom`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.FixedLevelPAInduction
open LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxioms
open LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## The three model-induction interfaces -/

/-- Ordinary successor induction for the semantic predicate obtained by
placing the induction variable at the right-hand end of a coded bound
environment. -/
def SemanticInduction (Sat : V → V → V → Prop) : Prop :=
  ∀ {base free K : V},
    Sat (base ⁀' 0) free K →
    (∀ x, Sat (base ⁀' x) free K →
      Sat (base ⁀' (x + 1)) free K) →
    ∀ x, Sat (base ⁀' x) free K

/-- A shift-fixed bounded formula is insensitive to the chosen genuine
free-variable environment.  The fixed-source realization proves this by
induction on the internally coded environment length. -/
def FreeEnvironmentIndependence
    (level : V) (Sat : V → V → V → Prop) : Prop :=
  ∀ {bound p free₁ free₂ : V},
    QuantifierBoundedCode ℒₒᵣ level p →
    shift ℒₒᵣ p = p →
    Arithmetic.Seq free₁ → Arithmetic.Seq free₂ →
    (Sat bound free₁ p ↔ Sat bound free₂ p)

/-- Introduction of a possibly nonstandard block `qqAlls b m`.  The body is
required under every genuine bound environment of the advertised length. -/
def UniversalClosureIntroduction
    (level : V) (Sat : V → V → V → Prop) : Prop :=
  ∀ {m b free : V},
    QuantifierBoundedCode ℒₒᵣ level (qqAlls b m) →
    Arithmetic.Seq free →
    (∀ base, Arithmetic.Seq base → lh base = m →
      Sat base free b) →
    Sat 0 free (qqAlls b m)

/-! The induction vectors contain typed quotations, rather than plain
casts of standard codes.  This local adequacy lemma keeps that distinction
visible and prevents simplification from silently changing the code being
evaluated. -/

private theorem termValue_typedQuote_iff_val {k : ℕ} (bound free : V)
    (t : SyntacticSemiterm ℒₒᵣ k) :
    termValue bound free
        (⌜ t ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val =
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
              (⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ
              (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.addIndex : V)
                ?[(⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val,
                  (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) +
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_add hv0 hv1, ih 0, ih 1]
      | mul =>
          have hv0 : IsUTerm ℒₒᵣ
              (⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ
              (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val :=
            (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.mulIndex : V)
                ?[(⌜ v 0 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val,
                  (⌜ v 1 ⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).val]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) *
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_mul hv0 hv1, ih 0, ih 1]

/-! ## Rank inversion for the represented induction body -/

private lemma bounded_imp_parts {level p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (h : QuantifierBoundedCode ℒₒᵣ level (imp ℒₒᵣ p q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
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

private lemma bounded_all_body {level p : V}
    (hp : IsUFormula ℒₒᵣ p)
    (h : QuantifierBoundedCode ℒₒᵣ level (^∀ p)) :
    QuantifierBoundedCode ℒₒᵣ level p := by
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isSigmaCode_all_zero hp hs).elim
    · have hpPi : IsPiCode ℒₒᵣ level p :=
        ((isSigmaCode_all_succ_iff hp).mp hs).1
      exact (hpPi.mono (by simp)).quantifierBounded
  · exact ((isPiCode_all_iff hp).mp hpi).1.quantifierBounded

private theorem sat_imp_iff
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat) {bound free p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level (imp ℒₒᵣ p q)) :
    Sat bound free (imp ℒₒᵣ p q) ↔
      (Sat bound free p → Sat bound free q) := by
  have hparts := bounded_imp_parts hp hq hbounded
  have hshape : imp ℒₒᵣ p q = neg ℒₒᵣ p ^⋎ q := rfl
  rw [hshape, laws.or_iff (by simpa [hshape] using hbounded),
    laws.neg_iff hparts.1]
  tauto

/-! ## Arbitrary-base singleton substitution -/

/-- Specialize the represented simultaneous-substitution field to a
one-entry vector.  Unlike `AbstractSoundness.Laws.substs1_iff`, the
substituting term may refer to the current bound environment; this is needed
for the induction successor term `#0 + 1`. -/
theorem sat_subst_one
    {level : V} {Sat : V → V → V → Prop}
    (hsubstitution : ∀ q, SubstitutionInvariantAt Sat level q)
    {bound free m w p value : V}
    (hbound : Arithmetic.Seq bound) (hfree : Arithmetic.Seq free)
    (hw : IsSemitermVec ℒₒᵣ 1 m w) (hlen : lh bound = m)
    (hp : IsSemiformula ℒₒᵣ 1 p)
    (hvalue : termValue bound free w.[0] = value)
    (hdom : QuantifierBoundedCode ℒₒᵣ level p) :
    Sat bound free (subst ℒₒᵣ w p) ↔
      Sat (0 ⁀' value) free p := by
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
  exact hsubstitution p (0 ⁀' value) w m free bound 1
    hw hlen.symm hsub hp hdom

/-! ## The recovered induction body -/

/-- The raw induction body recognized inside PA is true for every semantic
relation satisfying the bounded Tarski clauses, full represented
substitution, and semantic successor induction. -/
theorem indBodyVal_true
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hsubstitution : ∀ q, SubstitutionInvariantAt Sat level q)
    (hinduction : SemanticInduction Sat)
    {K free : V}
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hbody : QuantifierBoundedCode ℒₒᵣ level (indBodyVal K))
    (hfree : Arithmetic.Seq free) :
    Sat 0 free (indBodyVal K) := by
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
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] :
        SemitermVec V ℒₒᵣ 1 1)
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
  have hrootBound : QuantifierBoundedCode ℒₒᵣ level
      (imp ℒₒᵣ baseCode tail) := by
    simpa only [hshape] using hbody
  have hrootParts := bounded_imp_parts hbaseU htailU hrootBound
  have htailParts := bounded_imp_parts
    hstepAllU hconclusionU hrootParts.2
  have hstepBound := bounded_all_body hstepU htailParts.1
  have hstepParts := bounded_imp_parts hK.isUFormula hnextU hstepBound
  have hKBound : QuantifierBoundedCode ℒₒᵣ level K :=
    bounded_all_body hK.isUFormula htailParts.2
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hzeroValue : termValue (0 : V) free
      (inductionZeroVec (V := V)).[0] = 0 := by
    simpa [inductionZeroVec] using
      (termValue_typedQuote_iff_val (V := V) (0 : V) free
        (‘0’ : ArithmeticSemiterm ℕ 0))
  have hzeroSub := sat_subst_one hsubstitution
    hzeroSeq hfree hzeroVec hlhZero hK hzeroValue hKBound
  rw [hshape, sat_imp_iff laws hbaseU htailU hrootBound]
  intro hbase
  rw [sat_imp_iff laws hstepAllU hconclusionU hrootParts.2]
  intro hstep
  rw [laws.all_iff htailParts.2]
  apply hinduction
  · exact hzeroSub.mp (by simpa [baseCode] using hbase)
  · intro x hx
    have hstepAt : Sat (0 ⁀' x) free stepCode :=
      (laws.all_iff htailParts.1).mp hstep x
    have hnext : Sat (0 ⁀' x) free nextCode :=
      (sat_imp_iff laws hK.isUFormula hnextU hstepBound).mp hstepAt hx
    have hboundX : Arithmetic.Seq (0 ⁀' x) := hzeroSeq.seqCons x
    have hlenX : lh (0 ⁀' x) = 1 := by
      rw [Seq.lh_seqCons _ hzeroSeq, hlhZero]
      simp
    have hsuccValue : termValue (0 ⁀' x) free
        (inductionSuccVec (V := V)).[0] = x + 1 := by
      have hval := termValue_typedQuote_iff_val (V := V)
        (0 ⁀' x) free (‘#0 + 1’ : ArithmeticSemiterm ℕ 1)
      simpa [inductionSuccVec,
        quotedBoundAssignment_seqCons (k := 0) hzeroSeq hlhZero x] using hval
    have hsuccSub := sat_subst_one hsubstitution
      hboundX hfree hsuccVec hlenX hK hsuccValue hKBound
    exact hsuccSub.mp (by simpa [nextCode] using hnext)

/-! ## Transport back to the nonstandard universal closure -/

/-- Transfer truth of the recovered raw induction body through `fvarVec`
and then change from the Skolem-coded free environment to the requested one. -/
theorem inductionClosureBody_true
    {level : V} {Sat : V → V → V → Prop}
    (hsubstitution : ∀ q, SubstitutionInvariantAt Sat level q)
    (hfreeIndependent : FreeEnvironmentIndependence level Sat)
    {m b K free base : V}
    (hbU : IsUFormula ℒₒᵣ b) (hshift : shift ℒₒᵣ b = b)
    (hbv : bv ℒₒᵣ b = m)
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hsubst : subst ℒₒᵣ (fvarVec m) b = indBodyVal K)
    (hbBound : QuantifierBoundedCode ℒₒᵣ level b)
    (hindBody : ∀ codedFree, Arithmetic.Seq codedFree →
      Sat 0 codedFree (indBodyVal K))
    (hfree : Arithmetic.Seq free) (hbase : Arithmetic.Seq base)
    (hlen : lh base = m) :
    Sat base free b := by
  rcases exists_fvarVec_substitutionEnvironment hbase hlen with
    ⟨codedFree, hcodedFree, hsub⟩
  have hbSemi : IsSemiformula ℒₒᵣ m b :=
    ⟨hbU, by simp [hbv]⟩
  have hfvar : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
    isSemitermVec_fvarVec m
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have htransport := hsubstitution b base (fvarVec m) 0
    codedFree 0 m hfvar hlhZero.symm hsub hbSemi hbBound
  have hbCoded : Sat base codedFree b :=
    htransport.mp (by
      simpa only [hsubst] using hindBody codedFree hcodedFree)
  exact (hfreeIndependent hbBound hshift hcodedFree hfree).mp hbCoded

/-! ## Soundness of the represented PA recognizer -/

/-- Every represented induction axiom in the bounded domain is true.  The
formula code and closure length remain arbitrary elements of the model. -/
theorem of_inductionUnivR
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hsubstitution : ∀ q, SubstitutionInvariantAt Sat level q)
    (hinduction : SemanticInduction Sat)
    (hfreeIndependent : FreeEnvironmentIndependence level Sat)
    (hclosure : UniversalClosureIntroduction level Sat)
    {p free : V}
    (hind : InductionUnivR p)
    (hp : QuantifierBoundedCode ℒₒᵣ level p)
    (hfree : Arithmetic.Seq free) :
    Sat 0 free p := by
  rcases bounded_inductionUnivR_data hind hp with
    ⟨m, b, K, hpcode, hbU, hshift, hbv, hK, hsubst,
      hbBound, hbodyBound, _hKBound⟩
  have hclosureBound : QuantifierBoundedCode ℒₒᵣ level
      (qqAlls b m) := by
    simpa only [← hpcode] using hp
  rw [hpcode]
  apply hclosure hclosureBound hfree
  intro base hbase hlen
  apply inductionClosureBody_true hsubstitution hfreeIndependent
      hbU hshift hbv hK hsubst hbBound _ hfree hbase hlen
  intro codedFree hcodedFree
  exact indBodyVal_true laws hsubstitution hinduction
    hK hbodyBound hcodedFree

/-- Theory-independent final split of PA's represented axiom recognizer.
The finite `PA⁻` branch is deliberately an input: for dynamic successor
truth it is supplied by standard quotation adequacy, while the nonstandard
induction branch is discharged by the theorem above. -/
theorem of_mem_pa_delta1Class
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    (hsubstitution : ∀ q, SubstitutionInvariantAt Sat level q)
    (hinduction : SemanticInduction Sat)
    (hfreeIndependent : FreeEnvironmentIndependence level Sat)
    (hclosure : UniversalClosureIntroduction level Sat)
    (hminus : ∀ {p free : V},
      p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ level p →
      Arithmetic.Seq free → Sat 0 free p)
    {p free : V}
    (hp : p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level p)
    (hfree : Arithmetic.Seq free) :
    Sat 0 free p := by
  rcases mem_pa_delta1Class_iff.mp hp with hfinite | hind
  · exact hminus hfinite hbounded hfree
  · exact of_inductionUnivR laws hsubstitution hinduction
      hfreeIndependent hclosure hind hbounded hfree

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
