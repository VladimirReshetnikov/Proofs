import BoundedPAConsistency.FixedLevelTruthDefinability
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

set_option maxHeartbeats 800000

/-!
# Model induction for externally indexed coded truth

The code recognized by PA's internal induction-axiom predicate may be
nonstandard.  Its recovered one-variable body therefore cannot be decoded as
a Lean formula.  What PA gives us instead is ordinary induction for the
*definable semantic predicate* obtained by evaluating that code under an HFS
bound-variable environment ending in the induction variable.

This module isolates that bridge.  It deliberately does not mention the
shape of an induction axiom or any particular proof calculus.  The later PA
axiom-soundness proof can use the two lemmas below after the fixed-level
Tarski and substitution clauses have converted the base and step hypotheses
to truth of the recovered body.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAInduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Rank inheritance through a nonstandard universal closure -/

/-- Removing an internally finite block of leading universal quantifiers
cannot increase the least oriented hierarchy level of its body.

The iteration count may be nonstandard, so the proof uses induction in the
ambient arithmetic model rather than recursion in Lean. -/
theorem quantifierBoundedCode_of_qqAlls {bound p k : V}
    (h : QuantifierBoundedCode ℒₒᵣ bound (qqAlls p k)) :
    QuantifierBoundedCode ℒₒᵣ bound p := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => simpa using h
  case succ k ih =>
    rw [qqAlls_succ] at h
    have hchildU : IsUFormula ℒₒᵣ (qqAlls p k) := by
      simpa using h.1
    have hchild : QuantifierBoundedCode ℒₒᵣ bound (qqAlls p k) := by
      rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hp
      · rcases zero_or_succ bound with rfl | ⟨level, rfl⟩
        · exact (not_isSigmaCode_all_zero hchildU hs).elim
        · have hpi : IsPiCode ℒₒᵣ level (qqAlls p k) :=
            (isSigmaCode_all_succ_iff hchildU).mp hs |>.1
          exact (hpi.mono (by simp)).quantifierBounded
      · exact ((isPiCode_all_iff hchildU).mp hp |>.1).quantifierBounded
    exact ih hchild

/-! ## Rank inheritance from the raw induction body -/

/-- A hierarchy bound on the raw induction implication bounds its recovered
one-variable core at the same level.

Only the base-case occurrence is needed for this inversion.  It occurs as
the antecedent of the outer implication, hence under one coded negation.
Whichever orientation realizes the least rank of the complete implication,
negation switches it to an orientation for the substituted base instance;
substitution invariance then transports that orientation back to `K`.
-/
theorem quantifierBoundedCode_of_indBodyVal {bound K : V}
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hbody : QuantifierBoundedCode ℒₒᵣ bound (indBodyVal K)) :
    QuantifierBoundedCode ℒₒᵣ bound K := by
  let zeroVec : V :=
    SemitermVec.val
      (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)
  let succVec : V :=
    SemitermVec.val
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)
  let base : V := subst ℒₒᵣ zeroVec K
  let next : V := subst ℒₒᵣ succVec K
  let stepBody : V := imp ℒₒᵣ K next
  let stepAll : V := ^∀ stepBody
  let conclusion : V := ^∀ K
  let tail : V := imp ℒₒᵣ stepAll conclusion
  have hzeroVec : IsSemitermVec ℒₒᵣ 1 0 zeroVec := by
    dsimp [zeroVec]
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)
  have hsuccVec : IsSemitermVec ℒₒᵣ 1 1 succVec := by
    dsimp [succVec]
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)
  have hbaseU : IsUFormula ℒₒᵣ base := by
    exact (hK.subst hzeroVec).isUFormula
  have hnextU : IsUFormula ℒₒᵣ next := by
    exact (hK.subst hsuccVec).isUFormula
  have hstepBodyU : IsUFormula ℒₒᵣ stepBody := by
    simp [stepBody, hK.isUFormula, hnextU]
  have hstepAllU : IsUFormula ℒₒᵣ stepAll := by
    simp [stepAll, hstepBodyU]
  have hconclusionU : IsUFormula ℒₒᵣ conclusion := by
    simp [conclusion, hK.isUFormula]
  have htailU : IsUFormula ℒₒᵣ tail := by
    simp [tail, hstepAllU, hconclusionU]
  have hshape : indBodyVal K = neg ℒₒᵣ base ^⋎ tail := by
    rfl
  rw [hshape] at hbody
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp hbody with hs | hp
  · have hbaseNeg : IsSigmaCode ℒₒᵣ bound (neg ℒₒᵣ base) :=
      (isSigmaCode_or_iff hbaseU.neg htailU).mp hs |>.1
    have hbasePi : IsPiCode ℒₒᵣ bound base :=
      (isSigmaCode_neg_iff hbaseU).mp hbaseNeg
    exact ((isPiCode_subst_iff hK hzeroVec).mp hbasePi).quantifierBounded
  · have hbaseNeg : IsPiCode ℒₒᵣ bound (neg ℒₒᵣ base) :=
      (isPiCode_or_iff hbaseU.neg htailU).mp hp |>.1
    have hbaseSigma : IsSigmaCode ℒₒᵣ bound base :=
      (isPiCode_neg_iff hbaseU).mp hbaseNeg
    exact ((isSigmaCode_subst_iff hK hzeroVec).mp hbaseSigma).quantifierBounded

/-! ## Enriching the internal PA induction recognizer -/

/-- The nonstandard free-variable vector used by the recognizer is a genuine
vector of `m` closed-with-respect-to-bound-variables terms. -/
theorem isSemitermVec_fvarVec (m : V) :
    IsSemitermVec ℒₒᵣ m 0 (fvarVec m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨len_fvarVec m, ?_⟩
  intro i hi
  rw [nth_fvarVec m i hi]
  simp

/-- A bounded code accepted by the nonstandard induction recognizer comes
with a bounded recovered core and a bounded raw induction body.

This is the rank bookkeeping needed before any semantic argument starts.  In
particular, `m`, `b`, and `K` remain elements of the ambient model; the proof
does not assert that they are standard syntax objects.
-/
theorem bounded_inductionUnivR_data {bound p : V}
    (hind : InductionUnivR p)
    (hp : QuantifierBoundedCode ℒₒᵣ bound p) :
    ∃ m b K,
      p = qqAlls b m ∧
      IsUFormula ℒₒᵣ b ∧
      shift ℒₒᵣ b = b ∧
      bv ℒₒᵣ b = m ∧
      IsSemiformula ℒₒᵣ 1 K ∧
      subst ℒₒᵣ (fvarVec m) b = indBodyVal K ∧
      QuantifierBoundedCode ℒₒᵣ bound b ∧
      QuantifierBoundedCode ℒₒᵣ bound (indBodyVal K) ∧
      QuantifierBoundedCode ℒₒᵣ bound K := by
  rcases hind with
    ⟨m, _, b, _, hpcode, hbU, hshift, hbv,
      K, _, hK, hsubst⟩
  have hbBound : QuantifierBoundedCode ℒₒᵣ bound b := by
    apply quantifierBoundedCode_of_qqAlls
    simpa [hpcode] using hp
  have hbsemi : IsSemiformula ℒₒᵣ m b := by
    exact ⟨hbU, by simp [hbv]⟩
  have hfvar : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
    isSemitermVec_fvarVec m
  have hindBodyBound :
      QuantifierBoundedCode ℒₒᵣ bound (indBodyVal K) := by
    have := hbBound.subst hbsemi hfvar
    simpa [hsubst] using this
  exact ⟨m, b, K, hpcode, hbU, hshift, hbv, hK, hsubst,
    hbBound, hindBodyBound,
    quantifierBoundedCode_of_indBodyVal hK hindBodyBound⟩

/-! ## Semantic assembly of the raw induction body -/

/-- The singleton term vector coding the base instance `K(0)`. -/
noncomputable def inductionZeroVec : V :=
  SemitermVec.val
    (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)

/-- The singleton term vector coding the successor instance `K(x + 1)`. -/
noncomputable def inductionSuccVec : V :=
  SemitermVec.val
    (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)

/-- Abstract semantic correctness of `indBodyVal`.

The hypotheses are precisely the four interfaces supplied by a partial truth
predicate: implication, universal quantification, the two concrete
substitution instances, and semantic induction for the definable predicate
`x ↦ Sat (base ⁀' x) free K`.  Separating this propositional assembly
from the certificate implementation keeps the later PA-specific proof small
and makes the environment convention explicit.
-/
theorem indBodyVal_true_of_semantic_induction
    (Sat : V → V → V → Prop) {base free K : V}
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (imp_iff : ∀ {bound p q : V},
      IsUFormula ℒₒᵣ p → IsUFormula ℒₒᵣ q →
      (Sat bound free (imp ℒₒᵣ p q) ↔
        (Sat bound free p → Sat bound free q)))
    (all_iff : ∀ {bound p : V}, IsUFormula ℒₒᵣ p →
      (Sat bound free (^∀ p) ↔ ∀ x, Sat (bound ⁀' x) free p))
    (zero_subst_iff :
      Sat base free (subst ℒₒᵣ (inductionZeroVec (V := V)) K) ↔
        Sat (base ⁀' 0) free K)
    (succ_subst_iff : ∀ x,
      Sat (base ⁀' x) free
          (subst ℒₒᵣ (inductionSuccVec (V := V)) K) ↔
        Sat (base ⁀' (x + 1)) free K)
    (induction :
      Sat (base ⁀' 0) free K →
      (∀ x, Sat (base ⁀' x) free K →
        Sat (base ⁀' (x + 1)) free K) →
      ∀ x, Sat (base ⁀' x) free K) :
    Sat base free (indBodyVal K) := by
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
  have hshape : indBodyVal K = imp ℒₒᵣ baseCode tail := by
    rfl
  rw [hshape, imp_iff hbaseU htailU]
  intro hbase
  rw [imp_iff hstepAllU hconclusionU]
  intro hstep
  rw [all_iff hK.isUFormula]
  apply induction
  · exact zero_subst_iff.mp (by simpa [baseCode] using hbase)
  · intro x hx
    have hstepAt : Sat (base ⁀' x) free stepCode :=
      (all_iff hstepU).mp hstep x
    have hnext : Sat (base ⁀' x) free nextCode :=
      (imp_iff hK.isUFormula hnextU).mp hstepAt hx
    exact succ_subst_iff x |>.mp (by simpa [nextCode] using hnext)

/-!
The base environment is an arbitrary HFS code.  In the intended application
it contains the values of binders outside the recovered induction body; the
new value is appended because `TermEvaluation` reads de Bruijn variable zero
from the right-hand end of its bound environment.
-/

/-- Successor induction for Sigma-oriented fixed-level truth. -/
theorem sigmaTrue_succ_induction (n : ℕ) {base free p : V}
    (zero : SigmaTrue n (base ⁀' 0) free p)
    (succ : ∀ x, SigmaTrue n (base ⁀' x) free p →
      SigmaTrue n (base ⁀' (x + 1)) free p) :
    ∀ x, SigmaTrue n (base ⁀' x) free p := by
  letI : V↓[ℒₒᵣ] ⊧* ISigma (n + 1) := models_of_subtheory hPA
  apply InductionOnHierarchy.succ_induction (V := V)
    (P := fun x : V ↦ SigmaTrue n (base ⁀' x) free p)
    (Polarity.sigma) (n + 1)
  · apply HierarchySymbol.DefinableRel₃.comp (sigmaTrue_definable n)
    · definability
    · simp
    · simp
  · exact zero
  · exact succ

/-- Successor induction for Pi-oriented fixed-level truth.

Full PA supplies Pi induction at the same external level via the standard
Sigma/Pi induction equivalence for arithmetic models. -/
theorem piTrue_succ_induction (n : ℕ) {base free p : V}
    (zero : PiTrue n (base ⁀' 0) free p)
    (succ : ∀ x, PiTrue n (base ⁀' x) free p →
      PiTrue n (base ⁀' (x + 1)) free p) :
    ∀ x, PiTrue n (base ⁀' x) free p := by
  letI : V↓[ℒₒᵣ] ⊧* ISigma (n + 1) := models_of_subtheory hPA
  apply InductionOnHierarchy.succ_induction (V := V)
    (P := fun x : V ↦ PiTrue n (base ⁀' x) free p)
    (Polarity.pi) (n + 1)
  · apply HierarchySymbol.DefinableRel₃.comp (piTrue_definable n)
    · definability
    · simp
    · simp
  · exact zero
  · exact succ

end LeanProofs.BoundedPAConsistency.FixedLevelPAInduction
