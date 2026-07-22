import BoundedPAConsistency.QuantifierFreeSoundness
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Foundation.FirstOrder.Arithmetic.Basic.Model

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-!
# Rank-zero axioms recognized by the internal PA axiom predicate

This file discharges the theory-specific premise left by
`QuantifierFreeSoundness`.  Its statements range over arbitrary models of PA
and over arbitrary (possibly nonstandard) formula codes.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.TermEvaluation

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

private lemma isQuantifierFreeCode_imp_iff {p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    IsQuantifierFreeCode (imp ℒₒᵣ p q) ↔
      IsQuantifierFreeCode p ∧ IsQuantifierFreeCode q := by
  rw [show imp ℒₒᵣ p q = neg ℒₒᵣ p ^⋎ q by rfl,
    isQuantifierFreeCode_or_iff (by simp [hp]) hq,
    isQuantifierFreeCode_neg_iff hp]

/-! ## The nonstandard induction branch -/

/-- The raw body assembled by the induction-axiom recognizer always contains
an actual universal quantifier.  Consequently it cannot have hierarchy rank
zero, even when its input is a nonstandard one-variable formula code. -/
lemma not_isQuantifierFreeCode_indBodyVal {K : V}
    (hK : IsSemiformula ℒₒᵣ 1 K) :
    ¬IsQuantifierFreeCode (indBodyVal K) := by
  intro hqf
  have hKU : IsUFormula ℒₒᵣ K := hK.isUFormula
  let a : V := subst ℒₒᵣ
    (SemitermVec.val
      (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)) K
  let s₁ : V := subst ℒₒᵣ
    (SemitermVec.val
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)) K
  have haU : IsUFormula ℒₒᵣ a := by
    dsimp [a]
    apply (hK.subst (m := 0) ?_).isUFormula
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝] : SemitermVec V ℒₒᵣ 1 0)
  have hs₁U : IsUFormula ℒₒᵣ s₁ := by
    dsimp [s₁]
    apply (hK.subst (m := 1) ?_).isUFormula
    simpa using SemitermVec.isSemitermVec
      (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)
  have hi₁U : IsUFormula ℒₒᵣ (imp ℒₒᵣ K s₁) := by simp [hKU, hs₁U]
  have halli₁U : IsUFormula ℒₒᵣ (^∀ (imp ℒₒᵣ K s₁)) := by simp [hi₁U]
  have hallKU : IsUFormula ℒₒᵣ (^∀ K) := by simp [hKU]
  have hi₂U : IsUFormula ℒₒᵣ
      (imp ℒₒᵣ (^∀ (imp ℒₒᵣ K s₁)) (^∀ K)) := by
    simp [halli₁U, hallKU]
  have hqf' : IsQuantifierFreeCode
      (imp ℒₒᵣ a
        (imp ℒₒᵣ (^∀ (imp ℒₒᵣ K s₁)) (^∀ K))) := by
    simpa [indBodyVal, a, s₁] using hqf
  have hinner := (isQuantifierFreeCode_imp_iff haU hi₂U).mp hqf' |>.2
  have hallK :=
    (isQuantifierFreeCode_imp_iff halli₁U hallKU).mp hinner |>.2
  exact not_isQuantifierFreeCode_all hKU hallK

/-- No code accepted by the nonstandard universal-induction recognizer can
be rank zero.  This proof uses the recognizer's internal witnesses directly;
it does not decode them as standard formulas. -/
lemma not_isQuantifierFreeCode_of_inductionUnivR {p : V}
    (hp : InductionUnivR p) : ¬IsQuantifierFreeCode p := by
  rintro hqf
  rcases hp with ⟨m, -, b, -, hpcode, hbU, -, hbv, K, -, hK, hsubst⟩
  rw [hpcode] at hqf
  by_cases hm : m = 0
  · rw [hm, qqAlls_zero] at hqf
    rw [hm] at hsubst
    have hbsemi : IsSemiformula ℒₒᵣ 0 b :=
      ⟨hbU, by simp [hbv, hm]⟩
    have hqfSubst : IsQuantifierFreeCode
        (subst ℒₒᵣ (fvarVec 0) b) :=
      QuantifierBoundedCode.subst (m := 0) hbsemi (by simp) hqf
    rw [hsubst] at hqfSubst
    exact not_isQuantifierFreeCode_indBodyVal hK hqfSubst
  · rcases zero_or_succ m with (h | ⟨k, h⟩)
    · exact (hm h).elim
    · rw [h, qqAlls_succ] at hqf
      exact not_isQuantifierFreeCode_all
        (isUFormula_qqAlls.mpr hbU) hqf

/-! ## Splitting the PA recognizer -/

lemma mem_pa_delta1Class_iff {p : V} :
    p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class ↔
      p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class ∨
      InductionUnivR p := by
  have hch : (Peano : Theory ℒₒᵣ).Δ₁ch =
      (PeanoMinus : Theory ℒₒᵣ).Δ₁ch ⋎ chUniv := rfl
  change V ⊧/![p] ((Peano : Theory ℒₒᵣ).Δ₁ch.val) ↔ _
  rw [hch]
  simp only [HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  change
    (p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class ∨
      V ⊧/![p] chUniv.val) ↔ _
  simp

/-! ## Finite theory recognizers in nonstandard models -/

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `Theory.Δ₁.ofList` has no nonstandard elements: its defining formula
is literally a finite disjunction of equalities to standard Gödel numerals. -/
private lemma eval_ofList_delta1Class (l : List (Sentence L)) (p : V) :
    V ⊧/![p] (Theory.Δ₁.ofList l).ch.val ↔
      ∃ σ ∈ l, p = (⌜σ⌝ : V) := by
  induction l with
  | nil =>
      have hch : (Theory.Δ₁.ofList ([] : List (Sentence L))).ch =
          (⊥ : 𝚫₁.Semisentence 1) := rfl
      rw [hch]
      simp
  | cons φ l ih =>
      have hch : (Theory.Δ₁.ofList (φ :: l)).ch =
          (Theory.Δ₁.singleton φ).ch ⋎
            (Theory.Δ₁.ofList l).ch := rfl
      rw [hch]
      simp only [HierarchySymbol.Semiformula.val_or,
        LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, ih]
      rw [Theory.Δ₁.singleton_toTDef_ch_val]
      have heq : (ORingStructure.numeral (Encodable.encode φ) : V) =
          (⌜φ⌝ : V) := by
        rw [Sentence.quote_eq_encode]
        exact numeral_eq_natCast_app _
      simpa [heq]

/-- The same standardness statement for the finite-set wrapper used by
`PeanoMinus.delta1`.  The implementation chooses an arbitrary list ordering,
which is irrelevant to the disjunction it recognizes. -/
private lemma eval_ofFinite_delta1Class (T : Theory L) (hT : Set.Finite T)
    (p : V) :
    V ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val ↔
      ∃ σ ∈ T, p = (⌜σ⌝ : V) := by
  have hch : (Theory.Δ₁.ofFinite T hT).ch =
      (Theory.Δ₁.ofList hT.toFinset.toList).ch := rfl
  rw [hch, eval_ofList_delta1Class]
  simp

omit [L.Encodable] [L.LORDefinable] in
lemma mem_peanoMinus_delta1Class_iff {p : V} :
    p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class ↔
      ∃ σ ∈ (PeanoMinus : Theory ℒₒᵣ), p = (⌜σ⌝ : V) := by
  change V ⊧/![p] PeanoMinus.delta1.ch.val ↔ _
  exact eval_ofFinite_delta1Class PeanoMinus PeanoMinus.finite p

/-! ## Absoluteness on the standard codes in the finite branch -/

/-- Rank zero is `Δ₁`, so its value on a standard quoted formula is
absolute between `ℕ` and an arbitrary model of PA. -/
lemma isQuantifierFreeCode_quote_absolute (σ : ArithmeticSentence) :
    IsQuantifierFreeCode (V := V) (⌜σ⌝ : V) ↔
      IsQuantifierFreeCode (V := ℕ) (⌜σ⌝ : ℕ) := by
  have h := LO.FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V)
    (σ := quantifierBoundedCodeDef ℒₒᵣ) (by simp) (by simp)
    (e := ![(0 : ℕ), (⌜σ⌝ : ℕ)])
  simp only [(QuantifierBoundedCode.defined ℒₒᵣ (V := V)).iff,
    (QuantifierBoundedCode.defined ℒₒᵣ (V := ℕ)).iff] at h
  simpa [IsQuantifierFreeCode, Sentence.coe_quote_eq_quote] using h

/-- The represented Boolean evaluator is likewise absolute on standard
environments and a standard formula code.  This is the function-graph form
of `Δ₁` absoluteness; it does not assume that arbitrary nonstandard codes
can be decoded. -/
lemma qfValue_quote_absolute (σ : ArithmeticSentence) :
    (qfValue (V := ℕ) 0 0 (⌜σ⌝ : ℕ) : V) =
      qfValue (V := V) 0 0 (⌜σ⌝ : V) := by
  have h := LO.FirstOrder.Arithmetic.DefinedFunction.shigmaOne_absolute_func V
    (qfValue.defined (V := ℕ)) (qfValue.defined (V := V))
    ![(0 : ℕ), (0 : ℕ), (⌜σ⌝ : ℕ)]
  simpa [Function.comp_def, Sentence.coe_quote_eq_quote] using h

private lemma quantifierGroups_eq_zero_of_qf_quote {σ : ArithmeticSentence}
    (hqf : IsQuantifierFreeCode (V := ℕ) (⌜σ⌝ : ℕ)) :
    quantifierGroups (Rewriting.emb σ : ArithmeticSemiproposition 0) = 0 := by
  rw [Sentence.quote_def] at hqf
  have hrank := (quantifierBoundedCode_quote_iff
    (Rewriting.emb σ : ArithmeticSemiproposition 0)).mp hqf
  omega

lemma qfValue_zeroLtOne_nat :
    qfValue (V := ℕ) 0 0 (⌜PeanoMinus.Axiom.zeroLtOne⌝ : ℕ) = 1 := by
  rw [Sentence.quote_eq]
  simp [PeanoMinus.Axiom.zeroLtOne]
  rw [Arithmetic.qqLT]
  have hz : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.zero : ℕ) :=
    (Bootstrapping.Arithmetic.zero_semiterm (V := ℕ) (n := 0)).isUTerm
  have ho : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.one : ℕ) :=
    (Bootstrapping.Arithmetic.one_semiterm (V := ℕ) (n := 0)).isUTerm
  rw [qfValue_lt_atom_iff hz ho]
  simp [Bootstrapping.Arithmetic.zero, Bootstrapping.Arithmetic.one,
    qqFuncN_eq_qqFunc]
  have he : IsUTermVec (V := ℕ) ℒₒᵣ 0 0 :=
    IsUTermVec.empty_iff.mpr rfl
  rw [show Arithmetic.zeroIndex = 0 by rfl,
    show Arithmetic.oneIndex = 1 by rfl]
  have hfz : (ℒₒᵣ).IsFunc (0 : ℕ) 0 := by
    have h := Arithmetic.LOR_func_zeroIndex (V := ℕ)
    rw [Arithmetic.coe_zeroIndex_eq] at h
    exact h
  have hfo : (ℒₒᵣ).IsFunc (0 : ℕ) 1 := by
    have h := Arithmetic.LOR_func_oneIndex (V := ℕ)
    rw [Arithmetic.coe_oneIndex_eq] at h
    exact h
  rw [termValue_func (V := ℕ) hfz he,
    termValue_func (V := ℕ) hfo he]
  simp [applyFunction]

lemma qfValue_eq_funcExt_zero_nat (f : (ℒₒᵣ).Func 0) :
    qfValue (V := ℕ) 0 0 (⌜Theory.Eq.funcExt f⌝ : ℕ) = 1 := by
  let t : ℕ := ^func 0 (⌜f⌝ : ℕ) 0
  have hf : (ℒₒᵣ).IsFunc (0 : ℕ) (⌜f⌝ : ℕ) := by
    simpa using codeIn_func_quote (V := ℕ) (L := ℒₒᵣ) f
  have ht : IsUTerm ℒₒᵣ t :=
    IsUTerm.func hf IsUTermVec.empty
  have hrel : (ℒₒᵣ).IsRel (2 : ℕ) Arithmetic.eqIndex := by
    have heqcode : Arithmetic.eqIndex =
        (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : ℕ) := by
      change Encodable.encode (Language.Eq.eq : (ℒₒᵣ).Rel 2) =
        ORingStructure.numeral (Encodable.encode
          (Language.Eq.eq : (ℒₒᵣ).Rel 2))
      exact (Nat.numeral_eq _).symm
    rw [heqcode]
    exact codeIn_rel_quote (V := ℕ) (L := ℒₒᵣ) Language.Eq.eq
  have htv : IsUTermVec (V := ℕ) ℒₒᵣ 2 ?[t, t] :=
    IsUTermVec.two_iff.mpr ⟨t, t, ht, ht, rfl⟩
  have heqU : IsUFormula ℒₒᵣ (t ^= t) := by
    unfold Arithmetic.qqEQ
    exact (isQuantifierFreeCode_rel hrel htv).1
  have hself : qfValue (V := ℕ) 0 0 (t ^= t) = 1 := by
    unfold Arithmetic.qqEQ
    exact (qfValue_eq_atom_iff ht ht).mpr rfl
  rw [Sentence.quote_eq]
  simp [Theory.Eq.funcExt, Matrix.conj]
  change qfValue (V := ℕ) 0 0 (imp ℒₒᵣ ^⊤ (t ^= t)) = 1
  rw [show imp ℒₒᵣ ^⊤ (t ^= t) = ^⊥ ^⋎ (t ^= t) by
    simp [Bootstrapping.imp]]
  rw [qfValue_or (by simp) heqU]
  simp [hself, bitOr]

/-! The finite standard case split.  Every constructor except `0 < 1` and
the two nullary function-congruence axioms has a visible outer universal
quantifier, contradicting the external rank-zero equation. -/
lemma qfValue_peanoMinus_axiom_nat {σ : ArithmeticSentence}
    (hσ : PeanoMinus σ)
    (hqf : IsQuantifierFreeCode (V := ℕ) (⌜σ⌝ : ℕ)) :
    qfValue (V := ℕ) 0 0 (⌜σ⌝ : ℕ) = 1 := by
  have hrank := quantifierGroups_eq_zero_of_qf_quote hqf
  cases hσ with
  | equal φ hφ =>
      cases hφ with
      | refl =>
          exfalso
          simpa [Theory.Eq.refl, quantifierGroups, sigmaRank, piRank,
            Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
      | symm =>
          exfalso
          simpa [Theory.Eq.symm, quantifierGroups, sigmaRank, piRank,
            Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
      | trans =>
          exfalso
          simpa [Theory.Eq.trans, quantifierGroups, sigmaRank, piRank,
            Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
      | funcExt f =>
          cases f with
          | zero => exact qfValue_eq_funcExt_zero_nat _
          | one => exact qfValue_eq_funcExt_zero_nat _
          | add =>
              exfalso
              simpa [Theory.Eq.funcExt, quantifierGroups, sigmaRank, piRank,
                Rewriting.emb_allClosure, allClosure_succ,
                Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
          | mul =>
              exfalso
              simpa [Theory.Eq.funcExt, quantifierGroups, sigmaRank, piRank,
                Rewriting.emb_allClosure, allClosure_succ,
                Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
      | relExt r =>
          cases r <;>
            exfalso <;>
            simpa [Theory.Eq.relExt, quantifierGroups, sigmaRank, piRank,
              Rewriting.emb_allClosure, allClosure_succ,
              Semiformula.rewAux, Rewriting.emb, Rew.emb] using hrank
  | zeroLtOne => exact qfValue_zeroLtOne_nat
  | addZero | addAssoc | addComm | addEqOfLt | zeroLe |
      oneLeOfZeroLt | addLtAdd | mulZero | mulOne | mulAssoc | mulComm |
      mulLtMul | distr | ltIrrefl | ltTrans | ltTri =>
      exfalso
      simp_all [PeanoMinus.Axiom.addZero, PeanoMinus.Axiom.addAssoc,
        PeanoMinus.Axiom.addComm, PeanoMinus.Axiom.addEqOfLt,
        PeanoMinus.Axiom.zeroLe, PeanoMinus.Axiom.oneLeOfZeroLt,
        PeanoMinus.Axiom.addLtAdd, PeanoMinus.Axiom.mulZero,
        PeanoMinus.Axiom.mulOne, PeanoMinus.Axiom.mulAssoc,
        PeanoMinus.Axiom.mulComm, PeanoMinus.Axiom.mulLtMul,
        PeanoMinus.Axiom.distr, PeanoMinus.Axiom.ltIrrefl,
        PeanoMinus.Axiom.ltTrans, PeanoMinus.Axiom.ltTri,
        quantifierGroups, sigmaRank, piRank,
        Rewriting.emb, Rew.emb]

/-! ## The PA-specific rank-zero axiom premise -/

/-- Every rank-zero code accepted by the finite `PA⁻` recognizer is true in
the internal Boolean semantics of an arbitrary model of PA. -/
lemma qfTrue_of_mem_peanoMinus_delta1Class {p : V}
    (hp : p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class)
    (hqf : IsQuantifierFreeCode p) : QFTrue 0 0 p := by
  rcases mem_peanoMinus_delta1Class_iff.mp hp with ⟨σ, hσ, rfl⟩
  have hqfNat : IsQuantifierFreeCode (V := ℕ) (⌜σ⌝ : ℕ) :=
    (isQuantifierFreeCode_quote_absolute (V := V) σ).mp hqf
  have hvalNat : qfValue (V := ℕ) 0 0 (⌜σ⌝ : ℕ) = 1 :=
    qfValue_peanoMinus_axiom_nat hσ hqfNat
  refine ⟨hqf, ?_⟩
  rw [← qfValue_quote_absolute (V := V) σ]
  simp [hvalNat]

/-- The exact axiom premise required by rank-zero logical soundness.  The
finite branch is true; the nonstandard induction branch is impossible. -/
theorem qfTrue_of_mem_pa_delta1Class {p : V}
    (hp : p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class)
    (hqf : IsQuantifierFreeCode p) : QFTrue 0 0 p := by
  rcases mem_pa_delta1Class_iff.mp hp with hminus | hind
  · exact qfTrue_of_mem_peanoMinus_delta1Class hminus hqf
  · exact (not_isQuantifierFreeCode_of_inductionUnivR hind hqf).elim

/-- Every (possibly nonstandard) model of PA satisfies rank-zero restricted
consistency. -/
theorem restrictedConsistent_pa_zero :
    RestrictedConsistent (V := V) Peano (0 : V) :=
  QuantifierFreeSoundness.restrictedConsistent_zero_of_qf_axioms
    Peano (fun _ hp hqf ↦ qfTrue_of_mem_pa_delta1Class hp hqf)

/-- The rank-zero consistency assertion is therefore an actual PA theorem.
Completeness is applied at universe level zero so that its model quantifier
matches the arbitrary-model theorem above. -/
theorem pa_proves_restrictedConsistency_zero :
    Peano ⊢
      (paRestrictedConsistencySentence 0 : ArithmeticSentence) := by
  apply LO.FirstOrder.Arithmetic.complete.{0} Peano _
  intro M _ _
  simpa [models_iff] using
    (eval_paRestrictedConsistencySentence_iff (V := M) 0).mpr
      (restrictedConsistent_pa_zero (V := M))

end LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms
