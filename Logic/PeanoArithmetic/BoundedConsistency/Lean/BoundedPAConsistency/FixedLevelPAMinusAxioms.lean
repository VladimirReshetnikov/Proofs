import BoundedPAConsistency.FixedLevelTruthSubstitution
import BoundedPAConsistency.QuantifierFreePAAxioms

set_option maxHeartbeats 1000000
set_option maxRecDepth 5000

/-!
# Fixed-level truth of the finite axioms of PA minus

The finite `PeanoMinus` recognizer has only standard outputs, even when it is
interpreted in a nonstandard model.  This module connects that observation to
fixed-level truth.  The main technical bridge is quotation adequacy: evaluation
of a standard quoted arithmetic term or formula agrees with ordinary Tarski
semantics in the ambient model.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthTarski
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Standard terms in coded environments -/

/-- Decode a finite standard de Bruijn index from the model-coded bound
environment.  `boundPosition` accounts for the fact that coded sequences are
stored oldest-first whereas de Bruijn indices are newest-first. -/
noncomputable def quotedBoundAssignment {k : ℕ} (bound : V) (i : Fin k) : V :=
  znth bound (boundPosition bound (↑(i : ℕ) : V))

/-- Decode a standard free-variable index from a model-coded free environment. -/
noncomputable def quotedFreeAssignment (free : V) (x : ℕ) : V :=
  znth free (x : V)

/-- Ordinary evaluation of a standard arithmetic term agrees with the
represented evaluator on its quote. -/
theorem termValue_quote_iff_val {k : ℕ} (bound free : V)
    (t : SyntacticSemiterm ℒₒᵣ k) :
    termValue bound free (⌜t⌝ : V) =
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
          have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
            (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
            (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.addIndex : V)
                ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) +
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_add hv0 hv1, ih 0, ih 1]
      | mul =>
          have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
            (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
            (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
          change termValue bound free
              (^func 2 (Arithmetic.mulIndex : V)
                ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) =
            (v 0).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free) *
              (v 1).val (quotedBoundAssignment bound)
                (quotedFreeAssignment free)
          rw [termValue_mul hv0 hv1, ih 0, ih 1]

/-- Appending one model element to a correctly sized coded bound environment
implements the semantic de Bruijn extension operation. -/
theorem quotedBoundAssignment_seqCons {k : ℕ} {bound : V}
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

/-! ## Standard quotation and the coded hierarchy bound -/

/-- The Delta-one hierarchy-bound checker is absolute on a standard formula
code and a standard external level.  This removes all dependence on the
ambient model from the syntactic side of quotation adequacy. -/
theorem quantifierBoundedCode_quote_iff_standard (n : ℕ)
    {k : ℕ} (φ : ArithmeticSemiproposition k) :
    QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) (⌜φ⌝ : V) ↔
      quantifierGroups φ ≤ n := by
  have habs := LO.FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V)
    (σ := quantifierBoundedCodeDef ℒₒᵣ) (by simp) (by simp)
    (e := ![(n : ℕ), (⌜φ⌝ : ℕ)])
  simp only [(QuantifierBoundedCode.defined ℒₒᵣ (V := V)).iff,
    (QuantifierBoundedCode.defined ℒₒᵣ (V := ℕ)).iff] at habs
  have hcode :
      QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) (⌜φ⌝ : V) ↔
        QuantifierBoundedCode ℒₒᵣ n (⌜φ⌝ : ℕ) := by
    simpa [levelCode, numeral_eq_natCast_app,
      Semiformula.coe_quote_eq_quote] using habs
  exact hcode.trans (quantifierBoundedCode_quote_iff φ)

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

/-- On the one-level-raised bounded domain, Sigma truth has a direct
universal Tarski clause.  Internally this uses the Pi clause plus same-level
coherence; no formula code is decoded. -/
private theorem sigmaTrue_succ_all_iff_of_bounded (n : ℕ)
    {bound free p : V}
    (hp : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (^∀ p)) :
    SigmaTrue (n + 1) bound free (^∀ p) ↔
      ∀ a, SigmaTrue (n + 1) (bound ⁀' a) free p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using hp.1
  have hsAll := sigmaDomain_of_bounded n hp
  have hpiAll := piDomain_of_bounded n hp
  have hpiBody : IsPiCode ℒₒᵣ
      (levelCode (V := V) (n + 1)) p :=
    ((isPiCode_all_iff hpU).mp hpiAll).1
  have hsAll' : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) n + 1) (^∀ p) := by
    simpa only [← levelCode_succ] using hsAll
  have hpiBodyLower : IsPiCode ℒₒᵣ
      (levelCode (V := V) n) p :=
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

/-! The next four inversion lemmas keep the recursive adequacy proof on the
same lower bound.  Boolean connectives preserve either oriented rank, while a
quantifier is inverted from the opposite orientation one level above. -/

private lemma bounded_and_parts {level p q : V}
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋏ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  have hu : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using h.1
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hp
  · have hparts := (isSigmaCode_and_iff hu.1 hu.2).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_and_iff hu.1 hu.2).mp hp
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

private lemma bounded_or_parts {level p q : V}
    (h : QuantifierBoundedCode ℒₒᵣ level (p ^⋎ q)) :
    QuantifierBoundedCode ℒₒᵣ level p ∧
      QuantifierBoundedCode ℒₒᵣ level q := by
  have hu : IsUFormula ℒₒᵣ p ∧ IsUFormula ℒₒᵣ q := by
    simpa using h.1
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hp
  · have hparts := (isSigmaCode_or_iff hu.1 hu.2).mp hs
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩
  · have hparts := (isPiCode_or_iff hu.1 hu.2).mp hp
    exact ⟨hparts.1.quantifierBounded, hparts.2.quantifierBounded⟩

private lemma bounded_all_body (n : ℕ) {p : V}
    (h : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) (^∀ p)) :
    QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using h.1
  have hs : IsSigmaCode ℒₒᵣ
      (levelCode (V := V) n + 1) (^∀ p) := by
    simpa only [← levelCode_succ] using sigmaDomain_of_bounded n h
  exact ((isSigmaCode_all_succ_iff
    (n := levelCode (V := V) n) hpU).mp hs).1.quantifierBounded

private lemma bounded_exs_body (n : ℕ) {p : V}
    (h : QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) (^∃ p)) :
    QuantifierBoundedCode ℒₒᵣ (levelCode (V := V) n) p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using h.1
  have hp : IsPiCode ℒₒᵣ
      (levelCode (V := V) n + 1) (^∃ p) := by
    simpa only [← levelCode_succ] using piDomain_of_bounded n h
  exact ((isPiCode_exs_succ_iff
    (n := levelCode (V := V) n) hpU).mp hp).1.quantifierBounded

/-! ## Quotation adequacy for standard arithmetic formulae -/

private theorem sigmaTrue_succ_quote_rel_iff_eval (n : ℕ)
    {k arity : ℕ} (R : (ℒₒᵣ).Rel arity)
    (v : Fin arity → SyntacticSemiterm ℒₒᵣ k)
    (bound free : V) :
    SigmaTrue (n + 1) bound free (⌜Semiformula.rel R v⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) (Semiformula.rel R v) := by
  have hqf : IsQuantifierFreeCode
      (⌜Semiformula.rel R v⌝ : V) := by
    apply isQuantifierFreeCode_rel
    · simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) R
    · exact SemitermVec.isUTermVec
        (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))
  rw [sigmaTrue_succ_qf_iff n hqf]
  cases R with
  | eq =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^rel 2 (Arithmetic.eqIndex : V)
            ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        (v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) =
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_eq_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]
  | lt =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^rel 2 (Arithmetic.ltIndex : V)
            ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        (v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) <
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_lt_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]

private theorem sigmaTrue_succ_quote_nrel_iff_eval (n : ℕ)
    {k arity : ℕ} (R : (ℒₒᵣ).Rel arity)
    (v : Fin arity → SyntacticSemiterm ℒₒᵣ k)
    (bound free : V) :
    SigmaTrue (n + 1) bound free (⌜Semiformula.nrel R v⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) (Semiformula.nrel R v) := by
  have hqf : IsQuantifierFreeCode
      (⌜Semiformula.nrel R v⌝ : V) := by
    apply isQuantifierFreeCode_nrel
    · simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) R
    · exact SemitermVec.isUTermVec
        (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))
  rw [sigmaTrue_succ_qf_iff n hqf]
  cases R with
  | eq =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^nrel 2 (Arithmetic.eqIndex : V)
            ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        (v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) ≠
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_neq_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]
  | lt =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^nrel 2 (Arithmetic.ltIndex : V)
            ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        ¬(v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) <
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_nlt_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]

/-- Fixed successor-level truth is adequate for every standard quoted
arithmetic semiproposition whose quantifier-group count is within the lower
coded bound. -/
theorem sigmaTrue_succ_quote_iff_eval (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemiproposition k) {bound free : V}
    (hbound : Arithmetic.Seq bound) (hlen : lh bound = (k : V))
    (hbounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (⌜φ⌝ : V)) :
    SigmaTrue (n + 1) bound free (⌜φ⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) φ := by
  induction φ using Semiformula.rec' generalizing bound with
  | hrel R v =>
      exact sigmaTrue_succ_quote_rel_iff_eval n R v bound free
  | hnrel R v =>
      exact sigmaTrue_succ_quote_nrel_iff_eval n R v bound free
  | hverum =>
      rw [Semiformula.quote_verum,
        sigmaTrue_succ_qf_iff n isQuantifierFreeCode_verum]
      simp
  | hfalsum =>
      rw [Semiformula.quote_falsum,
        sigmaTrue_succ_qf_iff n isQuantifierFreeCode_falsum]
      simp
  | hand p q ihp ihq =>
      have hparts := bounded_and_parts hbounded
      have hpU : IsUFormula ℒₒᵣ (⌜p⌝ : V) :=
        (Semiformula.quote_isSemiformula p).isUFormula
      have hqU : IsUFormula ℒₒᵣ (⌜q⌝ : V) :=
        (Semiformula.quote_isSemiformula q).isUFormula
      change SigmaTrue (n + 1) bound free
          ((⌜p⌝ : V) ^⋏ (⌜q⌝ : V)) ↔
        Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p ∧
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q
      rw [sigmaTrue_and_iff hpU hqU,
        ihp hbound hlen hparts.1,
        ihq hbound hlen hparts.2]
  | hor p q ihp ihq =>
      have hparts := bounded_or_parts hbounded
      have hpU : IsUFormula ℒₒᵣ (⌜p⌝ : V) :=
        (Semiformula.quote_isSemiformula p).isUFormula
      have hqU : IsUFormula ℒₒᵣ (⌜q⌝ : V) :=
        (Semiformula.quote_isSemiformula q).isUFormula
      have hpSigma := sigmaDomain_of_bounded n hparts.1
      have hqSigma := sigmaDomain_of_bounded n hparts.2
      change SigmaTrue (n + 1) bound free
          ((⌜p⌝ : V) ^⋎ (⌜q⌝ : V)) ↔
        Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p ∨
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q
      rw [sigmaTrue_or_iff hpU hqU hpSigma hqSigma,
        ihp hbound hlen hparts.1,
        ihq hbound hlen hparts.2]
  | hall p ih =>
      have hbody := bounded_all_body n hbounded
      change SigmaTrue (n + 1) bound free (^∀ (⌜p⌝ : V)) ↔
        ∀ a : V, Semiformula.Eval
          (a :> quotedBoundAssignment bound)
          (quotedFreeAssignment free) p
      have hall :
          SigmaTrue (n + 1) bound free (^∀ (⌜p⌝ : V)) ↔
            ∀ a : V, SigmaTrue (n + 1) (bound ⁀' a) free
              (⌜p⌝ : V) := by
        apply sigmaTrue_succ_all_iff_of_bounded n
        simpa only [Semiformula.quote_all] using hbounded
      rw [hall]
      apply forall_congr'
      intro a
      calc
        SigmaTrue (n + 1) (bound ⁀' a) free (⌜p⌝ : V) ↔
            Semiformula.Eval (quotedBoundAssignment (bound ⁀' a))
              (quotedFreeAssignment free) p :=
          ih (hbound.seqCons a) (by simp [hbound, hlen]) hbody
        _ ↔ Semiformula.Eval (a :> quotedBoundAssignment bound)
              (quotedFreeAssignment free) p := by
          rw [quotedBoundAssignment_seqCons hbound hlen a]
  | hexs p ih =>
      have hbody := bounded_exs_body n hbounded
      have hpU : IsUFormula ℒₒᵣ (⌜p⌝ : V) :=
        (Semiformula.quote_isSemiformula p).isUFormula
      change SigmaTrue (n + 1) bound free (^∃ (⌜p⌝ : V)) ↔
        ∃ a : V, Semiformula.Eval
          (a :> quotedBoundAssignment bound)
          (quotedFreeAssignment free) p
      rw [sigmaTrue_exs_iff hpU]
      apply exists_congr
      intro a
      calc
        SigmaTrue (n + 1) (bound ⁀' a) free (⌜p⌝ : V) ↔
            Semiformula.Eval (quotedBoundAssignment (bound ⁀' a))
              (quotedFreeAssignment free) p :=
          ih (hbound.seqCons a) (by simp [hbound, hlen]) hbody
        _ ↔ Semiformula.Eval (a :> quotedBoundAssignment bound)
              (quotedFreeAssignment free) p := by
          rw [quotedBoundAssignment_seqCons hbound hlen a]

/-! ## The finite Peano-minus recognizer -/

/-- Sentence specialization of quotation adequacy.  The coded free
environment is arbitrary: a standard sentence has no free variables to read. -/
theorem sigmaTrue_succ_sentence_quote_iff_models (n : ℕ)
    (σ : ArithmeticSentence) (free : V)
    (hbounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) (⌜σ⌝ : V)) :
    SigmaTrue (n + 1) 0 free (⌜σ⌝ : V) ↔
      V↓[ℒₒᵣ] ⊧ σ := by
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hformula := sigmaTrue_succ_quote_iff_eval n
    (Rewriting.emb σ : ArithmeticSemiproposition 0)
    (bound := (0 : V)) (free := free)
    hzeroSeq hlhZero (by
      simpa only [Sentence.quote_def] using hbounded)
  simpa [Sentence.quote_def, models_iff, Semiformula.eval_emb,
    Matrix.empty_eq] using hformula

/-- Every code accepted by the finite `PeanoMinus` recognizer and lying in
the externally fixed quantifier-group bound is true in the unified successor
truth predicate.  The recognizer's standardness theorem is essential here:
it rules out nonstandard fake axioms before quotation adequacy is invoked. -/
theorem sigmaTrue_succ_of_mem_peanoMinus_delta1Class (n : ℕ)
    {free p : V}
    (hp : p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) 0 free p := by
  rcases mem_peanoMinus_delta1Class_iff.mp hp with ⟨σ, hσ, rfl⟩
  apply (sigmaTrue_succ_sentence_quote_iff_models n σ free hbounded).mpr
  letI : V↓[ℒₒᵣ] ⊧* PeanoMinus := models_of_subtheory hPA
  exact models_of_mem hσ

/-- Version with the genuine-environment premise used by the derivation
soundness interface.  The stronger theorem above shows that this premise is
not needed for standard sentence codes. -/
theorem sigmaTrue_succ_of_mem_peanoMinus_delta1Class_of_seq (n : ℕ)
    {free p : V}
    (_hfree : Arithmetic.Seq free)
    (hp : p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) p) :
    SigmaTrue (n + 1) 0 free p :=
  sigmaTrue_succ_of_mem_peanoMinus_delta1Class n hp hbounded

end LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms
