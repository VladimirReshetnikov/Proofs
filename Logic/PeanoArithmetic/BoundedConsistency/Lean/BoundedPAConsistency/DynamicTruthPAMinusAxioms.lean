import BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic

set_option maxHeartbeats 1000000
set_option maxRecDepth 5000

/-!
# Finite PA-minus axioms for dynamic successor truth

The finite part of PA's represented axiom recognizer has only standard
outputs.  Consequently it can be handled by external recursion on the quoted
axiom, even when the hierarchy level and the lower truth predicate are
nonstandard.  Atomic formulae reduce directly to the canonical coded
quantifier-free evaluator; the remaining cases use the abstract dynamic
Tarski laws.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthPAMinusAxioms

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
open LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.TermEvaluation

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

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

private lemma bounded_all_body {level p : V}
    (h : QuantifierBoundedCode ℒₒᵣ level (^∀ p)) :
    QuantifierBoundedCode ℒₒᵣ level p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using h.1
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isSigmaCode_all_zero hpU hs).elim
    · exact (((isSigmaCode_all_succ_iff hpU).mp hs).1.mono
        (by simp)).quantifierBounded
  · exact ((isPiCode_all_iff hpU).mp hpi).1.quantifierBounded

private lemma bounded_exs_body {level p : V}
    (h : QuantifierBoundedCode ℒₒᵣ level (^∃ p)) :
    QuantifierBoundedCode ℒₒᵣ level p := by
  have hpU : IsUFormula ℒₒᵣ p := by simpa using h.1
  rcases quantifierBoundedCode_iff_sigma_or_pi.mp h with hs | hpi
  · exact ((isSigmaCode_exs_iff hpU).mp hs).1.quantifierBounded
  · rcases zero_or_succ level with rfl | ⟨level, rfl⟩
    · exact (not_isPiCode_exs_zero hpU hpi).elim
    · exact (((isPiCode_exs_succ_iff hpU).mp hpi).1.mono
        (by simp)).quantifierBounded

/-! ## Atomic quotation adequacy -/

private theorem successorTruth_quote_rel_iff_eval
    {lower : V → V → V → Prop} {lowerLevel upperLevel : V}
    {k arity : ℕ} (R : (ℒₒᵣ).Rel arity)
    (v : Fin arity → SyntacticSemiterm ℒₒᵣ k)
    (bound free : V) :
    SuccessorTruth lower lowerLevel upperLevel bound free
        (⌜Semiformula.rel R v⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) (Semiformula.rel R v) := by
  have hR : (ℒₒᵣ).IsRel (arity : V) (⌜R⌝ : V) := by
    simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) R
  have hterms : IsUTermVec ℒₒᵣ (arity : V)
      (SemitermVec.val
        (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))) :=
    SemitermVec.isUTermVec
      (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))
  change SuccessorTruth lower lowerLevel upperLevel bound free
      (^rel (arity : V) (⌜R⌝ : V)
        (SemitermVec.val
          (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k)))) ↔ _
  rw [SuccessorTruth.rel_iff hR hterms]
  cases R with
  | eq =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^rel 2 (Arithmetic.eqIndex : V) ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
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
          (^rel 2 (Arithmetic.ltIndex : V) ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        (v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) <
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_lt_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]

private theorem successorTruth_quote_nrel_iff_eval
    {lower : V → V → V → Prop} {lowerLevel upperLevel : V}
    {k arity : ℕ} (R : (ℒₒᵣ).Rel arity)
    (v : Fin arity → SyntacticSemiterm ℒₒᵣ k)
    (bound free : V) :
    SuccessorTruth lower lowerLevel upperLevel bound free
        (⌜Semiformula.nrel R v⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) (Semiformula.nrel R v) := by
  have hR : (ℒₒᵣ).IsRel (arity : V) (⌜R⌝ : V) := by
    simpa using codeIn_rel_quote (V := V) (L := ℒₒᵣ) R
  have hterms : IsUTermVec ℒₒᵣ (arity : V)
      (SemitermVec.val
        (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))) :=
    SemitermVec.isUTermVec
      (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k))
  change SuccessorTruth lower lowerLevel upperLevel bound free
      (^nrel (arity : V) (⌜R⌝ : V)
        (SemitermVec.val
          (fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V ℒₒᵣ k)))) ↔ _
  rw [SuccessorTruth.nrel_iff hR hterms]
  cases R with
  | eq =>
      have hv0 : IsUTerm ℒₒᵣ (⌜v 0⌝ : V) :=
        (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      have hv1 : IsUTerm ℒₒᵣ (⌜v 1⌝ : V) :=
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ k).isUTerm
      change QFTrue bound free
          (^nrel 2 (Arithmetic.eqIndex : V) ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
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
          (^nrel 2 (Arithmetic.ltIndex : V) ?[(⌜v 0⌝ : V), (⌜v 1⌝ : V)]) ↔
        ¬(v 0).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free) <
          (v 1).val (quotedBoundAssignment bound)
            (quotedFreeAssignment free)
      rw [qfTrue_nlt_atom_iff hv0 hv1,
        termValue_quote_iff_val, termValue_quote_iff_val]

/-! ## Standard formula quotation adequacy -/

/-- Dynamic successor truth agrees with ordinary Tarski evaluation on every
standard quoted arithmetic formula in the advertised bounded domain. -/
theorem successorTruth_quote_iff_eval
    {lower : V → V → V → Prop} {level nextLevel : V}
    (laws : Laws level (SuccessorTruth lower level nextLevel))
    {k : ℕ} (phi : ArithmeticSemiproposition k) {bound free : V}
    (hbound : Arithmetic.Seq bound) (hlen : lh bound = (k : V))
    (hbounded : QuantifierBoundedCode ℒₒᵣ level (⌜phi⌝ : V)) :
    SuccessorTruth lower level nextLevel bound free (⌜phi⌝ : V) ↔
      Semiformula.Eval (quotedBoundAssignment bound)
        (quotedFreeAssignment free) phi := by
  induction phi using Semiformula.rec' generalizing bound with
  | hrel R v =>
      exact successorTruth_quote_rel_iff_eval R v bound free
  | hnrel R v =>
      exact successorTruth_quote_nrel_iff_eval R v bound free
  | hverum =>
      constructor
      · intro _
        simp
      · intro _
        exact laws.verum bound free
  | hfalsum =>
      constructor
      · intro h
        exact (laws.falsum bound free h).elim
      · simp
  | hand p q ihp ihq =>
      have hparts := bounded_and_parts hbounded
      have hpcode : (⌜p⌝ : V) = (Semiformula.typedQuote V p).val :=
        Semiformula.quote_def p
      have hqcode : (⌜q⌝ : V) = (Semiformula.typedQuote V q).val :=
        Semiformula.quote_def q
      have ihp' : SuccessorTruth lower level nextLevel bound free
          (Semiformula.typedQuote V p).val ↔
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p := by
        rw [← hpcode]
        exact ihp hbound hlen hparts.1
      have ihq' : SuccessorTruth lower level nextLevel bound free
          (Semiformula.typedQuote V q).val ↔
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q := by
        rw [← hqcode]
        exact ihq hbound hlen hparts.2
      change SuccessorTruth lower level nextLevel bound free
          ((Semiformula.typedQuote V p).val ^⋏
            (Semiformula.typedQuote V q).val) ↔
        Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p ∧
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q
      rw [laws.and_iff hbounded, ihp', ihq']
  | hor p q ihp ihq =>
      have hparts := bounded_or_parts hbounded
      have hpcode : (⌜p⌝ : V) = (Semiformula.typedQuote V p).val :=
        Semiformula.quote_def p
      have hqcode : (⌜q⌝ : V) = (Semiformula.typedQuote V q).val :=
        Semiformula.quote_def q
      have ihp' : SuccessorTruth lower level nextLevel bound free
          (Semiformula.typedQuote V p).val ↔
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p := by
        rw [← hpcode]
        exact ihp hbound hlen hparts.1
      have ihq' : SuccessorTruth lower level nextLevel bound free
          (Semiformula.typedQuote V q).val ↔
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q := by
        rw [← hqcode]
        exact ihq hbound hlen hparts.2
      change SuccessorTruth lower level nextLevel bound free
          ((Semiformula.typedQuote V p).val ^⋎
            (Semiformula.typedQuote V q).val) ↔
        Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) p ∨
          Semiformula.Eval (quotedBoundAssignment bound)
            (quotedFreeAssignment free) q
      rw [laws.or_iff hbounded, ihp', ihq']
  | hall p ih =>
      have hbody := bounded_all_body hbounded
      have hpcode : (⌜p⌝ : V) = (Semiformula.typedQuote V p).val :=
        Semiformula.quote_def p
      change SuccessorTruth lower level nextLevel bound free
          (^∀ (Semiformula.typedQuote V p).val) ↔
        ∀ a : V, Semiformula.Eval
          (a :> quotedBoundAssignment bound)
          (quotedFreeAssignment free) p
      rw [laws.all_iff hbounded]
      apply forall_congr'
      intro a
      calc
        SuccessorTruth lower level nextLevel (bound ⁀' a) free
            (Semiformula.typedQuote V p).val ↔
            Semiformula.Eval (quotedBoundAssignment (bound ⁀' a))
              (quotedFreeAssignment free) p :=
          by
            rw [← hpcode]
            exact ih (hbound.seqCons a)
              (by simp [hbound, hlen]) hbody
        _ ↔ Semiformula.Eval (a :> quotedBoundAssignment bound)
              (quotedFreeAssignment free) p := by
          rw [quotedBoundAssignment_seqCons hbound hlen a]
  | hexs p ih =>
      have hbody := bounded_exs_body hbounded
      have hpcode : (⌜p⌝ : V) = (Semiformula.typedQuote V p).val :=
        Semiformula.quote_def p
      change SuccessorTruth lower level nextLevel bound free
          (^∃ (Semiformula.typedQuote V p).val) ↔
        ∃ a : V, Semiformula.Eval
          (a :> quotedBoundAssignment bound)
          (quotedFreeAssignment free) p
      rw [laws.exs_iff hbounded]
      apply exists_congr
      intro a
      calc
        SuccessorTruth lower level nextLevel (bound ⁀' a) free
            (Semiformula.typedQuote V p).val ↔
            Semiformula.Eval (quotedBoundAssignment (bound ⁀' a))
              (quotedFreeAssignment free) p :=
          by
            rw [← hpcode]
            exact ih (hbound.seqCons a)
              (by simp [hbound, hlen]) hbody
        _ ↔ Semiformula.Eval (a :> quotedBoundAssignment bound)
              (quotedFreeAssignment free) p := by
          rw [quotedBoundAssignment_seqCons hbound hlen a]

/-- Sentence specialization of dynamic quotation adequacy. -/
theorem successorTruth_sentence_quote_iff_models
    {lower : V → V → V → Prop} {level nextLevel : V}
    (laws : Laws level (SuccessorTruth lower level nextLevel))
    (sigma : ArithmeticSentence) (free : V)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level (⌜sigma⌝ : V)) :
    SuccessorTruth lower level nextLevel 0 free (⌜sigma⌝ : V) ↔
      V↓[ℒₒᵣ] ⊧ sigma := by
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  have hformula := successorTruth_quote_iff_eval laws
    (Rewriting.emb sigma : ArithmeticSemiproposition 0)
    (bound := (0 : V)) (free := free) hzeroSeq hlhZero (by
      simpa only [Sentence.quote_def] using hbounded)
  simpa [Sentence.quote_def, models_iff, Semiformula.eval_emb,
    Matrix.empty_eq] using hformula

/-- Every code accepted by the finite `PeanoMinus` recognizer is true in
dynamic successor truth, uniformly in the lower predicate and model levels. -/
theorem successorTruth_of_mem_peanoMinus_delta1Class
    {lower : V → V → V → Prop} {level nextLevel : V}
    (laws : Laws level (SuccessorTruth lower level nextLevel))
    {free p : V}
    (hp : p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level p) :
    SuccessorTruth lower level nextLevel 0 free p := by
  rcases mem_peanoMinus_delta1Class_iff.mp hp with ⟨sigma, hsigma, rfl⟩
  apply (successorTruth_sentence_quote_iff_models
    laws sigma free hbounded).mpr
  letI : V↓[ℒₒᵣ] ⊧* PeanoMinus := models_of_subtheory hPA
  exact models_of_mem hsigma

/-- Environment-premise form consumed by dynamic PA-axiom soundness. -/
theorem successorTruth_of_mem_peanoMinus_delta1Class_of_seq
    {lower : V → V → V → Prop} {level nextLevel : V}
    (laws : Laws level (SuccessorTruth lower level nextLevel))
    {free p : V}
    (_hfree : Arithmetic.Seq free)
    (hp : p ∈ (PeanoMinus : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level p) :
    SuccessorTruth lower level nextLevel 0 free p :=
  successorTruth_of_mem_peanoMinus_delta1Class laws hp hbounded

/-! ## Complete PA recognizer -/

/-- Complete dynamic PA-axiom soundness once the three explicit model-
induction interfaces have been supplied.  This theorem is the semantic core
that the fixed-source proof compiler specializes at adjacent model-coded
levels. -/
theorem successorTruth_of_mem_pa_delta1Class
    {lower : V → V → V → Prop} {level nextLevel : V}
    (laws : Laws level (SuccessorTruth lower level nextLevel))
    (hsubstitution : ∀ q,
      DynamicTruthSubstitutionInvariantPositiveRankStrongStep.SubstitutionInvariantAt
        (SuccessorTruth lower level nextLevel) level q)
    (hinduction : SemanticInduction
      (SuccessorTruth lower level nextLevel))
    (hfreeIndependent : FreeEnvironmentIndependence level
      (SuccessorTruth lower level nextLevel))
    (hclosure : UniversalClosureIntroduction level
      (SuccessorTruth lower level nextLevel))
    {free p : V}
    (hp : p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ level p)
    (hfree : Arithmetic.Seq free) :
    SuccessorTruth lower level nextLevel 0 free p := by
  apply of_mem_pa_delta1Class laws hsubstitution hinduction
    hfreeIndependent hclosure _ hp hbounded hfree
  intro q assignment hq hqBound hassignment
  exact successorTruth_of_mem_peanoMinus_delta1Class_of_seq
    laws hassignment hq hqBound

end LeanProofs.BoundedPAConsistency.DynamicTruthPAMinusAxioms
