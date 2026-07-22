import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
import BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero
import BoundedPAConsistency.DynamicTruthCompiledLocalBundle
import BoundedPAConsistency.DynamicTruthCrossLevelFormula
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import Foundation.FirstOrder.Completeness

/-!
# Zero premise for dynamic PA-axiom soundness

The axiom-soundness induction predicate is guarded both by PA's represented
axiom recognizer and by the represented hierarchy domain.  At formula code
zero the latter guard is impossible at every level.  We reuse the explicit
PA non-domain theorem from the shift-invariance base case and construct the
exact source, model-coded, orbit, and staged proof terms needed by the final
axiom-soundness kernel.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZero

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Fixed source zero branch -/

/-- Formula-code zero lifted into the common dynamic-truth source language. -/
noncomputable def sourceFormulaCodeZeroTerm :
    ClosedSemiterm SourceLanguage 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap (arithmeticHom 3 2)

/-- The exact source instance of axiom soundness at formula code zero. -/
noncomputable def sourceAxiomSoundnessZeroSentence :
    Sentence SourceLanguage :=
  sourceAxiomSoundnessPredicate/[sourceFormulaCodeZeroTerm]

/-- One quantifier separates the unary formula-code argument from its
occurrence in the axiom-soundness body. -/
private lemma subst_q_bvar_one {L : Language} {k : Type*}
    (t : Semiterm L k 0) :
    (Rew.subst ![t]).q (#1 : Semiterm L k 2) = Rew.bShift t := by
  change (Rew.subst ![t]).q (#(Fin.succ (0 : Fin 1))) = _
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  simp

/-- A fixed lifted-PA proof of the zero branch.  The recognized-axiom and
free-sequence assumptions are retained, but the bounded-domain assumption
contradicts PA's theorem that zero is not a formula code. -/
noncomputable def sourceAxiomSoundnessZeroProof :
    parameterTemplatePeano 3 2 ⊢! sourceAxiomSoundnessZeroSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro ambient _structure hmodels
    letI : Nonempty _ := ⟨ambient⟩
    have hzero := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero.arithmeticZeroNotBoundedSentence.lMap
            (arithmeticHom 3 2) from
        ⟨LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero.liftedArithmeticZeroNotBoundedProof⟩)
    simp [models_iff,
      LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero.arithmeticZeroNotBoundedSentence,
      Semiformula.eval_rew, Semiformula.eval_lMap] at hzero
    simp [models_iff, sourceAxiomSoundnessZeroSentence,
      sourceAxiomSoundnessPredicate, sourceAxiomSoundnessBody,
      sourceAxiomBoundedDomain, DynamicTruthTemplateFormula.apply₂,
      liftArithmeticFormula, sourceFormulaCodeZeroTerm,
      Semiformula.eval_rew, Semiformula.eval_lMap]
    intro free _recognized hbounded _freeSequence
    let lowerLevel : _ :=
      (parameterTerm (n := 1) (0 : Fin 2)).val ![free] Empty.elim
    exfalso
    apply hzero lowerLevel
    convert hbounded using 1
    congr 1
    funext i
    cases i using Fin.cases with
    | zero =>
        simp [Function.comp_def, lowerLevel, parameterTerm]
        congr 2
        funext j
        exact j.elim0
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            simp only [Function.comp_def, Rew.subst_bvar,
              Matrix.cons_val_succ, Matrix.cons_val_zero,
              FirstOrder.Semiterm.val_bvar]
            rw [subst_q_bvar_one]
            simp [FirstOrder.Semiterm.val_bShift,
              FirstOrder.Semiterm.val_lMap]
        | succ i => exact i.elim0).get

/-! ## Exact model-coded specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Typed quotation of the lifted formula-code zero. -/
noncomputable def typedFormulaCodeZeroTerm :
    Bootstrapping.Semiterm V ℒₒᵣ 0 :=
  ⌜(Rew.emb (‘0’ : ArithmeticSemiterm Empty 0) :
      ArithmeticSemiterm ℕ 0)⌝

@[simp] theorem typedFormulaCodeZeroTerm_eq_zero :
    typedFormulaCodeZeroTerm (V := V) =
      (⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
        Bootstrapping.Semiterm V ℒₒᵣ 0) := by
  ext
  simp [typedFormulaCodeZeroTerm]

@[simp] theorem translate_sourceFormulaCodeZeroTerm
    (parameters : Fin 2 → V) :
    translateTerm parameters
        (Rew.emb sourceFormulaCodeZeroTerm :
          SyntacticSemiterm SourceLanguage 0) =
      typedFormulaCodeZeroTerm := by
  simpa only [sourceFormulaCodeZeroTerm, typedFormulaCodeZeroTerm,
    Rew.emb, Semiterm.lMap_map] using
    ModelCodedPredicateParameters.translateTerm_lMap_arithmetic
      parameters (Rew.emb (‘0’ : ArithmeticSemiterm Empty 0))

/-- Literal translation of the source zero branch. -/
@[simp] theorem translate_sourceAxiomSoundnessZeroSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomSoundnessZeroSentence) =
      (axiomSoundnessPredicateFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        lowerLevel).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simp [sourceAxiomSoundnessZeroSentence,
    Rewriting.emb_subst_eq_subst_coe₁]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Compile the fixed source derivation at arbitrary model-coded lower truth
syntax and arbitrary hierarchy levels. -/
noncomputable def compiledAxiomSoundnessZeroProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      (axiomSoundnessPredicateFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        lowerLevel).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simpa only [translate_sourceAxiomSoundnessZeroSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel]
      hlower sourceAxiomSoundnessZeroProof)

/-- Exact positive-orbit axiom-soundness zero proof. -/
noncomputable def orbitAxiomSoundnessZeroProof (n : V) :
    Peano.internalize V ⊢!
      (axiomSoundnessPredicateFormula
        (truthFormula (n + 1)) (n + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simpa only [truthFormula_succ] using
    (compiledAxiomSoundnessZeroProof
      (truthFormula n) (n + 1) (n + 1 + 1)
      (truthFormula_shift n))

variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- Install the unconditional zero branch under the complete staged context
used by axiom-soundness induction. -/
noncomputable def orbitAxiomSoundnessZeroProofFromSubstitutionContext
    (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      substitutionContext previous
          (LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle.orbitCompiledLocalBundle n)
          (LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula.orbitSuccessorCrossLevelFormula n)
          (LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula.orbitSuccessorShiftInvariantFormula n)
          (LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula.orbitSuccessorSubstitutionInvariantFormula n) 🡒
        (axiomSoundnessPredicateFormula
          (truthFormula (n + 1)) (n + 1)).subst
            ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
              Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  Entailment.C_of_conseq (orbitAxiomSoundnessZeroProof n)

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSourceZero
