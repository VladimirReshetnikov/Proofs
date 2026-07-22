import BoundedPAConsistency.DynamicTruthShiftInvariantFormula
import BoundedPAConsistency.DynamicTruthCompiledLocalBundle
import BoundedPAConsistency.DynamicTruthCrossLevelFormula
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import Foundation.FirstOrder.Completeness

/-!
# Zero premise for dynamic shift invariance

The shift-invariance field is proved by induction on a represented formula
code.  At code zero its bounded-formula guard is impossible, independently
of the lower truth predicate and of every field already accumulated by the
staged compiler.  This module turns that elementary observation into the
exact typed PA proof required by `PAInductionKernel.proveZero`.

The source proof is a fixed finite derivation.  Its later specialization may
insert a nonstandard lower truth formula and nonstandard hierarchy levels;
neither is decoded.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## The uniform arithmetic non-domain fact -/

/-- In every PA model, code zero is outside the bounded formula domain at
every hierarchy level. -/
noncomputable def arithmeticZeroNotBoundedSentence : ArithmeticSentence :=
  ∀⁰ ∼((quantifierBoundedCodeDef ℒₒᵣ).val/[
    #0, (‘0’ : ArithmeticSemiterm Empty 1)])

/-- PA proves the non-domain fact used by the structural zero branch. -/
noncomputable def arithmeticZeroNotBoundedProof :
    Peano ⊢! arithmeticZeroNotBoundedSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hPA
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
    simp [models_iff, arithmeticZeroNotBoundedSentence,
      Semiformula.eval_substs, QuantifierBoundedCode]).get

/-- Transport the arithmetic theorem into the fixed source language. -/
noncomputable def liftedArithmeticZeroNotBoundedProof :
    parameterTemplatePeano 3 2 ⊢!
      arithmeticZeroNotBoundedSentence.lMap (arithmeticHom 3 2) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticZeroNotBoundedSentence from
        ⟨arithmeticZeroNotBoundedProof⟩))).get

/-! ## Fixed source zero branch -/

/-- Arithmetic zero lifted into the shift-invariance source language. -/
noncomputable def sourceZeroTerm : ClosedSemiterm SourceLanguage 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap (arithmeticHom 3 2)

/-- The exact source instance of the unary induction predicate at zero. -/
noncomputable def sourceZeroSentence : Sentence SourceLanguage :=
  sourceShiftInvariantPredicate/[sourceZeroTerm]

/-- Three quantifiers separate the original unary formula-code argument from
its occurrence in the shift-invariance body. -/
private lemma subst_q3_bvar_three {L : Language} {k : Type*}
    (t : Semiterm L k 0) :
    (Rew.subst ![t]).q.q.q (#3 : Semiterm L k 4) =
      Rew.bShift (Rew.bShift (Rew.bShift t)) := by
  change (Rew.subst ![t]).q.q.q
    (#(Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))) = _
  rw [Rew.q_bvar_succ, Rew.q_bvar_succ, Rew.q_bvar_succ,
    Rew.subst_bvar]
  simp

/-- A fixed lifted-PA derivation of the shift-invariance zero branch.  The
free-tail premise is irrelevant because the bounded-domain premise already
contradicts the arithmetic non-domain theorem. -/
noncomputable def sourceZeroProof :
    parameterTemplatePeano 3 2 ⊢! sourceZeroSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro ambient _structure hmodels
    letI : Nonempty _ := ⟨ambient⟩
    have hzero := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          arithmeticZeroNotBoundedSentence.lMap (arithmeticHom 3 2) from
        ⟨liftedArithmeticZeroNotBoundedProof⟩)
    simp [models_iff, arithmeticZeroNotBoundedSentence,
      Semiformula.eval_rew, Semiformula.eval_lMap] at hzero
    simp [models_iff, sourceZeroSentence,
      sourceShiftInvariantPredicate, sourceShiftInvariantBody,
      sourceBoundedDomain, DynamicTruthTemplateFormula.apply₂,
      liftArithmeticFormula, sourceZeroTerm,
      Semiformula.eval_rew, Semiformula.eval_lMap]
    intro bound shifted free _freeTail hbounded
    let lowerLevel : _ :=
      (parameterTerm (n := 3) (0 : Fin 2)).val
        ![free, shifted, bound] Empty.elim
    exfalso
    apply hzero lowerLevel
    convert hbounded using 1
    congr 1
    funext i
    cases i using Fin.cases with
    | zero =>
        simp [Function.comp_def, lowerLevel, parameterTerm]
        congr 2
        funext i
        exact i.elim0
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            simp only [Function.comp_def, Rew.subst_bvar,
              Matrix.cons_val_succ, Matrix.cons_val_zero,
              FirstOrder.Semiterm.val_bvar]
            rw [subst_q3_bvar_three]
            simp [FirstOrder.Semiterm.val_bShift,
              FirstOrder.Semiterm.val_lMap]
        | succ i => exact i.elim0).get

/-! ## Exact model-coded specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The quotation obtained after eliminating the impossible source free
variable type from arithmetic zero. -/
noncomputable def typedSourceZeroTerm :
    Bootstrapping.Semiterm V ℒₒᵣ 0 :=
  ⌜(Rew.emb (‘0’ : ArithmeticSemiterm Empty 0) :
      ArithmeticSemiterm ℕ 0)⌝

@[simp] theorem typedSourceZeroTerm_eq_zero :
    typedSourceZeroTerm (V := V) =
      (⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
        Bootstrapping.Semiterm V ℒₒᵣ 0) := by
  ext
  simp [typedSourceZeroTerm]

/-- The lifted zero term specializes to the typed represented zero. -/
@[simp] theorem translate_sourceZeroTerm (parameters : Fin 2 → V) :
    translateTerm parameters
        (Rew.emb sourceZeroTerm : SyntacticSemiterm SourceLanguage 0) =
      typedSourceZeroTerm := by
  simpa only [sourceZeroTerm, typedSourceZeroTerm, Rew.emb,
    Semiterm.lMap_map] using
    ModelCodedPredicateParameters.translateTerm_lMap_arithmetic
      parameters (Rew.emb (‘0’ : ArithmeticSemiterm Empty 0))

/-- Specializing the source branch yields literally the zero premise of the
advertised typed shift-invariance predicate. -/
@[simp] theorem translate_sourceZeroSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceZeroSentence) =
      (shiftInvariantPredicateFormula lower lowerLevel upperLevel).subst
        ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
          Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simp [sourceZeroSentence, Rewriting.emb_subst_eq_subst_coe₁]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Compile the fixed source proof at arbitrary model-coded lower syntax and
hierarchy levels. -/
noncomputable def compiledShiftInvariantZeroProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      (shiftInvariantPredicateFormula lower lowerLevel upperLevel).subst
        ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
          Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simpa only [translate_sourceZeroSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel]
      hlower sourceZeroProof)

/-- Exact positive-orbit zero proof. -/
noncomputable def orbitShiftInvariantZeroProof (n : V) :
    Peano.internalize V ⊢!
      (shiftInvariantPredicateFormula
        (truthFormula n) (n + 1) (n + 1 + 1)).subst
        ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
          Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  compiledShiftInvariantZeroProof
    (truthFormula n) (n + 1) (n + 1 + 1) (truthFormula_shift n)

variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- Install the unconditional zero branch under the complete staged context
used by the shift-invariance kernel. -/
noncomputable def orbitShiftInvariantZeroProofFromCrossContext
    (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      crossContext previous
          (LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle.orbitCompiledLocalBundle n)
          (LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula.orbitSuccessorCrossLevelFormula n) 🡒
        (shiftInvariantPredicateFormula
          (truthFormula n) (n + 1) (n + 1 + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  Entailment.C_of_conseq (orbitShiftInvariantZeroProof n)

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantSourceZero
