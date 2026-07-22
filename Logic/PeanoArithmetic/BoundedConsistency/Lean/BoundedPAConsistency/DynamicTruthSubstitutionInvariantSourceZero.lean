import BoundedPAConsistency.DynamicTruthCompiledLocalBundle
import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
import BoundedPAConsistency.DynamicTruthCrossLevelFormula
import BoundedPAConsistency.DynamicTruthShiftInvariantFormula
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import Foundation.FirstOrder.Completeness

/-!
# Zero case for the structural substitution-invariance source predicate

The substitution stage of the staged certificate proof runs after the new
local, cross-level, and shift fields have been established.  We retain those
fields as an ordinary source formula in the same one-predicate language as
the substitution invariant.  No nullary atom stands in for that context.

At the formula-code induction base the distinguished code is zero.  Code
zero is not a semiformula code, so the guarded substitution implication is
vacuous.  This module constructs the corresponding fixed lifted-PA proof and
compiles it to the exact represented zero premise.  A final projection lemma
records how the complete staged `shiftContext` supplies the smaller
structural antecedent used here.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## The actual source antecedent available before substitution -/

/-- The already established new fields, retaining their source syntax and
right-associated certificate order.  The preceding master sentence is not
encoded by an opaque source atom: the staged context projects to this
antecedent by a concrete Hilbert derivation below. -/
noncomputable def sourceAvailableContext : Sentence SourceLanguage :=
  (localProjectionSentence ⋏
      (memberValiditySentence ⋏ universalLeafProjectionSentence)) ⋏
    (sourceCrossLevelSentence ⋏ sourceShiftInvariantSentence)

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Typed form of the structural antecedent. -/
noncomputable def availableContextFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  (localProjectionFormula lower lowerLevel upperLevel ⋏
      (memberValidityFormula lower lowerLevel upperLevel ⋏
        universalLeafProjectionFormula lower lowerLevel upperLevel)) ⋏
    (crossLevelFormula lower lowerLevel upperLevel ⋏
      shiftInvariantFormula lower lowerLevel upperLevel)

/-- Literal specialization of the structural source antecedent. -/
@[simp] theorem translate_sourceAvailableContext
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAvailableContext) =
      availableContextFormula lower lowerLevel upperLevel := by
  simp [sourceAvailableContext, availableContextFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! ## Arithmetic non-domain fact -/

/-- Uniform arithmetic statement that code zero is not a semiformula code,
at any bound-variable arity. -/
noncomputable def arithmeticZeroSemiformulaSentence : ArithmeticSentence :=
  ∀⁰
    ∼((isSemiformula ℒₒᵣ).sigma.val/[
      #0, (‘0’ : ArithmeticSemiterm Empty 1)])

/-- PA proves that zero is outside every semiformula-code domain. -/
noncomputable def arithmeticZeroSemiformulaProof :
    Peano ⊢! arithmeticZeroSemiformulaSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hPA
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
    simp [models_iff, arithmeticZeroSemiformulaSentence,
      Semiformula.eval_substs]).get

/-- Transport the arithmetic fact into the one-predicate, two-parameter
source language without adding any axiom about the placeholder. -/
noncomputable def liftedArithmeticZeroSemiformulaProof :
    parameterTemplatePeano 3 2 ⊢!
      arithmeticZeroSemiformulaSentence.lMap (arithmeticHom 3 2) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticZeroSemiformulaSentence from
        ⟨arithmeticZeroSemiformulaProof⟩))).get

/-! ## The literal source zero premise -/

/-- Arithmetic zero in the fixed substitution source language. -/
noncomputable def sourceZeroTerm : ClosedSemiterm SourceLanguage 0 :=
  ((‘0’ : ArithmeticSemiterm Empty 0)).lMap (arithmeticHom 3 2)

/-- The quotation obtained by eliminating the impossible free-variable type
from the source arithmetic zero. -/
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

/-- The source zero term specializes to the literal represented arithmetic
zero expected by `PAInductionKernel.proveZero`. -/
@[simp] theorem translate_sourceZeroTerm (parameters : Fin 2 → V) :
    translateTerm parameters
        (Rew.emb sourceZeroTerm : SyntacticSemiterm SourceLanguage 0) =
      typedSourceZeroTerm := by
  simpa only [sourceZeroTerm, typedSourceZeroTerm,
    Rew.emb, Semiterm.lMap_map] using
    ModelCodedPredicateParameters.translateTerm_lMap_arithmetic
      parameters (Rew.emb (‘0’ : ArithmeticSemiterm Empty 0))

/-- The exact structural-context zero premise for formula-code induction. -/
noncomputable def sourceZeroSentence : Sentence SourceLanguage :=
  sourceAvailableContext 🡒
    sourceSubstitutionInvariantPredicate/[sourceZeroTerm]

/-- Six quantifiers separate the unary predicate argument from its original
body occurrence at de Bruijn index six. -/
private lemma subst_q6_bvar_six {L : Language} {k : Type*}
    (t : Semiterm L k 0) :
    (Rew.subst ![t]).q.q.q.q.q.q (#6 : Semiterm L k 7) =
      Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (Rew.bShift (Rew.bShift t))))) := by
  change (Rew.subst ![t]).q.q.q.q.q.q
    (#(Fin.succ (Fin.succ (Fin.succ (Fin.succ
      (Fin.succ (Fin.succ (0 : Fin 1)))))))) = _
  rw [Rew.q_bvar_succ, Rew.q_bvar_succ, Rew.q_bvar_succ,
    Rew.q_bvar_succ, Rew.q_bvar_succ, Rew.q_bvar_succ,
    Rew.subst_bvar]
  simp

/-- A fixed lifted-PA derivation of the substitution-invariance base case. -/
noncomputable def sourceZeroProof :
    parameterTemplatePeano 3 2 ⊢! sourceZeroSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceZeroSentence, sourceAvailableContext,
      sourceSubstitutionInvariantPredicate,
      sourceSubstitutionInvariantBody, sourceSemiformula,
      DynamicTruthTemplateFormula.apply₂,
      liftArithmeticFormula, sourceZeroTerm,
      Semiformula.eval_rew, Semiformula.eval_lMap]
    intro ambient _structure hmodels
      _local _member _leaf _cross _shift
      subBound terms termBound free bound arity
      _terms _boundLength _environment hsemiformula
    letI : Nonempty _ := ⟨ambient⟩
    have hzero := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          arithmeticZeroSemiformulaSentence.lMap (arithmeticHom 3 2) from
        ⟨liftedArithmeticZeroSemiformulaProof⟩)
    simp [models_iff, arithmeticZeroSemiformulaSentence,
      Semiformula.eval_rew, Semiformula.eval_lMap] at hzero
    exfalso
    apply hzero arity
    convert hsemiformula using 1
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => simp [Function.comp_def]
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            simp only [Function.comp_def, Rew.subst_bvar,
              Matrix.cons_val_succ, Matrix.cons_val_zero,
              FirstOrder.Semiterm.val_bvar]
            rw [subst_q6_bvar_six]
            simp [FirstOrder.Semiterm.val_bShift,
              FirstOrder.Semiterm.val_lMap]
        | succ i => exact i.elim0
    ).get

/-! ## Exact compilation of the zero premise -/

/-- Specialization of the fixed source sentence is exactly the zero premise
for the advertised unary substitution-invariance predicate. -/
@[simp] theorem translate_sourceZeroSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceZeroSentence) =
      availableContextFormula lower lowerLevel upperLevel 🡒
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simp [sourceZeroSentence, Semiformula.imp_def,
    Rewriting.emb_subst_eq_subst_coe₁]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Compile the fixed standard derivation at arbitrary, possibly
nonstandard, lower truth syntax and hierarchy levels. -/
noncomputable def compiledSubstitutionInvariantZeroProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      availableContextFormula lower lowerLevel upperLevel 🡒
        (substitutionInvariantPredicateFormula
          lower lowerLevel upperLevel).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simpa only [translate_sourceZeroSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel]
      hlower sourceZeroProof)

/-! ## Alignment with the positive orbit and the staged context -/

/-- The three concrete fields available immediately before substitution at
one positive dynamic-truth step. -/
noncomputable def orbitAvailableContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  orbitCompiledLocalBundle n ⋏
    (orbitSuccessorCrossLevelFormula n ⋏
      orbitSuccessorShiftInvariantFormula n)

/-- The fixed source antecedent specializes literally to those three orbit
fields. -/
@[simp] theorem availableContextFormula_orbit (n : V) :
    availableContextFormula (truthFormula n) (n + 1) (n + 1 + 1) =
      orbitAvailableContext n := by
  simp [availableContextFormula, orbitAvailableContext,
    orbitCompiledLocalBundle, orbitLocalProjectionFormula,
    localProjectionFormula,
    orbitMemberValidityFormula, orbitUniversalLeafProjectionFormula,
    orbitSuccessorCrossLevelFormula,
    orbitSuccessorShiftInvariantFormula, truthFormula_succ]

/-- Exact represented zero premise at an arbitrary positive orbit step. -/
noncomputable def orbitSubstitutionInvariantZeroProof (n : V) :
    Peano.internalize V ⊢!
      orbitAvailableContext n 🡒
        (substitutionInvariantPredicateFormula
          (truthFormula n) (n + 1) (n + 1 + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] := by
  simpa only [availableContextFormula_orbit] using
    (compiledSubstitutionInvariantZeroProof
      (truthFormula n) (n + 1) (n + 1 + 1)
      (truthFormula_shift n))

variable [V↓[ℒₒᵣ] ⊧* Peano]

/-- The full staged context proves the smaller structural antecedent used by
the source zero proof.  This is the explicit seam to `shiftContext`: the
preceding master sentence is retained by the staged compiler, then discarded
by ordinary conjunction elimination rather than represented by a source
assumption. -/
noncomputable def proveAvailableFromShiftContext
    (previous : TruthCertificateFields (V := V))
    (localField crossField shiftField : Bootstrapping.Formula V ℒₒᵣ) :
    Peano.internalize V ⊢!
      shiftContext previous localField crossField shiftField 🡒
        (localField ⋏ (crossField ⋏ shiftField)) := by
  unfold shiftContext crossContext localContext
  exact Entailment.CK_of_C_of_C
    (Entailment.C_trans Entailment.and₁ <|
      Entailment.C_trans Entailment.and₁ Entailment.and₂)
    (Entailment.CK_of_C_of_C
      (Entailment.C_trans Entailment.and₁ Entailment.and₂)
      Entailment.and₂)

/-- Orbit-specialized projection from the exact context used by the staged
substitution kernel. -/
noncomputable def proveOrbitAvailableFromShiftContext
    (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      shiftContext previous
          (orbitCompiledLocalBundle n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n) 🡒
        orbitAvailableContext n := by
  simpa only [orbitAvailableContext] using
    (proveAvailableFromShiftContext previous
      (orbitCompiledLocalBundle n)
      (orbitSuccessorCrossLevelFormula n)
      (orbitSuccessorShiftInvariantFormula n))

/-- The production local field contains the three structural eliminators as
its left conjunct and the quantifier-free introduction anchor as its right
conjunct.  Project the older source antecedent from that larger field without
discarding the anchor from the staged certificate itself. -/
noncomputable def proveOrbitAvailableFromAugmentedShiftContext
    (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      shiftContext previous
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n) 🡒
        orbitAvailableContext n := by
  unfold shiftContext crossContext localContext orbitAvailableContext
  unfold orbitCompiledLocalBundleWithQuantifierFreeIntroduction
  exact Entailment.CK_of_C_of_C
    (Entailment.C_trans Entailment.and₁ <|
      Entailment.C_trans Entailment.and₁ <|
        Entailment.C_trans Entailment.and₂ Entailment.and₁)
    (Entailment.CK_of_C_of_C
      (Entailment.C_trans Entailment.and₁ Entailment.and₂)
      Entailment.and₂)

/-- The exact zero premise under the complete staged substitution context.
This term can be installed directly as `PAInductionKernel.proveZero` once the
matching successor premise has been constructed. -/
noncomputable def orbitSubstitutionInvariantZeroProofFromShiftContext
    (previous : TruthCertificateFields (V := V)) (n : V) :
    Peano.internalize V ⊢!
      shiftContext previous
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n) 🡒
        (substitutionInvariantPredicateFormula
          (truthFormula n) (n + 1) (n + 1 + 1)).subst
          ![(⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ :
            Bootstrapping.Semiterm V ℒₒᵣ 0)] :=
  Entailment.C_trans
    (proveOrbitAvailableFromAugmentedShiftContext previous n)
    (orbitSubstitutionInvariantZeroProof n)

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantSourceZero
