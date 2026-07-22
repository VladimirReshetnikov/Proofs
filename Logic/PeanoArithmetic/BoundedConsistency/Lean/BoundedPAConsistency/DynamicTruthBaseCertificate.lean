import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.DynamicTruthFamily
import BoundedPAConsistency.FixedLevelTruthSubstitution
import Foundation.FirstOrder.Completeness

/-!
# Proof-producing base certificate for the dynamic truth orbit

The represented certificate recursion cannot start from external truth alone:
its zero entry must contain genuine PA derivations of the exact model-coded
field formulas.  At level zero every field is standard syntax, because the
upper truth predicate is the quotation of `SigmaTrue 1`.  This file makes that
bridge explicit.  Each ordinary arithmetic sentence is first proved in PA,
then D1 transports the derivation into an arbitrary ambient PA model.

The definitions intentionally mirror the displayed model-coded formulas.
Their quotation lemmas are syntactic equalities, so no appeal to semantic
extensionality is hidden in the final certificate proof.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Shift-invariance field -/

/-- Ordinary syntax for the free-environment tail premise. -/
noncomputable def standardFreeTailFormula : ArithmeticSemisentence 4 :=
  standardApply₂ isFreeTailDef.val (#1) (#2)

/-- Ordinary syntax for the level-zero bounded-formula premise. -/
noncomputable def standardZeroBoundedDomainFormula :
    ArithmeticSemisentence 4 :=
  standardApply₂ (quantifierBoundedCodeDef ℒₒᵣ).val
    (‘0’ : ArithmeticSemiterm Empty 4) (#3)

/-- Ordinary represented-shift witness evaluated by the first positive truth
predicate. -/
noncomputable def standardLevelZeroShiftedTruthWitness :
    ArithmeticSemisentence 4 :=
  ∃⁰
    (standardApply₂ (shiftGraph ℒₒᵣ).val (#0) (#4) ⋏
      LogicalConnective.iff
        (standardApply₃ levelZeroTruthSyntax (#1) (#2) (#0))
        (standardApply₃ levelZeroTruthSyntax (#1) (#3) (#4)))

/-- The ordinary arithmetic sentence whose quotation is the exact base
shift-invariance certificate field. -/
noncomputable def standardBaseShiftInvariantSentence : ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰
    (Arrow.arrow
      (standardFreeTailFormula ⋏ standardZeroBoundedDomainFormula)
      standardLevelZeroShiftedTruthWitness)

/-- Quotation commutes with every constructor in the ordinary base shift
sentence. -/
@[simp] theorem typedQuote_standardBaseShiftInvariantSentence :
    (⌜standardBaseShiftInvariantSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      baseShiftInvariantFormula := by
  simp [standardBaseShiftInvariantSentence,
    standardFreeTailFormula, standardZeroBoundedDomainFormula,
    standardLevelZeroShiftedTruthWitness,
    baseShiftInvariantFormula_eq_upper,
    upperShiftInvariantFormula, freeTailFormula, boundedDomainFormula,
    shiftedTruthWitnessFormula, DynamicTruthFormula.apply₃,
    DynamicTruthFormula.levelZeroTruthFormula_eq_typedQuote]

/-- PA proves the ordinary level-zero shift law.  The semantic argument is
uniform over arbitrary PA models and arbitrary, possibly nonstandard, coded
formulas and environments. -/
noncomputable def standardBaseShiftInvariantProof :
    Peano ⊢! standardBaseShiftInvariantSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseShiftInvariantSentence,
      standardFreeTailFormula, standardZeroBoundedDomainFormula,
      standardLevelZeroShiftedTruthWitness, standardApply₂,
      standardApply₃]
    intro p shifted free bound htail hbounded
    have hbounded' : QuantifierBoundedCode ℒₒᵣ
        (levelCode (V := M) 0) p := by
      apply OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mpr
      simpa [levelCode] using hbounded
    simpa [eval_levelZeroTruthSyntax_iff] using
      (sigmaTrue_succ_shift_iff (V := M) 0 htail hbounded')).get

/-- The actual typed PA derivation of the exact base shift field. -/
noncomputable def baseShiftInvariantProof :
    Peano.internalize V ⊢! baseShiftInvariantFormula := by
  rw [← typedQuote_standardBaseShiftInvariantSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseShiftInvariantSentence from
      ⟨standardBaseShiftInvariantProof⟩)).get

/-! ## Cross-level coherence field -/

/-- Ordinary Sigma-oriented rank-zero domain. -/
noncomputable def standardZeroSigmaDomain : ArithmeticSemisentence 3 :=
  standardApply₂ isSigmaCodeDef.val
    (‘0’ : ArithmeticSemiterm Empty 3) (#2)

/-- Ordinary Pi-oriented rank-zero domain. -/
noncomputable def standardZeroPiDomain : ArithmeticSemisentence 3 :=
  standardApply₂ isPiCodeDef.val
    (‘0’ : ArithmeticSemiterm Empty 3) (#2)

/-- The lower Pi presentation at level zero, with the represented negation
witness left explicit exactly as in the model-coded field. -/
noncomputable def standardBaseLowerPiTruth : ArithmeticSemisentence 3 :=
  standardZeroPiDomain ⋏
    (∃⁰
      (standardApply₂ (negGraph ℒₒᵣ).val (#0) (#3) ⋏
        ∼(standardApply₃ qfTruthDef.val (#1) (#2) (#0))))

/-- Both ordinary rank-zero coherence clauses at fixed environments and
formula code. -/
noncomputable def standardBaseCrossLevelBody :
    ArithmeticSemisentence 3 :=
  (Arrow.arrow standardZeroSigmaDomain
      (LogicalConnective.iff
        (standardApply₃ levelZeroTruthSyntax (#0) (#1) (#2))
        (standardApply₃ qfTruthDef.val (#0) (#1) (#2)))) ⋏
    (Arrow.arrow standardZeroPiDomain
      (LogicalConnective.iff
        (standardApply₃ levelZeroTruthSyntax (#0) (#1) (#2))
        standardBaseLowerPiTruth))

/-- Ordinary sentence whose quotation is the exact base cross-level field. -/
noncomputable def standardBaseCrossLevelSentence : ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ standardBaseCrossLevelBody

/-- Applying a typed ternary formula to the three ambient bound variables in
their original order is syntactically the identity. -/
@[simp] private theorem typedApply₃_bvars_eq_self
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    DynamicTruthFormula.apply₃ S
        (Bootstrapping.Semiterm.bvar (0 : Fin 3))
        (Bootstrapping.Semiterm.bvar (1 : Fin 3))
        (Bootstrapping.Semiterm.bvar (2 : Fin 3)) = S := by
  apply Bootstrapping.Semiformula.subst_eq_self
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i => exact i.elim0

/-- The explicit negation-graph application used by the old field syntax is
the same closed substitution used by `standardApply₂`. -/
private theorem typedQuote_negGraph_application :
    (⌜((negGraph ℒₒᵣ).val/[#0, #3] :
        ArithmeticSemisentence 4)⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 4) =
    (⌜(negGraph ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar (0 : Fin 4),
        Bootstrapping.Semiterm.bvar (3 : Fin 4)] := by
  simpa [standardApply₂] using
    (typedQuote_standardApply₂ (V := V) (negGraph ℒₒᵣ).val
      (#0) (#3))

/-- The ordinary and model-coded presentations of base coherence are
literally the same syntax after quotation. -/
@[simp] theorem typedQuote_standardBaseCrossLevelSentence :
    (⌜standardBaseCrossLevelSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      baseCrossLevelFormula := by
  simp [standardBaseCrossLevelSentence, standardBaseCrossLevelBody,
    standardBaseLowerPiTruth, standardZeroSigmaDomain,
    standardZeroPiDomain, baseCrossLevelFormula, crossLevelFormula,
    crossLevelPredicateFormula, crossLevelBodyFormula,
    sigmaDomainFormula, piDomainFormula, lowerPiTruthFormula,
    baseTruthFormula, levelZeroTruthSyntax,
    typedQuote_negGraph_application]

/-- PA proves coherence between quantifier-free truth and the first positive
truth level on both oriented rank-zero domains. -/
noncomputable def standardBaseCrossLevelProof :
    Peano ⊢! standardBaseCrossLevelSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseCrossLevelSentence,
      standardBaseCrossLevelBody, standardBaseLowerPiTruth,
      standardZeroSigmaDomain, standardZeroPiDomain,
      standardApply₂, standardApply₃]
    intro p free bound
    constructor
    · intro hs
      have hs' : OrientedHierarchy.IsSigmaCode ℒₒᵣ
          (levelCode (V := M) 0) p := by
        simpa [levelCode] using hs
      simpa [eval_levelZeroTruthSyntax_iff, qfTruthDef,
        QFTrue, IsQuantifierFreeCode] using
        (sigmaTrue_succ_iff_of_isSigmaCode (V := M) 0 hs')
    · intro hp
      have hp' : OrientedHierarchy.IsPiCode ℒₒᵣ
          (levelCode (V := M) 0) p := by
        simpa [levelCode] using hp
      simpa [eval_levelZeroTruthSyntax_iff, piTrue_iff,
        qfTruthDef, QFTrue, IsQuantifierFreeCode] using
        (sigmaTrue_succ_iff_piTrue_of_isPiCode (V := M) 0 hp')).get

/-- Genuine typed PA proof of the exact base cross-level field. -/
noncomputable def baseCrossLevelProof :
    Peano.internalize V ⊢! baseCrossLevelFormula := by
  rw [← typedQuote_standardBaseCrossLevelSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseCrossLevelSentence from
      ⟨standardBaseCrossLevelProof⟩)).get

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseCertificate
