import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula
import Foundation.FirstOrder.Completeness

/-!
# A compiled universal-leaf projection for dynamic truth

The universal branch of a successor truth certificate stores a negated call
to the lower truth predicate.  This file extracts precisely that call while
retaining the fixed decoder witnesses which tie its arguments to the
certificate record.

This is intentionally an isolated sub-law rather than the complete
`crossLevel` certificate field.  Its source proof is a genuine existential
and conjunction projection: it forgets the rank and universal-code side
conditions, but preserves the record-bound, record-free, record-formula, and
negation-code graphs.  The fixed proof is then compiled at an arbitrary
model-coded lower formula and finally at the nonstandard dynamic truth orbit.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## The fixed source projection -/

/-- The information retained from a universal-branch witness.

Under the five existential binders the variables are, from low de Bruijn
index to high, `negp`, `q`, `p`, `free`, and `bound`; the three outer
variables are `lowerLevel`, `C`, and `r`.  The otherwise-unused `q` witness is
kept so this formula can reuse the branch witnesses without any reindexing.
The four fixed graphs ensure that the lower call is made at the tuple decoded
from `r`, with `negp` the code of the negation of its formula field. -/
noncomputable def decodedLeafWitness :
    Semisentence SourceLanguage 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    (liftArithmeticFormula (recordBoundDef.val/[#4, #7]) ⋏
      (liftArithmeticFormula (recordFreeDef.val/[#3, #7]) ⋏
        (liftArithmeticFormula (recordFormulaDef.val/[#2, #7]) ⋏
          (liftArithmeticFormula ((negGraph ℒₒᵣ).val/[#0, #2]) ⋏
            ∼(lowerAtom (#4) (#3) (#0))))))

/-- One accepted record, explicitly restricted to the universal branch,
contains a decoded lower-truth counterexample. -/
noncomputable def universalLeafLocalLaw :
    Semisentence SourceLanguage 2 :=
  (successorRecordValid ⋏
      apply₃ universalRecordBranch (parameterTerm 0) (#0) (#1)) 🡒
    apply₃ decodedLeafWitness (parameterTerm 0) (#0) (#1)

/-- Universal closure over the certificate code and its member record. -/
noncomputable def universalLeafProjectionSentence : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ universalLeafLocalLaw

/-- A single standard proof of the universal-leaf projection.

Completeness is used only to construct this fixed finite source derivation.
The semantic argument is pure first-order logic: the witnesses of the
universal branch are reused, four conjuncts of its fixed prefix are retained,
and the stored negated placeholder atom is projected. -/
noncomputable def sourceProof :
    parameterTemplatePeano 3 2 ⊢! universalLeafProjectionSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, universalLeafProjectionSentence,
      universalLeafLocalLaw, decodedLeafWitness,
      DynamicTruthTemplateFormula.universalRecordBranch,
      DynamicTruthFormula.universalRecordPrefixDef,
      DynamicTruthTemplateFormula.apply₃,
      DynamicTruthTemplateFormula.liftArithmeticFormula]
    intro ambient _structure _modelsPeano C r _recordValid
      bound free p q negp hbound hfree hformula _hsubformula
      _hall _hrank hneg hlower
    exact ⟨bound, free, p, q, negp,
      hbound, hfree, hformula, hneg, hlower⟩).get

/-! ## Exact specialization at model-coded truth -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Typed counterpart of `decodedLeafWitness`. -/
noncomputable def decodedLeafWitnessFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    ((⌜(recordBoundDef.val/[#4, #7] : ArithmeticSemisentence 8)⌝ :
        Bootstrapping.Semiformula V ℒₒᵣ 8) ⋏
      ((⌜(recordFreeDef.val/[#3, #7] : ArithmeticSemisentence 8)⌝ :
          Bootstrapping.Semiformula V ℒₒᵣ 8) ⋏
        ((⌜(recordFormulaDef.val/[#2, #7] : ArithmeticSemisentence 8)⌝ :
            Bootstrapping.Semiformula V ℒₒᵣ 8) ⋏
          ((⌜((negGraph ℒₒᵣ).val/[#0, #2] :
              ArithmeticSemisentence 8)⌝ :
              Bootstrapping.Semiformula V ℒₒᵣ 8) ⋏
            ∼(DynamicTruthFormula.apply₃ lower
              (Semiterm.bvar (4 : Fin 8))
              (Semiterm.bvar (3 : Fin 8))
              (Semiterm.bvar (0 : Fin 8)))))))

/-- The concrete typed projection at arbitrary, possibly nonstandard, model
levels. -/
noncomputable def universalLeafProjectionFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰
    ((DynamicTruthFormula.successorRecordValid lower lowerLevel upperLevel ⋏
        (DynamicTruthFormula.universalRecordBranch lower).subst
          ![Arithmetic.typedNumeral lowerLevel,
            Semiterm.bvar (0 : Fin 2), Semiterm.bvar (1 : Fin 2)]) 🡒
      (decodedLeafWitnessFormula lower).subst
        ![Arithmetic.typedNumeral lowerLevel,
          Semiterm.bvar (0 : Fin 2), Semiterm.bvar (1 : Fin 2)])

/-- Translation of the fixed source sentence is exactly the advertised
typed universal-leaf projection. -/
@[simp] theorem translate_universalLeafProjectionSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb universalLeafProjectionSentence) =
      universalLeafProjectionFormula lower lowerLevel upperLevel := by
  simp [universalLeafProjectionSentence, universalLeafLocalLaw,
    decodedLeafWitness, decodedLeafWitnessFormula,
    universalLeafProjectionFormula,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def,
    DynamicTruthFormula.apply₃]
  calc
    translateFormula lower ![lowerLevel, upperLevel]
        (Semiformula.neg
          ((Rewriting.app Rew.emb)
              DynamicTruthTemplateFormula.successorRecordValid ⋏
            (Rewriting.app Rew.emb)
              (DynamicTruthTemplateFormula.apply₃
                DynamicTruthTemplateFormula.universalRecordBranch
                (parameterTerm 0) (#0) (#1)))) =
      ∼translateFormula lower ![lowerLevel, upperLevel]
        ((Rewriting.app Rew.emb)
            DynamicTruthTemplateFormula.successorRecordValid ⋏
          (Rewriting.app Rew.emb)
            (DynamicTruthTemplateFormula.apply₃
              DynamicTruthTemplateFormula.universalRecordBranch
              (parameterTerm 0) (#0) (#1))) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedPredicateParameters.translateFormula_neg
            lower ![lowerLevel, upperLevel]
            ((Rewriting.app Rew.emb)
                DynamicTruthTemplateFormula.successorRecordValid ⋏
              (Rewriting.app Rew.emb)
                (DynamicTruthTemplateFormula.apply₃
                  DynamicTruthTemplateFormula.universalRecordBranch
                  (parameterTerm 0) (#0) (#1))))
    _ = _ := by
      simp [ModelCodedPredicateParameters.translateFormula,
        ModelCodedPredicateParameters.translateTerm]

/-- Compile the fixed proof at arbitrary model-coded lower syntax. -/
noncomputable def compiledUniversalLeafProjectionProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      universalLeafProjectionFormula lower lowerLevel upperLevel := by
  simpa only [translate_universalLeafProjectionSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower sourceProof)

set_option backward.isDefEq.respectTransparency false in
/-- The compiled derivation has an actual represented PA proof code. -/
theorem compiledUniversalLeafProjectionProof_isPAProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Proof Peano
      (compiledUniversalLeafProjectionProof lower lowerLevel upperLevel
        hlower).val
      (universalLeafProjectionFormula lower lowerLevel upperLevel).val := by
  simpa [Proof] using
    (compiledUniversalLeafProjectionProof lower lowerLevel upperLevel
      hlower).derivationOf

/-! ## The exact nonstandard-orbit instance -/

/-- The isolated universal-leaf sub-law at the actual successor of the
dynamic truth orbit. -/
noncomputable def orbitUniversalLeafProjectionFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  universalLeafProjectionFormula
    (truthFormula n) (n + 1) (n + 1 + 1)

/-- A typed PA proof of the universal-leaf sub-law at every model level,
including nonstandard levels. -/
noncomputable def orbitUniversalLeafProjectionProof (n : V) :
    Peano.internalize V ⊢! orbitUniversalLeafProjectionFormula n :=
  compiledUniversalLeafProjectionProof
    (truthFormula n) (n + 1) (n + 1 + 1) (truthFormula_shift n)

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of the orbit specialization. -/
theorem orbitUniversalLeafProjectionProof_isPAProof (n : V) :
    Proof Peano (orbitUniversalLeafProjectionProof n).val
      (orbitUniversalLeafProjectionFormula n).val := by
  simpa [Proof] using (orbitUniversalLeafProjectionProof n).derivationOf

end LeanProofs.BoundedPAConsistency.DynamicTruthUniversalLeafTemplate
