import BoundedPAConsistency.DynamicTruthCertificateSemantics
import BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof
import BoundedPAConsistency.DynamicTruthPredecessorFormula

/-!
# A source interface for the lower truth predicate's existential law

The universal clause of a dynamic truth successor needs the existential
Tarski law of its lower predicate.  At a nonstandard orbit index that lower
predicate is itself model-coded, so the law must occur as represented syntax.

This module defines one fixed sentence in the common one-predicate source
language.  Its placeholder is the lower truth relation itself (rather than
the predecessor from which that relation was constructed), and its semantic
realization is exactly `DynamicTruthSuccessorLaws.ExistentialLaws`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Fixed source syntax -/

/-- The formula-code variable is a well-formed arithmetic formula. -/
noncomputable def sourceLowerFormulaDomain : Semisentence L 3 :=
  DynamicTruthAxiomSoundnessFormula.apply₁
    (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val) (#2)

/-- A witness and the represented sequence obtained by adjoining it to the
bound-variable environment.

The outer variables are `(bound, free, formula)`.  Beneath the two
existentials, `#1` is the witness, `#0` is the extended sequence, and the
outer values have shifted to `#3`, `#4`, and `#5`. -/
noncomputable def sourceLowerExtendedTruthWitness : Semisentence L 4 :=
  ∃⁰ ∃⁰
    (apply₃ (liftArithmeticFormula seqConsDef.val) (#0) (#3) (#1) ⋏
      lowerAtom (#0) (#4) (#5))

/-- The represented existential-code graph followed by the lower relation's
Tarski equivalence. -/
noncomputable def sourceLowerExistentialCodeWitness : Semisentence L 3 :=
  ∃⁰
    (apply₂ (liftArithmeticFormula qqExsDef.val) (#0) (#3) ⋏
      LogicalConnective.iff
        (lowerAtom (#1) (#2) (#0))
        sourceLowerExtendedTruthWitness)

/-- Pointwise existential law, guarded by formula well-formedness. -/
noncomputable def sourceLowerExistentialBody : Semisentence L 3 :=
  sourceLowerFormulaDomain 🡒 sourceLowerExistentialCodeWitness

/-- Closed source assertion that the placeholder satisfies the existential
truth law at every bound environment, free environment, and formula code. -/
noncomputable def sourceLowerExistentialLawsSentence : Sentence L :=
  ∀⁰ ∀⁰ ∀⁰ sourceLowerExistentialBody

/-! ## Arbitrary model-coded specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Exact translated formula for an arbitrary model-coded lower relation.
The named levels are retained because the common source compiler carries
them, although this particular sentence does not inspect either value. -/
noncomputable def lowerExistentialLawsFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceLowerExistentialLawsSentence)

@[simp] theorem translate_sourceLowerExistentialLawsSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceLowerExistentialLawsSentence) =
      lowerExistentialLawsFormula lower lowerLevel upperLevel := rfl

@[simp] theorem translate_sourceLowerLevelSuccessor
    (parameters : Fin 2 → V) (hpositive : 0 < parameters 0) :
    ModelCodedPredicateParameters.translateTerm parameters
        (Rew.emb (sourceLowerLevelSuccessor (n := n)) :
          SyntacticSemiterm L n) =
      (Arithmetic.typedNumeral (parameters 0 + 1) :
        Bootstrapping.Semiterm V ℒₒᵣ n) := by
  simp [sourceLowerLevelSuccessor, sourceOne,
    DynamicTruthTemplateFormula.parameterTerm,
    ModelCodedPredicateParameters.translateTerm]
  exact (Arithmetic.numeral_succ_pos' hpositive).symm

@[simp] theorem translate_sourceDerivedSuccessorRecordValid
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceDerivedSuccessorRecordValid) =
      successorRecordValid lower lowerLevel (lowerLevel + 1) := by
  simp [sourceDerivedSuccessorRecordValid,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.successorRecordValid,
    translate_sourceLowerLevelSuccessor
      (n := 2) (parameters := ![lowerLevel, upperLevel]) hpositive]

@[simp] theorem translate_sourceDerivedSuccessorTruthFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceDerivedSuccessorTruthFormula) =
      successorTruthFormula lower lowerLevel (lowerLevel + 1) := by
  simp [sourceDerivedSuccessorTruthFormula,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.successorTruthFormula,
    Bootstrapping.Semiformula.imp_def,
    translate_sourceDerivedSuccessorRecordValid _ _ _ hpositive]
  let memberSource : Semisentence L 5 :=
    DynamicTruthTemplateFormula.apply₂
      (liftArithmeticFormula hfsMemDef.val) (#0) (#1)
  calc
    translateFormula lower ![lowerLevel, upperLevel]
        (∼(Rewriting.emb memberSource)) =
      ∼translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb memberSource) :=
      ModelCodedPredicateParameters.translateFormula_neg
        lower ![lowerLevel, upperLevel] (Rewriting.emb memberSource)
    _ = _ := by
      simp [memberSource,
        ModelCodedPredicateParameters.translateTerm]

/-- The older successor-specific existential-law source and the direct
lower-predicate source compile to the same arithmetic sentence once the
direct placeholder is instantiated by that represented successor. -/
theorem successorExistentialLawsFormula_eq_lowerExistentialLawsFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    successorExistentialLawsFormula lower lowerLevel upperLevel =
      lowerExistentialLawsFormula
        (successorTruthFormula lower lowerLevel (lowerLevel + 1))
        lowerLevel upperLevel := by
  have hdomain :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceFormulaDomain) =
        translateFormula
          (successorTruthFormula lower lowerLevel (lowerLevel + 1))
          ![lowerLevel, upperLevel]
          (Rewriting.emb sourceFormulaDomain) := by
    change
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb
            (DynamicTruthAxiomSoundnessFormula.apply₁
              (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val) (#2))) =
        translateFormula
          (successorTruthFormula lower lowerLevel (lowerLevel + 1))
          ![lowerLevel, upperLevel]
          (Rewriting.emb
            (DynamicTruthAxiomSoundnessFormula.apply₁
              (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val) (#2)))
    simp
  have hdomainNeg :
      translateFormula lower ![lowerLevel, upperLevel]
          (∼(Rewriting.emb sourceFormulaDomain)) =
        translateFormula
          (successorTruthFormula lower lowerLevel (lowerLevel + 1))
          ![lowerLevel, upperLevel]
          (∼(Rewriting.emb sourceFormulaDomain)) := by
    rw [ModelCodedPredicateParameters.translateFormula_neg,
      ModelCodedPredicateParameters.translateFormula_neg, hdomain]
  simp [successorExistentialLawsFormula,
    lowerExistentialLawsFormula,
    sourceSuccessorExistentialLawsSentence,
    sourceSuccessorExistentialBody,
    sourceExistentialCodeWitness,
    sourceExtendedTruthWitness,
    sourceFormulaDomain,
    sourceLowerExistentialLawsSentence,
    sourceLowerExistentialBody,
    sourceLowerExistentialCodeWitness,
    sourceLowerExtendedTruthWitness,
    sourceLowerFormulaDomain,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    translate_sourceDerivedSuccessorTruthFormula _ _ _ hpositive,
    FirstOrder.Semiformula.iff_eq]
  exact hdomainNeg

/-- A genuine internal PA derivation of the direct existential law for every
positive member of the represented truth orbit.  The index is written as
`n + 1` deliberately: the model-coded numeral constructor exposes successor
addition syntactically only under this positivity witness. -/
noncomputable def orbitLowerExistentialLawsProof (n : V) :
    Peano.internalize V ⊢!
      lowerExistentialLawsFormula
        (truthFormula (n + 1)) (n + 1) (n + 1 + 1) := by
  rw [truthFormula_succ]
  rw [← successorExistentialLawsFormula_eq_lowerExistentialLawsFormula
    (truthFormula n) (n + 1) (n + 1 + 1) (by simp)]
  exact DynamicTruthLowerExistentialLawsProof.orbitSuccessorExistentialLawsProof n

/-! ## Semantics -/

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

include hArithmeticReduct in
@[simp] theorem eval_sourceLowerFormulaDomain (v : Fin 3 → M) :
    sourceLowerFormulaDomain.Evalb (M := M) v ↔
      IsUFormula ℒₒᵣ (v 2) := by
  simp [sourceLowerFormulaDomain,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceLowerExtendedTruthWitness (v : Fin 4 → M) :
    sourceLowerExtendedTruthWitness.Evalb (M := M) v ↔
      ∃ a, lowerRelation (v 1 ⁀' a) (v 2) (v 3) := by
  simp [sourceLowerExtendedTruthWitness,
    DynamicTruthTemplateSemantics.eval_apply₃,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_lowerAtom]

include hArithmeticReduct in
@[simp] theorem eval_sourceLowerExistentialCodeWitness (v : Fin 3 → M) :
    sourceLowerExistentialCodeWitness.Evalb (M := M) v ↔
      (lowerRelation (v 0) (v 1) (^∃ (v 2)) ↔
        ∃ a, lowerRelation (v 0 ⁀' a) (v 1) (v 2)) := by
  simp [sourceLowerExistentialCodeWitness,
    DynamicTruthTemplateSemantics.eval_apply₂,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_lowerAtom,
    eval_sourceLowerExtendedTruthWitness hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceLowerExistentialLawsSentence :
    sourceLowerExistentialLawsSentence.Evalb (M := M) ![] ↔
      ExistentialLaws (lowerRelation (M := M)) := by
  simp [sourceLowerExistentialLawsSentence,
    sourceLowerExistentialBody, ExistentialLaws,
    eval_sourceLowerFormulaDomain hArithmeticReduct,
    eval_sourceLowerExistentialCodeWitness hArithmeticReduct]
  constructor
  · intro h bound free q hq
    exact h q free bound hq
  · intro h q free bound hq
    exact h hq

end LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface
