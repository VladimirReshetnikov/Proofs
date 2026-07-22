import BoundedPAConsistency.DynamicTruthTemplateFormula
import BoundedPAConsistency.DynamicTruthSuccessorLaws
import BoundedPAConsistency.ModelCodedPredicateEqualityQuotient

/-!
# A fixed source formula for the lower successor's existential law

The universal clause of the next dynamic truth predicate needs only one fact
about its opaque lower predicate: truth of a coded existential is equivalent
to truth of its body at some extended bound-variable environment.  In the
truth orbit that lower predicate is itself a successor.  This file expresses
that fact in the same one-predicate, two-parameter source language used by the
other dynamic certificate fields.

All code-building operations remain represented by their arithmetic graph
formulae.  In particular, neither a possibly nonstandard formula code nor a
possibly nonstandard sequence code is decoded in the metatheory.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## Fixed source syntax -/

/-- Arithmetic one in the expanded source language. -/
def sourceOne {n : ℕ} : ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![]

/-- The source term `lowerLevel + 1`. -/
def sourceLowerLevelSuccessor {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
    ![parameterTerm 0, sourceOne]

/-- Record validity for the successor whose upper level is computed
arithmetically from the named lower level. -/
noncomputable def sourceDerivedSuccessorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      sourceLowerLevelSuccessor (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ universalRecordBranch (parameterTerm 0) (#0) (#1))

/-- The represented successor predicate at levels `(lower, lower + 1)`.

Computing the upper level inside the fixed source formula removes any need to
prove a separate model-coded adjacency equation after specialization. -/
noncomputable def sourceDerivedSuccessorTruthFormula :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ sourceDerivedSuccessorRecordValid (#1) (#0))))

/-- The source assertion that the formula-code variable `#2` is well formed.

The three surrounding variables are `(bound, free, formula)` in de Bruijn
order. -/
noncomputable def sourceFormulaDomain : Semisentence SourceLanguage 3 :=
  (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val) ⇜ ![(#2)]

/-- A represented extension of the bound-variable environment.

This formula is used below two existential binders.  There `#0` is the new
environment, `#1` is the witness, `#3` is the old environment, and `#4` is
the unchanged free-variable environment. -/
noncomputable def sourceExtendedTruthWitness :
    Semisentence SourceLanguage 4 :=
  ∃⁰ ∃⁰
    (apply₃ (liftArithmeticFormula seqConsDef.val) (#0) (#3) (#1) ⋏
      apply₃ sourceDerivedSuccessorTruthFormula (#0) (#4) (#5))

/-- The graph witness for the existential code, followed by the desired truth
equivalence.  Under the outer existential binder `#0` is the represented
existential code and the original `(bound, free, body)` variables have become
`#1`, `#2`, and `#3`. -/
noncomputable def sourceExistentialCodeWitness :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (apply₂ (liftArithmeticFormula qqExsDef.val) (#0) (#3) ⋏
      LogicalConnective.iff
        (apply₃ sourceDerivedSuccessorTruthFormula (#1) (#2) (#0))
        sourceExtendedTruthWitness)

/-- Pointwise existential law for the represented successor predicate. -/
noncomputable def sourceSuccessorExistentialBody :
    Semisentence SourceLanguage 3 :=
  sourceFormulaDomain 🡒 sourceExistentialCodeWitness

/-- The universally closed existential law. -/
noncomputable def sourceSuccessorExistentialLawsSentence :
    Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceSuccessorExistentialBody

/-! ## Typed specializations -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The exact model-coded specialization of the fixed existential-law
sentence.  Keeping this definition by translation makes its source origin
  visible and avoids duplicating a delicate six-binder formula.  The
  `upperLevel` parameter is retained for compatibility with the common
  two-parameter compiler, although this derived source uses `lowerLevel + 1`
  literally. -/
noncomputable def successorExistentialLawsFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceSuccessorExistentialLawsSentence)

@[simp] theorem translate_sourceSuccessorExistentialLawsSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSuccessorExistentialLawsSentence) =
      successorExistentialLawsFormula lower lowerLevel upperLevel := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
