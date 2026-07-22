import BoundedPAConsistency.DynamicTruthCrossLevelSourceZero
import Foundation.FirstOrder.Completeness

/-!
# Exact decomposition of the structural cross-level successor obligation

This file keeps the successor obligation in the fixed two-predicate source
language.  It does not replace either predicate placeholder by a semantic
relation, and every branch retains `sourcePriorCrossLevelContext` as its
literal antecedent.

The complete successor proof naturally separates into the Sigma- and
Pi-oriented guarded clauses.  The unguarded, off-domain part is already pure
first-order logic: if the successor code belongs to neither advertised
domain, both implications in `sourceNextCrossLevelBody` are vacuous.  The two
valid-domain branches are exposed as the remaining proof-producing interface.

This decomposition also pinpoints the first missing mathematical input.  The
prior cross-level context relates the two arbitrary predicate placeholders on
the old domain, but it contains no local Tarski law anchoring the current
placeholder to quantifier-free evaluation.  Consequently the atomic case of
a structural formula induction cannot yet be discharged from this context.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate

/-! ## Literal successor syntax -/

/-- The exact closed successor sentence required by
`TwoPredicateSourceContextInductionKernel.Template.proveSuccessor`. -/
noncomputable def sourceSuccessorSentence : Sentence SourceLanguage :=
  successorSentence sourcePriorCrossLevelContext
    sourceNextCrossLevelInvariant

/-- The Sigma-oriented conjunct of the next cross-level body. -/
noncomputable def sourceNextSigmaClause : Semisentence SourceLanguage 3 :=
  sourceCurrentSigmaDomain 🡒
    (sourceCurrentSuccessorTruth 🡘
      currentAtom (#0) (#1) (#2))

/-- The Pi-oriented conjunct of the next cross-level body. -/
noncomputable def sourceNextPiClause : Semisentence SourceLanguage 3 :=
  sourceCurrentPiDomain 🡒
    (sourceCurrentSuccessorTruth 🡘 sourceCurrentPiTruth)

@[simp] theorem sourceNextCrossLevelBody_eq_clauses :
    sourceNextCrossLevelBody =
      sourceNextSigmaClause ⋏ sourceNextPiClause := by
  rfl

/-- Unary closure of just the Sigma-oriented clause. -/
noncomputable def sourceNextSigmaInvariant :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceNextSigmaClause

/-- Unary closure of just the Pi-oriented clause. -/
noncomputable def sourceNextPiInvariant :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceNextPiClause

/-- The next body after replacing its formula-code argument by the arithmetic
successor of the numeric induction variable.  The two `.q` operations are
the de Bruijn lifts through the bound- and free-environment quantifiers. -/
noncomputable def sourceSuccessorBody : Semisentence SourceLanguage 3 :=
  (Rew.subst ![successorTerm 3 3 3]).q.q ▹
    sourceNextCrossLevelBody

/-- The corresponding normalized Sigma clause. -/
noncomputable def sourceSuccessorSigmaClause :
    Semisentence SourceLanguage 3 :=
  (Rew.subst ![successorTerm 3 3 3]).q.q ▹
    sourceNextSigmaClause

/-- The corresponding normalized Pi clause. -/
noncomputable def sourceSuccessorPiClause :
    Semisentence SourceLanguage 3 :=
  (Rew.subst ![successorTerm 3 3 3]).q.q ▹
    sourceNextPiClause

@[simp] theorem sourceSuccessorBody_eq_clauses :
    sourceSuccessorBody =
      sourceSuccessorSigmaClause ⋏ sourceSuccessorPiClause := by
  simp [sourceSuccessorBody, sourceSuccessorSigmaClause,
    sourceSuccessorPiClause, sourceNextCrossLevelBody_eq_clauses]

@[simp] theorem subst_sourceNextCrossLevelInvariant_successor :
    sourceNextCrossLevelInvariant/[successorTerm 3 3 3] =
      ∀⁰ ∀⁰ sourceSuccessorBody := by
  simp [sourceNextCrossLevelInvariant, sourceSuccessorBody]

@[simp] theorem subst_sourceNextSigmaInvariant_successor :
    sourceNextSigmaInvariant/[successorTerm 3 3 3] =
      ∀⁰ ∀⁰ sourceSuccessorSigmaClause := by
  simp [sourceNextSigmaInvariant, sourceSuccessorSigmaClause]

@[simp] theorem subst_sourceNextPiInvariant_successor :
    sourceNextPiInvariant/[successorTerm 3 3 3] =
      ∀⁰ ∀⁰ sourceSuccessorPiClause := by
  simp [sourceNextPiInvariant, sourceSuccessorPiClause]

/-- The Sigma-domain half of the literal successor obligation. -/
noncomputable def sourceSuccessorSigmaSentence : Sentence SourceLanguage :=
  Arrow.arrow sourcePriorCrossLevelContext
    (∀⁰ Arrow.arrow sourceNextCrossLevelInvariant
      (sourceNextSigmaInvariant/[
        successorTerm 3 3 3]))

/-- The Pi-domain half of the literal successor obligation. -/
noncomputable def sourceSuccessorPiSentence : Sentence SourceLanguage :=
  Arrow.arrow sourcePriorCrossLevelContext
    (∀⁰ Arrow.arrow sourceNextCrossLevelInvariant
      (sourceNextPiInvariant/[
        successorTerm 3 3 3]))

/-! ## Proof-producing recombination -/

/-- Actual PA derivations of the two guarded successor branches.  This is a
proof interface, not a semantic hypothesis: both fields are derivations in
the original lifted-PA source theory and both formulas retain the literal
prior-coherence antecedent. -/
structure SourceSuccessorCases where
  sigma : twoPredicateParameterPeano 3 3 3 ⊢!
    sourceSuccessorSigmaSentence
  pi : twoPredicateParameterPeano 3 3 3 ⊢!
    sourceSuccessorPiSentence

/-- Recombine derivations of the two guarded clauses into the exact
`Template.proveSuccessor` judgment.  Completeness is used only for the fixed
propositional/quantifier bookkeeping; the two mathematical branches remain
ordinary source-theory proof objects. -/
noncomputable def SourceSuccessorCases.proveSuccessor
    (cases : SourceSuccessorCases) :
    twoPredicateParameterPeano 3 3 3 ⊢! sourceSuccessorSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro _nonempty _structure hmodels
    have hsigma := models_of_provable hmodels
      (show twoPredicateParameterPeano 3 3 3 ⊢
          sourceSuccessorSigmaSentence from ⟨cases.sigma⟩)
    have hpi := models_of_provable hmodels
      (show twoPredicateParameterPeano 3 3 3 ⊢
          sourceSuccessorPiSentence from ⟨cases.pi⟩)
    simp [models_iff, sourceSuccessorSigmaSentence,
      sourceSuccessorPiSentence,
      sourceNextCrossLevelInvariant, sourceNextSigmaInvariant,
      sourceNextPiInvariant] at hsigma hpi
    simp [models_iff, sourceSuccessorSentence, successorSentence,
      sourceNextCrossLevelInvariant,
      sourceNextCrossLevelBody_eq_clauses]
    intro hcontext p hp bound free
    exact ⟨hsigma hcontext p hp bound free,
      hpi hcontext p hp bound free⟩).get

/-! ## The domain-free branch -/

/-- At one formula code, both oriented guards being false suffices for the
next cross-level body, independently of the two truth predicates. -/
noncomputable def sourceOffDomainBody : Semisentence SourceLanguage 3 :=
  ((∼sourceCurrentSigmaDomain) ⋏
      (∼sourceCurrentPiDomain)) 🡒
    sourceNextCrossLevelBody

/-- Unary closure of the off-domain implication. -/
noncomputable def sourceOffDomainInvariant :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceOffDomainBody

/-- The off-domain portion at the successor numeral, in exactly the same
context and under exactly the same pointwise induction hypothesis as the
full successor sentence. -/
noncomputable def sourceSuccessorOffDomainSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourcePriorCrossLevelContext
    (∀⁰ Arrow.arrow sourceNextCrossLevelInvariant
      (sourceOffDomainInvariant/[
        successorTerm 3 3 3]))

set_option maxHeartbeats 800000 in
/-- The complete off-domain successor branch is a fixed theorem of the
source theory.  Neither the context nor the induction hypothesis is erased;
they remain antecedents and are simply unnecessary in this vacuous case. -/
noncomputable def sourceSuccessorOffDomainProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      sourceSuccessorOffDomainSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceSuccessorOffDomainSentence,
      sourceOffDomainInvariant, sourceOffDomainBody,
      sourceNextCrossLevelInvariant, sourceNextCrossLevelBody]
    aesop).get

/-! ## First missing valid-domain input -/

/-- Arithmetic zero lifted as a closed term with any number of bound
variables.  It is used below as the fixed quantifier-group bound. -/
noncomputable def sourceArithmeticZero {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  ((‘0’ : ArithmeticSemiterm Empty n).lMap
    (arithmeticHom 3 3 3))

/-- The fixed quantifier-free formula-code domain in the source language. -/
noncomputable def sourceQuantifierFreeDomain :
    Semisentence SourceLanguage 3 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    sourceArithmeticZero (#2)

/-- The canonical represented quantifier-free evaluator, applied to the
three local arguments `(bound, free, formula)`. -/
noncomputable def sourceQuantifierFreeTruth :
    Semisentence SourceLanguage 3 :=
  apply₃ (liftArithmeticFormula qfTruthDef.val)
    (#0) (#1) (#2)

/-- The constructor base law that is absent from
`sourcePriorCrossLevelContext`: on quantifier-free codes, the current
placeholder must agree with the canonical evaluator.

This is intentionally exposed only as syntax.  There is no derivation of it
from the present context; adding such a derivation would silently assume the
very local truth law that the staged compiler still has to provide. -/
noncomputable def sourceMissingQuantifierFreeAnchorBody :
    Semisentence SourceLanguage 3 :=
  sourceQuantifierFreeDomain 🡒
    (currentAtom (#0) (#1) (#2) 🡘
      sourceQuantifierFreeTruth)

/-- Universal closure of the first missing constructor-local law. -/
noncomputable def sourceMissingQuantifierFreeAnchor :
    Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceMissingQuantifierFreeAnchorBody

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
