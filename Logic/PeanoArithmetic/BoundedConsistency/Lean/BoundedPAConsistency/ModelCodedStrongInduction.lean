import BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
import Foundation.FirstOrder.Completeness
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory

/-!
# Strong induction for a model-coded unary formula

The source language in this module is used only for finite logical and
arithmetic bookkeeping.  Its first placeholder is a closed context `C`; its
second placeholder is a unary formula `P`.  The actual induction is *not*
performed in this expanded source theory (which has no induction axioms for
arbitrary predicates).  Instead, the source proofs establish the zero and
successor premises for the prefix predicate

`K(x) := C -> forall y < x, P(y)`.

After arbitrary model-coded formulas are substituted for `C` and `P`, PA's
represented induction axiom proves `forall x, K(x)`.  A final fixed source
proof extracts `C -> forall x, P(x)`.  Thus the public adapter returns a
single internal PA proof code and applies equally to nonstandard formula
codes.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Fixed source syntax -/

/-- Arithmetic with a nullary context placeholder and a unary target
placeholder.  No named constants are required by generic strong induction. -/
abbrev SourceLanguage :=
  TwoPredicateSourceContextInductionKernel.Language 0 1 0

/-- The closed source atom which specializes to the model-coded context. -/
def sourceContextAtom {n : ℕ} : Semisentence SourceLanguage n :=
  firstAtom (arity₀ := 0) (arity₁ := 1) (count := 0) ![]

/-- Apply the unary target placeholder to one source term. -/
def sourcePredicateAtom {n : ℕ}
    (t : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  secondAtom (arity₀ := 0) (arity₁ := 1) (count := 0) ![t]

/-- The arithmetic guard `y < x` below the prefix quantifier.  Naming the
guard keeps its evaluation visibly aligned with the lifted PA theorem that
no number is below zero. -/
noncomputable def sourcePrefixGuard : Semisentence SourceLanguage 2 :=
  .rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2))
    ![(#0 : ClosedSemiterm SourceLanguage 2),
      (#1 : ClosedSemiterm SourceLanguage 2)]

/-- `forall y < x, P(y)`, with `x` the sole outer bound variable. -/
noncomputable def sourcePrefixPredicate : Semisentence SourceLanguage 1 :=
  ∀⁰[sourcePrefixGuard]
    sourcePredicateAtom (#0 : ClosedSemiterm SourceLanguage 2)

/-- The represented strong-step premise under the closed context. -/
noncomputable def sourceStrongStepContext : Sentence SourceLanguage :=
  Arrow.arrow (sourceContextAtom (n := 0))
    (∀⁰ Arrow.arrow sourcePrefixPredicate
      (sourcePredicateAtom (#0 : ClosedSemiterm SourceLanguage 1)))

/-- Equality replacement for the unary placeholder.  Lifted PA contains
equality replacement only for arithmetic symbols, so this law is kept
explicit in the fixed source interface.  After specialization it is proved
uniformly for every model-coded arithmetic formula by PA's represented
formula-replacement theorem. -/
noncomputable def sourcePredicateCongruence : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ Arrow.arrow
    (.rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
      ![(#1 : ClosedSemiterm SourceLanguage 2),
        (#0 : ClosedSemiterm SourceLanguage 2)])
    (Arrow.arrow
      (sourcePredicateAtom (#1 : ClosedSemiterm SourceLanguage 2))
      (sourcePredicateAtom (#0 : ClosedSemiterm SourceLanguage 2)))

/-- Complete context used by ordinary PA induction on the prefix. -/
noncomputable def sourceInductionContext : Sentence SourceLanguage :=
  sourceStrongStepContext ⋏ sourcePredicateCongruence

/-- The ordinary induction predicate.  Context is placed inside the
predicate so PA can prove its universal closure without first receiving a
proof of the context itself. -/
noncomputable def sourceContextualPrefix :
    Semisentence SourceLanguage 1 :=
  Arrow.arrow (sourceContextAtom (n := 1)) sourcePrefixPredicate

/-! ## Fixed source proofs of the numeric induction premises -/

/-- The only arithmetic fact needed for the zero prefix.  Keeping it as an
ordinary arithmetic theorem makes clear that no source-language induction is
being smuggled into the adapter. -/
noncomputable def arithmeticNoLessThanZeroSentence : ArithmeticSentence :=
  “∀ x, x ≮ 0”

/-- PA proves that no number is below zero. -/
noncomputable def arithmeticNoLessThanZeroProof :
    Peano ⊢! arithmeticNoLessThanZeroSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hPA
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
    simp [models_iff, arithmeticNoLessThanZeroSentence]).get

/-- Transport the arithmetic zero fact to the expanded source language. -/
noncomputable def liftedArithmeticNoLessThanZeroProof :
    twoPredicateParameterPeano 0 1 0 ⊢!
      arithmeticNoLessThanZeroSentence.lMap (arithmeticHom 0 1 0) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticNoLessThanZeroSentence from
        ⟨arithmeticNoLessThanZeroProof⟩))).get

/-- Arithmetic splitting below a successor.  This is the sole order fact
used in the successor premise for the prefix induction. -/
noncomputable def arithmeticBelowSuccessorSentence : ArithmeticSentence :=
  ∀⁰ ∀⁰ Arrow.arrow
    (.rel Language.LT.lt
      ![(#0 : ArithmeticSemiterm Empty 2),
        (‘#1 + 1’ : ArithmeticSemiterm Empty 2)])
    ((.rel Language.LT.lt
        ![(#0 : ArithmeticSemiterm Empty 2),
          (#1 : ArithmeticSemiterm Empty 2)]) ⋎
      (.rel Language.Eq.eq
        ![(#1 : ArithmeticSemiterm Empty 2),
          (#0 : ArithmeticSemiterm Empty 2)]))

noncomputable def arithmeticBelowSuccessorProof :
    Peano ⊢! arithmeticBelowSuccessorSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hPA
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
    simp [models_iff, arithmeticBelowSuccessorSentence,
      lt_succ_iff_le]
    intro x y hyx
    exact hyx.lt_or_eq.imp_right Eq.symm).get

noncomputable def liftedArithmeticBelowSuccessorProof :
    twoPredicateParameterPeano 0 1 0 ⊢!
      arithmeticBelowSuccessorSentence.lMap (arithmeticHom 0 1 0) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticBelowSuccessorSentence from
        ⟨arithmeticBelowSuccessorProof⟩))).get

/-- The prefix below zero is empty, independently of both placeholders. -/
noncomputable def sourcePrefixZeroProof :
    twoPredicateParameterPeano 0 1 0 ⊢!
      zeroSentence sourceInductionContext sourceContextualPrefix :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, zeroSentence, sourceInductionContext,
      sourceStrongStepContext, sourcePredicateCongruence,
      sourceContextualPrefix, sourcePrefixPredicate, sourcePrefixGuard,
      sourceContextAtom,
      sourcePredicateAtom, firstAtom, secondAtom, zeroTerm,
      Semiformula.eval_rew]
    intro ambient _structure hmodels _strongStep _congruence _context
    letI : Nonempty _ := ⟨ambient⟩
    have hzero := models_of_provable hmodels
      (show twoPredicateParameterPeano 0 1 0 ⊢
          arithmeticNoLessThanZeroSentence.lMap
            (arithmeticHom 0 1 0) from
        ⟨liftedArithmeticNoLessThanZeroProof⟩)
    simp [models_iff, arithmeticNoLessThanZeroSentence] at hzero
    intro y
    intro hy
    exfalso
    apply hzero y
    simp only [FirstOrder.Semiformula.lMap_rel,
      FirstOrder.Semiformula.lMap_subst,
      FirstOrder.Semiformula.lMap_emb,
      Semiformula.Operator.val,
      Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq,
      Semiformula.EvalAux, Semiformula.eval_substs,
      Semiformula.eval_emb, Semiformula.eval_rel,
      FirstOrder.Semiterm.val_bShift,
      FirstOrder.Semiterm.val_lMap, Function.comp_def,
      Matrix.empty_eq]
    convert hy using 1
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        have hi : i = 0 := Fin.eq_zero i
        subst i
        symm
        change FirstOrder.Semiterm.val ![y] Empty.elim
            ((Rew.subst
              ![Semiterm.lMap (arithmeticHom 0 1 0)
                (‘0’ : ArithmeticSemiterm Empty 0)]).q
              (#(Fin.succ (0 : Fin 1)))) = _
        rw [Rew.q_bvar_succ, Rew.subst_bvar]
        simp [FirstOrder.Semiterm.val_bShift,
          FirstOrder.Semiterm.val_lMap,
          Matrix.empty_eq]).get

/-- One prefix step uses the supplied strong-step premise only at the new
endpoint `x`; all smaller values are inherited from the induction
hypothesis. -/
noncomputable def sourcePrefixSuccessorProof :
    twoPredicateParameterPeano 0 1 0 ⊢!
      successorSentence sourceInductionContext sourceContextualPrefix :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, successorSentence, sourceInductionContext,
      sourceStrongStepContext, sourcePredicateCongruence,
      sourceContextualPrefix, sourcePrefixPredicate, sourcePrefixGuard,
      sourceContextAtom, sourcePredicateAtom, firstAtom, secondAtom,
      successorTerm]
    intro ambient _structure hmodels hstrong hcongruence x hprefix
      hcontext y hy
    letI : Nonempty _ := ⟨ambient⟩
    have hbelow := models_of_provable hmodels
      (show twoPredicateParameterPeano 0 1 0 ⊢
          arithmeticBelowSuccessorSentence.lMap
            (arithmeticHom 0 1 0) from
        ⟨liftedArithmeticBelowSuccessorProof⟩)
    simp [models_iff, arithmeticBelowSuccessorSentence,
      FirstOrder.Semiterm.val_lMap, Function.comp_def] at hbelow
    rcases hbelow x y (by
      convert hy using 1
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          symm
          change FirstOrder.Semiterm.val ![y, x] Empty.elim
              ((Rew.subst
                ![Semiterm.lMap (arithmeticHom 0 1 0)
                  (‘#0 + 1’ : ArithmeticSemiterm Empty 1)]).q
                (#(Fin.succ (0 : Fin 1)))) = _
          rw [Rew.q_bvar_succ, Rew.subst_bvar]
          simp [FirstOrder.Semiterm.val_lMap, Function.comp_def]
          congr 1
          funext j
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              have hj : j = 0 := Fin.eq_zero j
              subst j
              simp [Matrix.constant_eq_singleton]) with
      hlt | heq
    · apply hprefix hcontext y
      simpa [Matrix.fun_eq_vec_two] using hlt
    · apply hcongruence x y
      · simpa [Matrix.fun_eq_vec_two] using heq
      · exact hstrong hcontext x (hprefix hcontext)).get

/-! ## Extraction after ordinary induction -/

/-- Universal closure of the contextual prefix predicate. -/
noncomputable def sourceAllContextualPrefixes : Sentence SourceLanguage :=
  ∀⁰ sourceContextualPrefix

/-- The desired conclusion of strong induction in the fixed source
language. -/
noncomputable def sourceStrongInductionConclusion : Sentence SourceLanguage :=
  Arrow.arrow (sourceContextAtom (n := 0))
    (∀⁰ sourcePredicateAtom
      (#0 : ClosedSemiterm SourceLanguage 1))

/-- Once every contextual prefix is available, the original strong-step
premise yields the target predicate at every endpoint. -/
noncomputable def sourcePrefixExtractionSentence : Sentence SourceLanguage :=
  Arrow.arrow sourceStrongStepContext
    (Arrow.arrow sourceAllContextualPrefixes
      sourceStrongInductionConclusion)

/-- Fixed logical proof which performs the final endpoint extraction. -/
noncomputable def sourcePrefixExtractionProof :
    twoPredicateParameterPeano 0 1 0 ⊢!
      sourcePrefixExtractionSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourcePrefixExtractionSentence,
      sourceAllContextualPrefixes, sourceStrongInductionConclusion,
      sourceStrongStepContext, sourceContextualPrefix,
      sourcePrefixPredicate, sourcePrefixGuard, sourceContextAtom,
      sourcePredicateAtom, firstAtom, secondAtom]
    aesop).get

/-- The complete fixed source template consumed by represented PA
induction. -/
noncomputable def sourcePrefixTemplate : Template 0 1 0 where
  context := sourceInductionContext
  predicate := sourceContextualPrefix
  proveZero := sourcePrefixZeroProof
  proveSuccessor := sourcePrefixSuccessorProof

/-! ## Specialization to arbitrary model-coded arithmetic formulas -/

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The represented strong-step premise after substituting the actual
closed context and unary formula. -/
noncomputable def strongStepFormula
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula context predicate ![]
    (Rewriting.emb sourceStrongStepContext)

/-- The equality-replacement law specialized to the unary formula. -/
noncomputable def predicateCongruenceFormula
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula context predicate ![]
    (Rewriting.emb sourcePredicateCongruence)

/-- Complete context of the represented ordinary induction kernel. -/
noncomputable def inductionContextFormula
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula context predicate ![]
    (Rewriting.emb sourceInductionContext)

/-- Unary contextual-prefix predicate after specialization. -/
noncomputable def contextualPrefixPredicate
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula context predicate ![]
    (Rewriting.emb sourceContextualPrefix)

/-- Friendly target spelling of the fixed extraction theorem. -/
noncomputable def prefixExtractionFormula
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Bootstrapping.Formula V ℒₒᵣ :=
  strongStepFormula context predicate 🡒
    (∀⁰ contextualPrefixPredicate context predicate) 🡒
      context 🡒 ∀⁰ predicate

@[simp] theorem translate_sourceInductionContext
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    inductionContextFormula context predicate =
      strongStepFormula context predicate ⋏
        predicateCongruenceFormula context predicate := by
  rfl

@[simp] theorem translate_sourceAllContextualPrefixes
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    translateFormula context predicate ![]
        (Rewriting.emb sourceAllContextualPrefixes) =
      ∀⁰ contextualPrefixPredicate context predicate := by
  simp only [sourceAllContextualPrefixes, contextualPrefixPredicate,
    Rewriting.app_all,
    ModelCodedTwoPredicateParameters.translateFormula]
  congr 1

@[simp] theorem translate_sourceStrongInductionConclusion
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    translateFormula context predicate ![]
        (Rewriting.emb sourceStrongInductionConclusion) =
      context 🡒 ∀⁰ predicate := by
  change
    translateFormula context predicate ![]
        (∼(Rewriting.emb (sourceContextAtom (n := 0)))) ⋎
      translateFormula context predicate ![]
        (Rewriting.emb
          (∀⁰ sourcePredicateAtom
            (#0 : ClosedSemiterm SourceLanguage 1))) =
      context 🡒 ∀⁰ predicate
  rw [translateFormula_neg]
  simp [sourceContextAtom, sourcePredicateAtom, firstAtom, secondAtom,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def,
    Function.comp_def, Matrix.constant_eq_singleton]

@[simp] theorem translate_sourcePrefixExtractionSentence
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    translateFormula context predicate ![]
        (Rewriting.emb sourcePrefixExtractionSentence) =
      prefixExtractionFormula context predicate := by
  change
    translateFormula context predicate ![]
        (∼(Rewriting.emb sourceStrongStepContext)) ⋎
      (translateFormula context predicate ![]
          (∼(Rewriting.emb sourceAllContextualPrefixes)) ⋎
        translateFormula context predicate ![]
          (Rewriting.emb sourceStrongInductionConclusion)) =
      prefixExtractionFormula context predicate
  rw [translateFormula_neg, translateFormula_neg,
    translate_sourceAllContextualPrefixes,
    translate_sourceStrongInductionConclusion]
  rfl

/-- PA proves equality replacement uniformly for the inserted model-coded
formula.  This is exactly the extra law which the expanded fixed source
theory cannot assume about an arbitrary relation interpretation. -/
noncomputable def predicateCongruenceProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Peano.internalize V ⊢! predicateCongruenceFormula context predicate := by
  let equalityAtom : Semisentence SourceLanguage 2 :=
    .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
      ![(#1 : ClosedSemiterm SourceLanguage 2),
        (#0 : ClosedSemiterm SourceLanguage 2)]
  let leftPredicateAtom : Semisentence SourceLanguage 2 :=
    sourcePredicateAtom (#1 : ClosedSemiterm SourceLanguage 2)
  let rightPredicateAtom : Semisentence SourceLanguage 2 :=
    sourcePredicateAtom (#0 : ClosedSemiterm SourceLanguage 2)
  have heqNeg := translateFormula_neg context predicate ![]
    (Rewriting.emb equalityAtom)
  have hpNeg := translateFormula_neg context predicate ![]
    (Rewriting.emb leftPredicateAtom)
  change Peano.internalize V ⊢!
    ∀⁰ ∀⁰
      (translateFormula context predicate ![]
          (∼(Rewriting.emb equalityAtom)) ⋎
        (translateFormula context predicate ![]
            (∼(Rewriting.emb leftPredicateAtom)) ⋎
          translateFormula context predicate ![]
            (Rewriting.emb rightPredicateAtom)))
  rw [heqNeg, hpNeg]
  simpa [sourcePredicateAtom, secondAtom, translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def,
    equalityAtom, leftPredicateAtom, rightPredicateAtom,
    Function.comp_def,
    Matrix.fun_eq_vec_two, Matrix.constant_eq_singleton] using
    (LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.replace'
      Peano predicate).get

/-! ## The represented strong-induction compiler -/

/-- Ordinary PA-induction kernel on contextual prefixes. -/
noncomputable def prefixInductionKernel
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate) :
    PAInductionKernel (inductionContextFormula context predicate) := by
  simpa only [inductionContextFormula, sourcePrefixTemplate] using
    (sourcePrefixTemplate.toPAInductionKernel
      context predicate ![] hcontext hpredicate)

/-- A proof of the strong-step premise supplies the induction kernel's
conjunctive context, because formula congruence is already a theorem of PA. -/
noncomputable def strongStepToInductionContextProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    Peano.internalize V ⊢!
      strongStepFormula context predicate 🡒
        inductionContextFormula context predicate := by
  rw [translate_sourceInductionContext]
  exact Entailment.CK_of_C_of_C
    Entailment.C_id
    (Entailment.C_of_conseq
      (predicateCongruenceProof context predicate))

/-- Compile the fixed endpoint-extraction source proof. -/
noncomputable def compiledPrefixExtractionProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate) :
    Peano.internalize V ⊢! prefixExtractionFormula context predicate := by
  simpa only [translate_sourcePrefixExtractionSentence] using
    (compilePeanoTemplate context predicate ![] hcontext hpredicate
      sourcePrefixExtractionProof)

/-- Uniform strong induction for an arbitrary, possibly nonstandard,
model-coded arithmetic formula.  The output retains the strong-step premise
as an implication, so callers can compose it under their own staged
certificate context. -/
noncomputable def strongInductionImplicationProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate) :
    Peano.internalize V ⊢!
      strongStepFormula context predicate 🡒
        context 🡒 ∀⁰ predicate := by
  have hallPrefixesFromInductionContext :
      Peano.internalize V ⊢!
        inductionContextFormula context predicate 🡒
          ∀⁰ contextualPrefixPredicate context predicate := by
    simpa only [contextualPrefixPredicate, inductionContextFormula,
      sourcePrefixTemplate,
      TwoPredicateSourceContextInductionKernel.Template.toPAInductionKernel,
      TwoPredicateSourceContextInductionKernel.specializedPredicate] using
      (sourcePrefixTemplate.toPAInductionKernel
        context predicate ![] hcontext hpredicate).compileImplication
  have hallPrefixesFromStrongStep :
      Peano.internalize V ⊢!
        strongStepFormula context predicate 🡒
          ∀⁰ contextualPrefixPredicate context predicate :=
    Entailment.C_trans
      (strongStepToInductionContextProof context predicate)
      hallPrefixesFromInductionContext
  exact (compiledPrefixExtractionProof context predicate
      hcontext hpredicate) ⨀₁ hallPrefixesFromStrongStep

/-- Modus-ponens form for callers which have already constructed the
represented strong-step proof. -/
noncomputable def strongInductionProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate)
    (hstep : Peano.internalize V ⊢!
      strongStepFormula context predicate) :
    Peano.internalize V ⊢! context 🡒 ∀⁰ predicate :=
  TProof.modusPonens
    (strongInductionImplicationProof context predicate
      hcontext hpredicate)
    hstep

set_option backward.isDefEq.respectTransparency false in
/-- The compiler's returned value is accepted by PA's represented proof
predicate. -/
theorem strongInductionProof_isPAProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate)
    (hstep : Peano.internalize V ⊢!
      strongStepFormula context predicate) :
    Proof Peano
      (strongInductionProof context predicate hcontext hpredicate hstep).val
      (context 🡒 ∀⁰ predicate).val := by
  simpa [Proof] using
    (strongInductionProof context predicate
      hcontext hpredicate hstep).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction
