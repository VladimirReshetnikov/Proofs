import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula

/-!
# The model-coded PA-axiom-soundness field

The final soundness argument needs a sentence saying that every code accepted
by PA's represented axiom recognizer is true in the current partial-truth
predicate, provided the code lies in the advertised quantifier-group domain.
At a nonstandard truth level neither the formula code nor the truth predicate
can be decoded into Lean syntax, so the complete assertion must itself be
assembled as model-coded arithmetic syntax.

This module fixes that syntax in the same source language as the dynamic
truth successor.  It proves literal specialization at arbitrary model-coded
lower truth syntax, identifies the base and positive orbit instances, and
represents the positive field-code function by a Sigma-one graph.  The later
formula-induction proof that the field holds is intentionally separate.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## Fixed source syntax -/

/-- Arithmetic zero lifted into the source language. -/
noncomputable def sourceZeroTerm {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  ((‘0’ : ArithmeticSemiterm Empty n)).lMap (arithmeticHom 3 2)

/-- Apply a unary source formula to one closed source term. -/
noncomputable def apply₁ {n : ℕ}
    (p : Semisentence SourceLanguage 1)
    (t : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t]

/-- The formula-code variable `#1` is accepted by PA's fixed Delta-one axiom
recognizer.  The surrounding variables are `(free, formula)`. -/
noncomputable def sourceRecognizedPAAxiom :
    Semisentence SourceLanguage 2 :=
  apply₁ (liftArithmeticFormula (Peano : Theory ℒₒᵣ).Δ₁ch.val) (#1)

/-- The formula code lies in the domain bounded by the lower hierarchy
level. -/
noncomputable def sourceAxiomBoundedDomain :
    Semisentence SourceLanguage 2 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (parameterTerm 0) (#1)

/-- The free-variable environment is a genuine coded HFS sequence. -/
noncomputable def sourceFreeSequence :
    Semisentence SourceLanguage 2 :=
  apply₁ (liftArithmeticFormula seqDef.val) (#0)

/-- A recognized bounded PA axiom is true at empty bound environment and the
supplied free-variable environment. -/
noncomputable def sourceAxiomSoundnessBody :
    Semisentence SourceLanguage 2 :=
  Arrow.arrow
    (sourceRecognizedPAAxiom ⋏
      (sourceAxiomBoundedDomain ⋏ sourceFreeSequence))
    (apply₃ successorTruthFormula sourceZeroTerm (#0) (#1))

/-- Unary induction predicate: only the formula code remains free. -/
noncomputable def sourceAxiomSoundnessPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ sourceAxiomSoundnessBody

/-- The universally closed axiom-soundness certificate field. -/
noncomputable def sourceAxiomSoundnessSentence : Sentence SourceLanguage :=
  ∀⁰ sourceAxiomSoundnessPredicate

/-! ## Typed model-coded syntax -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Typed quotation of source arithmetic zero.  Retaining `Rew.emb` makes
the exact source-specialization theorem definitionally transparent: it only
changes the impossible source free-variable type to `Nat`. -/
noncomputable def typedSourceZeroTerm {n : ℕ} :
    Bootstrapping.Semiterm V ℒₒᵣ n :=
  ⌜(Rew.emb (‘0’ : ArithmeticSemiterm Empty n) :
      ArithmeticSemiterm ℕ n)⌝

/-- Typed application of PA's fixed represented axiom recognizer. -/
noncomputable def recognizedPAAxiomFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  (⌜(Peano : Theory ℒₒᵣ).Δ₁ch.val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 1).subst
    ![Semiterm.bvar (1 : Fin 2)]

/-- Typed application of the bounded quantifier-group domain. -/
noncomputable def axiomBoundedDomainFormula (lowerLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  (⌜(quantifierBoundedCodeDef ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral lowerLevel,
      Semiterm.bvar (1 : Fin 2)]

/-- Typed assertion that the free environment is a sequence. -/
noncomputable def freeSequenceFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  (⌜seqDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst
    ![Semiterm.bvar (0 : Fin 2)]

/-- The concrete soundness implication for one formula code. -/
noncomputable def axiomSoundnessBodyFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (boundedLevel : V) : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  Arrow.arrow
    (recognizedPAAxiomFormula ⋏
      (axiomBoundedDomainFormula boundedLevel ⋏ freeSequenceFormula))
    (DynamicTruthFormula.apply₃ upper
      typedSourceZeroTerm
      (Semiterm.bvar (0 : Fin 2))
      (Semiterm.bvar (1 : Fin 2)))

/-- Unary formula-code predicate consumed by the later induction kernel. -/
noncomputable def axiomSoundnessPredicateFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (boundedLevel : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ axiomSoundnessBodyFormula upper boundedLevel

/-- Universally closed field for an upper truth predicate supplied directly. -/
noncomputable def upperAxiomSoundnessFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (boundedLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ axiomSoundnessPredicateFormula upper boundedLevel

/-- Field constructed together with one dynamic truth successor. -/
noncomputable def axiomSoundnessFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  upperAxiomSoundnessFormula
    (DynamicTruthFormula.successorTruthFormula
      lower lowerLevel upperLevel)
    lowerLevel

/-! ## Exact source specialization -/

@[simp] theorem translate_sourceZeroTerm
    (parameters : Fin 2 → V) :
    translateTerm parameters
        (Rew.emb (sourceZeroTerm (n := n)) :
          SyntacticSemiterm SourceLanguage n) =
      (typedSourceZeroTerm : Bootstrapping.Semiterm V ℒₒᵣ n) := by
  simpa only [sourceZeroTerm, typedSourceZeroTerm, Rew.emb,
    Semiterm.lMap_map] using
    ModelCodedPredicateParameters.translateTerm_lMap_arithmetic
      parameters
      (Rew.emb (‘0’ : ArithmeticSemiterm Empty n))

/-- Translation commutes exactly with unary source application. -/
@[simp] theorem translate_apply₁
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 1)
    (t : ClosedSemiterm SourceLanguage n) :
    translateFormula lower parameters
        (Rewriting.emb (apply₁ p t)) =
      (translateFormula lower parameters (Rewriting.emb p)).subst
        ![translateTerm parameters
          (Rew.emb t : SyntacticSemiterm SourceLanguage n)] := by
  rw [apply₁, Semiformula.coe_subst_eq_subst_coe,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

@[simp] theorem translate_sourceRecognizedPAAxiom
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceRecognizedPAAxiom) =
      recognizedPAAxiomFormula := by
  rw [sourceRecognizedPAAxiom, translate_apply₁,
    translate_liftArithmeticFormula]
  simp [recognizedPAAxiomFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceAxiomBoundedDomain
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomBoundedDomain) =
      axiomBoundedDomainFormula lowerLevel := by
  simp [sourceAxiomBoundedDomain, axiomBoundedDomainFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceFreeSequence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceFreeSequence) =
      freeSequenceFormula := by
  rw [sourceFreeSequence, translate_apply₁,
    translate_liftArithmeticFormula]
  simp [freeSequenceFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceAxiomSoundnessBody
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomSoundnessBody) =
      axiomSoundnessBodyFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        lowerLevel := by
  simp [sourceAxiomSoundnessBody, axiomSoundnessBodyFormula,
    Bootstrapping.Semiformula.imp_def,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourceAxiomSoundnessPredicate
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomSoundnessPredicate) =
      axiomSoundnessPredicateFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        lowerLevel := by
  simp [sourceAxiomSoundnessPredicate, axiomSoundnessPredicateFormula,
    ModelCodedPredicateParameters.translateFormula]

/-- Specialization of the complete fixed source sentence is literally the
advertised typed axiom-soundness field. -/
@[simp] theorem translate_sourceAxiomSoundnessSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomSoundnessSentence) =
      axiomSoundnessFormula lower lowerLevel upperLevel := by
  simp [sourceAxiomSoundnessSentence, axiomSoundnessFormula,
    upperAxiomSoundnessFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! ## Represented orbit instances -/

/-- Base field for the first positive truth predicate. -/
noncomputable def baseAxiomSoundnessFormula :
    Bootstrapping.Formula V ℒₒᵣ :=
  axiomSoundnessFormula baseTruthFormula 0 1

/-- At the base, the upper predicate is literally `truthFormula 0`. -/
theorem baseAxiomSoundnessFormula_eq_upper :
    baseAxiomSoundnessFormula (V := V) =
      upperAxiomSoundnessFormula (truthFormula 0) 0 := by
  simp [baseAxiomSoundnessFormula, axiomSoundnessFormula,
    truthFormula_zero, DynamicTruthFormula.levelZeroTruthFormula]

/-- Positive successor field over the represented dynamic orbit. -/
noncomputable def orbitSuccessorAxiomSoundnessFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  axiomSoundnessFormula (truthFormula n) (n + 1) (n + 1 + 1)

/-- The positive branch uses the next orbit member as its upper truth
predicate and bounds formulas at the matching lower level. -/
theorem orbitSuccessorAxiomSoundnessFormula_eq_upper (n : V) :
    orbitSuccessorAxiomSoundnessFormula n =
      upperAxiomSoundnessFormula (truthFormula (n + 1)) (n + 1) := by
  simp [orbitSuccessorAxiomSoundnessFormula, axiomSoundnessFormula,
    truthFormula_succ]

/-! ## Representability of the positive-branch code -/

/-- The raw positive axiom-soundness field code has a Sigma-one graph.
Every displayed operation is a represented syntax constructor, and the only
recursive input is the already represented dynamic truth orbit. -/
theorem orbitSuccessorAxiomSoundnessFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitSuccessorAxiomSoundnessFormula n).val) := by
  simp only [orbitSuccessorAxiomSoundnessFormula, axiomSoundnessFormula,
    upperAxiomSoundnessFormula, axiomSoundnessPredicateFormula,
    axiomSoundnessBodyFormula, recognizedPAAxiomFormula,
    axiomBoundedDomainFormula, freeSequenceFormula, typedSourceZeroTerm,
    DynamicTruthFormula.successorTruthFormula_val_eq_code,
    DynamicTruthFormula.apply₃_val,
    Semiformula.val_all, Semiformula.val_imp, Semiformula.val_and,
    Bootstrapping.Semiformula.val_substs]
  definability

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
