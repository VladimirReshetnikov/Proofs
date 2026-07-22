import BoundedPAConsistency.ModelCodedPredicateParameters

/-!
# A compiled named-parameter transport theorem for model-coded truth

Truth-certificate proofs repeatedly specialize a law which is universal in
one environment coordinate at a particular, possibly nonstandard, coded
environment.  This file supplies that proof template in the standard source
language and compiles it to an actual represented PA derivation.

The source predicate is ternary, with arguments `(bound, free, formula)`.
Two named constants fix `free` and `formula`; a third names the particular
`bound` code.  The source theorem is the genuine quantifier-elimination law

`(forall bound, Truth(bound, free, formula)) ->
  Truth(namedBound, free, formula)`.

Unlike an identity tautology, the proof performs a real universal
specialization.  Its three nullary symbols may be interpreted by arbitrary
elements of the ambient PA model, so the compiled proof works unchanged for
nonstandard environment and formula codes.
-/

namespace LeanProofs.BoundedPAConsistency.NamedTruthTransportTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## The fixed source theorem -/

/-- A ternary predicate and three nullary symbols, in the order
`free`, `formula`, and `bound`. -/
abbrev SourceLanguage := parameterTemplateLanguage 3 3

/-- The `i`-th named constant, usable at any binder depth. -/
def parameterTerm (i : Fin 3) {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inr (Sum.inr (.parameter i))) ![]

/-- The unary slice `Truth(bound, namedFree, namedFormula)` of the ternary
placeholder. -/
def truthSlice : Semisentence SourceLanguage 1 :=
  .rel (Sum.inr (Sum.inl PlaceholderRel.predicate))
    ![(#0), parameterTerm 0, parameterTerm 1]

/-- Universal specialization at the third named constant. -/
noncomputable def transportSentence : Sentence SourceLanguage :=
  (∀⁰ truthSlice) 🡒 truthSlice/[parameterTerm (n := 0) 2]

/-- A fixed source derivation of the transport sentence.

`Theory.Proof.specialize` is the first-order universal-elimination theorem;
no premise about the placeholder relation and no extra nonlogical axiom is
introduced here. -/
noncomputable def sourceProof :
    parameterTemplatePeano 3 3 ⊢! transportSentence :=
  (Theory.Proof.specialize truthSlice (parameterTerm 2)).get

/-! ## Specialization at an arbitrary model-coded predicate -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The unary typed slice obtained after interpreting the first two source
constants by arbitrary model elements. -/
noncomputable def specializedSlice
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  S.subst ![
    Semiterm.bvar 0,
    Arithmetic.typedNumeral (parameters 0),
    Arithmetic.typedNumeral (parameters 1)]

/-- The explicit target of the compiled proof. -/
noncomputable def transportFormula
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  (∀⁰ specializedSlice S parameters) 🡒
    S.subst ![
      Arithmetic.typedNumeral (parameters 2),
      Arithmetic.typedNumeral (parameters 0),
      Arithmetic.typedNumeral (parameters 1)]

@[simp] theorem translate_parameterTerm
    (parameters : Fin 3 → V) (i : Fin 3) :
    ModelCodedPredicateParameters.translateTerm parameters
        (Rew.emb (parameterTerm (n := n) i) :
          SyntacticSemiterm SourceLanguage n) =
      Arithmetic.typedNumeral (parameters i) := by
  rfl

@[simp] theorem translate_truthSlice
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    ModelCodedPredicateParameters.translateFormula S parameters
        (Rewriting.emb truthSlice) = specializedSlice S parameters := by
  simp only [truthSlice, specializedSlice]
  congr 1

@[simp] theorem translate_truthSlice_at_namedBound
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    ModelCodedPredicateParameters.translateFormula S parameters
        (Rewriting.emb (truthSlice/[parameterTerm (n := 0) 2])) =
      S.subst ![
        Arithmetic.typedNumeral (parameters 2),
        Arithmetic.typedNumeral (parameters 0),
        Arithmetic.typedNumeral (parameters 1)] := by
  simp only [truthSlice, parameterTerm]
  congr 1

@[simp] theorem translate_universalTruthSlice
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    ModelCodedPredicateParameters.translateFormula S parameters
        (Rewriting.emb (∀⁰ truthSlice)) =
      ∀⁰ specializedSlice S parameters := by
  simp only [Rewriting.app_all,
    ModelCodedPredicateParameters.translateFormula]
  congr 1

/-- Specializing the fixed source syntax gives exactly the advertised typed
transport formula. -/
@[simp] theorem translate_transportSentence
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) :
    ModelCodedPredicateParameters.translateFormula
        S parameters (Rewriting.emb transportSentence) =
      transportFormula S parameters := by
  change
    ModelCodedPredicateParameters.translateFormula S parameters
        (∼(Rewriting.emb (∀⁰ truthSlice))) ⋎
      ModelCodedPredicateParameters.translateFormula S parameters
        (Rewriting.emb (truthSlice/[parameterTerm (n := 0) 2])) =
      transportFormula S parameters
  rw [ModelCodedPredicateParameters.translateFormula_neg]
  rw [translate_truthSlice_at_namedBound]
  simp only [transportFormula, Bootstrapping.Semiformula.imp_def]
  congr 1

/-- Compile universal specialization into a genuine typed PA proof about an
arbitrary closed model-coded ternary predicate. -/
noncomputable def compiledTransportProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hS : S.shift = S) :
    Peano.internalize V ⊢! transportFormula S parameters := by
  simpa only [translate_transportSentence] using
    (compilePeanoTemplate S parameters hS sourceProof)

/- The proof compiler itself returns a code accepted by PA's represented
proof predicate.  This is the raw-code bridge; it is stated before casting
the typed conclusion to the friendlier `transportFormula` spelling so that
the code is literally the compiler output. -/
set_option backward.isDefEq.respectTransparency false in
/-- The raw compiler output is recognized by PA's proof predicate. -/
theorem compilerOutput_isPAProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hS : S.shift = S) :
    Proof Peano (compilePeanoTemplate S parameters hS sourceProof).val
      (transportFormula S parameters).val := by
  simpa only [translate_transportSentence] using
    (compilePeanoTemplate_isPAProof S parameters hS sourceProof)

/- The `.val` of the explicitly typed wrapper is likewise a represented PA
proof.  Its code may contain the equality cast used to expose the friendly
target formula, so this statement is obtained from that typed derivation
rather than pretending the cast is definitionally absent. -/
set_option backward.isDefEq.respectTransparency false in
/-- The explicitly typed wrapper is also recognized by PA's proof predicate. -/
theorem compiledTransportProof_isPAProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 3 → V) (hS : S.shift = S) :
    Proof Peano (compiledTransportProof S parameters hS).val
      (transportFormula S parameters).val := by
  simpa [Proof] using
    (compiledTransportProof S parameters hS).derivationOf

end LeanProofs.BoundedPAConsistency.NamedTruthTransportTemplate
