import BoundedPAConsistency.FixedLevelTruthDefinability
import BoundedPAConsistency.UniformInternalProvability
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed

/-!
# A model-coded successor operation for partial-truth formulas

The externally indexed `SigmaTrue` hierarchy is useful for proving each
standard bounded-consistency instance, but it cannot itself be iterated up to
a nonstandard element of a model of PA.  This file starts the genuinely
uniform construction: a successor truth formula is assembled directly from
an arbitrary *model-coded* ternary formula representing the lower truth
predicate.  Consequently no decoding of that formula into Lean syntax is
needed.

The construction below deliberately separates the syntactic operation from
its eventual PA proof certificate.  Its evaluation theorem is the semantic
contract that the proof compiler must certify using model-internal typed
derivations.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-! ## The concrete base formula -/

/-- A named Sigma-one formula for quantifier-free truth.

`QFTrue.definable` only asserts that some formula exists.  A uniform formula
compiler needs a stable piece of syntax which can be quoted into every PA
model, so we expose the defining formula rather than selecting an anonymous
definability witness. -/
noncomputable def qfTruthDef : HierarchySymbol.sigmaOne.Semisentence 3 :=
  .mkSigma
    “bound free p.
      !(quantifierBoundedCodeDef ℒₒᵣ).sigma 0 p ∧
      ∃ y, !qfValueGraph y bound free p ∧ y = 1”

instance qfTruth_defined :
    HierarchySymbol.DefinedRel₃ (V := V) HierarchySymbol.sigmaOne
      QFTrue qfTruthDef := .mk fun v ↦ by
  simp [qfTruthDef, QFTrue, IsQuantifierFreeCode]

/-- The base truth formula as syntax *inside* an arbitrary arithmetic model.

The code can be manipulated by the typed proof constructors even when later
successor formulas are nonstandard. -/
noncomputable def baseTruthFormula : Semiformula V ℒₒᵣ 3 :=
  ⌜qfTruthDef.val⌝

@[simp] theorem baseTruthFormula_val :
    (baseTruthFormula (V := V)).val = (⌜qfTruthDef.val⌝ : V) := rfl

@[simp] private theorem typedQuote_val_eq_quote
    (formula : ArithmeticSemisentence n) :
    (⌜formula⌝ : Semiformula V ℒₒᵣ n).val =
      (⌜formula⌝ : V) := rfl

@[simp] private theorem typedQuote_semisentence_shift
    (formula : ArithmeticSemisentence n) :
    (⌜formula⌝ : Semiformula V ℒₒᵣ n).shift = ⌜formula⌝ := by
  let φ : ArithmeticSemiproposition n := Rewriting.emb formula
  have hφ : Rewriting.shift φ = φ := by
    apply Semiformula.rew_eq_self_of
    · simp
    · intro x hx
      have hx' : x ∈ φ.freeVariables := by simpa using hx
      simpa [φ] using hx'
  rw [Sentence.typed_quote_def, ← Semiformula.typed_quote_shift]
  exact congr_arg (⌜·⌝ : ArithmeticSemiproposition n →
    Semiformula V ℒₒᵣ n) hφ

@[simp] theorem baseTruthFormula_shift :
    shift ℒₒᵣ (baseTruthFormula (V := V)).val =
      (baseTruthFormula (V := V)).val := by
  exact congr_arg Semiformula.val
    (typedQuote_semisentence_shift (V := V) qfTruthDef.val)

@[simp] private theorem typedNumeral_shift (x : V) :
    (Arithmetic.typedNumeral x : Semiterm V ℒₒᵣ n).shift =
      Arithmetic.typedNumeral x := by
  ext
  simp [Arithmetic.typedNumeral, Semiterm.shift]

/-! ## Typed applications of fixed represented relations -/

/-- Apply a model-coded ternary formula to three typed terms. -/
noncomputable def apply₃ {n : ℕ}
    (S : Semiformula V ℒₒᵣ 3)
    (t₀ t₁ t₂ : Semiterm V ℒₒᵣ n) :
    Semiformula V ℒₒᵣ n :=
  S.subst ![t₀, t₁, t₂]

@[simp] theorem apply₃_val {n : ℕ}
    (S : Semiformula V ℒₒᵣ 3)
    (t₀ t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (apply₃ S t₀ t₁ t₂).val =
      subst ℒₒᵣ ?[t₀.val, t₁.val, t₂.val] S.val := by
  simp [apply₃]

/-! ## Fixed syntax used by the successor operation -/

/-- A named Sigma-one definition of the Sigma-oriented rank domain. -/
noncomputable def isSigmaCodeDef :
    HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “level p. !((isUFormula ℒₒᵣ).sigma) p ∧
    ∃ ranks, !(rankPairGraph ℒₒᵣ) ranks p ∧
    ∃ sigmaRank, !pi₁Def sigmaRank ranks ∧ sigmaRank ≤ level”

instance isSigmaCode_defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaOne
      (OrientedHierarchy.IsSigmaCode ℒₒᵣ) isSigmaCodeDef := .mk fun v ↦ by
  simp [isSigmaCodeDef, OrientedHierarchy.IsSigmaCode,
    sigmaRankCode]

/-- A named Sigma-one definition of the Pi-oriented rank domain. -/
noncomputable def isPiCodeDef :
    HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “level p. !((isUFormula ℒₒᵣ).sigma) p ∧
    ∃ ranks, !(rankPairGraph ℒₒᵣ) ranks p ∧
    ∃ piRank, !pi₂Def piRank ranks ∧ piRank ≤ level”

instance isPiCode_defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaOne
      (OrientedHierarchy.IsPiCode ℒₒᵣ) isPiCodeDef := .mk fun v ↦ by
  simp [isPiCodeDef, OrientedHierarchy.IsPiCode, piRankCode,
    recordWitness]

/-- The lower-independent alternatives of one successor-certificate record:
quantifier-free leaves, conjunction, disjunction, and existential witness.

The remaining universal-leaf alternative is assembled separately because it
contains the arbitrary model-coded lower truth formula. -/
noncomputable def positiveRecordBranchesDef :
    HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “C r.
    ∃ bound, !recordBoundDef bound r ∧
    ∃ free, !recordFreeDef free r ∧
    ∃ p, !recordFormulaDef p r ∧
      (!qfTruthDef.val bound free p ∨
       (∃ p₁ < p, ∃ p₂ < p,
          !qqAndDef p p₁ p₂ ∧
          !hasTruthStateDef C bound free p₁ ∧
          !hasTruthStateDef C bound free p₂) ∨
       (∃ p₁ < p, ∃ p₂ < p,
          !qqOrDef p p₁ p₂ ∧
          (!hasTruthStateDef C bound free p₁ ∨
           !hasTruthStateDef C bound free p₂)) ∨
       (∃ q < p, !qqExsDef p q ∧
          ∃ witness, !pi₂Def witness r ∧
          ∃ extended, !seqConsDef extended bound witness ∧
            !hasTruthStateDef C extended free q))”

/-- Semantics of the lower-independent record alternatives. -/
def PositiveRecordBranches (C r : V) : Prop :=
  let bound := recordBound r
  let free := recordFree r
  let p := recordFormula r
  QFTrue bound free p ∨
    (∃ p₁ < p, ∃ p₂ < p,
      p = p₁ ^⋏ p₂ ∧
      HasTruthState C bound free p₁ ∧
      HasTruthState C bound free p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p,
      p = p₁ ^⋎ p₂ ∧
      (HasTruthState C bound free p₁ ∨
       HasTruthState C bound free p₂)) ∨
    (∃ q < p,
      p = ^∃ q ∧
      HasTruthState C (bound ⁀' recordWitness r) free q)

instance positiveRecordBranches_defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaOne
      PositiveRecordBranches positiveRecordBranchesDef := .mk fun v ↦ by
  simp [positiveRecordBranchesDef, PositiveRecordBranches]

/-- Fixed part of the universal-leaf branch.

The variables are ordered to make the first five (`negp`, `q`, `p`, `free`,
`bound`) disappear under five existential binders.  The remaining variables
are `lowerLevel`, `C`, and `r`. -/
noncomputable def universalRecordPrefixDef :
    HierarchySymbol.sigmaOne.Semisentence 8 := .mkSigma
  “negp q p free bound lowerLevel C r.
    !recordBoundDef bound r ∧
    !recordFreeDef free r ∧
    !recordFormulaDef p r ∧
    q < p ∧ !qqAllDef p q ∧
    !isPiCodeDef.val lowerLevel p ∧
    !(negGraph ℒₒᵣ) negp p”

/-- Semantics of the fixed prefix of a universal-leaf record. -/
def UniversalRecordPrefix
    (negp q p free bound lowerLevel _C r : V) : Prop :=
  recordBound r = bound ∧
  recordFree r = free ∧
  recordFormula r = p ∧
  q < p ∧ p = ^∀ q ∧
  OrientedHierarchy.IsPiCode ℒₒᵣ lowerLevel p ∧
  negp = neg ℒₒᵣ p

instance universalRecordPrefix_defined :
    HierarchySymbol.Defined (V := V)
      (fun v : Fin 8 → V ↦
        UniversalRecordPrefix
          (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7))
      universalRecordPrefixDef := .mk fun v ↦ by
  simp [universalRecordPrefixDef, UniversalRecordPrefix, eq_comm]

/-- The universal-leaf branch obtained by inserting the lower truth formula.

Its three arguments are `(lowerLevel, C, r)`. -/
noncomputable def universalRecordBranch
    (lower : Semiformula V ℒₒᵣ 3) : Semiformula V ℒₒᵣ 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    ((⌜universalRecordPrefixDef.val⌝ : Semiformula V ℒₒᵣ 8) ⋏
      ∼(apply₃ lower
        (Semiterm.bvar (4 : Fin 8))
        (Semiterm.bvar (3 : Fin 8))
        (Semiterm.bvar (0 : Fin 8))))

/-- Domain of a record at the advertised upper Sigma level.

Its arguments are `(upperLevel, C, r)`; `C` is retained to keep the same
argument order as the other record components. -/
noncomputable def recordDomainDef :
    HierarchySymbol.sigmaOne.Semisentence 3 := .mkSigma
  “upperLevel C r. ∃ p,
    !recordFormulaDef p r ∧ !isSigmaCodeDef.val upperLevel p”

/-- Semantics of the successor-record domain formula. -/
def RecordDomain (upperLevel _C r : V) : Prop :=
  OrientedHierarchy.IsSigmaCode ℒₒᵣ upperLevel (recordFormula r)

instance recordDomain_defined :
    HierarchySymbol.DefinedRel₃ (V := V) HierarchySymbol.sigmaOne
      RecordDomain recordDomainDef := .mk fun v ↦ by
  simp [recordDomainDef, RecordDomain]

/-- Syntactic local-validity predicate for one successor certificate.

Unlike `SigmaRecordValid`, this is an actual model-coded binary formula.  Its
arguments are `(C,r)`, and arbitrary (including nonstandard) model elements
may be supplied for the two hierarchy levels. -/
noncomputable def successorRecordValid
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V) :
    Semiformula V ℒₒᵣ 2 :=
  ((⌜recordDomainDef.val⌝ : Semiformula V ℒₒᵣ 3).subst
      ![Arithmetic.typedNumeral upperLevel, Semiterm.bvar (0 : Fin 2),
        Semiterm.bvar (1 : Fin 2)]) ⋏
    ((⌜positiveRecordBranchesDef.val⌝ : Semiformula V ℒₒᵣ 2) ⋎
      (universalRecordBranch lower).subst
        ![Arithmetic.typedNumeral lowerLevel, Semiterm.bvar (0 : Fin 2),
          Semiterm.bvar (1 : Fin 2)])

/-- A tiny fixed formula for HFS membership, used to form the bounded
universal certificate check. -/
noncomputable def hfsMemDef : HierarchySymbol.sigmaZero.Semisentence 2 :=
  .mkSigma “x y. x ∈ y”

instance hfsMem_defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaZero
      (fun x y : V ↦ x ∈ y) hfsMemDef := .mk fun v ↦ by
  simp [hfsMemDef]

/-! ## Standard syntax corresponding to one dynamic successor

The model-coded constructors below are the objects needed at a nonstandard
stage.  At a standard stage we can also assemble the same formula in Lean's
ordinary syntax and quote it.  Recording both constructions, and proving
that quotation commutes with them, is the bridge which lets us reuse the
existing fixed-level semantic truth theorems to obtain actual PA proof
objects at the base of the represented recursion. -/

/-- Apply an ordinary closed ternary formula to three ordinary closed terms.

This is the standard-syntax counterpart of `apply₃`. -/
theorem typedQuote_closedSubst {k n : ℕ}
    (S : ArithmeticSemisentence k)
    (w : Fin k → ClosedSemiterm ℒₒᵣ n) :
    (⌜S ⇜ w⌝ : Semiformula V ℒₒᵣ n) =
      (⌜S⌝ : Semiformula V ℒₒᵣ k).subst
        (fun i ↦ (⌜w i⌝ : Semiterm V ℒₒᵣ n)) := by
  rw [Sentence.typed_quote_def,
    Semiformula.coe_subst_eq_subst_coe,
    Semiformula.typed_quote_substs]
  simp only [Semiterm.empty_typed_quote_def, Sentence.typed_quote_def]

noncomputable def standardApply₃ {n : ℕ}
    (S : ArithmeticSemisentence 3)
    (t₀ t₁ t₂ : ClosedSemiterm ℒₒᵣ n) :
    ArithmeticSemisentence n :=
  S ⇜ ![t₀, t₁, t₂]

@[simp] theorem typedQuote_standardApply₃ {n : ℕ}
    (S : ArithmeticSemisentence 3)
    (t₀ t₁ t₂ : ClosedSemiterm ℒₒᵣ n) :
    (⌜standardApply₃ S t₀ t₁ t₂⌝ : Semiformula V ℒₒᵣ n) =
      apply₃ (⌜S⌝ : Semiformula V ℒₒᵣ 3)
        (⌜t₀⌝ : Semiterm V ℒₒᵣ n)
        (⌜t₁⌝ : Semiterm V ℒₒᵣ n)
        (⌜t₂⌝ : Semiterm V ℒₒᵣ n) := by
  rw [standardApply₃, typedQuote_closedSubst]
  unfold apply₃
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i => exact i.elim0

/-- Binary variant used for the membership and record-validity applications
inside the standard successor formula. -/
noncomputable def standardApply₂ {n : ℕ}
    (S : ArithmeticSemisentence 2)
    (t₀ t₁ : ClosedSemiterm ℒₒᵣ n) :
    ArithmeticSemisentence n :=
  S ⇜ ![t₀, t₁]

@[simp] theorem typedQuote_standardApply₂ {n : ℕ}
    (S : ArithmeticSemisentence 2)
    (t₀ t₁ : ClosedSemiterm ℒₒᵣ n) :
    (⌜standardApply₂ S t₀ t₁⌝ : Semiformula V ℒₒᵣ n) =
      (⌜S⌝ : Semiformula V ℒₒᵣ 2).subst
        ![(⌜t₀⌝ : Semiterm V ℒₒᵣ n),
          (⌜t₁⌝ : Semiterm V ℒₒᵣ n)] := by
  rw [standardApply₂, typedQuote_closedSubst]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0

/-- Standard syntax for the universal-record leaf after inserting a lower
truth formula. -/
noncomputable def standardUniversalRecordBranch
    (lower : ArithmeticSemisentence 3) : ArithmeticSemisentence 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    (universalRecordPrefixDef.val ⋏
      ∼(standardApply₃ lower (#4) (#3) (#0)))

@[simp] theorem typedQuote_standardUniversalRecordBranch
    (lower : ArithmeticSemisentence 3) :
    (⌜standardUniversalRecordBranch lower⌝ :
        Semiformula V ℒₒᵣ 3) =
      universalRecordBranch (⌜lower⌝ : Semiformula V ℒₒᵣ 3) := by
  simp [standardUniversalRecordBranch, universalRecordBranch]

/-- Ordinary semantics of the dynamically variable universal leaf. -/
@[simp] theorem eval_standardUniversalRecordBranch_iff
    (lower : ArithmeticSemisentence 3) (v : Fin 3 → V) :
    (standardUniversalRecordBranch lower).Evalb (M := V) v ↔
      ∃ q < recordFormula (v 2),
        recordFormula (v 2) = ^∀ q ∧
        OrientedHierarchy.IsPiCode ℒₒᵣ (v 0) (recordFormula (v 2)) ∧
        ¬lower.Evalb (M := V)
          ![recordBound (v 2), recordFree (v 2),
            neg ℒₒᵣ (recordFormula (v 2))] := by
  simp [standardUniversalRecordBranch, standardApply₃,
    UniversalRecordPrefix, eq_comm]
  constructor
  · rintro ⟨⟨q, hq, hformula, hpi⟩, hlower⟩
    exact ⟨q, hq, hformula, hpi, hlower⟩
  · rintro ⟨q, hq, hformula, hpi, hlower⟩
    exact ⟨⟨q, hq, hformula, hpi⟩, hlower⟩

/-- Standard syntax for one successor-certificate record. -/
noncomputable def standardSuccessorRecordValid
    (lower : ArithmeticSemisentence 3)
    (lowerLevel upperLevel : ℕ) : ArithmeticSemisentence 2 :=
  standardApply₃ recordDomainDef.val (↑upperLevel) (#0) (#1) ⋏
    (positiveRecordBranchesDef.val ⋎
      standardApply₃ (standardUniversalRecordBranch lower)
        (↑lowerLevel) (#0) (#1))

@[simp] theorem typedQuote_standardSuccessorRecordValid
    (lower : ArithmeticSemisentence 3)
    (lowerLevel upperLevel : ℕ) :
    (⌜standardSuccessorRecordValid lower lowerLevel upperLevel⌝ :
        Semiformula V ℒₒᵣ 2) =
      successorRecordValid
        (⌜lower⌝ : Semiformula V ℒₒᵣ 3)
        (ORingStructure.numeral lowerLevel)
        (ORingStructure.numeral upperLevel) := by
  simp [standardSuccessorRecordValid, successorRecordValid,
    apply₃, numeral_eq_natCast]

/-- Ordinary semantics of a standard successor-record formula. -/
@[simp] theorem eval_standardSuccessorRecordValid_iff
    (lower : ArithmeticSemisentence 3)
    (lowerLevel upperLevel : ℕ) (v : Fin 2 → V) :
    (standardSuccessorRecordValid lower lowerLevel upperLevel).Evalb
        (M := V) v ↔
      SigmaRecordValid
        (fun bound free p ↦
          lower.Evalb (M := V) ![bound, free, p])
        (ORingStructure.numeral lowerLevel)
        (ORingStructure.numeral upperLevel)
        (v 0) (v 1) := by
  simp [standardSuccessorRecordValid, standardApply₃,
    SigmaRecordValid, RecordDomain, PositiveRecordBranches,
    LowerPiTrue, numeral_eq_natCast]
  aesop

/-- The ordinary arithmetic formula whose quotation is one standard
instance of the dynamic successor constructor. -/
noncomputable def standardSuccessorTruthFormula
    (lower : ArithmeticSemisentence 3)
    (lowerLevel upperLevel : ℕ) : ArithmeticSemisentence 3 :=
  ∃⁰
    (hasTruthStateDef.val ⋏
      (∀⁰
        (standardApply₂ hfsMemDef.val (#0) (#1) 🡒
          standardApply₂
            (standardSuccessorRecordValid lower lowerLevel upperLevel)
            (#1) (#0))))

/-- One syntactic successor step on a carried model-coded truth formula.

The result again has the three arguments `(bound, free, p)`.  Its witness is
an HFS certificate `C`; every member of `C` must satisfy
`successorRecordValid`. -/
noncomputable def successorTruthFormula
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V) :
    Semiformula V ℒₒᵣ 3 :=
  ∃⁰
    ((⌜hasTruthStateDef.val⌝ : Semiformula V ℒₒᵣ 4) ⋏
      (∀⁰
        (((⌜hfsMemDef.val⌝ : Semiformula V ℒₒᵣ 2).subst
            ![Semiterm.bvar (0 : Fin 5), Semiterm.bvar (1 : Fin 5)]) 🡒
          (successorRecordValid lower lowerLevel upperLevel).subst
            ![Semiterm.bvar (1 : Fin 5), Semiterm.bvar (0 : Fin 5)])))

/-- Quoting a standard successor formula produces exactly the typed dynamic
constructor.  This is syntactic equality, not merely semantic equivalence. -/
@[simp] theorem typedQuote_standardSuccessorTruthFormula
    (lower : ArithmeticSemisentence 3)
    (lowerLevel upperLevel : ℕ) :
    (⌜standardSuccessorTruthFormula lower lowerLevel upperLevel⌝ :
        Semiformula V ℒₒᵣ 3) =
      successorTruthFormula (⌜lower⌝ : Semiformula V ℒₒᵣ 3)
        (ORingStructure.numeral lowerLevel)
        (ORingStructure.numeral upperLevel) := by
  simp [standardSuccessorTruthFormula, successorTruthFormula,
    numeral_eq_natCast]

/-! ## The underlying total code transformer -/

/-- Raw code of the dynamically inserted universal-record branch.

This operation is total on model elements.  Well-formedness is imposed by a
package relation, rather than hidden in the function's domain. -/
noncomputable def universalRecordBranchCode (lower : V) : V :=
  ^∃ ^∃ ^∃ ^∃ ^∃
    ((⌜universalRecordPrefixDef.val⌝ : V) ^⋏
      neg ℒₒᵣ (subst ℒₒᵣ ?[^#4, ^#3, ^#0] lower))

/-- Raw code of local validity for one successor-certificate record. -/
noncomputable def successorRecordValidCode
    (lower lowerLevel upperLevel : V) : V :=
  subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral upperLevel, ^#0, ^#1]
      (⌜recordDomainDef.val⌝ : V) ^⋏
    ((⌜positiveRecordBranchesDef.val⌝ : V) ^⋎
      subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral lowerLevel, ^#0, ^#1]
        (universalRecordBranchCode lower))

/-- Total raw code operation underlying `successorTruthFormula`. -/
noncomputable def successorTruthFormulaCode
    (lower lowerLevel upperLevel : V) : V :=
  ^∃
    ((⌜hasTruthStateDef.val⌝ : V) ^⋏
      ^∀
        (imp ℒₒᵣ
          (subst ℒₒᵣ ?[^#0, ^#1] (⌜hfsMemDef.val⌝ : V))
          (subst ℒₒᵣ ?[^#1, ^#0]
            (successorRecordValidCode lower lowerLevel upperLevel))))

@[simp] theorem universalRecordBranch_val_eq_code
    (lower : Semiformula V ℒₒᵣ 3) :
    (universalRecordBranch lower).val =
      universalRecordBranchCode lower.val := by
  simp [universalRecordBranch, universalRecordBranchCode, apply₃]

@[simp] theorem successorRecordValid_val_eq_code
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V) :
    (successorRecordValid lower lowerLevel upperLevel).val =
      successorRecordValidCode lower.val lowerLevel upperLevel := by
  simp [successorRecordValid, successorRecordValidCode]

@[simp] theorem successorTruthFormula_val_eq_code
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V) :
    (successorTruthFormula lower lowerLevel upperLevel).val =
      successorTruthFormulaCode lower.val lowerLevel upperLevel := by
  simp [successorTruthFormula, successorTruthFormulaCode]

/-- The code transformer is Sigma-one definable.  This is the part needed to
put the formula field of a truth certificate into the package relation. -/
instance successorTruthFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₃ (V := V)
      successorTruthFormulaCode := by
  unfold successorTruthFormulaCode successorRecordValidCode
    universalRecordBranchCode
  definability

@[simp] theorem successorTruthFormula_isSemiformula
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V) :
    IsSemiformula ℒₒᵣ 3
      (successorTruthFormula lower lowerLevel upperLevel).val :=
  (successorTruthFormula lower lowerLevel upperLevel).isSemiformula

private theorem subst_shift_fixed
    (formula : Semiformula V ℒₒᵣ k)
    (terms : SemitermVec V ℒₒᵣ k n)
    (hformula : formula.shift = formula)
    (hterms : ∀ i, (terms i).shift = terms i) :
    (formula.subst terms).shift = formula.subst terms := by
  rw [Semiformula.shift_substs, hformula]
  congr
  funext i
  exact hterms i

private theorem apply₃_shift_fixed
    (lower : Semiformula V ℒₒᵣ 3)
    (t₀ t₁ t₂ : Semiterm V ℒₒᵣ n)
    (hlower : lower.shift = lower)
    (ht₀ : t₀.shift = t₀) (ht₁ : t₁.shift = t₁)
    (ht₂ : t₂.shift = t₂) :
    (apply₃ lower t₀ t₁ t₂).shift =
      apply₃ lower t₀ t₁ t₂ := by
  apply subst_shift_fixed lower ![t₀, t₁, t₂] hlower
  intro i
  cases i using Fin.cases with
  | zero => exact ht₀
  | succ i =>
      cases i using Fin.cases with
      | zero => exact ht₁
      | succ i =>
          cases i using Fin.cases with
          | zero => exact ht₂
          | succ i => exact i.elim0

private theorem universalRecordBranch_shift_fixed
    (lower : Semiformula V ℒₒᵣ 3) (hlower : lower.shift = lower) :
    (universalRecordBranch lower).shift = universalRecordBranch lower := by
  have hprefix :
      (⌜universalRecordPrefixDef.val⌝ : Semiformula V ℒₒᵣ 8).shift =
        ⌜universalRecordPrefixDef.val⌝ :=
    typedQuote_semisentence_shift universalRecordPrefixDef.val
  have hlowerAt :
      (apply₃ lower
          (Semiterm.bvar (4 : Fin 8))
          (Semiterm.bvar (3 : Fin 8))
          (Semiterm.bvar (0 : Fin 8))).shift =
        apply₃ lower
          (Semiterm.bvar (4 : Fin 8))
          (Semiterm.bvar (3 : Fin 8))
          (Semiterm.bvar (0 : Fin 8)) := by
    apply apply₃_shift_fixed lower _ _ _ hlower <;> simp
  simp only [universalRecordBranch, Semiformula.shift_exs,
    Semiformula.shift_and, Semiformula.shift_neg, hprefix, hlowerAt]

private theorem successorRecordValid_shift_fixed
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V)
    (hlower : lower.shift = lower) :
    (successorRecordValid lower lowerLevel upperLevel).shift =
      successorRecordValid lower lowerLevel upperLevel := by
  have hdomain :
      (((⌜recordDomainDef.val⌝ : Semiformula V ℒₒᵣ 3).subst
        ![Arithmetic.typedNumeral upperLevel, Semiterm.bvar (0 : Fin 2),
          Semiterm.bvar (1 : Fin 2)])).shift =
      ((⌜recordDomainDef.val⌝ : Semiformula V ℒₒᵣ 3).subst
        ![Arithmetic.typedNumeral upperLevel, Semiterm.bvar (0 : Fin 2),
          Semiterm.bvar (1 : Fin 2)]) := by
    apply subst_shift_fixed _ _
        (typedQuote_semisentence_shift recordDomainDef.val)
    intro i
    cases i using Fin.cases with
    | zero => exact typedNumeral_shift upperLevel
    | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i =>
            cases i using Fin.cases with
            | zero => simp
            | succ i => exact i.elim0
  have hpositive :
      (⌜positiveRecordBranchesDef.val⌝ : Semiformula V ℒₒᵣ 2).shift =
        ⌜positiveRecordBranchesDef.val⌝ :=
    typedQuote_semisentence_shift positiveRecordBranchesDef.val
  have huniversal :
      (((universalRecordBranch lower).subst
        ![Arithmetic.typedNumeral lowerLevel, Semiterm.bvar (0 : Fin 2),
          Semiterm.bvar (1 : Fin 2)])).shift =
      (universalRecordBranch lower).subst
        ![Arithmetic.typedNumeral lowerLevel, Semiterm.bvar (0 : Fin 2),
          Semiterm.bvar (1 : Fin 2)] := by
    apply subst_shift_fixed _ _
        (universalRecordBranch_shift_fixed lower hlower)
    intro i
    cases i using Fin.cases with
    | zero => exact typedNumeral_shift lowerLevel
    | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i =>
            cases i using Fin.cases with
            | zero => simp
            | succ i => exact i.elim0
  simp only [successorRecordValid, Semiformula.shift_and,
    Semiformula.shift_or, hdomain, hpositive, huniversal]

/-- The successor constructor preserves the absence of free variables.

This syntactic theorem is one of the key preconditions for using the
model-coded PA induction axiom on certificate invariants.  It does not assume
that the carried lower formula is standard. -/
theorem successorTruthFormula_shift_of_lower
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V)
    (hlower : lower.shift = lower) :
    (successorTruthFormula lower lowerLevel upperLevel).shift =
      successorTruthFormula lower lowerLevel upperLevel := by
  have hstate :
      (⌜hasTruthStateDef.val⌝ : Semiformula V ℒₒᵣ 4).shift =
        ⌜hasTruthStateDef.val⌝ :=
    typedQuote_semisentence_shift hasTruthStateDef.val
  have hmem :
      (((⌜hfsMemDef.val⌝ : Semiformula V ℒₒᵣ 2).subst
        ![Semiterm.bvar (0 : Fin 5), Semiterm.bvar (1 : Fin 5)])).shift =
      ((⌜hfsMemDef.val⌝ : Semiformula V ℒₒᵣ 2).subst
        ![Semiterm.bvar (0 : Fin 5), Semiterm.bvar (1 : Fin 5)]) := by
    apply subst_shift_fixed _ _
        (typedQuote_semisentence_shift hfsMemDef.val)
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i => exact i.elim0
  have hvalid :
      (((successorRecordValid lower lowerLevel upperLevel).subst
        ![Semiterm.bvar (1 : Fin 5), Semiterm.bvar (0 : Fin 5)])).shift =
      (successorRecordValid lower lowerLevel upperLevel).subst
        ![Semiterm.bvar (1 : Fin 5), Semiterm.bvar (0 : Fin 5)] := by
    apply subst_shift_fixed _ _
        (successorRecordValid_shift_fixed lower lowerLevel upperLevel hlower)
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i => exact i.elim0
  simp only [successorTruthFormula, Semiformula.shift_exs,
    Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_imp,
    hstate, hmem, hvalid]

/-- Code-level form of `successorTruthFormula_shift_of_lower`. -/
theorem successorTruthFormula_val_shift_of_lower
    (lower : Semiformula V ℒₒᵣ 3) (lowerLevel upperLevel : V)
    (hlower : shift ℒₒᵣ lower.val = lower.val) :
    shift ℒₒᵣ (successorTruthFormula lower lowerLevel upperLevel).val =
      (successorTruthFormula lower lowerLevel upperLevel).val := by
  have hlower' : lower.shift = lower := Semiformula.ext hlower
  exact congr_arg Semiformula.val
    (successorTruthFormula_shift_of_lower lower lowerLevel upperLevel hlower')

/-- The actual satisfaction formula used for the level-zero consistency
argument: one successor-certificate layer over quantifier-free truth. -/
noncomputable def levelZeroTruthFormula : Semiformula V ℒₒᵣ 3 :=
  successorTruthFormula baseTruthFormula 0 1

/-- Ordinary syntax for the first positive partial-truth level. -/
noncomputable def levelZeroTruthSyntax : ArithmeticSemisentence 3 :=
  standardSuccessorTruthFormula qfTruthDef.val 0 1

/-- The dynamic level-zero formula is exactly the quotation of the ordinary
first-level formula.  In particular the base package can be justified by a
standard PA proof while later stages remain genuinely model-coded. -/
@[simp] theorem levelZeroTruthFormula_eq_typedQuote :
    levelZeroTruthFormula (V := V) =
      (⌜levelZeroTruthSyntax⌝ : Semiformula V ℒₒᵣ 3) := by
  symm
  simpa [levelZeroTruthFormula, levelZeroTruthSyntax,
    baseTruthFormula] using
    (typedQuote_standardSuccessorTruthFormula (V := V)
      qfTruthDef.val 0 1)

@[simp] theorem levelZeroTruthFormula_val_eq_quote :
    (levelZeroTruthFormula (V := V)).val =
      (⌜levelZeroTruthSyntax⌝ : V) := by
  rw [levelZeroTruthFormula_eq_typedQuote]
  rfl

set_option maxHeartbeats 800000 in
/-- Semantic identification of the standard base formula.

This theorem unfolds only ordinary syntax, so it is legitimate to use
Foundation's formula semantics.  It is deliberately stated separately from
the model-coded successor operation, whose lower formula need not decode to
ordinary syntax at a nonstandard stage. -/
@[simp] theorem eval_levelZeroTruthSyntax_iff
    (v : Fin 3 → V) :
    levelZeroTruthSyntax.Evalb (M := V) v ↔
      SigmaTrue 1 (v 0) (v 1) (v 2) := by
  simp [levelZeroTruthSyntax, standardSuccessorTruthFormula,
    standardApply₂, SigmaTrue]

@[simp] theorem levelZeroTruthFormula_shift :
    shift ℒₒᵣ (levelZeroTruthFormula (V := V)).val =
      (levelZeroTruthFormula (V := V)).val := by
  exact successorTruthFormula_val_shift_of_lower baseTruthFormula 0 1
    baseTruthFormula_shift

/-! ## A proof-producing base checkpoint -/

/-- The exact level-zero final-consistency field used by the uniform target.

Using the canonical instance of `paRestrictedConsistencyTemplate` keeps its
code definitionally aligned with `substNumeral` via
`substNumeral_paRestrictedConsistencyTemplate_eq_quote`. -/
noncomputable def baseFinalConsistencyFormula :
    Bootstrapping.Formula V ℒₒᵣ :=
  ⌜(paRestrictedConsistencyTemplate/[(0 : ℕ)] : ArithmeticSentence)⌝

/-- A genuine typed PA proof of the base final-consistency field.

This uses D1 only at the standard base point.  Unlike a semantic truth
argument, the returned object contains a derivation code in the ambient model
and can therefore be stored in a proof package. -/
noncomputable def baseFinalConsistencyProof :
    Peano.internalize V ⊢! baseFinalConsistencyFormula := by
  exact (internal_provable_of_outer_provable (V := V)
    (pa_proves_paRestrictedConsistencyTemplate_instance 0)).get

set_option backward.isDefEq.respectTransparency false in
/-- The `.val` projection of `baseFinalConsistencyProof` is accepted by the
represented PA proof predicate. -/
theorem baseFinalConsistencyProof_isPAProof :
    Proof Peano (baseFinalConsistencyProof (V := V)).val
      (baseFinalConsistencyFormula (V := V)).val := by
  simpa [Proof] using (baseFinalConsistencyProof (V := V)).derivationOf

/-- The base proof concludes exactly the code used by the selector target at
model numeral zero. -/
theorem baseFinalConsistencyFormula_val_eq_target :
    (baseFinalConsistencyFormula (V := V)).val =
      Bootstrapping.Arithmetic.substNumeral
        (⌜paRestrictedConsistencyTemplate⌝ : V) 0 := by
  symm
  exact substNumeral_paRestrictedConsistencyTemplate_eq_quote 0

/-- Explicit base witness for the model-internal selector relation. -/
theorem exists_paProof_restrictedConsistency_zero :
    ∃ d : V, Proof Peano d
      (Bootstrapping.Arithmetic.substNumeral
        (⌜paRestrictedConsistencyTemplate⌝ : V) 0) := by
  refine ⟨(baseFinalConsistencyProof (V := V)).val, ?_⟩
  rw [← baseFinalConsistencyFormula_val_eq_target (V := V)]
  exact baseFinalConsistencyProof_isPAProof

end LeanProofs.BoundedPAConsistency.DynamicTruthFormula
