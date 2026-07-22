import PAListCoding.Basic

/-!
# PA-representable predicates on coded finite lists

All predicates below are stated directly in the arithmetic structure.  They
therefore make sense in every model of `IΣ₁` (and hence in every model of PA),
not merely after decoding a standard natural number into a Lean `List`.

The existential witnesses are themselves coded sequences:

* `ConcatAll` uses a trace of successive partial concatenations;
* `Occurrences` uses a trace of running counts;
* `SumElements` and `ProductElements` use traces of partial aggregates;
* `Permutation` and `Subsequence` use lists of source indices.

These choices are important: every quantifier in the definitions is an
ordinary first-order arithmetic quantifier, and Foundation's definability
machinery consequently produces an actual arithmetic formula for each one.
-/

namespace PAListCoding

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `v` is a valid list code of length `n`. -/
def HasLength (v n : V) : Prop := Seq v ∧ lh v = n

/-- The indexing convention is zero-based: `k = 0` denotes the first entry. -/
def Entry (v k m : V) : Prop := Seq v ∧ k < lh v ∧ znth v k = m

/-- `v` is exactly the one-element list `[m]`. -/
def Singleton (v m : V) : Prop := Seq v ∧ lh v = 1 ∧ znth v 0 = m

/-- `v` is `t` followed by `u`.  All three arguments must be valid codes. -/
def Concat (v t u : V) : Prop :=
  Seq v ∧ Seq t ∧ Seq u ∧ lh v = lh t + lh u ∧
    (∀ i < lh t, znth v i = znth t i) ∧
    ∀ j < lh u, znth v (lh t + j) = znth u j

/--
`v` concatenates, in order, every coded list occurring in `w`.

The trace has length `lh w + 1`.  Its zeroth entry is the empty list, and
entry `i+1` is obtained by appending list `w[i]` to entry `i`.
-/
def ConcatAll (v w : V) : Prop :=
  Seq v ∧ Seq w ∧ (∀ i < lh w, Seq (znth w i)) ∧
    ∃ trace, Seq trace ∧ lh trace = lh w + 1 ∧ znth trace 0 = ∅ ∧
      (∀ i < lh w,
        Concat (znth trace (i + 1)) (znth trace i) (znth w i)) ∧
      znth trace (lh w) = v

/--
`v` contains exactly `n` occurrences of `m`.

The witness trace stores the running count: it starts at zero and at every
position either increments (when the current entry is `m`) or stays fixed.
-/
def Occurrences (v n m : V) : Prop :=
  Seq v ∧ ∃ trace, Seq trace ∧ lh trace = lh v + 1 ∧ znth trace 0 = 0 ∧
    (∀ i < lh v,
      (znth v i = m ∧ znth trace (i + 1) = znth trace i + 1) ∨
      (znth v i ≠ m ∧ znth trace (i + 1) = znth trace i)) ∧
    znth trace (lh v) = n

/--
`p` is the sum of the entries of `v`.

The trace contains one more entry than `v`: entry `i` is the sum of the first
`i` inputs.  In particular, the empty code has the one-entry trace `[0]` and
therefore has sum zero.
-/
def SumElements (p v : V) : Prop :=
  Seq v ∧ ∃ trace, Seq trace ∧ lh trace = lh v + 1 ∧ znth trace 0 = 0 ∧
    (∀ i < lh v,
      znth trace (i + 1) = znth trace i + znth v i) ∧
    znth trace (lh v) = p

/--
`p` is the product of the entries of `v`.

This is the multiplicative analogue of `SumElements`; starting the trace at
one makes the empty product equal to one.
-/
def ProductElements (p v : V) : Prop :=
  Seq v ∧ ∃ trace, Seq trace ∧ lh trace = lh v + 1 ∧ znth trace 0 = 1 ∧
    (∀ i < lh v,
      znth trace (i + 1) = znth trace i * znth v i) ∧
    znth trace (lh v) = p

/-- `m` occurs in nonempty `v` and bounds every entry from above. -/
def Greatest (m v : V) : Prop :=
  Seq v ∧ ∃ i < lh v, znth v i = m ∧
    ∀ j < lh v, znth v j ≤ m

/-- `m` occurs in nonempty `v` and bounds every entry from below. -/
def Least (m v : V) : Prop :=
  Seq v ∧ ∃ i < lh v, znth v i = m ∧
    ∀ j < lh v, m ≤ znth v j

/-- A valid coded list whose entries at distinct positions are distinct. -/
def NoDuplicates (v : V) : Prop :=
  Seq v ∧ ∀ i < lh v, ∀ j < lh v, i < j → znth v i ≠ znth v j

/--
`v` is a permutation of `w`.

The witness `indices` maps each output position to a source position.  Equal
lengths, range bounds, and `NoDuplicates indices` make this injection a
bijection between the two finite initial segments.
-/
def Permutation (v w : V) : Prop :=
  Seq v ∧ Seq w ∧ lh v = lh w ∧
    ∃ indices, NoDuplicates indices ∧ lh indices = lh v ∧
      ∀ i < lh v,
        znth indices i < lh w ∧ znth v i = znth w (znth indices i)

/-- `v` occurs contiguously inside `w`, beginning at some bounded offset. -/
def Substring (v w : V) : Prop :=
  Seq v ∧ Seq w ∧ ∃ offset < lh w + 1,
    offset + lh v ≤ lh w ∧
      ∀ i < lh v, znth v i = znth w (offset + i)

/-- A valid coded list of strictly increasing indices. -/
def IncreasingIndices (indices : V) : Prop :=
  Seq indices ∧ ∀ i < lh indices, ∀ j < lh indices,
    i < j → znth indices i < znth indices j

/--
`v` is a (not necessarily contiguous) subsequence of `w`.

The strictly increasing witness list gives the selected positions of `w`.
-/
def Subsequence (v w : V) : Prop :=
  Seq v ∧ Seq w ∧ ∃ indices,
    IncreasingIndices indices ∧ lh indices = lh v ∧
      ∀ i < lh v,
        znth indices i < lh w ∧ znth v i = znth w (znth indices i)

/-- A valid numeric list sorted in non-decreasing order. -/
def Nondecreasing (v : V) : Prop :=
  Seq v ∧ ∀ i < lh v,
    i + 1 < lh v → znth v i ≤ znth v (i + 1)

/--
`m` is twice the median of the entries of nonempty `v`.

The witness `sorted` is a non-decreasing permutation.  If the length is
`2k+1`, twice the median is twice entry `k`; if it is `2(k+1)`, it is the sum
of entries `k` and `k+1`.  Writing the definition this way avoids division
and parity predicates and is well behaved in every model of PA.
-/
def TwiceMedian (m v : V) : Prop :=
  Seq v ∧ ∃ sorted,
    Permutation sorted v ∧ Nondecreasing sorted ∧
      ((∃ k, lh v = k + k + 1 ∧
          m = znth sorted k + znth sorted k) ∨
       ∃ k, lh v = (k + 1) + (k + 1) ∧
          m = znth sorted k + znth sorted (k + 1))

/--
`m` occurs in `v` and has strictly larger multiplicity than every different
entry.  Quantifying over positions rather than arbitrary numbers keeps the
comparison bounded; every possible competitor necessarily occurs at one of
those positions.
-/
def UniqueMode (m v : V) : Prop :=
  Seq v ∧ ∃ i < lh v, znth v i = m ∧
    ∀ j < lh v, znth v j ≠ m →
      ∃ cm cx,
        Occurrences v cm m ∧ Occurrences v cx (znth v j) ∧ cx < cm

/-- The usual lexicographic non-strict order on two valid coded lists. -/
def LexLE (a b : V) : Prop :=
  Seq a ∧ Seq b ∧
    ((lh a ≤ lh b ∧ ∀ i < lh a, znth a i = znth b i) ∨
      ∃ i < lh a, i < lh b ∧
        (∀ j < i, znth a j = znth b j) ∧ znth a i < znth b i)

/-- A valid list of valid list codes, sorted lexicographically. -/
def LexSorted (v : V) : Prop :=
  Seq v ∧ (∀ i < lh v, Seq (znth v i)) ∧
    ∀ i < lh v,
      i + 1 < lh v → LexLE (znth v i) (znth v (i + 1))

/--
`v` lists every distinct permutation of `w`, exactly once, in lexicographic
order.  Soundness says every entry is a permutation; the final (unbounded)
clause is completeness.  `NoDuplicates v` turns completeness into exact-once
enumeration, while `LexSorted v` fixes the requested order.
-/
def AllPermutations (v w : V) : Prop :=
  Seq v ∧ Seq w ∧ NoDuplicates v ∧ LexSorted v ∧
    (∀ i < lh v, PAListCoding.Permutation (znth v i) w) ∧
    ∀ p : V, Seq p → PAListCoding.Permutation p w →
      ∃ i < lh v, znth v i = p

namespace AllPermutations

theorem output_valid {v w : V} (h : AllPermutations v w) : Seq v := h.1

theorem input_valid {v w : V} (h : AllPermutations v w) : Seq w := h.2.1

theorem noDuplicates {v w : V} (h : AllPermutations v w) :
    NoDuplicates v := h.2.2.1

theorem lexSorted {v w : V} (h : AllPermutations v w) :
    LexSorted v := h.2.2.2.1

theorem sound {v w : V} (h : AllPermutations v w) {i : V} (hi : i < lh v) :
    PAListCoding.Permutation (znth v i) w := h.2.2.2.2.1 i hi

theorem complete {v w p : V} (h : AllPermutations v w) (hp : Seq p)
    (hperm : PAListCoding.Permutation p w) :
    ∃ i < lh v, znth v i = p := h.2.2.2.2.2 p hp hperm

end AllPermutations

/-!
## Definability

We use `𝚺-[2]` uniformly for all relations above except
`AllPermutations`.  This is a convenient common upper bound; several of them
are in fact bounded (`𝚺₀`).
The proofs below synthesize formulas from the closure of representable
relations under Boolean operations, bounded quantification, and coded
existential witnesses.
-/

@[simp, definability] instance hasLength_definable :
    𝚺-[2]-Relation (HasLength : V → V → Prop) := by definability

@[simp, definability] instance entry_definable :
    𝚺-[2]-Relation₃ (Entry : V → V → V → Prop) := by definability

@[simp, definability] instance singleton_definable :
    𝚺-[2]-Relation (Singleton : V → V → Prop) := by definability

@[simp, definability] instance concat_definable :
    𝚺-[2]-Relation₃ (Concat : V → V → V → Prop) := by definability

@[simp, definability] instance concatAll_definable :
    𝚺-[2]-Relation (ConcatAll : V → V → Prop) := by definability

@[simp, definability] instance occurrences_definable :
    𝚺-[2]-Relation₃ (Occurrences : V → V → V → Prop) := by definability

@[simp, definability] instance sumElements_definable :
    𝚺-[2]-Relation (SumElements : V → V → Prop) := by definability

@[simp, definability] instance productElements_definable :
    𝚺-[2]-Relation (ProductElements : V → V → Prop) := by definability

@[simp, definability] instance greatest_definable :
    𝚺-[2]-Relation (Greatest : V → V → Prop) := by definability

@[simp, definability] instance least_definable :
    𝚺-[2]-Relation (Least : V → V → Prop) := by definability

@[simp, definability] instance noDuplicates_definable :
    𝚺-[2]-Predicate (NoDuplicates : V → Prop) := by definability

@[simp, definability] instance permutation_definable :
    𝚺-[2]-Relation (Permutation : V → V → Prop) := by definability

@[simp, definability] instance substring_definable :
    𝚺-[2]-Relation (Substring : V → V → Prop) := by definability

@[simp, definability] instance increasingIndices_definable :
    𝚺-[2]-Predicate (IncreasingIndices : V → Prop) := by definability

@[simp, definability] instance subsequence_definable :
    𝚺-[2]-Relation (Subsequence : V → V → Prop) := by definability

@[simp, definability] instance nondecreasing_definable :
    𝚺-[2]-Predicate (Nondecreasing : V → Prop) := by definability

@[simp, definability] instance twiceMedian_definable :
    𝚺-[2]-Relation (TwiceMedian : V → V → Prop) := by definability

@[simp, definability] instance uniqueMode_definable :
    𝚺-[2]-Relation (UniqueMode : V → V → Prop) := by definability

@[simp, definability] instance lexLE_definable :
    𝚺-[2]-Relation (LexLE : V → V → Prop) := by definability

@[simp, definability] instance lexSorted_definable :
    𝚺-[2]-Predicate (LexSorted : V → Prop) := by definability

/-!
`AllPermutations` mixes an existential soundness predicate with a universal
completeness predicate.  For this last relation we deliberately erase the
unneeded hierarchy annotation and use unrestricted first-order definability.
The result is still syntax in the language of arithmetic and hence is exactly
the sort of PA formula required here.
-/

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private theorem rawDefinable {k : ℕ} {R : (Fin k → V) → Prop}
    (h : 𝚺-[2].Definable R) :
    LO.FirstOrder.Language.Definable ℒₒᵣ R := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨φ.val, hφ.df⟩

private instance seq_raw_definable :
    LO.FirstOrder.Language.DefinablePred (M := V) ℒₒᵣ (Seq : V → Prop) :=
  rawDefinable (seq_definable' (V := V) (𝚺-[2]))

private instance lh_raw_definable :
    LO.FirstOrder.Language.DefinableFunction₁ (M := V) ℒₒᵣ (lh : V → V) :=
  rawDefinable (lh_definable' (V := V) (𝚺-[2]))

private instance znth_raw_definable :
    LO.FirstOrder.Language.DefinableFunction₂ (M := V) ℒₒᵣ (znth : V → V → V) :=
  rawDefinable (znth_definable' (V := V) (𝚺-[2]))

private instance noDuplicates_raw_definable :
    LO.FirstOrder.Language.DefinablePred (M := V) ℒₒᵣ
      (NoDuplicates : V → Prop) :=
  rawDefinable (noDuplicates_definable (V := V))

private instance lexSorted_raw_definable :
    LO.FirstOrder.Language.DefinablePred (M := V) ℒₒᵣ
      (LexSorted : V → Prop) :=
  rawDefinable (lexSorted_definable (V := V))

private instance permutation_raw_definable :
    LO.FirstOrder.Language.DefinableRel (M := V) ℒₒᵣ
      (PAListCoding.Permutation : V → V → Prop) :=
  rawDefinable (permutation_definable (V := V))

@[simp, definability] instance allPermutations_definable :
    LO.FirstOrder.Language.DefinableRel (M := V) ℒₒᵣ
      (AllPermutations : V → V → Prop) := by
  definability

/-!
## Concrete PA formula witnesses

`PAFormula k` is an arithmetic formula with `k` object variables and standard
natural-number parameters.  `formulaOf` chooses the formula supplied by the
definability proof.  The following theorem records, once and for all, that the
chosen syntax has exactly the intended interpretation in the standard model.
-/

abbrev PAFormula (k : ℕ) := ArithmeticSemiformula ℕ k

noncomputable def formulaOf {k : ℕ} {R : (Fin k → ℕ) → Prop}
    (h : 𝚺-[2].Definable R) : PAFormula k :=
  (Classical.choose h.definable).val

@[simp] theorem formulaOf_spec {k : ℕ} {R : (Fin k → ℕ) → Prop}
    (h : 𝚺-[2].Definable R) (v : Fin k → ℕ) :
    (formulaOf h).Eval v id ↔ R v := by
  exact (Classical.choose_spec h.definable).iff

noncomputable def lengthFormula : PAFormula 2 :=
  formulaOf (hasLength_definable (V := ℕ))

@[simp] theorem lengthFormula_spec (v n : ℕ) :
    lengthFormula.Eval ![v, n] id ↔ HasLength v n := by
  exact formulaOf_spec (hasLength_definable (V := ℕ)) ![v, n]

noncomputable def entryFormula : PAFormula 3 :=
  formulaOf (entry_definable (V := ℕ))

@[simp] theorem entryFormula_spec (v k m : ℕ) :
    entryFormula.Eval ![v, k, m] id ↔ Entry v k m := by
  exact formulaOf_spec (entry_definable (V := ℕ)) ![v, k, m]

noncomputable def singletonFormula : PAFormula 2 :=
  formulaOf (singleton_definable (V := ℕ))

@[simp] theorem singletonFormula_spec (v m : ℕ) :
    singletonFormula.Eval ![v, m] id ↔ Singleton v m := by
  exact formulaOf_spec (singleton_definable (V := ℕ)) ![v, m]

noncomputable def concatFormula : PAFormula 3 :=
  formulaOf (concat_definable (V := ℕ))

@[simp] theorem concatFormula_spec (v t u : ℕ) :
    concatFormula.Eval ![v, t, u] id ↔ Concat v t u := by
  exact formulaOf_spec (concat_definable (V := ℕ)) ![v, t, u]

noncomputable def concatAllFormula : PAFormula 2 :=
  formulaOf (concatAll_definable (V := ℕ))

@[simp] theorem concatAllFormula_spec (v w : ℕ) :
    concatAllFormula.Eval ![v, w] id ↔ ConcatAll v w := by
  exact formulaOf_spec (concatAll_definable (V := ℕ)) ![v, w]

noncomputable def occurrencesFormula : PAFormula 3 :=
  formulaOf (occurrences_definable (V := ℕ))

@[simp] theorem occurrencesFormula_spec (v n m : ℕ) :
    occurrencesFormula.Eval ![v, n, m] id ↔ Occurrences v n m := by
  exact formulaOf_spec (occurrences_definable (V := ℕ)) ![v, n, m]

noncomputable def permutationFormula : PAFormula 2 :=
  formulaOf (permutation_definable (V := ℕ))

@[simp] theorem permutationFormula_spec (v w : ℕ) :
    permutationFormula.Eval ![v, w] id ↔ Permutation v w := by
  exact formulaOf_spec (permutation_definable (V := ℕ)) ![v, w]

noncomputable def sumElementsFormula : PAFormula 2 :=
  formulaOf (sumElements_definable (V := ℕ))

@[simp] theorem sumElementsFormula_spec (p v : ℕ) :
    sumElementsFormula.Eval ![p, v] id ↔ SumElements p v := by
  exact formulaOf_spec (sumElements_definable (V := ℕ)) ![p, v]

noncomputable def productElementsFormula : PAFormula 2 :=
  formulaOf (productElements_definable (V := ℕ))

@[simp] theorem productElementsFormula_spec (p v : ℕ) :
    productElementsFormula.Eval ![p, v] id ↔ ProductElements p v := by
  exact formulaOf_spec (productElements_definable (V := ℕ)) ![p, v]

noncomputable def greatestFormula : PAFormula 2 :=
  formulaOf (greatest_definable (V := ℕ))

@[simp] theorem greatestFormula_spec (m v : ℕ) :
    greatestFormula.Eval ![m, v] id ↔ Greatest m v := by
  exact formulaOf_spec (greatest_definable (V := ℕ)) ![m, v]

noncomputable def leastFormula : PAFormula 2 :=
  formulaOf (least_definable (V := ℕ))

@[simp] theorem leastFormula_spec (m v : ℕ) :
    leastFormula.Eval ![m, v] id ↔ Least m v := by
  exact formulaOf_spec (least_definable (V := ℕ)) ![m, v]

noncomputable def twiceMedianFormula : PAFormula 2 :=
  formulaOf (twiceMedian_definable (V := ℕ))

@[simp] theorem twiceMedianFormula_spec (m v : ℕ) :
    twiceMedianFormula.Eval ![m, v] id ↔ TwiceMedian m v := by
  exact formulaOf_spec (twiceMedian_definable (V := ℕ)) ![m, v]

noncomputable def uniqueModeFormula : PAFormula 2 :=
  formulaOf (uniqueMode_definable (V := ℕ))

@[simp] theorem uniqueModeFormula_spec (m v : ℕ) :
    uniqueModeFormula.Eval ![m, v] id ↔ UniqueMode m v := by
  exact formulaOf_spec (uniqueMode_definable (V := ℕ)) ![m, v]

noncomputable def substringFormula : PAFormula 2 :=
  formulaOf (substring_definable (V := ℕ))

@[simp] theorem substringFormula_spec (v w : ℕ) :
    substringFormula.Eval ![v, w] id ↔ Substring v w := by
  exact formulaOf_spec (substring_definable (V := ℕ)) ![v, w]

noncomputable def subsequenceFormula : PAFormula 2 :=
  formulaOf (subsequence_definable (V := ℕ))

@[simp] theorem subsequenceFormula_spec (v w : ℕ) :
    subsequenceFormula.Eval ![v, w] id ↔ Subsequence v w := by
  exact formulaOf_spec (subsequence_definable (V := ℕ)) ![v, w]

noncomputable def noDuplicatesFormula : PAFormula 1 :=
  formulaOf (noDuplicates_definable (V := ℕ))

@[simp] theorem noDuplicatesFormula_spec (v : ℕ) :
    noDuplicatesFormula.Eval ![v] id ↔ NoDuplicates v := by
  exact formulaOf_spec (noDuplicates_definable (V := ℕ)) ![v]

noncomputable def nondecreasingFormula : PAFormula 1 :=
  formulaOf (nondecreasing_definable (V := ℕ))

@[simp] theorem nondecreasingFormula_spec (v : ℕ) :
    nondecreasingFormula.Eval ![v] id ↔ Nondecreasing v := by
  exact formulaOf_spec (nondecreasing_definable (V := ℕ)) ![v]

noncomputable def lexSortedFormula : PAFormula 1 :=
  formulaOf (lexSorted_definable (V := ℕ))

@[simp] theorem lexSortedFormula_spec (v : ℕ) :
    lexSortedFormula.Eval ![v] id ↔ LexSorted v := by
  exact formulaOf_spec (lexSorted_definable (V := ℕ)) ![v]

noncomputable def rawFormulaOf {k : ℕ} {R : (Fin k → ℕ) → Prop}
    (h : LO.FirstOrder.Language.Definable ℒₒᵣ R) : PAFormula k :=
  Classical.choose h.definable

@[simp] theorem rawFormulaOf_spec {k : ℕ} {R : (Fin k → ℕ) → Prop}
    (h : LO.FirstOrder.Language.Definable ℒₒᵣ R) (v : Fin k → ℕ) :
    (rawFormulaOf h).Eval v id ↔ R v := by
  exact (Classical.choose_spec h.definable).iff v

noncomputable def allPermutationsFormula : PAFormula 2 :=
  rawFormulaOf (allPermutations_definable (V := ℕ))

@[simp] theorem allPermutationsFormula_spec (v w : ℕ) :
    allPermutationsFormula.Eval ![v, w] id ↔ AllPermutations v w := by
  exact rawFormulaOf_spec (allPermutations_definable (V := ℕ)) ![v, w]

end PAListCoding
