import BoundedPAConsistency.TermEvaluation

/-!
# Semantic transport for coded arithmetic terms

The syntax operations in Foundation act on term codes inside an arbitrary
model of `I Sigma 1`.  Consequently their semantic laws cannot be obtained by
decoding to an external Lean term and inducting on that datatype.  This file
instead uses Foundation's *internal* structural induction principle for
`IsUTerm`; the resulting theorems therefore include nonstandard term codes.

Semantic environments are HFS sequences, whereas the `∷` notation used by
syntax vectors denotes a different, head-consed vector coding.  To keep that
distinction visible, free-variable shift is stated using the exact lookup law
required of an environment with one fresh head.  Bound substitution is stated
similarly using the exact de Bruijn lookup law induced by the substituting
term vector.  Internal Skolem-sequence arguments below show that both semantic
interfaces have genuine HFS-sequence witnesses.
-/

namespace LeanProofs.BoundedPAConsistency.TermEvaluationTransport

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TermEvaluation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- `shifted` is a free-variable environment obtained by putting an arbitrary
fresh value in front of `free`.  Only the tail is observable after applying
`termShift`, so this lookup equation is the precise semantic interface needed
by the transport theorem. -/
def IsFreeTail (shifted free : V) : Prop :=
  ∀ x : V, znth shifted (x + 1) = znth free x

/-- A well-formed free environment with `fresh` at index zero and all entries
of `free` shifted one position to the right. -/
def IsFreeHead (fresh shifted free : V) : Prop :=
  Seq free ∧
    Seq shifted ∧
    lh shifted = lh free + 1 ∧
    znth shifted 0 = fresh ∧
    IsFreeTail shifted free

/-- Every well-formed HFS sequence admits a semantic fresh-head extension.

Foundation's primitive sequence constructor appends at the *end*.  We use its
internal Sigma-one Skolem-sequence theorem here rather than confusing that
operation with the front extension needed by free-variable shift. -/
theorem exists_isFreeHead (fresh : V) {free : V} (hfree : Seq free) :
    ∃ shifted, IsFreeHead fresh shifted free := by
  let R : V → V → Prop := fun i y ↦
    (i = 0 ∧ y = fresh) ∨
      ∃ j, i = j + 1 ∧ y = znth free j
  have hR : 𝚺₁-Relation R := by
    dsimp [R]
    definability
  have htotal : ∀ i < lh free + 1, ∃ y, R i y := by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · exact ⟨fresh, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨znth free j, Or.inr ⟨j, rfl, rfl⟩⟩
  rcases sigmaOne_skolem_seq hR htotal with ⟨shifted, hshifted, hlen, hmem⟩
  refine ⟨shifted, hfree, hshifted, hlen, ?_, ?_⟩
  · have hzero : (0 : V) < lh shifted := by simp [hlen]
    rcases hmem 0 (znth shifted 0) (hshifted.znth hzero) with
      (h | ⟨j, hj, _⟩)
    · exact h.2
    · simp at hj
  · intro x
    by_cases hx : x < lh free
    · have hx' : x + 1 < lh shifted := by simpa [hlen] using hx
      rcases hmem (x + 1) (znth shifted (x + 1))
          (hshifted.znth hx') with
        (h | ⟨j, hj, hy⟩)
      · simp at h
      · have : x = j := add_right_cancel hj
        simpa [this] using hy
    · rw [znth_prop_not (Or.inr (not_lt.mp hx)), znth_prop_not]
      right
      simpa [hlen] using not_lt.mp hx

/-- Evaluation commutes with free-variable shift for every internally coded
well-formed term, including nonstandard codes in a nonstandard model.

No sequence well-formedness hypothesis is needed here: `znth` is total, and
`IsFreeTail` records exactly the lookup behavior used by shifted variables.
-/
theorem termValue_termShift_of_isFreeTail
    {bound shifted free t : V}
    (hfree : IsFreeTail shifted free)
    (ht : IsUTerm ℒₒᵣ t) :
    termValue bound shifted (termShift ℒₒᵣ t) =
      termValue bound free t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z
    simp
  · intro x
    simpa [IsFreeTail] using hfree x
  · intro k f terms hf hterms ih
    rw [termShift_func hf hterms,
      termValue_func hf hterms.termShiftVec,
      termValue_func hf hterms]
    congr 1
    apply nth_ext' k
      (by rw [length_termValues hterms.termShiftVec])
      (by rw [length_termValues hterms])
    intro i hi
    rw [nth_termValues hterms.termShiftVec hi,
      nth_termShiftVec hterms hi,
      nth_termValues hterms hi,
      ih i hi]

/-- Concrete fresh-head specialization of free-variable shift transport. -/
theorem termValue_termShift_of_isFreeHead
    {bound fresh shifted free t : V}
    (hfree : IsFreeHead fresh shifted free)
    (ht : IsUTerm ℒₒᵣ t) :
    termValue bound shifted (termShift ℒₒᵣ t) =
      termValue bound free t :=
  termValue_termShift_of_isFreeTail hfree.2.2.2.2 ht

/-- Vector form of `termValue_termShift_of_isFreeTail`. -/
theorem termValues_termShiftVec_of_isFreeTail
    {bound shifted free k terms : V}
    (hfree : IsFreeTail shifted free)
    (hterms : IsUTermVec ℒₒᵣ k terms) :
    termValues bound shifted k (termShiftVec ℒₒᵣ k terms) =
      termValues bound free k terms := by
  apply nth_ext' k
    (by rw [length_termValues hterms.termShiftVec])
    (by rw [length_termValues hterms])
  intro i hi
  rw [nth_termValues hterms.termShiftVec hi,
    nth_termShiftVec hterms hi,
    nth_termValues hterms hi,
    termValue_termShift_of_isFreeTail hfree (hterms.nth hi)]

/-- `subBound` is the bound-variable environment induced by evaluating the
first `n` entries of the substituting term vector `w` under `(bound, free)`.

The right side follows the direct indexing convention of `termSubst`; the
left side follows `termValue`'s reversed de Bruijn convention.  Keeping both
indices in the statement prevents an otherwise easy reversal bug.
-/
def IsSubstitutionBound
    (bound free n w subBound : V) : Prop :=
  ∀ z < n,
    znth subBound (boundPosition subBound z) =
      termValue bound free w.[z]

/-- A well-formed semantic environment induced by a substitution vector.
Both input environments are required to be genuine HFS sequences; the output
has exactly one entry for every substitutable bound variable. -/
def IsSubstitutionEnvironment
    (bound free n w subBound : V) : Prop :=
  IsUTermVec ℒₒᵣ n w ∧
    Seq bound ∧
    Seq free ∧
    Seq subBound ∧
    lh subBound = n ∧
    IsSubstitutionBound bound free n w subBound

/-- The values of a well-formed substitution vector can be assembled into a
genuine de Bruijn environment.  Entry `z` of the syntax vector is stored at
semantic position `n - (z + 1)`, since `termValue` reads bound environments
from the right. -/
theorem exists_isSubstitutionEnvironment
    {bound free n w : V}
    (hbound : Seq bound)
    (hfree : Seq free)
    (hw : IsUTermVec ℒₒᵣ n w) :
    ∃ subBound, IsSubstitutionEnvironment bound free n w subBound := by
  let R : V → V → Prop := fun i y ↦
    y = termValue bound free w.[n - (i + 1)]
  have hR : 𝚺₁-Relation R := by
    dsimp [R]
    definability
  have htotal : ∀ i < n, ∃ y, R i y := by
    intro i hi
    exact ⟨termValue bound free w.[n - (i + 1)], rfl⟩
  rcases sigmaOne_skolem_seq hR htotal with
    ⟨subBound, hsubBound, hlen, hmem⟩
  refine ⟨subBound, hw, hbound, hfree, hsubBound, hlen, ?_⟩
  intro z hz
  have hnpos : (0 : V) < n := lt_of_le_of_lt (by simp) hz
  have hindex : boundPosition subBound z < lh subBound := by
    simp only [boundPosition, hlen]
    exact tsub_lt_self hnpos (by simp)
  have hy := hmem (boundPosition subBound z)
    (znth subBound (boundPosition subBound z))
    (hsubBound.znth hindex)
  have hzle : z + 1 ≤ n := succ_le_iff_lt.mpr hz
  have hreversal : n - (boundPosition subBound z + 1) = z := by
    simp only [boundPosition, hlen]
    rw [← Arithmetic.sub_sub, tsub_tsub_cancel_of_le hzle]
    simp
  simpa [R, hreversal] using hy

/-- Evaluation commutes with simultaneous bound-variable substitution.

The source is an `n`-semiterm and `w` is a vector of `n` well-formed terms.
The target bound environment may still be nonempty: it is used when the terms
inside `w` themselves contain bound variables.
-/
theorem termValue_termSubst_of_isSubstitutionBound
    {bound free n w subBound t : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termValue bound free (termSubst ℒₒᵣ w t) =
      termValue subBound free t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termValue_bvar]
    exact (hsub z hz).symm
  · intro x
    simp
  · intro k f terms hf hterms ih
    have hsubst :
        IsUTermVec ℒₒᵣ k (termSubstVec ℒₒᵣ k w terms) :=
      ⟨(len_termSubstVec hterms.isUTerm).symm, fun i hi ↦ by
        rw [nth_termSubstVec hterms.isUTerm hi]
        exact hw.termSubst (hterms.nth hi)⟩
    rw [termSubst_func hf hterms.isUTerm,
      termValue_func hf hsubst,
      termValue_func hf hterms.isUTerm]
    congr 1
    apply nth_ext' k
      (by rw [length_termValues hsubst])
      (by rw [length_termValues hterms.isUTerm])
    intro i hi
    rw [nth_termValues hsubst hi,
      nth_termSubstVec hterms.isUTerm hi,
      nth_termValues hterms.isUTerm hi,
      ih i hi]

/-- Specialization to a fully well-formed induced substitution environment. -/
theorem termValue_termSubst_of_isSubstitutionEnvironment
    {bound free n w subBound t : V}
    (hsub : IsSubstitutionEnvironment bound free n w subBound)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termValue bound free (termSubst ℒₒᵣ w t) =
      termValue subBound free t :=
  termValue_termSubst_of_isSubstitutionBound hsub.1 hsub.2.2.2.2.2 ht

/-- Vector form of simultaneous-substitution transport. -/
theorem termValues_termSubstVec_of_isSubstitutionBound
    {bound free n w subBound k terms : V}
    (hw : IsUTermVec ℒₒᵣ n w)
    (hsub : IsSubstitutionBound bound free n w subBound)
    (hterms : IsSemitermVec ℒₒᵣ k n terms) :
    termValues bound free k (termSubstVec ℒₒᵣ k w terms) =
      termValues subBound free k terms := by
  have hsubst :
      IsUTermVec ℒₒᵣ k (termSubstVec ℒₒᵣ k w terms) :=
    ⟨(len_termSubstVec hterms.isUTerm).symm, fun i hi ↦ by
      rw [nth_termSubstVec hterms.isUTerm hi]
      exact hw.termSubst (hterms.nth hi)⟩
  apply nth_ext' k
    (by rw [length_termValues hsubst])
    (by rw [length_termValues hterms.isUTerm])
  intro i hi
  rw [nth_termValues hsubst hi,
    nth_termSubstVec hterms.isUTerm hi,
    nth_termValues hterms.isUTerm hi,
    termValue_termSubst_of_isSubstitutionBound hw hsub (hterms.nth hi)]

end LeanProofs.BoundedPAConsistency.TermEvaluationTransport
