import PAFiniteBasisReduction.Reduction

/-!
# A canonical hierarchy of finite-rank PA fragments

Every finite list of sealed PA axioms is dominated by one canonical fragment:
the six non-induction axioms together with all induction instances whose
source formula has structural rank at most `n`.  Rank counts term structure,
variable indices, logical connectives, and quantifiers.  In particular, each
constructor strictly raises rank and rank-bounded syntax is genuinely finite,
although the reduction below only needs domination of finite lists.

The arithmetic theorem still to be supplied is `PARankFragmentStrictness`:
each canonical rank fragment misses a sealed induction instance.  This module
checks that this single cofinal hierarchy formulation implies the arbitrary
finite-fragment strictness statements and hence the existing conditional
non-finite-axiomatizability headline.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

/-- Structural rank of an arithmetic term.  Including the variable index
makes every rank-bounded collection of terms finite. -/
def termRank : PA.Term → Nat
  | .var n => n + 1
  | .zero => 1
  | .succ t => termRank t + 1
  | .add a b => Nat.max (termRank a) (termRank b) + 1
  | .mul a b => Nat.max (termRank a) (termRank b) + 1

/-- Structural rank of an arithmetic formula.  Atomic rank also sees the
structure of both terms, and every logical constructor raises rank. -/
def formulaRank : PA.Formula → Nat
  | .eq a b => Nat.max (termRank a) (termRank b) + 1
  | .bot => 1
  | .imp a b => Nat.max (formulaRank a) (formulaRank b) + 1
  | .and a b => Nat.max (formulaRank a) (formulaRank b) + 1
  | .or a b => Nat.max (formulaRank a) (formulaRank b) + 1
  | .all a => formulaRank a + 1
  | .ex a => formulaRank a + 1

/-- The canonical PA fragment of rank `n`: all six sealed non-induction
axioms, and exactly the sealed induction instances whose source formula has
rank at most `n`. -/
def PARankFragment (n : Nat) (f : PA.Formula) : Prop :=
  f = PA.Formula.sealPA PA.Formula.succInj ∨
  f = PA.Formula.sealPA PA.Formula.zeroNotSucc ∨
  f = PA.Formula.sealPA PA.Formula.addZero ∨
  f = PA.Formula.sealPA PA.Formula.addSucc ∨
  f = PA.Formula.sealPA PA.Formula.mulZero ∨
  f = PA.Formula.sealPA PA.Formula.mulSucc ∨
  ∃ phi, formulaRank phi ≤ n ∧
    f = PA.Formula.sealPA (PA.Formula.inductionForm phi)

theorem paRankFragment_succInj (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.succInj) :=
  Or.inl rfl

theorem paRankFragment_zeroNotSucc (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.zeroNotSucc) :=
  Or.inr (Or.inl rfl)

theorem paRankFragment_addZero (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.addZero) :=
  Or.inr (Or.inr (Or.inl rfl))

theorem paRankFragment_addSucc (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.addSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem paRankFragment_mulZero (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.mulZero) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem paRankFragment_mulSucc (n : Nat) :
    PARankFragment n (PA.Formula.sealPA PA.Formula.mulSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem paRankFragment_induction {n : Nat} {phi : PA.Formula}
    (hphi : formulaRank phi ≤ n) :
    PARankFragment n
      (PA.Formula.sealPA (PA.Formula.inductionForm phi)) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨phi, hphi, rfl⟩)))))

/-- Every canonical rank fragment consists of genuine sealed PA axioms. -/
theorem paRankFragment_subset_ax_s {n : Nat} {f : PA.Formula}
    (hf : PARankFragment n f) : PA.Formula.Ax_s f := by
  rcases hf with h | h | h | h | h | h | ⟨phi, _, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨phi, h⟩)))))

/-- Canonical rank fragments are sentence theories. -/
theorem paRankFragment_sentences (n : Nat) :
    PA.Formula.Sentences (PARankFragment n) := by
  intro f hf
  exact PA.Formula.Ax_s_sentences f (paRankFragment_subset_ax_s hf)

/-- The canonical fragments increase with their rank bound. -/
theorem paRankFragment_mono {m n : Nat} (hmn : m ≤ n)
    {f : PA.Formula} (hf : PARankFragment m f) :
    PARankFragment n f := by
  rcases hf with h | h | h | h | h | h | ⟨phi, hphi, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨phi, Nat.le_trans hphi hmn, h⟩)))))

/-- Every genuine sealed PA axiom belongs to some canonical rank fragment. -/
theorem paAxiom_mem_some_rankFragment {f : PA.Formula}
    (hf : PA.Formula.Ax_s f) :
    ∃ n, PARankFragment n f := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩
  · exact ⟨0, paRankFragment_succInj 0⟩
  · exact ⟨0, paRankFragment_zeroNotSucc 0⟩
  · exact ⟨0, paRankFragment_addZero 0⟩
  · exact ⟨0, paRankFragment_addSucc 0⟩
  · exact ⟨0, paRankFragment_mulZero 0⟩
  · exact ⟨0, paRankFragment_mulSucc 0⟩
  · exact ⟨formulaRank phi, paRankFragment_induction (Nat.le_refl _)⟩

/-- Every finite list of genuine PA axioms is contained in one canonical
rank fragment.  This is the cofinality fact that replaces quantification over
arbitrary finite lists by quantification over the natural-number hierarchy. -/
theorem finitePAFragment_bounded_by_rank (Delta : List PA.Formula)
    (hDelta : ∀ delta, delta ∈ Delta → PA.Formula.Ax_s delta) :
    ∃ n, ∀ delta, delta ∈ Delta → PARankFragment n delta := by
  induction Delta with
  | nil =>
      exact ⟨0, by simp⟩
  | cons delta Delta ih =>
      obtain ⟨m, hm⟩ := paAxiom_mem_some_rankFragment
        (hDelta delta (by simp))
      obtain ⟨n, hn⟩ := ih (by
        intro gamma hgamma
        exact hDelta gamma (by simp [hgamma]))
      refine ⟨Nat.max m n, ?_⟩
      intro gamma hgamma
      rcases List.mem_cons.mp hgamma with rfl | hgamma
      · exact paRankFragment_mono (Nat.le_max_left m n) hm
      · exact paRankFragment_mono (Nat.le_max_right m n) (hn gamma hgamma)

/-- Arithmetic strictness restricted to the canonical cofinal hierarchy:
each rank fragment misses a further sealed induction instance. -/
def PARankFragmentStrictness : Prop :=
  ∀ n : Nat,
    ∃ phi : PA.Formula,
      ¬PA.Formula.BProv (PARankFragment n) []
        (PA.Formula.sealPA (PA.Formula.inductionForm phi))

/-- The weaker canonical-hierarchy separation statement: each rank fragment
misses some sentence theorem of PA. -/
def PARankFragmentSentenceStrictness : Prop :=
  ∀ n : Nat,
    ∃ psi : PA.Formula,
      PA.Formula.Sentence psi ∧
      PA.Formula.BProv PA.Formula.Ax_s [] psi ∧
      ¬PA.Formula.BProv (PARankFragment n) [] psi

/-- A raw arithmetic countermodel refutes relative derivability.  `M` is only
a `PA.PreModel`: it supplies interpretations of `0`, successor, addition, and
multiplication, but assumes neither the six PA laws nor induction. -/
theorem not_bprov_of_preModel_counterexample
    {alpha : Type u} (M : PA.PreModel alpha)
    {B : PA.Formula → Prop} {psi : PA.Formula} (e : Nat → alpha)
    (hB : ∀ b, B b → PA.Formula.Sat M e b)
    (hpsi : ¬PA.Formula.Sat M e psi) :
    ¬PA.Formula.BProv B [] psi := by
  intro hprov
  apply hpsi
  exact PA.Formula.soundness_BProv M hprov e hB (by
    intro g hg
    cases hg)

/-- Semantic countermodels for the canonical hierarchy.  At each rank, a raw
arithmetic structure satisfies the entire rank fragment at one valuation but
falsifies a genuine sealed PA axiom there.  All displayed fragment axioms and
the falsified PA axiom are sentences, so choosing one valuation loses no
first-order content while keeping this interface minimal. -/
def PARankFragmentCountermodels : Prop :=
  ∀ n : Nat,
    ∃ (alpha : Type u) (M : PA.PreModel alpha) (e : Nat → alpha)
      (psi : PA.Formula),
      (∀ f, PARankFragment n f → PA.Formula.Sat M e f) ∧
      PA.Formula.Ax_s psi ∧
      ¬PA.Formula.Sat M e psi

/-- Raw countermodels yield canonical rank-fragment sentence separation by
the soundness theorem for the first-order proof calculus. -/
theorem rankFragmentSentenceStrictness_of_countermodels
    (hmodels : PARankFragmentCountermodels.{u}) :
    PARankFragmentSentenceStrictness := by
  intro n
  obtain ⟨alpha, M, e, psi, hfragment, hax, hfalse⟩ := hmodels n
  exact ⟨psi, PA.Formula.Ax_s_sentences psi hax,
    PA.Formula.BProv_ax hax,
    not_bprov_of_preModel_counterexample M e hfragment hfalse⟩

/-- The stronger missed-induction formulation entails sentence separation
for the canonical hierarchy. -/
theorem rankFragmentSentenceStrictness_of_rankFragmentStrictness
    (hstrict : PARankFragmentStrictness) :
    PARankFragmentSentenceStrictness := by
  intro n
  obtain ⟨phi, hnot⟩ := hstrict n
  exact ⟨PA.Formula.sealPA (PA.Formula.inductionForm phi),
    PA.Formula.sealPA_sentence _,
    PA.Formula.BProv_ax (PA.Formula.Ax_s_induction phi), hnot⟩

/-- Strictness of the canonical rank hierarchy implies strictness of every
finite list of genuine PA axioms. -/
theorem inductionFragmentStrictness_of_rankFragmentStrictness
    (hstrict : PARankFragmentStrictness) :
    PAInductionFragmentStrictness := by
  intro Delta hDelta
  obtain ⟨n, hbound⟩ := finitePAFragment_bounded_by_rank Delta hDelta
  obtain ⟨phi, hnot⟩ := hstrict n
  refine ⟨phi, ?_⟩
  intro hprov
  apply hnot
  exact ⟨Delta, hbound, by simpa using hprov⟩

/-- Canonical-rank strictness supplies the exact arbitrary-sentence
separation premise used by the finite-basis reduction. -/
theorem finiteFragmentStrictness_of_rankFragmentStrictness
    (hstrict : PARankFragmentStrictness) :
    PAFiniteFragmentStrictness :=
  finiteFragmentStrictness_of_inductionFragmentStrictness
    (inductionFragmentStrictness_of_rankFragmentStrictness hstrict)

/-- Sentence separation on the cofinal rank hierarchy implies sentence
separation for every finite list of genuine PA axioms. -/
theorem finiteFragmentStrictness_of_rankFragmentSentenceStrictness
    (hstrict : PARankFragmentSentenceStrictness) :
    PAFiniteFragmentStrictness := by
  intro Delta hDelta
  obtain ⟨n, hbound⟩ := finitePAFragment_bounded_by_rank Delta hDelta
  obtain ⟨psi, hsentence, hPA, hnot⟩ := hstrict n
  refine ⟨psi, hsentence, hPA, ?_⟩
  intro hprov
  apply hnot
  exact ⟨Delta, hbound, by simpa using hprov⟩

/-- Raw countermodels of all canonical rank fragments supply the exact
finite-fragment strictness premise used by the finite-basis reduction. -/
theorem finiteFragmentStrictness_of_rankFragmentCountermodels
    (hmodels : PARankFragmentCountermodels.{u}) :
    PAFiniteFragmentStrictness :=
  finiteFragmentStrictness_of_rankFragmentSentenceStrictness
    (rankFragmentSentenceStrictness_of_countermodels hmodels)

/-- Canonical-rank strictness rules out every finite sentence axiomatization
of first-order PA in its original language. -/
theorem pa_not_finitely_axiomatizable_of_rankFragmentStrictness
    (hstrict : PARankFragmentStrictness) :
    ¬FiniteAxiomatization PA.Formula.Ax_s :=
  pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
    (finiteFragmentStrictness_of_rankFragmentStrictness hstrict)

/-- Semantic hierarchy route to the headline: raw countermodels for all
canonical rank fragments rule out a finite sentence axiomatization of PA. -/
theorem pa_not_finitely_axiomatizable_of_rankFragmentCountermodels
    (hmodels : PARankFragmentCountermodels.{u}) :
    ¬FiniteAxiomatization PA.Formula.Ax_s :=
  pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
    (finiteFragmentStrictness_of_rankFragmentCountermodels hmodels)

end PAFiniteBasisReduction
end LeanProofs
