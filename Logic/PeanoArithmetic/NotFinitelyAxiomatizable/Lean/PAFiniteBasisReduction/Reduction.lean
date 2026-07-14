import PAHF.PASyntax

/-!
# The finite-basis reduction for first-order Peano arithmetic

This module formalizes the compact, purely logical part of the standard proof
that first-order PA is not finitely axiomatizable.  Relative provability
`SetTheory.PA.Formula.BProv` stores the finite list of theory axioms used by a
proof. It follows that any finite axiomatization deductively equivalent to a
sentence theory can be replaced by a finite list of axioms of that theory
itself.

For PA, non-finite axiomatizability therefore reduces to strictness of all
finite PA fragments.  Establishing that strictness is the genuinely
arithmetic part of the Ryll-Nardzewski--Mostowski theorem (usually obtained
from finite-fragment reflection and Goedel's second incompleteness theorem).
It is stated here as a named proof boundary, not assumed as an axiom.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

/-- Turn a finite list of formulas into the theory consisting of its members. -/
def ListTheory (Γ : List PA.Formula) : PA.Formula → Prop :=
  fun φ => φ ∈ Γ

/-- For a finite list, theory-relative provability from no local assumptions
is exactly ordinary provability from that list.  This also makes explicit that
the Lean and Coq formulations below use the same notion. -/
theorem bprov_listTheory_iff_prov (Γ : List PA.Formula) (φ : PA.Formula) :
    PA.Formula.BProv (ListTheory Γ) [] φ ↔ PA.Formula.Prov Γ φ := by
  constructor
  · rintro ⟨L, hL, hp⟩
    apply PA.Formula.Prov_weaken (by simpa using hp) Γ
    intro x hx
    exact hL x hx
  · intro hp
    exact ⟨Γ, (fun _ hx => hx), by simpa using hp⟩

/-- Two theories are deductively equivalent when they prove the same
sentences from the empty local context. -/
def ProvablyEquivalent (B C : PA.Formula → Prop) : Prop :=
  ∀ φ, PA.Formula.Sentence φ →
    (PA.Formula.BProv B [] φ ↔ PA.Formula.BProv C [] φ)

/-- A finite axiomatization by sentences in the original PA language.  The
axioms need not themselves be members of the displayed theory. -/
def FiniteAxiomatization (B : PA.Formula → Prop) : Prop :=
  ∃ Γ : List PA.Formula,
    (∀ φ, φ ∈ Γ → PA.Formula.Sentence φ) ∧
    ProvablyEquivalent (ListTheory Γ) B

/-- A finite basis selected from the displayed theory itself. -/
def FiniteSubtheoryBasis (B : PA.Formula → Prop) : Prop :=
  ∃ Δ : List PA.Formula,
    (∀ φ, φ ∈ Δ → B φ) ∧
    ProvablyEquivalent (ListTheory Δ) B

theorem listTheory_sentences {Γ : List PA.Formula}
    (hΓ : ∀ φ, φ ∈ Γ → PA.Formula.Sentence φ) :
    PA.Formula.Sentences (ListTheory Γ) := by
  intro φ hφ
  exact hΓ φ hφ

/-- Every theorem of a finite subtheory is a theorem of the ambient theory. -/
theorem listTheory_weaker {B : PA.Formula → Prop} {Γ : List PA.Formula}
    (hΓ : ∀ φ, φ ∈ Γ → B φ) {ψ : PA.Formula}
    (hψ : PA.Formula.BProv (ListTheory Γ) [] ψ) :
    PA.Formula.BProv B [] ψ :=
  PA.Formula.BProv_theory_mono (fun φ hφ => hΓ φ hφ) hψ

/-- The compactness step at the level of derivations: finitely many formulas
provable from `B` have proofs over one shared finite list of `B`-axioms. -/
theorem bound_finite_axiomatization {B : PA.Formula → Prop}
    (Γ : List PA.Formula)
    (hΓ : ∀ φ, φ ∈ Γ → PA.Formula.BProv B [] φ) :
    ∃ Δ : List PA.Formula,
      (∀ δ, δ ∈ Δ → B δ) ∧
      ∀ γ, γ ∈ Γ → PA.Formula.BProv (ListTheory Δ) [] γ := by
  obtain ⟨Δ, hΔ, hproof⟩ := PA.Formula.BProv_bound_list B [] Γ hΓ
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ
  refine ⟨Δ, (fun δ hδ => hδ), ?_⟩
  simpa using hproof γ hγ

/-- Any finite sentence axiomatization of a sentence theory can be replaced by
a finite list of axioms drawn from the theory itself.  This is the nontrivial
logical reduction used before the arithmetic finite-fragment argument. -/
theorem finiteAxiomatization_to_finiteSubtheoryBasis
    {B : PA.Formula → Prop} (hfin : FiniteAxiomatization B) :
    FiniteSubtheoryBasis B := by
  obtain ⟨Γ, hΓsent, hΓequiv⟩ := hfin
  have hΓprov : ∀ γ, γ ∈ Γ → PA.Formula.BProv B [] γ := by
    intro γ hγ
    exact (hΓequiv γ (hΓsent γ hγ)).mp (PA.Formula.BProv_ax hγ)
  obtain ⟨Δ, hΔsub, hΔprovesΓ⟩ :=
    bound_finite_axiomatization Γ hΓprov
  refine ⟨Δ, hΔsub, ?_⟩
  intro φ hφsent
  constructor
  · exact listTheory_weaker hΔsub
  · intro hBφ
    have hΓφ : PA.Formula.BProv (ListTheory Γ) [] φ :=
      (hΓequiv φ hφsent).mpr hBφ
    exact PA.Formula.BProv_lift hΓφ
      (fun γ hγ => hΔprovesΓ γ hγ)
      (fun g hg => by cases hg)

/-- A finite subtheory basis is already a finite sentence axiomatization. -/
theorem finiteSubtheoryBasis_to_finiteAxiomatization
    {B : PA.Formula → Prop} (hB : PA.Formula.Sentences B)
    (hbasis : FiniteSubtheoryBasis B) : FiniteAxiomatization B := by
  obtain ⟨Δ, hΔsub, hΔequiv⟩ := hbasis
  exact ⟨Δ, fun φ hφ => hB φ (hΔsub φ hφ), hΔequiv⟩

/-- For every sentence theory in this finitary calculus, finite
axiomatizability is equivalent to possessing a finite basis of actual theory
axioms. -/
theorem finiteAxiomatization_iff_finiteSubtheoryBasis
    {B : PA.Formula → Prop} (hB : PA.Formula.Sentences B) :
    FiniteAxiomatization B ↔ FiniteSubtheoryBasis B := by
  exact ⟨finiteAxiomatization_to_finiteSubtheoryBasis,
    finiteSubtheoryBasis_to_finiteAxiomatization hB⟩

/-- The stronger Ryll--Nardzewski separation statement: every finite list of
PA axioms misses a further sealed induction instance.  Mostowski's proof only
needs the weaker sentence separation statement below. -/
def PAInductionFragmentStrictness : Prop :=
  ∀ Δ : List PA.Formula,
    (∀ δ, δ ∈ Δ → PA.Formula.Ax_s δ) →
    ∃ φ : PA.Formula,
      ¬PA.Formula.Prov Δ
        (PA.Formula.sealPA (PA.Formula.inductionForm φ))

/-- The exact separation statement required by the finite-basis reduction.
Unlike `PAInductionFragmentStrictness`, the missing PA theorem may be any
sentence.  In Mostowski's proof it is the canonical consistency sentence for
a fixed strong base extended by `Δ`. -/
def PAFiniteFragmentStrictness : Prop :=
  ∀ Δ : List PA.Formula,
    (∀ δ, δ ∈ Δ → PA.Formula.Ax_s δ) →
    ∃ ψ : PA.Formula,
      PA.Formula.Sentence ψ ∧
      PA.Formula.BProv PA.Formula.Ax_s [] ψ ∧
      ¬PA.Formula.Prov Δ ψ

/-- Ordinary syntactic consistency for a finite PA context. -/
def ConsistentList (Γ : List PA.Formula) : Prop :=
  ¬PA.Formula.Prov Γ PA.Formula.bot

/-- Every finite list of genuine PA axioms is consistent.  This part of the
Mostowski argument needs no arithmetization: soundness in the standard natural
number model rules out an ordinary derivation of falsity. -/
theorem paFiniteFragment_consistent (Γ : List PA.Formula)
    (hΓ : ∀ γ, γ ∈ Γ → PA.Formula.Ax_s γ) :
    ConsistentList Γ := by
  intro hbot
  have hfalse : PA.Formula.Sat PA.natModel (fun _ => 0) PA.Formula.bot :=
    PA.Formula.soundness PA.natModel hbot (fun _ => 0) (fun γ hγ =>
      PA.Formula.sat_axiom_s PA.natModel (fun _ => 0) γ (hΓ γ hγ))
  exact hfalse

/-- Ryll--Nardzewski's stronger induction-instance theorem implies the exact
sentence separation statement used by the finite-basis argument. -/
theorem finiteFragmentStrictness_of_inductionFragmentStrictness
    (hstrict : PAInductionFragmentStrictness) :
    PAFiniteFragmentStrictness := by
  intro Δ hΔ
  obtain ⟨φ, hnot⟩ := hstrict Δ hΔ
  exact ⟨PA.Formula.sealPA (PA.Formula.inductionForm φ),
    PA.Formula.sealPA_sentence _,
    PA.Formula.BProv_ax (PA.Formula.Ax_s_induction φ), hnot⟩

/-- The small but subtle fixed-base step in Mostowski's proof.

`Base` is a finite PA fragment strong enough for the chosen formalization of
Goedel's second incompleteness theorem, and `con T` is the *same* canonical
consistency sentence in the reflection and incompleteness hypotheses.  For an
arbitrary finite PA fragment `Δ`, use `T = Base ++ Δ`.  If `Δ` proved
`con T`, weakening would make `T` prove its own consistency, contradicting the
last hypothesis.

The two hard, intentionally explicit inputs are finite-fragment reflection
(`hreflect`) and an instantiated second incompleteness theorem (`hg2`). -/
theorem finiteFragmentStrictness_of_mostowski
    (Base : List PA.Formula)
    (con : List PA.Formula → PA.Formula)
    (hBase : ∀ β, β ∈ Base → PA.Formula.Ax_s β)
    (hconSentence : ∀ T, PA.Formula.Sentence (con T))
    (hreflect : ∀ T,
      (∀ θ, θ ∈ T → PA.Formula.Ax_s θ) →
      PA.Formula.BProv PA.Formula.Ax_s [] (con T))
    (hg2 : ∀ T,
      (∀ θ, θ ∈ T → PA.Formula.Sentence θ) →
      (∀ β, β ∈ Base → β ∈ T) →
      ConsistentList T →
      ¬PA.Formula.Prov T (con T)) :
    PAFiniteFragmentStrictness := by
  intro Δ hΔ
  let T := Base ++ Δ
  have hTpa : ∀ θ, θ ∈ T → PA.Formula.Ax_s θ := by
    intro θ hθ
    rcases List.mem_append.mp hθ with hθ | hθ
    · exact hBase θ hθ
    · exact hΔ θ hθ
  have hTsent : ∀ θ, θ ∈ T → PA.Formula.Sentence θ := by
    intro θ hθ
    exact PA.Formula.Ax_s_sentences θ (hTpa θ hθ)
  have hBaseT : ∀ β, β ∈ Base → β ∈ T := by
    intro β hβ
    exact List.mem_append.mpr (Or.inl hβ)
  have hnotT : ¬PA.Formula.Prov T (con T) :=
    hg2 T hTsent hBaseT (paFiniteFragment_consistent T hTpa)
  refine ⟨con T, hconSentence T, hreflect T hTpa, ?_⟩
  intro hΔcon
  apply hnotT
  exact PA.Formula.Prov_weaken hΔcon T (fun θ hθ =>
    List.mem_append.mpr (Or.inr hθ))

/-- Exact finite-fragment sentence separation rules out a finite basis of
actual PA axioms. -/
theorem no_finiteSubtheoryBasis_of_finiteFragmentStrictness
    (hstrict : PAFiniteFragmentStrictness) :
    ¬FiniteSubtheoryBasis PA.Formula.Ax_s := by
  rintro ⟨Δ, hΔsub, hΔequiv⟩
  obtain ⟨ψ, hψsent, hPAψ, hnot⟩ := hstrict Δ hΔsub
  apply hnot
  apply (bprov_listTheory_iff_prov Δ ψ).mp
  exact (hΔequiv ψ hψsent).mpr hPAψ

/-- Exactness of the arithmetic proof boundary.  Classically, sentence
separation for every finite PA fragment is not just sufficient to rule out a
finite basis: it is equivalent to that conclusion.  The reverse direction
extracts a missing sentence from the failure of the displayed finite fragment
to be a basis. -/
theorem finiteFragmentStrictness_iff_no_finiteSubtheoryBasis :
    PAFiniteFragmentStrictness ↔
      ¬FiniteSubtheoryBasis PA.Formula.Ax_s := by
  constructor
  · exact no_finiteSubtheoryBasis_of_finiteFragmentStrictness
  · intro hnobasis Δ hΔ
    classical
    by_cases hmissing : ∃ ψ : PA.Formula,
        PA.Formula.Sentence ψ ∧
        PA.Formula.BProv PA.Formula.Ax_s [] ψ ∧
        ¬PA.Formula.Prov Δ ψ
    · exact hmissing
    · exfalso
      apply hnobasis
      refine ⟨Δ, hΔ, ?_⟩
      intro ψ hψsent
      constructor
      · exact listTheory_weaker hΔ
      · intro hPAψ
        apply (bprov_listTheory_iff_prov Δ ψ).mpr
        by_cases hprov : PA.Formula.Prov Δ ψ
        · exact hprov
        · exact (hmissing ⟨ψ, hψsent, hPAψ, hprov⟩).elim

/-- Finite-fragment strictness rules out a finite basis of actual PA axioms. -/
theorem no_finiteSubtheoryBasis_of_strict_fragments
    (hstrict : PAInductionFragmentStrictness) :
    ¬FiniteSubtheoryBasis PA.Formula.Ax_s := by
  exact no_finiteSubtheoryBasis_of_finiteFragmentStrictness
    (finiteFragmentStrictness_of_inductionFragmentStrictness hstrict)

/-- Mostowski's exact final reduction: arbitrary sentence separation, rather
than the stronger induction-instance conclusion, suffices. -/
theorem pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
    (hstrict : PAFiniteFragmentStrictness) :
    ¬FiniteAxiomatization PA.Formula.Ax_s := by
  intro hfin
  have hbasis : FiniteSubtheoryBasis PA.Formula.Ax_s :=
    (finiteAxiomatization_iff_finiteSubtheoryBasis
      PA.Formula.Ax_s_sentences).mp hfin
  exact no_finiteSubtheoryBasis_of_finiteFragmentStrictness hstrict hbasis

/-- The exact arithmetic separation statement is classically equivalent to
the advertised non-finite-axiomatizability theorem.  Thus all purely logical
compactness and finite-support bookkeeping has been discharged on both sides
of the boundary. -/
theorem pa_not_finitely_axiomatizable_iff_finiteFragmentStrictness :
    (¬FiniteAxiomatization PA.Formula.Ax_s) ↔
      PAFiniteFragmentStrictness := by
  constructor
  · intro hnotfinite
    apply finiteFragmentStrictness_iff_no_finiteSubtheoryBasis.mpr
    intro hbasis
    exact hnotfinite
      (finiteSubtheoryBasis_to_finiteAxiomatization
        PA.Formula.Ax_s_sentences hbasis)
  · exact pa_not_finitely_axiomatizable_of_finiteFragmentStrictness

/-- The standard final reduction: the Ryll-Nardzewski--Mostowski
finite-fragment theorem implies that first-order PA has no finite sentence
axiomatization in its original language. -/
theorem pa_not_finitely_axiomatizable_of_strict_fragments
    (hstrict : PAInductionFragmentStrictness) :
    ¬FiniteAxiomatization PA.Formula.Ax_s := by
  exact pa_not_finitely_axiomatizable_of_finiteFragmentStrictness
    (finiteFragmentStrictness_of_inductionFragmentStrictness hstrict)

end PAFiniteBasisReduction
end LeanProofs
