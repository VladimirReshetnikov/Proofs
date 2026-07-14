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

/-- The exact arithmetic separation statement still needed after the logical
finite-basis reduction: every finite list of PA axioms misses a further sealed
induction instance. -/
def PAInductionFragmentStrictness : Prop :=
  ∀ Δ : List PA.Formula,
    (∀ δ, δ ∈ Δ → PA.Formula.Ax_s δ) →
    ∃ φ : PA.Formula,
      ¬PA.Formula.Prov Δ
        (PA.Formula.sealPA (PA.Formula.inductionForm φ))

/-- Finite-fragment strictness rules out a finite basis of actual PA axioms. -/
theorem no_finiteSubtheoryBasis_of_strict_fragments
    (hstrict : PAInductionFragmentStrictness) :
    ¬FiniteSubtheoryBasis PA.Formula.Ax_s := by
  rintro ⟨Δ, hΔsub, hΔequiv⟩
  obtain ⟨φ, hnot⟩ := hstrict Δ hΔsub
  apply hnot
  apply (bprov_listTheory_iff_prov Δ _).mp
  apply (hΔequiv _ (PA.Formula.sealPA_sentence _)).mpr
  exact PA.Formula.BProv_ax (PA.Formula.Ax_s_induction φ)

/-- The standard final reduction: the Ryll-Nardzewski--Mostowski
finite-fragment theorem implies that first-order PA has no finite sentence
axiomatization in its original language. -/
theorem pa_not_finitely_axiomatizable_of_strict_fragments
    (hstrict : PAInductionFragmentStrictness) :
    ¬FiniteAxiomatization PA.Formula.Ax_s := by
  intro hfin
  have hbasis : FiniteSubtheoryBasis PA.Formula.Ax_s :=
    (finiteAxiomatization_iff_finiteSubtheoryBasis
      PA.Formula.Ax_s_sentences).mp hfin
  exact no_finiteSubtheoryBasis_of_strict_fragments hstrict hbasis

end PAFiniteBasisReduction
end LeanProofs
