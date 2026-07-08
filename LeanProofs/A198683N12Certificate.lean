import LeanProofs.A198683N12Symbolic
import LeanProofs.A198683N12OverflowWitness

/-!
# The `A198683(12)` endgame: what is proved, what remains, and what pins the value

This module is the single entry point for the formal status of the disputed
value `A198683(12)`.  It packages the entire remaining uncertainty into

1. one **wide** hypothesis — the partition witness `N12PartitionWitness`, the
   mechanically-checkable-in-principle certificate that the interval-arithmetic
   pipeline of the research corpus is designed to produce — and
2. two **narrow** hypotheses — `NearOneSplit` and `OverflowIsolated` — each a
   single concrete separation question about explicit closed-form complex
   numbers,

and proves the complete decision tree relating them to `a198683 12`:

* `a198683_twelve_mem`: given only the wide witness,
  `a198683 12 ∈ {2924, 2925, 2926}` — **no** further hypotheses; the two
  narrow questions are absorbed by excluded middle.
* Each narrow hypothesis (or its negation) removes one branch, and any
  combination pins the exact value; in particular
  `a198683_twelve_eq_2926 : witness → NearOneSplit → OverflowIsolated →
  a198683 12 = 2926`.

## The mathematical situation (waves 1–4 of the research corpus)

`a198683 n` counts the distinct values of all binary parenthesizations of
`i^i^…^i` (`n` copies, principal powers throughout).  At `n = 12` the shared
recurrence produces `5139` candidate values, and every historical disagreement
(`2919`–`2927`) is a deduplication disagreement about those candidates
(see `src/Lean/Oeis/A198683/reports/wave-3/a198683-post-wave2-synthesis.md`).
The probe-refined partition of the retained table has `2926` classes
(`LeanProofs.A198683N12Probe` certifies the table bookkeeping), and its
residual uncertainty is *structural*, concentrated in exactly two places:

* **the near-`1` split** — whether representative `25` is genuinely distinct
  from the (provably equal) pair `{1404, 4239}`; and
* **the overflow singleton `57`** — whose exponent has imaginary part of
  magnitude `≈ 10^41232`, beyond mod-`2π` reduction at any finite precision.

Everything else in the partition is multi-precision-stable and, where it has
been attacked symbolically, provable: `LeanProofs.A198683N12Symbolic` proves
the fourteen near-`i^i` representatives all equal `i^i` exactly, the near-zero
pair `{2207, 3777}` equal exactly, and the near-one pair `{1404, 4239}` equal
exactly.  Those proved identities discharge the corresponding *cover*
obligations of a future `N12PartitionWitness`.

## The two narrow hypotheses

* `NearOneSplit : nearOne25 ≠ nearOne1404`.  An inequality between two
  explicit twelve-atom principal-power towers whose values agree to about
  `10^-1305`.  It is **not** an article of faith: the Symbolic module reduces
  it (through a fully proved ten-layer interval ladder) to the twenty-eight
  scalar endpoint estimates bundled here as `NearOneEndpointBounds` — each a
  rational bound on `Real.sin`/`Real.cos`/`Real.exp` at one explicit rational
  argument, each dischargeable by Taylor partial sums.  The companion
  Rocq/Coq development (`CoqProofs/A198683N12Bounds.v`) certifies the same
  boxes by interval arithmetic, so the numbers are known to be right; what
  remains here is Lean-side endpoint plumbing, not mathematical doubt.

* `OverflowIsolated w`: the value of the overflow candidate `57` — the
  explicit tower `overflowCandidate12`, whose membership in the `n = 12`
  value set is proved (`overflowCandidate12_mem`) — differs from the value of
  every other partition class.  This is the formal **no-miracles
  hypothesis**: its failure would mean that a principal-power tower whose
  exponent has imaginary part of magnitude `≈ 10^41232` lands *exactly* on
  one of the other `2925` class values — the kind of accidental
  transcendental coincidence (a power tower in `e` and `π` turning out to
  take an exact prescribed value) that the corpus's "no-miracles principle"
  rejects but that no finite computation has yet excluded.
  `LeanProofs.A198683N12Magnitude` and `LeanProofs.A198683N12OverflowWitness`
  already prove the log-modulus separation criteria (`exp_ne_of_re_lt`,
  `overflowCandidate12_ne_principalPow_of_im_gt_of_re_gt`) that reduce each
  individual inequality in `OverflowIsolated` to a real-part bound, so this
  hypothesis too is expected to be *provable* — for a concrete witness — once
  coarse magnitude bounds for the other class representatives are certified;
  no phase (mod-`2π`) information is required on that route.

## The decision tree

With `w : N12PartitionWitness` (writing `S` for `NearOneSplit` and `O` for
`OverflowIsolated w`):

| `S`?  | `O`?  | conclusion | theorem |
|-------|-------|------------|---------|
| —     | —     | `a198683 12 ∈ {2924, 2925, 2926}` | `a198683_twelve_mem` |
| yes   | —     | `a198683 12 ∈ {2925, 2926}` | `a198683_twelve_mem_of_nearOneSplit` |
| —     | yes   | `a198683 12 ∈ {2925, 2926}` | `a198683_twelve_mem_of_overflowIsolated` |
| yes   | yes   | `a198683 12 = 2926` | `a198683_twelve_eq_2926` |
| yes   | no    | `a198683 12 = 2925` | `a198683_twelve_eq_2925_of_overflowCollision` |
| no    | yes   | `a198683 12 = 2925` | `a198683_twelve_eq_2925_of_nearOneMerge` |
| no    | no    | `a198683 12 = 2924` | `a198683_twelve_eq_2924` |

The community-expected value is `2926` (the Wolfram computation and the
probe-refined partition agree); the table shows exactly which two facts that
expectation rests on.
-/

namespace LeanProofs

namespace A198683N12Certificate

open A198683N12Symbolic (nearOne25 nearOne1404)
open A198683N12OverflowWitness (overflowCandidate12)

/--
The **wide certificate**: a claimed system of `2926` class representatives for
the `n = 12` principal-power values, with

* `reps_mem`/`covers` — every representative is a genuine lexical
  parenthesization of twelve `i`s, and every parenthesization takes the same
  value as some representative (this is where all *within-class equalities* of
  the probe-refined partition live, including the identities already proved in
  `A198683N12Symbolic`);
* `separated` — representatives of distinct classes take distinct values,
  **except** that nothing is claimed about the two structurally uncertain
  comparisons: any pair involving the overflow class, and the pair
  `{idxNearOne25, idxNearOne1404}`;
* the three distinguished indices are pinned to the concrete closed forms
  studied by the Symbolic/OverflowWitness modules, so that the narrow
  hypotheses of this module are statements about explicit complex numbers.

This is the object the certified-arithmetic pipeline of
`Oeis/A198683/reports/wave-3/a198683-numerics-interval-feasibility.md` is
designed to produce; nothing below depends on *which* witness is supplied.
-/
structure N12PartitionWitness where
  /-- One lexical representative expression per claimed class. -/
  reps : Fin 2926 → IPowExpr
  /-- Every representative is a parenthesization of twelve `i`s. -/
  reps_mem : ∀ k, reps k ∈ IPowExpr.parenthesizations 12
  /-- Every parenthesization of twelve `i`s takes the value of some
  representative. -/
  covers : ∀ e ∈ IPowExpr.parenthesizations 12,
    ∃ k, IPowExpr.eval e = IPowExpr.eval (reps k)
  /-- The class of the near-`1` representative `25`. -/
  idxNearOne25 : Fin 2926
  /-- The class of the near-`1` representatives `{1404, 4239}`. -/
  idxNearOne1404 : Fin 2926
  /-- The overflow class `{57}`. -/
  idxOverflow : Fin 2926
  idxNearOne25_ne_idxNearOne1404 : idxNearOne25 ≠ idxNearOne1404
  idxNearOne25_ne_idxOverflow : idxNearOne25 ≠ idxOverflow
  idxNearOne1404_ne_idxOverflow : idxNearOne1404 ≠ idxOverflow
  /-- The `25` class representative evaluates to the concrete tower
  `A198683N12Symbolic.nearOne25`. -/
  eval_idxNearOne25 : IPowExpr.eval (reps idxNearOne25) = nearOne25
  /-- The `{1404, 4239}` class representative evaluates to the concrete tower
  `A198683N12Symbolic.nearOne1404`. -/
  eval_idxNearOne1404 : IPowExpr.eval (reps idxNearOne1404) = nearOne1404
  /-- The overflow class representative evaluates to the concrete tower
  `A198683N12OverflowWitness.overflowCandidate12`. -/
  eval_idxOverflow : IPowExpr.eval (reps idxOverflow) = overflowCandidate12
  /-- Cross-class separation, claimed for every pair **except** the two
  structurally uncertain comparisons. -/
  separated : ∀ j k : Fin 2926, j ≠ k →
    j ≠ idxOverflow → k ≠ idxOverflow →
    ¬(j = idxNearOne25 ∧ k = idxNearOne1404) →
    ¬(j = idxNearOne1404 ∧ k = idxNearOne25) →
    IPowExpr.eval (reps j) ≠ IPowExpr.eval (reps k)

/--
**Narrow hypothesis 1 (the near-`1` split).**  Representative `25` differs
from representatives `{1404, 4239}`.  Reduced by
`A198683N12Symbolic.nearOne25_ne_nearOne1404_of_endpoint_bounds` to the
twenty-eight scalar endpoint estimates in `NearOneEndpointBounds`
(see `nearOneSplit_of_endpointBounds` below).  Its *negation* would mean the
two towers agree exactly despite differing only at the `10^-1305` scale.
-/
def NearOneSplit : Prop := nearOne25 ≠ nearOne1404

/--
**Narrow hypothesis 2 (no miracles for the overflow class).**  The value of
the overflow candidate `57` differs from the value of every other class of
the witness.  See the module docstring: this is the formal no-miracles
hypothesis, and the proved log-modulus criteria reduce each instance to a
real-part bound, avoiding any astronomical mod-`2π` reduction.
-/
def OverflowIsolated (w : N12PartitionWitness) : Prop :=
  ∀ k, k ≠ w.idxOverflow →
    IPowExpr.eval (w.reps k) ≠ overflowCandidate12

namespace N12PartitionWitness

variable (w : N12PartitionWitness)

/-- The class-value map induced by the witness. -/
noncomputable def value (k : Fin 2926) : ℂ :=
  IPowExpr.eval (w.reps k)

theorem value_idxNearOne25 : w.value w.idxNearOne25 = nearOne25 :=
  w.eval_idxNearOne25

theorem value_idxNearOne1404 : w.value w.idxNearOne1404 = nearOne1404 :=
  w.eval_idxNearOne1404

theorem value_idxOverflow : w.value w.idxOverflow = overflowCandidate12 :=
  w.eval_idxOverflow

private theorem idxOverflow_ne_idxNearOne25' :
    w.idxOverflow ≠ w.idxNearOne25 :=
  Ne.symm w.idxNearOne25_ne_idxOverflow

/-- The lexical value set at `n = 12` is exactly the set of class values. -/
theorem lexicalValueSet_eq :
    a198683LexicalValueSet 12 = w.value '' Set.univ := by
  ext z
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨k, hk⟩ := w.covers e he
    exact ⟨k, trivial, hk.symm⟩
  · rintro ⟨k, -, rfl⟩
    exact ⟨w.reps k, w.reps_mem k, rfl⟩

/-- `a198683 12` is the number of distinct class values of any witness. -/
theorem a198683_twelve_eq_ncard :
    a198683 12 = (w.value '' Set.univ).ncard := by
  rw [a198683_eq_canonicalValueSet_ncard,
    ← a198683LexicalValueSet_eq_canonicalValueSet, w.lexicalValueSet_eq]

/-! ### Upper bounds

Each duplicated value lets the image be computed from one fewer index.
-/

include w in
theorem a198683_twelve_le : a198683 12 ≤ 2926 := by
  rw [w.a198683_twelve_eq_ncard]
  calc (w.value '' Set.univ).ncard
      ≤ (Set.univ : Set (Fin 2926)).ncard := Set.ncard_image_le Set.finite_univ
    _ = 2926 := by simp [Set.ncard_univ]

private theorem image_univ_subset_diff {s : Set (Fin 2926)}
    (h : ∀ i ∈ s, ∃ j, j ∉ s ∧ w.value i = w.value j) :
    w.value '' Set.univ ⊆ w.value '' (Set.univ \ s) := by
  rintro z ⟨k, -, rfl⟩
  by_cases hk : k ∈ s
  · obtain ⟨j, hj, hval⟩ := h k hk
    exact ⟨j, ⟨trivial, hj⟩, hval.symm⟩
  · exact ⟨k, ⟨trivial, hk⟩, rfl⟩

private theorem ncard_le_of_dup {s : Set (Fin 2926)}
    (h : ∀ i ∈ s, ∃ j, j ∉ s ∧ w.value i = w.value j) :
    a198683 12 ≤ 2926 - s.ncard := by
  rw [w.a198683_twelve_eq_ncard]
  calc (w.value '' Set.univ).ncard
      ≤ (w.value '' (Set.univ \ s)).ncard :=
        Set.ncard_le_ncard (w.image_univ_subset_diff h) ((Set.toFinite _).image _)
    _ ≤ (Set.univ \ s : Set (Fin 2926)).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ = 2926 - s.ncard := by
        rw [Set.ncard_sdiff (Set.subset_univ s)]
        simp [Set.ncard_univ]

include w in
theorem a198683_twelve_le_of_nearOneMerge (h : nearOne25 = nearOne1404) :
    a198683 12 ≤ 2925 := by
  have hdup : ∀ i ∈ ({w.idxNearOne25} : Set (Fin 2926)),
      ∃ j, j ∉ ({w.idxNearOne25} : Set (Fin 2926)) ∧ w.value i = w.value j := by
    rintro i rfl
    refine ⟨w.idxNearOne1404, ?_, ?_⟩
    · simpa using Ne.symm w.idxNearOne25_ne_idxNearOne1404
    · rw [w.value_idxNearOne25, w.value_idxNearOne1404, h]
  have hcard := w.ncard_le_of_dup hdup
  rw [Set.ncard_singleton] at hcard
  omega

theorem a198683_twelve_le_of_overflowCollision (h : ¬OverflowIsolated w) :
    a198683 12 ≤ 2925 := by
  simp only [OverflowIsolated] at h
  push_neg at h
  obtain ⟨k, hk, hval⟩ := h
  have hdup : ∀ i ∈ ({w.idxOverflow} : Set (Fin 2926)),
      ∃ j, j ∉ ({w.idxOverflow} : Set (Fin 2926)) ∧ w.value i = w.value j := by
    rintro i rfl
    refine ⟨k, by simpa using hk, ?_⟩
    rw [w.value_idxOverflow]
    exact hval.symm
  have hcard := w.ncard_le_of_dup hdup
  rw [Set.ncard_singleton] at hcard
  omega

theorem a198683_twelve_le_of_nearOneMerge_of_overflowCollision
    (h1 : nearOne25 = nearOne1404) (h2 : ¬OverflowIsolated w) :
    a198683 12 ≤ 2924 := by
  simp only [OverflowIsolated] at h2
  push_neg at h2
  obtain ⟨k, hk, hval⟩ := h2
  have hdup : ∀ i ∈ ({w.idxNearOne25, w.idxOverflow} : Set (Fin 2926)),
      ∃ j, j ∉ ({w.idxNearOne25, w.idxOverflow} : Set (Fin 2926)) ∧
        w.value i = w.value j := by
    rintro i (rfl | rfl)
    · -- the near-one class re-routes through `idxNearOne1404`
      refine ⟨w.idxNearOne1404, ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm w.idxNearOne25_ne_idxNearOne1404,
          w.idxNearOne1404_ne_idxOverflow⟩
      · rw [w.value_idxNearOne25, w.value_idxNearOne1404, h1]
    · -- the overflow class re-routes through its collision partner, unless
      -- that partner is the near-one class, in which case it re-routes all
      -- the way to `idxNearOne1404`
      by_cases hk25 : k = w.idxNearOne25
      · refine ⟨w.idxNearOne1404, ?_, ?_⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm w.idxNearOne25_ne_idxNearOne1404,
            w.idxNearOne1404_ne_idxOverflow⟩
        · have h25 : w.value w.idxNearOne25 = w.value w.idxNearOne1404 := by
            rw [w.value_idxNearOne25, w.value_idxNearOne1404, h1]
          calc w.value w.idxOverflow
              = w.value k := by rw [w.value_idxOverflow]; exact hval.symm
            _ = w.value w.idxNearOne1404 := by rw [hk25]; exact h25
      · refine ⟨k, ?_, ?_⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hk25, hk⟩
        · rw [w.value_idxOverflow]
          exact hval.symm
  have hcard := w.ncard_le_of_dup hdup
  rw [Set.ncard_pair w.idxNearOne25_ne_idxOverflow] at hcard
  omega

/-! ### Lower bounds

Each certified separation makes the value map injective on a larger index
set.
-/

private theorem ge_of_injOn {s : Set (Fin 2926)} (hinj : Set.InjOn w.value s) :
    s.ncard ≤ a198683 12 := by
  rw [w.a198683_twelve_eq_ncard]
  calc s.ncard = (w.value '' s).ncard := (hinj.ncard_image).symm
    _ ≤ (w.value '' Set.univ).ncard :=
        Set.ncard_le_ncard (Set.image_mono (Set.subset_univ s))
          ((Set.toFinite _).image _)

private theorem not_special_left {j k : Fin 2926} (hj : j ≠ w.idxNearOne25) :
    ¬(j = w.idxNearOne25 ∧ k = w.idxNearOne1404) :=
  fun hc => hj hc.1

private theorem not_special_right {j k : Fin 2926} (hk : k ≠ w.idxNearOne25) :
    ¬(j = w.idxNearOne1404 ∧ k = w.idxNearOne25) :=
  fun hc => hk hc.2

include w in
theorem a198683_twelve_ge : 2924 ≤ a198683 12 := by
  have hinj : Set.InjOn w.value
      (Set.univ \ {w.idxOverflow, w.idxNearOne25}) := by
    rintro j ⟨-, hj⟩ k ⟨-, hk⟩ heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hj hk
    by_contra hne
    exact w.separated j k hne hj.1 hk.1
      (w.not_special_left hj.2) (w.not_special_right hk.2) heq
  have hge := w.ge_of_injOn hinj
  rw [Set.ncard_sdiff (Set.subset_univ _),
    Set.ncard_pair w.idxOverflow_ne_idxNearOne25', Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin] at hge
  omega

include w in
theorem a198683_twelve_ge_of_nearOneSplit (h : NearOneSplit) :
    2925 ≤ a198683 12 := by
  have hinj : Set.InjOn w.value (Set.univ \ {w.idxOverflow}) := by
    rintro j ⟨-, hj⟩ k ⟨-, hk⟩ heq
    simp only [Set.mem_singleton_iff] at hj hk
    by_contra hne
    by_cases hjk : j = w.idxNearOne25 ∧ k = w.idxNearOne1404
    · obtain ⟨rfl, rfl⟩ := hjk
      rw [w.value_idxNearOne25, w.value_idxNearOne1404] at heq
      exact h heq
    by_cases hkj : j = w.idxNearOne1404 ∧ k = w.idxNearOne25
    · obtain ⟨rfl, rfl⟩ := hkj
      rw [w.value_idxNearOne1404, w.value_idxNearOne25] at heq
      exact h heq.symm
    exact w.separated j k hne hj hk hjk hkj heq
  have hge := w.ge_of_injOn hinj
  rw [Set.ncard_sdiff (Set.subset_univ _),
    Set.ncard_singleton, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin] at hge
  omega

theorem a198683_twelve_ge_of_overflowIsolated (h : OverflowIsolated w) :
    2925 ≤ a198683 12 := by
  have hinj : Set.InjOn w.value (Set.univ \ {w.idxNearOne25}) := by
    rintro j ⟨-, hj⟩ k ⟨-, hk⟩ heq
    simp only [Set.mem_singleton_iff] at hj hk
    by_contra hne
    by_cases hjo : j = w.idxOverflow
    · subst hjo
      have hko : k ≠ w.idxOverflow := Ne.symm hne
      exact h k hko (heq.symm.trans w.value_idxOverflow)
    by_cases hko : k = w.idxOverflow
    · subst hko
      exact h j hjo (heq.trans w.value_idxOverflow)
    exact w.separated j k hne hjo hko
      (w.not_special_left hj) (w.not_special_right hk) heq
  have hge := w.ge_of_injOn hinj
  rw [Set.ncard_sdiff (Set.subset_univ _),
    Set.ncard_singleton, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin] at hge
  omega

theorem a198683_twelve_ge_of_nearOneSplit_of_overflowIsolated
    (h1 : NearOneSplit) (h2 : OverflowIsolated w) :
    2926 ≤ a198683 12 := by
  have hinj : Set.InjOn w.value (Set.univ : Set (Fin 2926)) := by
    rintro j - k - heq
    by_contra hne
    by_cases hjo : j = w.idxOverflow
    · subst hjo
      have hko : k ≠ w.idxOverflow := Ne.symm hne
      exact h2 k hko (heq.symm.trans w.value_idxOverflow)
    by_cases hko : k = w.idxOverflow
    · subst hko
      exact h2 j hjo (heq.trans w.value_idxOverflow)
    by_cases hjk : j = w.idxNearOne25 ∧ k = w.idxNearOne1404
    · obtain ⟨rfl, rfl⟩ := hjk
      rw [w.value_idxNearOne25, w.value_idxNearOne1404] at heq
      exact h1 heq
    by_cases hkj : j = w.idxNearOne1404 ∧ k = w.idxNearOne25
    · obtain ⟨rfl, rfl⟩ := hkj
      rw [w.value_idxNearOne1404, w.value_idxNearOne25] at heq
      exact h1 heq.symm
    exact w.separated j k hne hjo hko hjk hkj heq
  have hge := w.ge_of_injOn hinj
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hge
  omega

/-! ### The decision tree -/

include w in
/-- Given any partition witness, the twelfth term is one of three values —
with **no** hypothesis about the near-`1` split or the overflow class. -/
theorem a198683_twelve_mem :
    a198683 12 ∈ ({2924, 2925, 2926} : Set ℕ) := by
  have h1 := w.a198683_twelve_ge
  have h2 := w.a198683_twelve_le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

include w in
/-- The near-`1` split rules out `2924`. -/
theorem a198683_twelve_mem_of_nearOneSplit (h : NearOneSplit) :
    a198683 12 ∈ ({2925, 2926} : Set ℕ) := by
  have h1 := w.a198683_twelve_ge_of_nearOneSplit h
  have h2 := w.a198683_twelve_le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The no-miracles hypothesis rules out `2924`. -/
theorem a198683_twelve_mem_of_overflowIsolated (h : OverflowIsolated w) :
    a198683 12 ∈ ({2925, 2926} : Set ℕ) := by
  have h1 := w.a198683_twelve_ge_of_overflowIsolated h
  have h2 := w.a198683_twelve_le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **The expected answer.**  Both narrow hypotheses pin the value at `2926`. -/
theorem a198683_twelve_eq_2926 (h1 : NearOneSplit) (h2 : OverflowIsolated w) :
    a198683 12 = 2926 :=
  le_antisymm w.a198683_twelve_le
    (w.a198683_twelve_ge_of_nearOneSplit_of_overflowIsolated h1 h2)

/-- If the near-`1` split holds but the overflow value collides, the count
is `2925`. -/
theorem a198683_twelve_eq_2925_of_overflowCollision
    (h1 : NearOneSplit) (h2 : ¬OverflowIsolated w) :
    a198683 12 = 2925 :=
  le_antisymm (w.a198683_twelve_le_of_overflowCollision h2)
    (w.a198683_twelve_ge_of_nearOneSplit h1)

/-- If the overflow value is isolated but the near-`1` towers coincide, the
count is `2925`. -/
theorem a198683_twelve_eq_2925_of_nearOneMerge
    (h1 : nearOne25 = nearOne1404) (h2 : OverflowIsolated w) :
    a198683 12 = 2925 :=
  le_antisymm (w.a198683_twelve_le_of_nearOneMerge h1)
    (w.a198683_twelve_ge_of_overflowIsolated h2)

/-- If both narrow hypotheses fail, the count is `2924`. -/
theorem a198683_twelve_eq_2924
    (h1 : nearOne25 = nearOne1404) (h2 : ¬OverflowIsolated w) :
    a198683 12 = 2924 :=
  le_antisymm (w.a198683_twelve_le_of_nearOneMerge_of_overflowCollision h1 h2)
    w.a198683_twelve_ge

end N12PartitionWitness

/-!
## The endpoint bundle for the near-`1` split

`A198683N12Symbolic.nearOne25_ne_nearOne1404_of_endpoint_bounds` reduces
`NearOneSplit` to twenty-eight scalar endpoint estimates.  We bundle them as
one `Prop`-valued structure so that discharging the split is exactly the task
of proving `NearOneEndpointBounds` — endpoint by endpoint, by Taylor partial
sums (mathlib's alternating-series lemmas for `sin`/`cos`, `Real.exp_bound'`
plus the 20-digit `exp 1` and `π` certificates for `exp`).
-/

/-- The twenty-eight scalar endpoint estimates that imply the near-`1`
split, verbatim from
`A198683N12Symbolic.nearOne25_ne_nearOne1404_of_endpoint_bounds`.  Field
groups: `t*` box `sin θ`/`cos θ` at the certified `θ`-box ends; `v*` box the
factors of `v = i^(i^(i^i))`; `hs*`/`h1*`/`h2*` box the level-by-level
`exp·(cos, sin)` products of the candidate-`25` tower; `hexp*`/`hcos*` are the
final level-3 factors. -/
structure NearOneEndpointBounds : Prop where
  htsin0 : (320764449975 : ℝ) / 1000000000000 <
    Real.sin ((326536474946 : ℝ) / 1000000000000)
  htsin1 : Real.sin ((326536474949 : ℝ) / 1000000000000) <
    (320764449985 : ℝ) / 1000000000000
  htcos0 : (947158998071 : ℝ) / 1000000000000 <
    Real.cos ((326536474949 : ℝ) / 1000000000000)
  htcos1 : Real.cos ((326536474946 : ℝ) / 1000000000000) <
    (947158998073 : ℝ) / 1000000000000
  hvexp0 : (60419661058 : ℝ) / 100000000000 <
    Real.exp (-(Real.pi / 2) * ((320764449985 : ℝ) / 1000000000000))
  hvexp1 : Real.exp (-(Real.pi / 2) * ((320764449975 : ℝ) / 1000000000000)) <
    (60419661060 : ℝ) / 100000000000
  hvcos0 : (8290717827 : ℝ) / 100000000000 <
    Real.cos (Real.pi / 2 * ((947158998073 : ℝ) / 1000000000000))
  hvcos1 : Real.cos (Real.pi / 2 * ((947158998071 : ℝ) / 1000000000000)) <
    (8290717829 : ℝ) / 100000000000
  hvsin0 : (99655727371 : ℝ) / 100000000000 <
    Real.sin (Real.pi / 2 * ((947158998071 : ℝ) / 1000000000000))
  hvsin1 : Real.sin (Real.pi / 2 * ((947158998073 : ℝ) / 1000000000000)) <
    (99655727372 : ℝ) / 100000000000
  hsrelo : (25669119 : ℝ) / 10000000 <
    Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) *
      Real.cos (Real.pi / 2 * ((50092237 : ℝ) / 1000000000))
  hsrehi : Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) *
      Real.cos (Real.pi / 2 * ((50092236 : ℝ) / 1000000000)) <
    (320864 : ℝ) / 125000
  hsimlo : (404789 : ℝ) / 2000000 <
    Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) *
      Real.sin (Real.pi / 2 * ((50092236 : ℝ) / 1000000000))
  hsimhi : Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) *
      Real.sin (Real.pi / 2 * ((50092237 : ℝ) / 1000000000)) <
    (1011973 : ℝ) / 5000000
  h1relo : (-(864443 : ℝ) / 1000000) <
    Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) *
      Real.cos (Real.pi / 2 * ((25669119 : ℝ) / 10000000))
  h1rehi : Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) *
      Real.cos (Real.pi / 2 * ((320864 : ℝ) / 125000)) <
    (-(432221 : ℝ) / 500000)
  h1imlo : (-(53417 : ℝ) / 50000) <
    Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) *
      Real.sin (Real.pi / 2 * ((320864 : ℝ) / 125000))
  h1imhi : Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) *
      Real.sin (Real.pi / 2 * ((25669119 : ℝ) / 10000000)) <
    (-(1068339 : ℝ) / 1000000)
  h2relo : (11317 : ℝ) / 10000 <
    Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) *
      Real.cos (Real.pi / 2 * (-(864443 : ℝ) / 1000000))
  h2rehi : Real.exp (Real.pi / 2 * ((53417 : ℝ) / 50000)) *
      Real.cos (Real.pi / 2 * (-(432221 : ℝ) / 500000)) <
    (5659 : ℝ) / 5000
  h2imlo : (-(52347 : ℝ) / 10000) <
    Real.exp (Real.pi / 2 * ((53417 : ℝ) / 50000)) *
      Real.sin (Real.pi / 2 * (-(864443 : ℝ) / 1000000))
  h2imhi : Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) *
      Real.sin (Real.pi / 2 * (-(432221 : ℝ) / 500000)) <
    (-(52346 : ℝ) / 10000)
  hexp0 : (3724 : ℝ) < Real.exp (Real.pi / 2 * ((52346 : ℝ) / 10000))
  hexp1 : Real.exp (Real.pi / 2 * ((52347 : ℝ) / 10000)) < 3725
  hcos0 : (-(257 : ℝ) / 1250) <
    Real.cos (Real.pi / 2 * ((5659 : ℝ) / 5000))
  hcos1 : Real.cos (Real.pi / 2 * ((11317 : ℝ) / 10000)) <
    (-(411 : ℝ) / 2000)

/-- The endpoint bundle implies the near-`1` split, via the proved
interval ladder of `A198683N12Symbolic`. -/
theorem nearOneSplit_of_endpointBounds (h : NearOneEndpointBounds) :
    NearOneSplit :=
  A198683N12Symbolic.nearOne25_ne_nearOne1404_of_endpoint_bounds
    h.htsin0 h.htsin1 h.htcos0 h.htcos1
    h.hvexp0 h.hvexp1 h.hvcos0 h.hvcos1 h.hvsin0 h.hvsin1
    h.hsrelo h.hsrehi h.hsimlo h.hsimhi
    h.h1relo h.h1rehi h.h1imlo h.h1imhi
    h.h2relo h.h2rehi h.h2imlo h.h2imhi
    h.hexp0 h.hexp1 h.hcos0 h.hcos1

end A198683N12Certificate

end LeanProofs
