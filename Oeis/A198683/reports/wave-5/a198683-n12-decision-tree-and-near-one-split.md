# A198683(12): the machine-checked decision tree and the proved near-1 split

- Status: wave-5 result report
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: the Lean formalization step that packages the entire residual
  `a(12)` uncertainty into named hypotheses and proves the near-`1` split
- Created (UTC): 2026-07-08T22:15:25Z
- Repository HEAD: 0609c247be9ff7cb059d0df42aedefc4c4a6de2d (branch
  `claude/lean-coq-proofs-review-6d6444`)

## Summary

Wave-5 delivers the certificate *shape* that wave-3 §7 asked for — a
conditional statement `a(12) ∈ S` with `|S| ≤ 3` and explicit cluster
hypotheses — as machine-checked Lean theorems, and then discharges one of the
two cluster hypotheses outright:

1. **The decision tree**
   ([`LeanProofs/A198683N12Certificate.lean`](../../../../LeanProofs/A198683N12Certificate.lean)).
   All residual uncertainty is packaged into one *wide* hypothesis — the
   partition witness `N12PartitionWitness`, i.e. the 2926-class representative
   certificate that the wave-3 interval pipeline is designed to produce, with
   cross-class separation deliberately *not* claimed for the two structurally
   uncertain comparisons — and two *narrow* hypotheses:
   `NearOneSplit : nearOne25 ≠ nearOne1404` and `OverflowIsolated`
   (the formal **no-miracles** hypothesis for the overflow candidate `57`).
   Lean proves, with no further assumptions:

   | given | conclusion |
   |-------|------------|
   | witness | `a198683 12 ∈ {2924, 2925, 2926}` |
   | witness + split | `a198683 12 ∈ {2925, 2926}` |
   | witness + no-miracles | `a198683 12 ∈ {2925, 2926}` |
   | witness + split + no-miracles | `a198683 12 = 2926` |
   | witness + split + collision | `a198683 12 = 2925` |
   | witness + merge + no-miracles | `a198683 12 = 2925` |
   | witness + merge + collision | `a198683 12 = 2924` |

   The membership row needs neither narrow hypothesis: excluded middle
   absorbs both dichotomies, so the three-element set is what the wide
   certificate alone determines.

2. **The near-`1` split is now a theorem**
   ([`LeanProofs/A198683N12Endpoints.lean`](../../../../LeanProofs/A198683N12Endpoints.lean)):
   `nearOneSplit : nearOne25 ≠ nearOne1404`, axioms exactly
   `[propext, Classical.choice, Quot.sound]`.  Every scalar endpoint estimate
   of the `A198683N12Symbolic` interval ladder is proved by alternating-series
   Taylor bounds for `sin`/`cos` on `[0, 1]`, rational `exp` certificates
   built from mathlib's 20-digit `exp 1` and `π` constants, monotone `π/2`
   transport, and quadrant reductions.  This settles wave-3 question Q3 in
   the *split* direction: representative `25` is genuinely distinct from the
   (provably equal) pair `{1404, 4239}`, as the multi-precision probe
   predicted.

   Consequently `a198683 12 ∈ {2925, 2926}` holds **given any partition
   witness alone** (`a198683_twelve_mem_of_witness`), and the overflow
   no-miracles hypothesis is the single remaining narrow question, deciding
   `2926` (`a198683_twelve_eq_2926_of_overflowIsolated`) versus `2925`
   (`a198683_twelve_eq_2925_of_overflowCollision`).

## A finding: two endpoint constants in the ladder were false

The endpoint work began by re-verifying all ladder hypotheses with exact
rational interval arithmetic before writing any Lean.  Two of the original
twenty-eight endpoint estimates in
`A198683N12Symbolic.nearOne25_ne_nearOne1404_of_endpoint_bounds` turned out
to be **false as stated**:

- `hexp0` claimed `3724 < exp((π/2)·5.2346)`; the true value is `3723.7647…`.
- `hcos1` claimed `cos((π/2)·1.1317) < −411/2000 = −0.2055`; the true value
  is `−0.2054014…`.

In both cases the constant had been transcribed from the *true* level-2
value (`≈ 5.23468`, `≈ 1.13179`) rather than from the propagated box
endpoint — so the hypothesis bundle was unsatisfiable, and the conditional
split theorem, while valid, could never have been discharged.  Both
refutations are kept as Lean lemmas (`uncorrected_hexp0_is_false`,
`uncorrected_hcos1_is_false`) in the endpoints module.

The repair: the level-3 target window widens from `(−766, −765)` to
`(−766, −764)` — the sine-negativity argument
(`sin((π/2)·x) < 0`) holds on the whole widened interval, because
`−766 ≡ 2` and `−764 ≡ 0 (mod 4)` — and the two constants become `3723` and
`−1027/5000`, after which the corrected interval arithmetic closes with
comfortable margin.  The repaired bundle has twenty-six estimates, all
proved.

This is a working demonstration of why the corpus insists on certificates
over heuristics: a plausible-looking, numerically-motivated hypothesis
chain contained a silent transcription bug that only an exactness-first
verification pass caught.

## What remains for `a(12) = 2926`

Two items, in decreasing order of size:

1. **The partition witness** — the wide certificate: 2926 representative
   parenthesizations with value-cover of all `n = 12` parenthesizations and
   pairwise separation outside the overflow class.  This is the wave-3
   engine's deliverable, now with a precise Lean-side type to target
   (`N12PartitionWitness`).  The already-proved symbolic identities (the
   fourteen near-`i^i` collapses, the near-zero and near-one merges)
   discharge the exceptional cover obligations.
2. **The overflow no-miracles hypothesis** — `OverflowIsolated w`: the value
   of candidate `57` differs from every other class value.  The proved
   log-modulus criteria
   (`overflowCandidate12_ne_principalPow_of_im_gt_of_re_gt`) reduce every
   instance to a real-part bound, provided a lower bound on
   `overflowBase11.im` (true magnitude `≈ 10^41232`) is certified; work on a
   coarse tower-box proof of `10^100 < overflowBase11.im` — which would
   convert the hypothesis into a per-class magnitude check with
   ~41000 orders of magnitude of slack — was in progress when this report
   was written.  No mod-`2π` reduction of the astronomical imaginary part is
   needed on this route.

## Companion Coq development

[`CoqProofs/A198683N12Bounds.v`](../../../../CoqProofs/A198683N12Bounds.v)
independently certifies the same separation content by interval arithmetic
(coq-interval): the `θ`/`ρ` boxes, the endpoint estimates, `base_im < 0`,
and the norm separation `‖nearOne1404‖ < 1 < ‖nearOne25‖` — proved directly
on the nested tower expressions, which is why the Coq side never depended on
the two faulty decomposed constants.

## Provenance

- Certificate module and decision tree: commit `c54a6e1c3`.
- Symbolic tidy (probe constants renamed, docstrings): commit `1a78f281f`.
- Endpoint proofs, refutations, ladder repair, `nearOneSplit`, tightened
  decision tree: commit `af3e10254`.
- Corpus README and this report's cross-references: commits `1a78f281f`,
  `0609c247b`.
