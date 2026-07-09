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
   `overflowBase11.im` is certified.  An independent 60-digit `mpmath`
   cross-check (this wave) pins the structure: `Im(overflowBase11) > 0` with
   magnitude `≈ 10^(4.12×10^34)` (the corpus's elided `10^41232…` notation
   denotes an exponent that itself has 35 digits), coming from
   `exp(−(π/2)·Im w10)·sin((π/2)·Re w10)` with `Im w10 ≈ −6.04×10^34` and
   the sine factor `≈ 0.5004` (`Re w10 mod 4 ≈ 1.666`, comfortably inside
   the positive-sine window `(0, 2)`).  No mod-`2π` reduction of the final
   astronomical imaginary part is needed — but certifying the *sine factor's
   sign* requires `Re w10 mod 4`, i.e. absolute precision `< 1` on a
   quantity of size `≈ 7×10^34`: a ~36-significant-digit certified chain
   through `w9`.  **This is now done**:
   [`LeanProofs/A198683N12OverflowBound.lean`](../../../../LeanProofs/A198683N12OverflowBound.lean)
   proves `overflowBase11_im_gt : (10 : ℝ)^100 < overflowBase11.im` (axioms:
   `propext`, `Classical.choice`, `Quot.sound`) by boxing the phase-critical
   `Re(w10)` with 44-digit rational endpoints while using only the crude
   `Im(w10) < −150` for the exponential factor — the full `10^(4.12×10^34)`
   magnitude is never materialized.  The derived criterion
   `overflowCandidate12_ne_of_moderate_logModulus` (any principal-power
   value with `Re(log a · b) > −(π/2)·10^100` differs from candidate `57`)
   converts `OverflowIsolated` into a per-class magnitude check: for a
   future witness it suffices to certify, per class, a crude lower bound on
   the log-modulus — no transcendence assumption, no mod-`2π` reduction.
   What remains of the "no-miracles" hypothesis is therefore only the
   moderate-magnitude certification of the other 2925 representatives,
   which the same interval pipeline that produces the witness will supply.

## Companion Coq development — full statement-for-statement parity

The endgame is now formalized on the Rocq/Coq side too, over Coquelicot's
`C`, in five modules (all under [`CoqProofs/`](../../../../CoqProofs/)):

- `A198683N12Bounds.v` — the original interval-certified real boxes: the
  `θ`/`ρ` boxes, endpoint estimates, `base_im < 0`, and the norm separation
  `‖nearOne1404‖ < 1 < ‖nearOne25‖`, proved directly on the nested tower
  expressions (which is why the Coq side never depended on the two faulty
  decomposed constants).
- `A198683Complex.v` — `Cexp`/`Cln`/`principalPow` over Coquelicot `C`
  (Rocq stdlib and Coquelicot ship no complex exponential), with the power
  re/im formulas and the log-modulus separation criterion.
- `A198683N12ComplexTowers.v` — the concrete towers as genuine complex
  numbers, the island identities (`i^i = ρ`, `(i^i)^i = −i` exactly), the
  re/im glue onto the Bounds quantities (reflexivity after the power
  formulas), and **`nearOne25C ≠ nearOne1404C`** — the Coq near-`1` split.
- `A198683N12Certificate.v` — the decision tree, generic over the value
  domain via a relational `DistinctCount` spec; notably the membership and
  2926-pinning theorems are **closed under the global context** (fully
  constructive — a smaller footprint than the Lean originals).
- `A198683N12OverflowBound.v` — `10^100 < Im overflowBase11C` and the
  moderate-log-modulus separation criterion, in ~250 lines and 4 s where
  the Lean counterpart needed ~900 lines of hand Taylor bounds:
  `interval with (i_prec 200)` certifies the phase-critical `Re(w10)` box
  through the 35-digit cancellation in one shot.
- `A198683N12CertificateC.v` — the instantiation at `C`: witness alone
  gives `count ∈ {2925, 2926}`, and the overflow no-miracles hypothesis
  decides `2926` versus `2925` — the same headline as Lean.

## Provenance

- Certificate module and decision tree: commit `c54a6e1c3`.
- Symbolic tidy (probe constants renamed, docstrings): commit `1a78f281f`.
- Endpoint proofs, refutations, ladder repair, `nearOneSplit`, tightened
  decision tree: commit `af3e10254`.
- Corpus README and this report's cross-references: commits `1a78f281f`,
  `0609c247b`.
