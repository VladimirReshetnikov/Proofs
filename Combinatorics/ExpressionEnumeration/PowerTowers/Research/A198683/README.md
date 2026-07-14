# OEIS A198683 Research Corpus

- Status: Informational, wave-organised; current Lean state captured by the wave-4 checkpoint
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Local artifacts for OEIS A198683 and the disputed value of `A198683(12)`
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-07-06
- Repository HEAD: not pinned; see git history for the exact checkpoint commit

OEIS A198683 counts the number of distinct values produced by all binary
parenthesizations of `i^i^...^i`, using the principal value of complex
exponentiation at every `^`. This directory is the single local home for the
post-`f906a31c0f82f92946a3524ac72e70d392258403` A198683 artifacts.

## Current State

The OEIS snapshot in [`sources/oeis-entry__2025-11-05.txt`](sources/oeis-entry__2025-11-05.txt)
records the accepted values through `n=11`:

```text
1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152
```

It also records the historical note that `a(12)` was said to be either
`2919` or `2926`. The local research on this question has been organised
into five temporal waves, each preserved intact under
[`reports/`](reports/README.md):

- **Wave-1** ([`reports/wave-1/`](reports/wave-1/README.md)) — the two
  original single-source result reports that reached `2919` (Python `mpmath`)
  and `2926` (Wolfram Language). Wave-2 invalidates the `2919` claim as a
  finite-precision deduplication artefact; wave-2 leaves the `2926` claim
  standing as the strongest recorded single-source computation while noting
  it is not a proof certificate.
- **Wave-2** ([`reports/wave-2/`](reports/wave-2/README.md)) — three
  independent root-cause analyses prepared in parallel on the branches
  `investigate-5.2`, `investigate-5.5`, and `investigate-cc`. They agree on
  the substantive findings (the disagreement is in deduplication, not in
  the recurrence) and diverge in diagnostic depth and bottom-line stance.
- **Wave-3** ([`reports/wave-3/`](reports/wave-3/README.md)) — the
  post-wave-2 synthesis plus the feasibility study for a certified
  evaluation pipeline.
- **Wave-4** ([`reports/wave-4/`](reports/wave-4/README.md)) — the
  Lean proof-state checkpoint after the shared lexical-definition refactor,
  including what has been proved, what has been tried, and promising future
  directions while further `a(12)` pinpointing is paused.
- **Wave-5** ([`reports/wave-5/`](reports/wave-5/README.md)) — the Lean
  decision-tree certificate (`A198683N12Certificate.lean`) and the proved
  near-`1` split (`A198683N12Endpoints.lean`), including the two
  refuted-and-repaired endpoint constants.

The single best entry point to the post-wave-2 corpus is
[`reports/wave-3/a198683-post-wave2-synthesis.md`](reports/wave-3/a198683-post-wave2-synthesis.md).
It records the eight-element plausible-value table, the three
structurally-degenerate candidate clusters that produce the residual
ambiguity, and the explicit inventory of unsettled questions.
For the current Lean formalization checkpoint, read
[`reports/wave-4/a198683-n12-lean-status-and-next-directions.md`](reports/wave-4/a198683-n12-lean-status-and-next-directions.md).

Since wave-4, the Lean module
[`../../Lean/PowerTowers/A198683/N12/N12Certificate.lean`](../../Lean/PowerTowers/A198683/N12/N12Certificate.lean)
packages the entire residual uncertainty as one machine-checked **decision
tree**: given a partition witness (the wide, interval-checkable certificate the
wave-3 pipeline is designed to produce), Lean proves
`a198683 12 ∈ {2924, 2925, 2926}` outright, and each of the two isolated
narrow hypotheses — the near-`1` split `nearOne25 ≠ nearOne1404` and the
overflow **no-miracles** hypothesis for candidate `57` — removes one branch;
both together pin `a198683 12 = 2926`.  The near-`1` split is now **proved**:
[`../../Lean/PowerTowers/A198683/N12/N12Endpoints.lean`](../../Lean/PowerTowers/A198683/N12/N12Endpoints.lean)
discharges every scalar endpoint estimate of the Symbolic module's interval
ladder by Taylor partial sums — settling question Q3 of the wave-3 synthesis
in the split direction, and en route exposing (and repairing) two
endpoint-vs-midpoint transcription errors in the ladder's original
constants, each refuted in Lean before correction.  Consequently
`a198683 12 ∈ {2925, 2926}` holds given any partition witness alone, and the
overflow no-miracles hypothesis is the single remaining narrow question,
deciding `2926` versus `2925`.  That module's docstring is the recommended
summary of exactly which facts the expected value `2926` rests on.
**No unconditional value of `a(n)` beyond `n = 7` is proved** — the witness
the decision tree consumes has not been constructed; the authoritative
proved / conditional / data-certified / heuristic ledger, with the measured
remaining work for each goal, is
[`reports/wave-5/a198683-formalization-status-and-remaining-work.md`](reports/wave-5/a198683-formalization-status-and-remaining-work.md).

## What is settled and what is not

After wave-2:

- **Settled**: The recurrence, the lower-term reproduction through `n = 11`,
  the `5139`-candidate count at `n = 12`, and the locus of the disagreement
  (deduplication of the `5139` candidates). The Python `2919` claim is
  invalidated. The Wolfram `2926` claim stands as the strongest
  single-source local computation.
- **Unsettled**: The true value of `A198683(12)`. The local heuristics span
  `{2919, 2920, 2921, 2922, 2924, 2925, 2926, 2927}` depending on the
  knob; the genuine count is among them but no wave-1 or wave-2 pipeline
  can discriminate without a certified arithmetic engine. The wave-3
  feasibility study sketches such an engine
  ([`reports/wave-3/a198683-numerics-interval-feasibility.md`](reports/wave-3/a198683-numerics-interval-feasibility.md));
  wave-4 records the current Lean proof checkpoint while exact pinpointing is
  paused.

The residual ambiguity localises to three structurally-degenerate clusters
in the candidate space — near `0`, near `i^i = e^(-pi/2)`, and near `1` —
identified by the wave-2 tolerance-policy diagnostic
[`reports/wave-2/a198683-n12-discrepancy-root-cause.md`](reports/wave-2/a198683-n12-discrepancy-root-cause.md).
A Schoenfield-style equivalence-class extension to `n = 12` listing all
**5139** candidate powers is preserved at
[`data/a198683-n12-equivalence-classes.txt`](data/a198683-n12-equivalence-classes.txt).
It uses a probe-refined partition: starting from the 2925 strict-policy
classes (`abs_eps = 0` value-space dedup), each of the four tentative
classes is re-examined at dps ∈ {260, 500, 1000} to distinguish
algebraic from numerical-noise differences. The probe shows that cluster C
(near `1`, members `{25, 1404, 4239}`) **splits** into `{25}` and
`{1404, 4239}` because `Re(e_25) - Re(e_1404) = 2.306566301e-1305` is
stable across all three precisions (precision-floor noise would shrink as
dps grows); the other three tentative classes either merge conclusively
or remain undecidable (the overflow singleton). The refined partition has
exactly **2926 classes** — matching the Wolfram count.
**2925** of those are conclusive (multi-precision evidence agrees) and
**1** remains tentative: the overflow singleton `{57}`, whose
`|Im(e)| ~ 10^41232...` is beyond mod-`2π` reduction at any finite
precision.

## Directory Layout

- [`computations/`](computations/README.md) — executable checks and scripts
  (`compute_a198683.py`, the six `diagnose_*.py` scripts added by wave-2
  `investigate-cc`, and the Wolfram check).
- [`reports/`](reports/README.md) — wave-1 / wave-2 / wave-3 / wave-4 reports plus
  exploratory background reading.
- [`data/`](data/README.md) — generated tabular data.
- [`sources/`](sources/README.md) — downloaded OEIS and Schoenfield source
  snapshots.
- [`../References/GuySelfridge1973/`](../References/GuySelfridge1973/) — the
  Guy-Selfridge paper and its extracted image assets.

## Reading Order

1. This file for the current-state map.
2. [`reports/README.md`](reports/README.md) for the wave-by-wave index.
3. [`reports/wave-3/a198683-post-wave2-synthesis.md`](reports/wave-3/a198683-post-wave2-synthesis.md)
   for the consolidated post-wave-2 picture, including the unsettled
   questions.
4. [`reports/wave-4/a198683-n12-lean-status-and-next-directions.md`](reports/wave-4/a198683-n12-lean-status-and-next-directions.md)
   for the current Lean state and next proof directions.
5. Any wave-1 result report or wave-2 root-cause report for depth on a
   specific evidence trail.
6. [`computations/README.md`](computations/README.md) when rerunning or
   comparing the Python and Wolfram computations.
7. [`sources/README.md`](sources/README.md) to locate the OEIS snapshot and
   Schoenfield table; the Guy-Selfridge paper is in
   [`../References/GuySelfridge1973/`](../References/GuySelfridge1973/).
