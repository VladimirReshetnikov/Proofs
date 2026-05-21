# OEIS A198683 Research Corpus

- Status: Informational, wave-organised; current state captured by the wave-3 synthesis
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Local artifacts for OEIS A198683 and the disputed value of `A198683(12)`
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

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
into three temporal waves, each preserved intact under
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

The single best entry point to the post-wave-2 corpus is
[`reports/wave-3/a198683-post-wave2-synthesis.md`](reports/wave-3/a198683-post-wave2-synthesis.md).
It records the eight-element plausible-value table, the three
structurally-degenerate candidate clusters that produce the residual
ambiguity, and the explicit inventory of unsettled questions.

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
  a wave-4 or later pipeline would be its execution.

The residual ambiguity localises to three structurally-degenerate clusters
in the candidate space — near `0`, near `i^i = e^(-pi/2)`, and near `1` —
identified by the wave-2 tolerance-policy diagnostic
[`reports/wave-2/a198683-n12-discrepancy-root-cause.md`](reports/wave-2/a198683-n12-discrepancy-root-cause.md).

## Directory Layout

- [`computations/`](computations/README.md) — executable checks and scripts
  (`compute_a198683.py`, the six `diagnose_*.py` scripts added by wave-2
  `investigate-cc`, and the Wolfram check).
- [`reports/`](reports/README.md) — wave-1 / wave-2 / wave-3 reports plus
  exploratory background reading.
- [`data/`](data/README.md) — generated tabular data.
- [`sources/`](sources/README.md) — downloaded or extracted source
  references (OEIS snapshot, Schoenfield table, Guy-Selfridge paper).

## Reading Order

1. This file for the current-state map.
2. [`reports/README.md`](reports/README.md) for the wave-by-wave index.
3. [`reports/wave-3/a198683-post-wave2-synthesis.md`](reports/wave-3/a198683-post-wave2-synthesis.md)
   for the consolidated post-wave-2 picture, including the unsettled
   questions.
4. Any wave-1 result report or wave-2 root-cause report for depth on a
   specific evidence trail.
5. [`computations/README.md`](computations/README.md) when rerunning or
   comparing the Python and Wolfram computations.
6. [`sources/README.md`](sources/README.md) to locate the OEIS snapshot,
   the Schoenfield table, and the Guy-Selfridge paper assets.
