# A198683 Reports

- Status: Informational index over the wave-1 / wave-2 / wave-3 / wave-4 report cycle
- Audience: Maintainers, OEIS contributors, future agents
- Scope: Historical, root-cause, synthesis, and exploratory reports about OEIS A198683
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-07-06
- Repository HEAD: not pinned; see git history for the exact checkpoint commit

This directory groups A198683 reports into four temporal waves plus an
exploratory background-reading directory. The wave structure reflects the
chronological order in which the work was done; each wave layer is preserved
intact.

| Wave | Directory | What lives there | Index |
|------|-----------|------------------|-------|
| 1 | [`wave-1/`](wave-1/) | Original single-source result reports (`2919` and `2926`) | [`wave-1/README.md`](wave-1/README.md) |
| 2 | [`wave-2/`](wave-2/) | Three independent root-cause analyses of the `2919` vs `2926` conflict | [`wave-2/README.md`](wave-2/README.md) |
| 3 | [`wave-3/`](wave-3/) | Post-wave-2 synthesis and the feasibility study for a certified pipeline | [`wave-3/README.md`](wave-3/README.md) |
| 4 | [`wave-4/`](wave-4/) | Lean proof-state checkpoint after the shared lexical-definition refactor | [`wave-4/README.md`](wave-4/README.md) |
| — | [`exploratory/`](exploratory/README.md) | Background-reading writeups about the sequence and possible certification strategies | [`exploratory/README.md`](exploratory/README.md) |

## Recommended reading order

For a reader new to the corpus:

1. The corpus root [`../README.md`](../README.md) — current-state map of
   the `A198683(12)` conflict.
2. One of the two **wave-1** result reports for context. Either of:
   - [`wave-1/a198683-n12-python-mpmath-2919.md`](wave-1/a198683-n12-python-mpmath-2919.md)
   - [`wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
3. **One** of the three **wave-2** root-cause reports for the diagnostic.
   The most mechanistic of the three is the tolerance-policy diagnostic:
   - [`wave-2/a198683-n12-discrepancy-root-cause.md`](wave-2/a198683-n12-discrepancy-root-cause.md)
4. The wave-3 synthesis:
   [`wave-3/a198683-post-wave2-synthesis.md`](wave-3/a198683-post-wave2-synthesis.md) —
   reconciles the three wave-2 reports and lists the open questions.
5. Optional: the wave-3 feasibility study
   [`wave-3/a198683-numerics-interval-feasibility.md`](wave-3/a198683-numerics-interval-feasibility.md)
   for the proposed certified pipeline.
6. The wave-4 Lean checkpoint:
   [`wave-4/a198683-n12-lean-status-and-next-directions.md`](wave-4/a198683-n12-lean-status-and-next-directions.md) —
   records the current formalization state, the paused `n = 12` work, and
   promising next directions.

## What is settled and what is not

After wave-2 (per
[`wave-3/a198683-post-wave2-synthesis.md`](wave-3/a198683-post-wave2-synthesis.md)):

- **Settled**: the recurrence, the lower-term reproduction through `n = 11`,
  the `5139`-candidate count at `n = 12`, the locus of the disagreement
  (deduplication of the `5139` candidates), the status of the Python `2919`
  claim (invalidated as a finite-precision artefact), and the status of the
  Wolfram `2926` claim (strongest single-source result but not a proof
  certificate).
- **Unsettled**: the true value of `A198683(12)`. The eight local heuristics
  span `{2919, 2920, 2921, 2922, 2924, 2925, 2926, 2927}`; the genuine count
  is among them but no wave-1 or wave-2 pipeline can discriminate without a
  certified arithmetic engine. The wave-3 feasibility study sketches such an
  engine; wave-4 records the current Lean proof checkpoint, not a final
  execution of that pipeline.
