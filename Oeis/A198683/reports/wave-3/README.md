# Wave-3: Post-Wave-2 Synthesis and Forward-Looking Plans

- Status: Informational index for the wave-3 outputs
- Audience: Maintainers, OEIS contributors, future agents
- Scope: Post-wave-2 outputs — the synthesis of the three wave-2 root-cause
  reports plus the feasibility study for a certified pipeline that could
  settle `A198683(12)`
- Created (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

This directory contains the corpus's post-wave-2 outputs. Wave-3 does not
add new heuristic evidence about `A198683(12)`; it consolidates the wave-2
findings and lays out a path to a certified value.

## Reports

- [`a198683-post-wave2-synthesis.md`](a198683-post-wave2-synthesis.md)
  — *Unified synthesis*. Records where the three wave-2 reports agree,
  where they diverge, the eight-element plausible-value table
  (`2919..2927`), the three structurally-degenerate clusters that the
  residue lives in, and an explicit inventory of the six remaining
  unsettled questions.
- [`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md)
  — *Feasibility study* for a certified evaluation of `A198683(12)` via
  the in-repo `src/Numerics/python` (`numerics`) package. Maps the
  certification strategy from
  [`../exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md)
  onto the existing engine, identifies the three needed extensions
  (a `π` constant, `sin` / `cos` on bounded ground intervals, a
  complex-interval wrapper), proposes an `i^Z` canonical form that
  sidesteps astronomical argument reduction, and explains why
  `numerics.equal`'s tri-valued semantics structurally exclude the
  silent-merge artefact wave-2 diagnosed.

## What wave-3 is not

- Wave-3 is not a new measurement of `A198683(12)`. The eight values in
  the plausible-value table are inherited from wave-1 and wave-2.
- Wave-3 is not a certificate. The feasibility study sizes the work but
  does not produce a verified count.
- Wave-3 does not adjudicate between the three wave-2 reports' bottom-line
  stances. They are preserved as independent voices.

## Where to go next

Wave-4 (or later) is expected to be the certified pipeline itself,
producing an audit trail of equality verdicts on the `5139` candidate
powers at `n = 12`. The feasibility study sketches the architecture and
sizes the work. The synthesis identifies the residual clusters that the
pipeline will have to either resolve or report explicitly as
`UndecidableCluster` events.

See [`a198683-post-wave2-synthesis.md`](a198683-post-wave2-synthesis.md)
§7 for what a "settled" answer would look like.
