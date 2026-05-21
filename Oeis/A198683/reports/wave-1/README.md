# Wave-1: Original A198683(12) Result Reports

- Status: Informational index for the wave-1 result reports
- Audience: Maintainers, OEIS contributors, future agents
- Scope: The two original single-source result reports about `A198683(12)` that
  existed before the wave-2 root-cause analyses
- Created (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

This directory preserves the two result reports about `A198683(12)` that
existed in the corpus before the wave-2 root-cause passes (`investigate-5.5`,
`investigate-cc`, `investigate-5.2`). They make mutually incompatible claims;
wave-2 explains why, and
[`../wave-3/a198683-post-wave2-synthesis.md`](../wave-3/a198683-post-wave2-synthesis.md)
records the post-wave-2 corpus state.

## Reports

- [`a198683-n12-python-mpmath-2919.md`](a198683-n12-python-mpmath-2919.md)
  — Python `mpmath` recurrence with numerical bucketing and `mp.almosteq`-based
  deduplication. Historical claim: `A198683(12) = 2919`. Wave-2 invalidates
  this claim as a finite-precision deduplication artefact.
- [`a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
  — Wolfram Language recurrence with `Union[..., SameTest -> Equal]` via the
  local Tungsten runner. Claim: `A198683(12) = 2926`. Wave-2 leaves this as the
  strongest recorded single-source local computation while noting it is not a
  proof certificate independent of Wolfram's symbolic equality engine.

## How to read these reports

Each wave-1 report has been amended in place with errata pointing to the
relevant wave-2 root-cause analyses. The body of each report is preserved as a
historical record of the method and its original conclusion; the errata at the
top of each file record the wave-2 interpretation.

Before citing either report as evidence for `A198683(12)`, read at least one
wave-2 root-cause report (see [`../wave-2/README.md`](../wave-2/README.md)) and
the wave-3 synthesis at
[`../wave-3/a198683-post-wave2-synthesis.md`](../wave-3/a198683-post-wave2-synthesis.md).
