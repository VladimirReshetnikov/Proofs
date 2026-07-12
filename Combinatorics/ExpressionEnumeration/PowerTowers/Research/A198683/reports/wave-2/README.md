# Wave-2: A198683(12) Root-Cause Analyses

- Status: Informational index for the wave-2 root-cause analyses
- Audience: Maintainers, OEIS contributors, future agents
- Scope: Three independent root-cause reports diagnosing the wave-1
  `2919` vs `2926` conflict on `A198683(12)`
- Created (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

This directory contains three independent root-cause analyses of the
historical "`A198683(12)` is either `2919` or `2926`" conflict recorded by
the OEIS entry. Each was prepared in parallel on a separate branch
(`investigate-5.5`, `investigate-cc`, `investigate-5.2`) and merged into
`main` without resolving the framing differences between them. The
[`../wave-3/a198683-post-wave2-synthesis.md`](../wave-3/a198683-post-wave2-synthesis.md)
report consolidates their findings.

## Reports

- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  — *Black-box precision sweep* (`investigate-5.5`). Reruns the Python
  recurrence from `--dps 180` to `--dps 3000` and shows the reported count
  drifts upward (`2919 → 2920 → 2921 → 2922 → 2924`). Bottom line: `2919`
  is *invalidated*; `2926` is *the strongest recorded local value*.
- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  — *White-box tolerance-policy diagnostic* (`investigate-cc`). Pinpoints
  the `abs_eps = rel_eps` floor in `mp.almosteq` as the structural cause,
  identifies an 8-element near-zero cluster collapsed by it, recovers 6 of
  the 7 missing classes by setting `abs_eps = 0`, and decomposes the
  residue across three structurally-degenerate clusters (near `0`,
  near `i^i = e^(-π/2)`, near `1`). Bottom line: strictly neutral; `2925`,
  `2926`, `2927` are *all* heuristics. Adds six `diagnose_*.py` scripts
  under [`../../computations/python/`](../../computations/python/).
- [`a198683-n12-precision-sweep-extended.md`](a198683-n12-precision-sweep-extended.md)
  — *Extended precision sweep* (`investigate-5.2`). Extends the precision
  sweep to `--dps 8000` and finds the Python output stabilises at `2924`
  from `--dps 3000` upward. Adds a `sys.set_int_max_str_digits(0)` guard
  to [`../../computations/python/compute_a198683.py`](../../computations/python/compute_a198683.py)
  so high-precision diagnostic runs do not crash on int-to-str
  conversions. Bottom line: cautious — `2919` invalidated, `2926` not a
  proof either; the remaining work is proof-quality equality
  certification.

## Shared findings

All three reports agree on these points (the synthesis at
[`../wave-3/a198683-post-wave2-synthesis.md`](../wave-3/a198683-post-wave2-synthesis.md)
states this in more detail):

- The recurrence, the lower-term reproduction through `n = 11`, and the
  `5139` candidate-power count at `n = 12` are correct in both
  implementations.
- The disagreement lives entirely in Python's deduplication of the `n = 12`
  candidates. It is not a branch-choice or wrap-integer ambiguity.
- The Python `2919` count is a finite-precision artefact.
- The Wolfram `2926` is not a proof independent of Wolfram's symbolic
  equality engine.
- The residue is structural — three small clusters in the candidate space
  that finite-precision numerics cannot discriminate. A certified
  arithmetic engine is required.

## Where the three reports diverge

They differ in **diagnostic depth** (one is mechanistic; the other two are
behavioural) and in **bottom-line stance** (one recommends `2926` as the
working answer; one is strictly neutral; one is cautious between the two).
None of the divergences is a factual contradiction; the corpus preserves
all three side by side.

See [`../wave-3/a198683-post-wave2-synthesis.md`](../wave-3/a198683-post-wave2-synthesis.md)
§4 for the full comparison.
