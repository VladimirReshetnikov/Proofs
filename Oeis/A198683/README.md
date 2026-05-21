# OEIS A198683 Research Corpus

- Status: Informational, unresolved-conflict index
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Local artifacts for OEIS A198683 and the disputed value of `A198683(12)`
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T02:27:23Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

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

It also records the historical unresolved note that `a(12)` was said to be
either `2919` or `2926`. The local corpus preserves the same contradiction
rather than resolving it.

Two later local investigations both reproduce the accepted values through
`n=11` and both use the dynamic-programming recurrence over distinct lower-level
sets, giving `5139` pairwise candidate powers at `n=12`. They disagree about
how those candidates should be deduplicated:

| Report | Method | Reported `A198683(12)` | Nature of the disagreement |
|---|---|---:|---|
| [`reports/a198683-n12-python-mpmath-2919.md`](reports/a198683-n12-python-mpmath-2919.md) | Python `mpmath`, scale-invariant numerical buckets, `almosteq`, and one special overflow bucket | 2919 | Treats one unmaterializable candidate separately and reports seven more effective merges than the Wolfram result. |
| [`reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md) | Wolfram Language recurrence using `Union[..., SameTest -> Equal]` through the local Tungsten runner | 2926 | Reports exact Wolfram equality classes and notes that `2919` would require seven additional exact equalities among those classes. |

The contradiction is therefore not about the OEIS definition, the lower terms,
or the number of generated `n=12` candidate powers. It is about equality
certification for a small number of candidate classes under principal complex
power semantics, in the presence of extreme intermediate magnitudes and branch
choice sensitivity.

[`reports/a198683-n12-discrepancy-root-cause.md`](reports/a198683-n12-discrepancy-root-cause.md)
isolates *where* in the candidate space the contradiction actually lives. Its
findings, in short:

- The 7-class gap is dominated by an artefact of the Python script's
  `mpmath.almosteq(rel_eps, abs_eps)` policy. The script sets
  `abs_eps = rel_eps = 10^-(dps/2)`, which makes `almosteq` declare **any** two
  candidates smaller in magnitude than `abs_eps` to be equal regardless of
  structure. At `n=12` an eight-element cluster of mathematically-distinct
  "near-zero" candidates collapses into one Python class. Setting
  `abs_eps = 0` in the same script at the `n=12` stage raises the count from
  `2919` to `2925`, recovering **six of the seven** missing classes.
- The remaining single-class gap lives in two further small clusters: one near
  `i^i = e^(-pi/2)` (where many parenthesizations evaluate, exactly or
  near-exactly, to `e^(-pi/2)`) and one near `1` (three candidates whose
  exponents are smaller than `10^-1300`). Whether tiny imaginary residuals in
  those clusters are numerical noise or genuine inequalities cannot be settled
  by either heuristic; both `2926` and `2927` are plausible depending on policy.
- Neither implementation is a proof. Both are heuristic equality predicates at
  finite precision. The interval-arithmetic certification strategy in
  [`reports/exploratory/A198683-report-2.md`](reports/exploratory/A198683-report-2.md)
  is the route to a rigorous answer.

This README does not declare either `2919` or `2926` to be authoritative. It
records that the structural cause of the disagreement is the Python script's
`abs_eps` floor, not a deep branch-choice ambiguity.

## Directory Layout

- [`computations/`](computations/README.md) contains executable checks and
  scripts.
- [`reports/`](reports/README.md) contains historical and exploratory writeups.
- [`data/`](data/README.md) contains generated tabular data.
- [`sources/`](sources/README.md) contains downloaded or extracted source
  references used by the reports.

## Reading Order

1. Read this file for the current-state map and the contradiction summary.
2. Read [`reports/README.md`](reports/README.md) before treating any individual
   report as evidence.
3. Inspect [`computations/README.md`](computations/README.md) when rerunning or
   comparing the Python and Wolfram computations.
4. Use [`sources/README.md`](sources/README.md) to locate the OEIS snapshot,
   Schoenfield table, and Guy-Selfridge paper assets.
