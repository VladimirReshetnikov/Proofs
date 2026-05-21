# OEIS A198683 Research Corpus

- Status: Informational, clarified-conflict index
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Local artifacts for OEIS A198683 and the disputed value of `A198683(12)`
- Created (UTC): 2026-05-21T00:59:34Z
- Repository HEAD: aa49ba4ec1370dbbaf8b3228f8b2c085b72ed5df

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
either `2919` or `2926`. A root-cause pass on 2026-05-21 clarified why the
preserved local reports disagreed: the `2919` report used finite-precision
mpmath clustering and found only a low-precision plateau; higher-precision
reruns drift upward. The `2926` report remains the strongest recorded local
result because it uses the OEIS-style exact Wolfram Language recurrence with
`Union[..., SameTest -> Equal]`.

Two later local investigations both reproduce the accepted values through
`n=11` and both use the dynamic-programming recurrence over distinct lower-level
sets, giving `5139` pairwise candidate powers at `n=12`. They disagree about
how those candidates should be deduplicated:

| Report | Method | Reported `A198683(12)` | Nature of the disagreement |
|---|---|---:|---|
| [`reports/a198683-n12-python-mpmath-2919.md`](reports/a198683-n12-python-mpmath-2919.md) | Python `mpmath`, scale-invariant numerical buckets, `almosteq`, and one special overflow bucket | 2919 | Historical finite-precision result. The claimed plateau breaks at higher precision (`2919 -> 2920 -> 2921 -> 2922 -> 2924` in local reruns), so it should not be cited as exact evidence. |
| [`reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md) | Wolfram Language recurrence using `Union[..., SameTest -> Equal]` through the local Tungsten runner | 2926 | Strongest recorded local result. It is exact with respect to Wolfram's symbolic equality engine, but it is not a standalone proof certificate independent of Wolfram. |
| [`reports/a198683-n12-contradiction-root-cause__9e7681d48134.md`](reports/a198683-n12-contradiction-root-cause__9e7681d48134.md) | Follow-up root-cause analysis | N/A | Explains that the contradiction comes from the Python report's approximate equality heuristic, not from the recurrence, candidate count, or OEIS definition. |

The contradiction is therefore not about the OEIS definition, the lower terms,
or the number of generated `n=12` candidate powers. It is about equality
certification for a small number of candidate classes under principal complex
power semantics, in the presence of extreme intermediate magnitudes and branch
choice sensitivity.

This README is no longer a neutral "either value may be right" index. It
preserves the conflicting reports, but the local evidence now invalidates `2919`
as a finite-precision artifact. Treat `2926` as the best recorded local value
while keeping the caveat that a formal independent certificate has not yet been
added to this corpus.

## Directory Layout

- [`computations/`](computations/README.md) contains executable checks and
  scripts.
- [`reports/`](reports/README.md) contains historical and exploratory writeups.
- [`data/`](data/README.md) contains generated tabular data.
- [`sources/`](sources/README.md) contains downloaded or extracted source
  references used by the reports.

## Reading Order

1. Read this file for the current-state map and the contradiction summary.
2. Read [`reports/README.md`](reports/README.md) and the root-cause report
   before treating any individual result report as evidence.
3. Inspect [`computations/README.md`](computations/README.md) when rerunning or
   comparing the Python and Wolfram computations.
4. Use [`sources/README.md`](sources/README.md) to locate the OEIS snapshot,
   Schoenfield table, and Guy-Selfridge paper assets.
