# OEIS A198683 Research Corpus

- Status: Informational, unresolved-conflict index
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
either `2919` or `2926`. The local corpus preserves the same contradiction
rather than resolving it.

Two later local investigations both reproduce the accepted values through
`n=11` and both use the dynamic-programming recurrence over distinct lower-level
sets, giving `5139` pairwise candidate powers at `n=12`. They disagree about
how those candidates should be deduplicated:

| Report | Method | Reported `A198683(12)` | Nature of the disagreement |
|---|---|---:|---|
| [`reports/a198683-n12-python-mpmath-2919.md`](reports/a198683-n12-python-mpmath-2919.md) | Python `mpmath`, scale-invariant numerical buckets, `almosteq`, and one special overflow bucket | 2919 | Precision-dependent numerical dedupe: the historical `2919` comes from low-hundreds precision; reruns at higher `--dps` increase the count (e.g. `2924` at `--dps 3000`/`8000`). |
| [`reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md) | Wolfram Language recurrence using `Union[..., SameTest -> Equal]` through the local Tungsten runner | 2926 | Exact Wolfram evaluation and equality as implemented by WL (`Equal` inside `Union`). Slow to rerun; still not a proof artifact independent of Wolfram’s symbolic engine. |

The contradiction is therefore not about the OEIS definition, the lower terms,
or the number of generated `n=12` candidate powers. It is about equality
certification for a small number of candidate classes under principal complex
power semantics, in the presence of extreme intermediate magnitudes and branch
choice sensitivity.

This README is a neutral index. It does not declare either `2919` or `2926` to
be authoritative.

## Root cause of the `2919` vs `2926` contradiction

The local conflict is not “two different recurrences” or “two different ways of
generating the `n=12` candidates”. Both pipelines:

- Use the same OEIS principal-power semantics (`z^w := Exp[w Log[z]]`).
- Use the same dynamic-programming recurrence over distinct lower-level sets.
- Agree on the lower-term counts through `n=11`.
- Agree that `n=12` produces `5139` pairwise candidate powers.

The divergence is in the **equality test** applied to those `5139` candidates:

- The Wolfram/Tungsten report uses exact Wolfram Language expressions and
  deduplicates with `Union[..., SameTest -> Equal]`.
- The Python/mpmath report evaluates candidates as arbitrary-precision
  bigfloats and deduplicates with numerical bucketing plus `mpmath.almosteq`,
  along with a special “overflow bucket” for the single unmaterializable case.

At `n=12`, a handful of candidates live in knife-edge regimes (extreme
magnitudes and branch-cut sensitivity). In that setting, *finite precision*
evaluation can make distinct values numerically indistinguishable, so any
numerical dedupe can accidentally merge classes.

### Evidence: the Python result is not stable under higher precision

The Python report validated stability only for `--dps` in the low-hundreds. If
you rerun the same script with substantially larger precision, the reported
count **increases**, meaning the `2919` claim is a precision artifact of that
workflow:

| `--dps` | `compute_a198683.py` `a(12)` |
|---:|---:|
| 260 | 2919 |
| 600 | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 3000 | 2924 |
| 8000 | 2924 |

So the historical `2919` is best viewed as a **lower bound produced by an
insufficient-precision numeric equality heuristic**, not as a settled value.

### What is still missing

Even `2926` is not a proof artifact independent of Wolfram’s symbolic engine;
it is the result returned by Wolfram Language’s exact recurrence plus
`Union[..., SameTest -> Equal]` under the local WL version. The remaining work,
if the goal is to actually resolve the OEIS dispute, is a **proof-quality**
equality check for the remaining near-collision candidates (e.g., interval
arithmetic / certified bounds that can decide each of the few hard
equalities/inequalities without relying on a specific CAS).

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
