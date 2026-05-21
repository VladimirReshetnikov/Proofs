# OEIS A198683 Research Corpus

- Status: Informational, clarified-conflict index with feasibility study for a certified pipeline
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Local artifacts for OEIS A198683 and the disputed value of `A198683(12)`
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T03:59:13Z
- Repository HEAD: f17b75114d0553b54fde626b9d9e325cf0f9eb4a

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
| [`reports/a198683-n12-python-mpmath-2919.md`](reports/a198683-n12-python-mpmath-2919.md) | Python `mpmath`, scale-invariant numerical buckets, `almosteq`, and one special overflow bucket | 2919 | Historical finite-precision result. The claimed plateau breaks at higher precision (`2919 -> 2920 -> 2921 -> 2922 -> 2924` in local reruns at `--dps` up to `8000`), so it should not be cited as exact evidence. |
| [`reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](reports/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md) | Wolfram Language recurrence using `Union[..., SameTest -> Equal]` through the local Tungsten runner | 2926 | Strongest recorded local result. It is exact with respect to Wolfram's symbolic equality engine, but it is not a standalone proof certificate independent of Wolfram. |
| [`reports/a198683-n12-contradiction-root-cause__9e7681d48134.md`](reports/a198683-n12-contradiction-root-cause__9e7681d48134.md) | Follow-up root-cause analysis (precision-sweep diagnostic) | N/A | Reruns the Python script at higher precision (`180 -> 3000` decimal digits) and shows the `2919` count drifts upward to `2924`, identifying the original `2919` plateau as a finite-precision merge artifact. |
| [`reports/a198683-n12-discrepancy-root-cause.md`](reports/a198683-n12-discrepancy-root-cause.md) | Follow-up root-cause analysis (tolerance-policy diagnostic) | N/A | Traces the 7-class gap to the `abs_eps = rel_eps` floor in Python's `mpmath.almosteq` call, identifies the specific eight-element "near-zero" cluster that collapses, and shows that setting `abs_eps = 0` raises the count from `2919` to `2925`. |

The contradiction is therefore not about the OEIS definition, the lower terms,
or the number of generated `n=12` candidate powers. It is about equality
certification for a small number of candidate classes under principal complex
power semantics, in the presence of extreme intermediate magnitudes and branch
choice sensitivity.

## Two Independent Root-Cause Passes

Two follow-up root-cause analyses were prepared independently and in parallel.
They agree on the substantive findings but differ in framing; both are preserved.

Shared findings (both reports):

- The recurrence, the lower-term reproduction through `n=11`, and the `5139`
  candidate-power count at `n=12` are correct in both implementations.
- The disagreement lives entirely in Python's deduplication of `n=12`
  candidates. It is not a branch-choice or wrap-integer ambiguity.
- The Python `2919` count is not a certified equality count; it is the output
  of a finite-precision merge heuristic.
- Neither implementation is a proof. A rigorous answer requires the
  interval-arithmetic certification described in
  [`reports/exploratory/A198683-report-2.md`](reports/exploratory/A198683-report-2.md).

Divergence in framing and diagnostic depth:

- [`reports/a198683-n12-contradiction-root-cause__9e7681d48134.md`](reports/a198683-n12-contradiction-root-cause__9e7681d48134.md)
  uses a black-box **precision-sweep** diagnostic. The reported count drifts
  upward (`2919 -> 2920 -> 2921 -> 2922 -> 2924`) as `--dps` rises from `500`
  to `3000`, which it offers as the diagnostic signature of an artefact. It
  ends with the bottom-line stance that `2919` is *invalidated* and `2926`
  should be treated as *the strongest recorded local value*.
- [`reports/a198683-n12-discrepancy-root-cause.md`](reports/a198683-n12-discrepancy-root-cause.md)
  uses a white-box **tolerance-policy** diagnostic. It pinpoints the
  `abs_eps = rel_eps = 10^-(dps/2)` setting in `_dedupe_mpc`'s `mp.almosteq`
  call as the structural cause: the `abs_eps` floor merges any pair of values
  with magnitude smaller than `abs_eps`, collapsing an eight-element near-zero
  cluster. Setting `abs_eps = 0` at the `n=12` stage raises the count from
  `2919` to `2925`, recovering six of the seven missing classes. The remaining
  single-class gap lives in two further small clusters near `i^i = e^(-pi/2)`
  and near `1`. This report keeps a strictly neutral stance: `2925`, `2926`,
  and `2927` are *all* heuristics, and it declines to declare either of the
  historical numbers authoritative.

The two stances are not in direct contradiction. They differ in how cautious
they are about treating `2926` as a recommended value. This README preserves
both reports rather than choosing between their bottom-line wordings.

## Forward-Looking Feasibility Study

A separate feasibility report,
[`reports/a198683-numerics-interval-feasibility.md`](reports/a198683-numerics-interval-feasibility.md),
evaluates whether the in-repo `src/Numerics/python` (`numerics`) package can
serve as the sound real-line interval-arithmetic engine for a certified
evaluation of `A198683(12)`, per
[`reports/exploratory/A198683-report-2.md`](reports/exploratory/A198683-report-2.md).
The verdict is *yes, with three well-scoped engine extensions* (a `pi`
constant, `sin` / `cos` on bounded ground intervals, and a complex-interval
wrapper) plus an application-layer `i^Z`-form pipeline that replaces
`mpmath.almosteq` with the tri-valued `numerics.equal`. That predicate
returns `True` / `False` / `Undefined` (see
`src/Numerics/python/numerics/arithmetic.py::equal`), so the silent-merge
artefact identified by both root-cause reports is structurally impossible:
overlapping intervals demand adaptive precision, never a quiet collapse.
Residual `near-i^i` / `near-1` clusters surface as explicit
`UndecidableCluster` events rather than being absorbed.

## Directory Layout

- [`computations/`](computations/README.md) contains executable checks and
  scripts.
- [`reports/`](reports/README.md) contains historical and exploratory writeups.
- [`data/`](data/README.md) contains generated tabular data.
- [`sources/`](sources/README.md) contains downloaded or extracted source
  references used by the reports.

## Reading Order

1. Read this file for the current-state map and the contradiction summary.
2. Read [`reports/README.md`](reports/README.md) and the two root-cause
   reports before treating any individual result report as evidence.
3. Inspect [`computations/README.md`](computations/README.md) when rerunning or
   comparing the Python and Wolfram computations.
4. Use [`sources/README.md`](sources/README.md) to locate the OEIS snapshot,
   Schoenfield table, and Guy-Selfridge paper assets.
