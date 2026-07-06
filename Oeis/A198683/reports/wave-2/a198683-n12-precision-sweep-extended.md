# A198683(12) Extended Precision-Sweep Diagnostic

- Status: Root-cause analysis (wave-2; third independent pass)
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: Diagnose the historical `2919` vs `2926` disagreement on `A198683(12)` by sweeping the Python/`mpmath` script's working precision over a wider range than the earlier wave-2 reports, and record the stabilisation behaviour
- Created (UTC): 2026-05-21T14:43:25Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55
- Source branch: `investigate-5.2` (commit `d4a921cee`)

## Summary

This is the third independent root-cause pass on the historical "`A198683(12)`
is either `2919` or `2926`" note. It complements the two earlier wave-2
analyses:

- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  — precision sweep up to `--dps 3000`.
- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  — tolerance-policy mechanism (`abs_eps = rel_eps` floor in `mp.almosteq`).

It agrees with both on the substantive findings: same recurrence, same `5139`
candidate powers at `n=12`, divergence localised in Python's deduplication
heuristic, neither pipeline a proof. Its distinctive contribution is to push
the precision sweep further (up to `--dps 8000`) and to record where the
Python output **stabilises** before reaching the Wolfram count:

| `--dps` | `compute_a198683.py` `a(12)` |
|---:|---:|
| 260  | 2919 |
| 600  | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 3000 | 2924 |
| 8000 | 2924 |

The Python heuristic stabilises at `2924`, two classes short of the Wolfram
`2926` (and one class short of the `2925` that
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
reaches by setting `abs_eps = 0` at `n = 12`). The residue is not closed by
more precision alone.

This report takes a strictly **cautious** bottom-line stance: `2919` is a
finite-precision artefact, but `2926` is not a proof either; the remaining
work is proof-quality equality certification for a small handful of
near-collision candidates.

## Setup and reproduction

The runs use the same Python script preserved at
[`../computations/python/compute_a198683.py`](../../computations/python/compute_a198683.py),
including the `sys.set_int_max_str_digits(0)` guard added by this pass —
high-precision runs would otherwise trip CPython's `int <-> str` digit limit
when formatting the overflow-exponent sample for diagnostics.

```powershell
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 260  --n 12
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 600  --n 12
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 1000 --n 12
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 1200 --n 12
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 3000 --n 12
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 8000 --n 12
```

Each invocation prints a single JSON-style record whose `a12` field is the
column reported above. The `candidate_total` field is `5139` in every run,
confirming that the recurrence and candidate generation are unaffected by
working precision; only the deduplication output changes.

## Why the local conflict is not a recurrence disagreement

Both pipelines — the Python `mpmath` recurrence and the Wolfram Language
recurrence under the local Tungsten runner — agree on every structural
quantity:

- Same OEIS principal-power semantics, `z^w := Exp[w Log[z]]`.
- Same dynamic-programming recurrence over distinct lower-level sets.
- Same lower-term counts through `n = 11`: `1, 1, 2, 3, 7, 15, 34, 77, 187,
  462, 1152`.
- Same `5139` pairwise candidate powers at `n = 12`.

The divergence appears only in the **equality test** applied to those
`5139` candidates:

- The Wolfram side uses exact Wolfram Language expressions and
  `Union[..., SameTest -> Equal]`. `Equal` for inexact complex numbers is
  precision-aware and does not introduce a tolerance floor.
- The Python side evaluates candidates as `mpmath` bigfloat complex numbers
  and deduplicates with a scale-invariant bucketed call to
  `mp.almosteq(z1, z2, rel_eps=cmp_tol, abs_eps=cmp_tol)`, plus a special
  "overflow bucket" for the single candidate whose magnitude cannot be
  materialised as a normal bigfloat complex value.

At `n = 12`, a handful of candidates live in knife-edge regimes — extreme
intermediate magnitudes and branch-cut-sensitive arguments. In that setting
*finite-precision* numerical evaluation can make distinct values
indistinguishable, so any numerical deduplicator can accidentally merge
classes.

## Evidence: the Python `2919` is a precision artefact

The original Python report validated stability only for `--dps` in the
"low-hundreds" range (`160`, `180`, `220`, `260`). The extended sweep above
breaks that plateau and shows that the count *increases* as precision rises:

- The first jump (`2919 -> 2920`) appears between `--dps 260` and `--dps 600`.
- The count rises monotonically through `2921`, `2922`, `2924` and then
  stabilises at `2924` from `--dps 3000` upward (verified at `--dps 8000`).
- A true exact equality count cannot rise monotonically under additional
  working precision; what we are observing is the dedup heuristic releasing
  previously-fused candidate classes as the comparison tolerance shrinks.

So the historical `2919` is best understood as a **lower bound produced by an
insufficient-precision numerical equality heuristic**, not as a settled value.
This conclusion matches what
[`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
already reports for the `--dps 180..3000` window; the present pass confirms it
holds at `--dps 8000` and locates the Python ceiling at `2924`.

## Why even `2926` is not a proof

The Wolfram side's `2926` is the strongest single-source local computation in
the corpus, but it is not a standalone proof certificate. Its correctness
rests on Wolfram Language's symbolic equality engine — the `Equal` semantics
used by `Union[..., SameTest -> Equal]` — applied at the local Wolfram
version's working precision. The corpus has no independent certificate that
the Wolfram engine's verdicts are correct on the specific near-collision
candidates that the Python heuristic misses.

The remaining gap between Python's `2924` ceiling and Wolfram's `2926` is
two classes. These two classes (together with the residue between `2925`
and `2926` that the tolerance-policy diagnostic in
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
identifies and assigns to "near-`i^i`" and "near-`1`" clusters) are exactly
the kind of small structural ambiguity that no amount of additional
finite-precision numerical work can settle.

## What is still missing

The natural next step for the corpus is the **proof-quality** equality check
called for by
[`exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md): interval
arithmetic with outward rounding, branch-cut-aware complex evaluation, and a
tri-valued equality predicate (proves equality, proves disequality, or refines
precision and reports residual undecidable clusters).

This pass does not provide that engine. It records, more sharply than
previously, where the Python heuristic's ceiling lies and how far it is from
the Wolfram result, so that a future certified pipeline knows the size of
the residue it needs to resolve.

## Diff to the existing script

The investigate-5.2 work touches `compute_a198683.py` with two small but
important changes that are now part of the merged script:

1. The script's docstring is rewritten to flag it as a finite-precision
   diagnostic rather than a certificate, and to record the
   precision-dependence of the `n = 12` count.
2. The `main()` function calls `sys.set_int_max_str_digits(0)` when the
   attribute is available, so high-precision runs can format the
   overflow-exponent sample without tripping CPython's int-string
   conversion limit. A `try / except ValueError` guards the `mp.nstr` call
   for the same reason.

These changes do not alter the recurrence, the candidate generation, or
the `_dedupe_mpc` policy. They only make the high-precision runs that
produced the sweep above reproducible without diagnostic-side crashes.

## Comparison with the other two wave-2 reports

| Aspect | precision-sweep (5.5) | tolerance-policy (cc) | this pass (5.2) |
|---|---|---|---|
| Diagnostic style | Black-box precision sweep | White-box tolerance policy | Black-box precision sweep, extended |
| `--dps` range probed | 180 - 3000 | 260 (single point, plus diagnostic scripts) | 260 - 8000 |
| Highest Python `a(12)` observed | 2924 (at 3000) | 2925 (with `abs_eps = 0` at n=12) | 2924 (stable from 3000 to 8000) |
| Mechanism named | "Finite-precision merge heuristic" | Specific `abs_eps` floor in `mp.almosteq` | "Numerical equality heuristic" |
| Structural cluster analysis | None | Near-zero / near-`i^i` / near-`1` | None |
| Diagnostic scripts added | None | Six `diagnose_*.py` scripts | Script docstring + `int_max_str_digits` guard |
| Bottom-line stance | `2919` *invalidated*, `2926` *strongest recorded local value* | Strictly neutral: `2925`, `2926`, `2927` are all heuristics | Cautious: `2919` invalidated, `2926` not a proof either, need certified arithmetic |

The three passes converge on the same substantive picture. They differ in
how aggressively they recommend treating `2926` as a working answer.

## References

- [`a198683-n12-python-mpmath-2919.md`](../wave-1/a198683-n12-python-mpmath-2919.md)
  — the wave-1 Python result report whose `2919` claim this pass refutes.
- [`a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](../wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
  — the wave-1 Wolfram result report whose `2926` claim this pass leaves
  standing as the strongest recorded local computation, while declining to
  treat it as a proof.
- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  — the sibling wave-2 precision-sweep diagnostic.
- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  — the sibling wave-2 tolerance-policy diagnostic.
- [`exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md)
  — the certification strategy this corpus has not yet executed.
- [`../../computations/python/compute_a198683.py`](../../computations/python/compute_a198683.py)
  — the script whose output produced the sweep above.
