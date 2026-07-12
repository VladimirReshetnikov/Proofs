# A198683 Computations

- Status: Informational
- Audience: Maintainers and future agents rerunning A198683 checks
- Scope: Executable computation artifacts for the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

This directory contains executable artifacts used by the wave-1 `n=12`
result reports and the wave-2 root-cause analyses. The scripts are
preserved because their behavior is part of the evidence trail; the corpus
README, the wave-3 synthesis, and the three wave-2 root-cause reports
remain the current-state authority for interpreting their conclusions.

## Contents

### Production scripts

- [`python/compute_a198683.py`](python/compute_a198683.py) is the Python
  `mpmath` computation used by the historical report that concludes `2919`.
  Treat it as a finite-precision diagnostic, not as a certified solver: reruns
  above the original precision window change the reported `n=12` count.
- [`wolfram/a198683-n12-check__2026-05-20.wl`](wolfram/a198683-n12-check__2026-05-20.wl)
  is the Wolfram Language check used by the report that concludes `2926`.

### Diagnostic scripts

These were added by [`reports/wave-2/a198683-n12-discrepancy-root-cause.md`](../reports/wave-2/a198683-n12-discrepancy-root-cause.md)
to isolate the 7-class gap between `2919` and `2926`. They are non-production
diagnostics and only meaningful in conjunction with that report.

- [`python/diagnose_dedup.py`](python/diagnose_dedup.py) — runs both the
  Python value-space dedup and a canonical-exponent dedup, and prints the
  partition refinement between them.
- [`python/diagnose_pairs.py`](python/diagnose_pairs.py) — for the three
  disputed Python equivalence classes, prints per-candidate `(Re(e), Im(e))`
  exponent data and pairwise `|dRe|, dIm mod 2pi` differences.
- [`python/diagnose_tol.py`](python/diagnose_tol.py) — sweeps the
  `(rel_eps, abs_eps)` tolerance pair at the `n=12` dedup stage; demonstrates
  the `2919 -> 2925` jump on `abs_eps = 0`.
- [`python/diagnose_naive.py`](python/diagnose_naive.py) — a naive `O(N^2)`
  canonical-exponent dedup; useful as a structural cross-check (and as a
  witness that strict canonical-form comparison without interval arithmetic
  over-splits).
- [`python/diagnose_tol_simple.py`](python/diagnose_tol_simple.py) — sweeps
  `abs_eps` at all levels (including `n <= 11`), to confirm the effect is
  localised to the `n = 12` stage.
- [`python/diagnose_levels.py`](python/diagnose_levels.py) — checks that
  `|V[n]|` for `n <= 11` is unaffected by the `abs_eps` policy.
- [`python/diagnose_overflow_magnitude.py`](python/diagnose_overflow_magnitude.py)
  — reads the retained `n = 12` candidate TSV and reports that the overflow
  singleton `idx=57` is the only row with an astronomically negative displayed
  `Re(e)` signature.
- [`python/trace_dp_expression.py`](python/trace_dp_expression.py) — re-runs
  the dynamic-programming recurrence while carrying representative expression
  strings, useful for identifying the lower-level expression behind a retained
  value index such as `values[11][57]`.

## Known Comparison Point

Both production computations agree on the accepted values through `n=11` and on
`5139` candidate powers produced from distinct lower-level sets at `n=12`. The
remaining issue is how equality among the resulting `n=12` candidates is
certified or inferred. The three independent wave-2 root-cause passes
diagnose this from different angles:

- The precision-sweep diagnostic
  ([`../reports/wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md`](../reports/wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md))
  observes that the Python script reports `2919` through `--dps 500` and
  then drifts upward at higher precision (`2920` at `800`, `2921` at `1000`,
  `2922` through `2000`, and `2924` at `3000`).
- The tolerance-policy diagnostic
  ([`../reports/wave-2/a198683-n12-discrepancy-root-cause.md`](../reports/wave-2/a198683-n12-discrepancy-root-cause.md))
  attributes most of the gap to the `abs_eps` floor in Python's
  `mpmath.almosteq` policy and shows that setting `abs_eps = 0` at the `n=12`
  stage raises the count from `2919` to `2925`.
- The extended precision-sweep diagnostic
  ([`../reports/wave-2/a198683-n12-precision-sweep-extended.md`](../reports/wave-2/a198683-n12-precision-sweep-extended.md))
  extends the sweep further and finds the Python output stabilises at
  `2924` from `--dps 3000` upward:

| `--dps` | `a(12)` |
|---:|---:|
| 260 | 2919 |
| 600 | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 3000 | 2924 |
| 8000 | 2924 |

`2924` is *still* below the Wolfram `2926`. The remaining gap is the
residue that requires proof-quality interval arithmetic, not more precision.
See
[`../reports/wave-3/a198683-post-wave2-synthesis.md`](../reports/wave-3/a198683-post-wave2-synthesis.md)
for the consolidated post-wave-2 picture.

Use the precision settings documented by the result reports only to reproduce
historical behavior; they are not enough to certify `A198683(12)`.
Lower-precision runs are useful only as path smoke tests; for example,
`--dps 80 --n 11` undercounts the accepted `n=11` value in this checkout.
