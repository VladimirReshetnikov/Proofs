# A198683 Computations

- Status: Informational
- Audience: Maintainers and future agents rerunning A198683 checks
- Scope: Executable computation artifacts for the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T02:27:23Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

This directory contains executable artifacts used by the conflicting `n=12`
reports. The scripts are preserved because their behavior is part of the
evidence trail; the corpus README and the two root-cause reports remain the
current-state authority for interpreting their conclusions.

## Contents

### Production scripts

- [`python/compute_a198683.py`](python/compute_a198683.py) is the Python
  `mpmath` computation used by the historical report that concludes `2919`.
  Treat it as a finite-precision diagnostic, not as a certified solver: reruns
  above the original precision window change the reported `n=12` count.
- [`wolfram/a198683-n12-check__2026-05-20.wl`](wolfram/a198683-n12-check__2026-05-20.wl)
  is the Wolfram Language check used by the report that concludes `2926`.

### Diagnostic scripts

These were added by [`reports/a198683-n12-discrepancy-root-cause.md`](../reports/a198683-n12-discrepancy-root-cause.md)
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

## Known Comparison Point

Both production computations agree on the accepted values through `n=11` and on
`5139` candidate powers produced from distinct lower-level sets at `n=12`. The
remaining issue is how equality among the resulting `n=12` candidates is
certified or inferred. Two independent root-cause passes diagnose this from
different angles:

- The precision-sweep diagnostic
  ([`../reports/a198683-n12-contradiction-root-cause__9e7681d48134.md`](../reports/a198683-n12-contradiction-root-cause__9e7681d48134.md))
  observes that, in local reruns, the Python script reports `2919` through
  `500` decimal digits and then drifts upward at higher precision (`2920` at
  `800`, `2921` at `1000`, `2922` through `2000`, and `2924` at `3000`).
- The tolerance-policy diagnostic
  ([`../reports/a198683-n12-discrepancy-root-cause.md`](../reports/a198683-n12-discrepancy-root-cause.md))
  attributes most of the gap to the `abs_eps` floor in Python's
  `mpmath.almosteq` policy and shows that setting `abs_eps = 0` at the `n=12`
  stage raises the count from `2919` to `2925`.

A third independent precision-sweep diagnostic (also using
`compute_a198683.py`) extended the sweep further:

| `--dps` | `a(12)` |
|---:|---:|
| 260 | 2919 |
| 600 | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 3000 | 2924 |
| 8000 | 2924 |

The Python output stabilises at `2924` somewhere between `--dps 2000` and
`8000`, but `2924` is *still* below the Wolfram `2926`. The remaining gap is
the residue that requires proof-quality interval arithmetic, not more
precision.

Use the precision settings documented by the result reports only to reproduce
historical behavior; they are not enough to certify `A198683(12)`.
Lower-precision runs are useful only as path smoke tests; for example,
`--dps 80 --n 11` undercounts the accepted `n=11` value in this checkout.
