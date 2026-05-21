# A198683 Computations

- Status: Informational
- Audience: Maintainers and future agents rerunning A198683 checks
- Scope: Executable computation artifacts for the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T02:27:23Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

This directory contains executable artifacts used by the conflicting `n=12`
reports. The scripts are preserved because their behavior is part of the
evidence trail.

## Contents

### Production scripts

- [`python/compute_a198683.py`](python/compute_a198683.py) is the Python
  `mpmath` computation used by the report that concludes `2919`.
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

Both production computations agree on the accepted values through `n=11` and
on `5139` candidate powers produced from distinct lower-level sets at `n=12`.
The remaining disagreement is how equality among the resulting `n=12`
candidates is certified or inferred; the root-cause report attributes most of
the gap to the `abs_eps` floor in Python's `mpmath.almosteq` policy.

Use the precision settings documented by the result reports when treating output
as evidence. Lower-precision runs are useful only as path smoke tests; for
example, `--dps 80 --n 11` undercounts the accepted `n=11` value in this checkout.
