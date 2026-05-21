# A198683 Computations

- Status: Informational
- Audience: Maintainers and future agents rerunning A198683 checks
- Scope: Executable computation artifacts for the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Repository HEAD: aa49ba4ec1370dbbaf8b3228f8b2c085b72ed5df

This directory contains executable artifacts used by the conflicting `n=12`
reports. The scripts are preserved because their behavior is part of the
evidence trail; the corpus README remains the current-state authority for the
fact that their conclusions disagree.

## Contents

- [`python/compute_a198683.py`](python/compute_a198683.py) is the Python
  `mpmath` computation used by the report that concludes `2919`.
- [`wolfram/a198683-n12-check__2026-05-20.wl`](wolfram/a198683-n12-check__2026-05-20.wl)
  is the Wolfram Language check used by the report that concludes `2926`.

## Known Comparison Point

Both computations agree on the accepted values through `n=11` and on `5139`
candidate powers produced from distinct lower-level sets at `n=12`. The
remaining disagreement is how equality among the resulting `n=12` candidates is
certified or inferred.

## Precision sensitivity (Python)

The Python computation is *not* a pure “exact recurrence”: it evaluates each
candidate as an arbitrary-precision `mpmath` bigfloat and deduplicates using a
numerical equality heuristic (`almosteq`). Because `n=12` contains near-collision
cases with extreme intermediate magnitudes, the reported `a(12)` depends on the
chosen precision (`--dps`).

Observed outputs from `python/compute_a198683.py` (same checkout, same code,
different `--dps`):

| `--dps` | `a(12)` |
|---:|---:|
| 260 | 2919 |
| 600 | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 3000 | 2924 |
| 8000 | 2924 |

This is why the `2919` report should be treated as a historical lower-bound
artifact, not a resolved value.

Use the precision settings documented by the result reports when treating output
as evidence. Lower-precision runs are useful only as path smoke tests; for
example, `--dps 80 --n 11` undercounts the accepted `n=11` value in this checkout.
