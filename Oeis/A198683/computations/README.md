# A198683 Computations

- Status: Informational
- Audience: Maintainers and future agents rerunning A198683 checks
- Scope: Executable computation artifacts for the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Repository HEAD: aa49ba4ec1370dbbaf8b3228f8b2c085b72ed5df

This directory contains executable artifacts used by the conflicting `n=12`
reports. The scripts are preserved because their behavior is part of the
evidence trail; the corpus README and the root-cause report remain the
current-state authority for interpreting their conclusions.

## Contents

- [`python/compute_a198683.py`](python/compute_a198683.py) is the Python
  `mpmath` computation used by the historical report that concludes `2919`.
  Treat it as a finite-precision diagnostic, not as a certified solver: reruns
  above the original precision window change the reported `n=12` count.
- [`wolfram/a198683-n12-check__2026-05-20.wl`](wolfram/a198683-n12-check__2026-05-20.wl)
  is the Wolfram Language check used by the report that concludes `2926`.

## Known Comparison Point

Both computations agree on the accepted values through `n=11` and on `5139`
candidate powers produced from distinct lower-level sets at `n=12`. The
remaining issue is how equality among the resulting `n=12` candidates is
certified or inferred.

Use the precision settings documented by the result reports only to reproduce
historical behavior. They are not enough to certify `A198683(12)`. In local
reruns, the Python script reports `2919` through `500` decimal digits, then
drifts upward at higher precision (`2920` at `800`, `2921` at `1000`, `2922`
through `2000`, and `2924` at `3000`). Lower-precision runs are useful only as
path smoke tests; for example, `--dps 80 --n 11` undercounts the accepted `n=11`
value in this checkout.

See
[`../reports/a198683-n12-contradiction-root-cause__9e7681d48134.md`](../reports/a198683-n12-contradiction-root-cause__9e7681d48134.md)
for the detailed interpretation.
