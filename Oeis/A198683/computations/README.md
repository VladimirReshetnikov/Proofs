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

Use the precision settings documented by the result reports when treating output
as evidence. Lower-precision runs are useful only as path smoke tests; for
example, `--dps 80 --n 11` undercounts the accepted `n=11` value in this checkout.
