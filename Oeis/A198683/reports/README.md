# A198683 Reports

- Status: Informational, unresolved-conflict index
- Audience: Maintainers, OEIS contributors, and future agents
- Scope: Historical and exploratory reports about OEIS A198683
- Created (UTC): 2026-05-21T00:59:34Z
- Repository HEAD: aa49ba4ec1370dbbaf8b3228f8b2c085b72ed5df

This directory preserves reports about A198683. Some reports make mutually
incompatible claims about `A198683(12)`. The contradiction is intentional in the
corpus: this consolidation records it and keeps the evidence adjacent, without
choosing a winner.

## Result Reports

- [`a198683-n12-python-mpmath-2919.md`](a198683-n12-python-mpmath-2919.md)
  concludes `A198683(12) = 2919`. It uses Python `mpmath`, numerical bucketing,
  `almosteq`, and special handling for one candidate that cannot be materialized
  as a normal bigfloat complex value.
- [`a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
  concludes `A198683(12) = 2926`. It extends the OEIS Wolfram Language recurrence
  to `n=12` and uses Wolfram `Equal` as the equality test through `Union`.

The numerical difference is seven classes. Both reports agree on the lower
terms and on `5139` pairwise candidate powers at `n=12`; they disagree over
whether seven additional equalities should be recognized.

Note: rerunning the Python computation with much larger `--dps` increases the
reported value (e.g. `2919` at `--dps 260`, `2924` at `--dps 3000`/`8000`). That
means the `2919` conclusion is precision-dependent and should be treated as a
historical artifact of the low-hundreds precision regime, not a settled value.

## Exploratory Reports

[`exploratory/`](exploratory/README.md) contains generated explanatory reports
that discuss the sequence, the `2919` vs `2926` historical dispute, and possible
certification strategies. They do not contain a completed proof-quality
resolution.
