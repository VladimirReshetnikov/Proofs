# A198683 Reports

- Status: Informational, unresolved-conflict index with root-cause analysis
- Audience: Maintainers, OEIS contributors, and future agents
- Scope: Historical and exploratory reports about OEIS A198683
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T02:27:23Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

This directory preserves reports about A198683. Some reports make mutually
incompatible claims about `A198683(12)`. The contradiction itself is preserved,
but a separate root-cause report identifies where in the candidate space the
disagreement actually lives.

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

## Root-Cause Diagnostic

- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  isolates the disagreement to three structurally-degenerate clusters of
  candidate values (near `0`, near `i^i = e^(-pi/2)`, near `1`) and shows that
  the dominant cause is the `abs_eps` floor in Python's `mpmath.almosteq`
  policy, not a branch-choice or wrap-integer ambiguity. Setting `abs_eps = 0`
  in the Python dedup at the `n=12` stage raises the reported count from
  `2919` to `2925`, recovering six of the seven missing classes. The remaining
  single-class gap lives in the "near `i^i`" and "near `1`" clusters and
  cannot be settled without proof-quality interval arithmetic.

## Exploratory Reports

[`exploratory/`](exploratory/README.md) contains generated explanatory reports
that discuss the sequence, the `2919` vs `2926` historical dispute, and possible
certification strategies. They do not contain a completed proof-quality
resolution.
