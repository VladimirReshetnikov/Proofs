# A198683 Reports

- Status: Informational, clarified-conflict index
- Audience: Maintainers, OEIS contributors, and future agents
- Scope: Historical and exploratory reports about OEIS A198683
- Created (UTC): 2026-05-21T00:59:34Z
- Repository HEAD: aa49ba4ec1370dbbaf8b3228f8b2c085b72ed5df

This directory preserves reports about A198683. Some reports make mutually
incompatible claims about `A198683(12)`. The corpus keeps those reports adjacent,
but the current interpretation is no longer symmetric: the `2919` result is now
understood as a finite-precision mpmath deduplication artifact, while the `2926`
result is the strongest recorded local computation.

Read
[`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
before citing either result report.

## Result Reports

- [`a198683-n12-python-mpmath-2919.md`](a198683-n12-python-mpmath-2919.md)
  historically concluded `A198683(12) = 2919`. It uses Python `mpmath`,
  numerical bucketing, `almosteq`, and special handling for one candidate that
  cannot be materialized as a normal bigfloat complex value. Higher-precision
  reruns invalidate the claimed precision plateau, so this report is preserved
  as a cautionary finite-precision experiment rather than as exact evidence.
- [`a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
  concludes `A198683(12) = 2926`. It extends the OEIS Wolfram Language recurrence
  to `n=12` and uses Wolfram `Equal` as the equality test through `Union`.
  This is the strongest recorded local result, while still not being a formal
  certificate independent of Wolfram's equality engine.

The numerical difference is seven classes. Both reports agree on the lower
terms and on `5139` pairwise candidate powers at `n=12`; the old disagreement is
whether seven additional equalities should be recognized. The root-cause pass
shows that the Python-side extra merges are not certified equalities.

## Root-Cause Report

- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  records the current explanation. Rerunning the Python script beyond the
  original precision window changes the result from `2919` to larger counts
  (`2920`, `2921`, `2922`, and `2924` in the recorded checks), which identifies
  the `2919` conclusion as a numerical-clustering artifact.

## Exploratory Reports

[`exploratory/`](exploratory/README.md) contains generated explanatory reports
that discuss the sequence, the `2919` vs `2926` historical dispute, and possible
certification strategies. They predate the root-cause report and do not contain
a completed proof-quality resolution.
