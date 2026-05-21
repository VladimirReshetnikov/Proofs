# A198683 Reports

- Status: Informational, clarified-conflict index with two root-cause analyses and one feasibility study
- Audience: Maintainers, OEIS contributors, and future agents
- Scope: Historical and exploratory reports about OEIS A198683
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T03:59:13Z
- Repository HEAD: f17b75114d0553b54fde626b9d9e325cf0f9eb4a

This directory preserves reports about A198683. Some reports make mutually
incompatible claims about `A198683(12)`. The corpus keeps those reports
adjacent, and two independently prepared root-cause reports (described below)
explain why they disagree. Read at least one root-cause report before citing
either of the result reports.

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
terms and on `5139` pairwise candidate powers at `n=12`; the old disagreement
is whether seven additional equalities should be recognized. Both root-cause
passes below conclude that the Python-side extra merges are not certified
equalities.

## Root-Cause Reports

Two follow-up reports were prepared independently and in parallel. They reach
the same substantive conclusion via different diagnostics, and they take
slightly different stances on whether to treat `2926` as a recommended value.
Both are preserved.

- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  uses a **precision-sweep** diagnostic. Rerunning the Python script beyond
  the original precision window changes the result from `2919` upward
  (`2920` at `--dps 800`, `2921` at `1000`, `2922` through `2000`, and `2924`
  at `3000`), which identifies the `2919` plateau as a numerical-clustering
  artifact. It takes the bottom-line position that `2919` is *invalidated*
  and `2926` is *the strongest recorded local value*.
- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  uses a **tolerance-policy** diagnostic. It isolates the disagreement to
  three structurally-degenerate clusters of candidate values (near `0`, near
  `i^i = e^(-pi/2)`, near `1`) and shows that the dominant cause is the
  `abs_eps` floor in Python's `mpmath.almosteq` policy, not a branch-choice
  or wrap-integer ambiguity. Setting `abs_eps = 0` in the Python dedup at the
  `n=12` stage raises the count from `2919` to `2925`, recovering six of the
  seven missing classes. The remaining single-class gap lives in the
  "near `i^i`" and "near `1`" clusters and cannot be settled without
  proof-quality interval arithmetic. This report keeps a strictly neutral
  stance: `2925`, `2926`, and `2927` are *all* heuristics, and it declines
  to declare either historical number authoritative.

The two stances are not in direct contradiction; they differ only in how
cautious they are about treating `2926` as the recommended value pending a
formal certificate.

## Forward-Looking Feasibility Studies

- [`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md)
  evaluates whether the in-repo `src/Numerics/python` (`numerics`) package
  can serve as the sound real-line interval-arithmetic engine for a certified
  evaluation of `A198683(12)`, per the strategy in
  [`exploratory/A198683-report-2.md`](exploratory/A198683-report-2.md). The
  verdict is *yes, with three well-scoped engine extensions* (a `pi` constant,
  `sin` / `cos` on bounded ground intervals, and a complex-interval wrapper)
  plus an application-layer `i^Z`-form pipeline that replaces `mpmath.almosteq`
  with the tri-valued `numerics.equal`. The report sizes the work in LoC,
  explains why `numerics`'s soundness contract structurally excludes the
  silent-merge artefact identified by the two root-cause reports above, and
  describes how the residual `near-i^i` / `near-1` clusters would surface as
  explicit `UndecidableCluster` events rather than being collapsed.

Note: rerunning the Python computation with much larger `--dps` increases the
reported value (e.g. `2919` at `--dps 260`, `2924` at `--dps 3000`/`8000`). That
means the `2919` conclusion is precision-dependent and should be treated as a
historical artifact of the low-hundreds precision regime, not a settled value.

## Exploratory Reports

[`exploratory/`](exploratory/README.md) contains generated explanatory reports
that discuss the sequence, the `2919` vs `2926` historical dispute, and possible
certification strategies. They predate the root-cause reports and do not
contain a completed proof-quality resolution.
