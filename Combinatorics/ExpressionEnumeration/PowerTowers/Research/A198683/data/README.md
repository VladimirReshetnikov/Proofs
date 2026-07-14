# A198683 Data

- Status: Informational
- Audience: Maintainers and future agents
- Scope: Generated tabular data retained with the A198683 corpus
- Created (UTC): 2026-05-21T00:59:34Z
- Last updated (UTC): 2026-05-21T15:59:06Z
- Repository HEAD: 7b5b6d04cad0d1c99826f8fc0fe7ec9b9b2b407d

This directory contains generated data used for local A198683 research.

## Contents

- [`oeis_a198683_n_up_to_11.csv`](oeis_a198683_n_up_to_11.csv) is a table of
  parenthesized expressions and numerical values through `n=11`. It supports
  lower-term comparison and exploratory analysis, but it does not settle the
  disputed `n=12` value.
- [`a198683-n12-equivalence-classes.txt`](a198683-n12-equivalence-classes.txt)
  is a Schoenfield-style equivalence-class extension to `n=12`. It lists
  all **5139** candidate powers, grouped into a **probe-refined**
  partition with **2926 classes** — matching the Wolfram count. The
  partition starts from the 2925 strict-policy classes (value-space dedup
  with `abs_eps = 0`, the wave-2 `cc` fix) and refines each tentative
  class by multi-precision probing at dps ∈ {260, 500, 1000}:
    - Cluster C `{25, 1404, 4239}` **splits** into `{25}` and
      `{1404, 4239}` (because `diff_Re(e_25, e_1404) = 2.306566301e-1305`
      is stable across all probed dps — algebraic, not noise).
    - Cluster B (14 candidates near `i^i = e^(-π/2)`) stays merged
      (pairwise differences shrink ~`10^-dps` with precision — noise).
    - Cluster A doubleton `{2207, 3777}` stays merged (differences at
      precision floor).
    - Cluster A overflow singleton `{57}` remains tentative
      (`|Im(e)| ~ 10^41232...` cannot be reduced mod `2π` at any finite
      precision).
  The refined partition has 2925 conclusive classes (multi-precision
  evidence agrees: 1389 singletons + 1536 multi-member classes) and 1
  tentative class (the overflow singleton).
- [`a198683-n12-candidates.tsv`](a198683-n12-candidates.tsv) is the
  per-candidate raw dump that the equivalence-class file is derived from:
  one row per candidate with the `(k, ia, ib)` split, regime, exponent
  summary, and class labels under four dedup policies (default value-space,
  strict value-space with `abs_eps=0`, canonical-exponent with
  `abs_eps=cmp_tol`, canonical-exponent with `abs_eps=0`).
