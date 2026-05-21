# OEIS A198683(12) Python/mpmath Investigation

- Status: Historical investigation (invalidated as exact evidence)
- Audience: Vladimir Reshetnikov, OEIS contributors, and future agents revisiting A198683
- Scope: Compute `A198683(12)` with Python, `mpmath`, numerical deduplication, and special handling for one unmaterializable candidate
- Created (UTC): 2026-05-20T22:13:19Z
- Repository HEAD: f906a31c0f82f92946a3524ac72e70d392258403

This report is preserved as one side of the local contradiction described in
[the A198683 corpus README](../README.md). It historically concluded
`A198683(12) = 2919`. A later root-cause pass invalidates that conclusion as
exact evidence: the `2919` count is a finite-precision numerical-deduplication
artifact, not a certified equality count.

See
[`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
before citing this report.

## Erratum: Precision Plateau Was False Evidence

The original report treated stability across `160`, `180`, `220`, and `260`
decimal digits as evidence for `2919`. Rerunning the same script at higher
precision breaks that plateau:

| Decimal digits | Script result |
|---:|---:|
| 180 | 2919 |
| 260 | 2919 |
| 500 | 2919 |
| 800 | 2920 |
| 1000 | 2921 |
| 1200 | 2922 |
| 2000 | 2922 |
| 3000 | 2924 |

The monotone upward drift shows that the script merged near candidates too
aggressively. The body below is retained as a historical record of the method
and its assumptions, not as a current recommendation to use `2919`.

## Goal

Establish the true value of `A198683(12)`, where `A198683(n)` is the number of *distinct* values taken by

`i^i^...^i` (with `n` copies of `i` and parentheses inserted in all possible ways),

interpreting `^` as the **principal value** complex power:

`a^b := exp(b * Log(a))`,

with `Log` the principal complex logarithm.

The OEIS entry records:

`A198683(1..11) = 1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152`

and historically `A198683(12)` was reported as “either 2919 or 2926”.

This report presents a reproducible computation that originally claimed to
resolve the ambiguity. That claim is superseded by the erratum above.

## Historical Reported Result

The original reported result was:

`A198683(12) = 2919`.

This value is stable only across the limited precision settings tested by the
original report. It is not stable under larger precision reruns, even though the
same implementation reproduces the accepted `A198683(n)` counts for `n <= 11`.

## What Makes n=12 Special

For `n=12` there are `Catalan(11)=58786` parenthesizations, but after quotienting by duplicates,
only a few thousand distinct values remain. So the problem is not “enumeration size”; it is numeric range.

Already at `n=11`, at least one value has an absolutely enormous magnitude (as described in the OEIS comments).
At `n=12`, raising `i` to that huge `n=11` value produces a value whose magnitude is effectively
double-exponential, far outside the range of conventional bigfloat complex representations:

- computing `exp(Re(e))` for `e = exponent * Log(base)` becomes impossible to materialize, because the
  decimal exponent itself has astronomically many digits.

This is why naive “just use Wolfram `N[]` everywhere and `Union[]`” can overflow or silently degrade.

## Implementation Strategy

### 1. Dynamic programming on distinct subexpressions

Let `V(n)` be the set of *distinct* values of expressions built from `n` copies of `i` with all parenthesizations.

Every full parenthesization splits as:

`(left_expression)^(right_expression)`

where the left uses `k` copies of `i` and the right uses `n-k` copies. Therefore:

`V(n) = Union_{k=1..n-1} { a^b : a in V(k), b in V(n-k) }`

This reduces work drastically. For `n=12`:

`Sum_{k=1..11} |V(k)| * |V(12-k)| = 5139`

so only ~5k exponentiations are required, rather than 58k full parenthesizations.

### 2. Use mpmath’s principal-branch power/log

We use Python + `mpmath` for arbitrary precision. `mpmath` defines `log(z)` on the principal branch
and complex `power` via `exp(w*log(z))`, matching the OEIS semantics.

### 3. Dedupe with scale-invariant bucketing + `almosteq`

Raw exact equality on bigfloat complexes is not appropriate because the same mathematical value can be
reached through different evaluation paths that differ by tiny numerical noise.

We dedupe values using:

1. A scale-invariant bucket key on `(Re, Im)` to keep candidate comparisons small.
2. A tight `almosteq` check to confirm equality inside a bucket.

This same dedupe logic reproduces the known counts for `n<=11`, but the erratum
above shows that this is not enough to certify the `n=12` near-collision cases.

### 4. Special handling for the single “too-small-to-materialize” `n=12` value

At `n=12` exactly **one** candidate value cannot be materialized as a bigfloat complex.
It arises from the split `k=1` (base is `i`) with the unique huge element of `V(11)` as exponent.

Instead of trying to build `exp(e)` directly (which fails), we treat this value as distinct and key it by the
exponent `e = b * Log(a)` itself (since in this extreme regime it is vastly separated in magnitude from all
other candidates, and it is the only case that overflows).

Empirically this “overflow bucket” contains exactly one value and no collisions.

## Reproducibility

Script:

- `src/Oeis/A198683/computations/python/compute_a198683.py`

Runs:

```powershell
python .\src\Oeis\A198683\computations\python\compute_a198683.py --dps 160 --n 12
python .\src\Oeis\A198683\computations\python\compute_a198683.py --dps 180 --n 12
python .\src\Oeis\A198683\computations\python\compute_a198683.py --dps 220 --n 12
python .\src\Oeis\A198683\computations\python\compute_a198683.py --dps 260 --n 12
```

Originally observed stability (all listed runs produced identical totals, now
understood as a low-precision plateau):

- `A198683(12) = 2919`
- `candidate_total = 5139`
- `success_total = 5138`
- `overflow_total = 1`
- `uniq_success = 2918`
- `uniq_overflow = 1`

Additionally, `--n 11` prints `A198683(1..11)` and matches the OEIS values.

## Notes on Wolfram/Tungsten

Tungsten is useful for interacting with the local Wolfram installation, and it is a good cross-check for
`n <= 11` if you keep computations exact/symbolic.

However, any approach that forces direct `N[...]` materialization of the huge `n=11` value and then tries
to compute `i^that_value` numerically is likely to overflow in WL because it exceeds WL’s maximum representable
bigfloat magnitude.

The Python approach above avoids this by never requiring full materialization of that single extreme `n=12`
result.
