# OEIS A198683(12): root cause of the 2919-vs-2926 discrepancy

- Status: Diagnostic (current-state explanation)
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Identify and explain, as concretely as the available evidence allows, why the local Python/`mpmath` recurrence reports `A198683(12) = 2919` while the local Wolfram `Equal`-based recurrence reports `A198683(12) = 2926`
- Created (UTC): 2026-05-21T02:27:23Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

## Summary

The two implementations agree on the OEIS lower terms through `n = 11`, on the dynamic-programming recurrence over distinct lower-level values, and on the `5139` pairwise candidate powers generated at `n = 12`. They disagree on the deduplication policy. The 7-class gap is **not** a deep mathematical disagreement about branch decisions or wrap integers; it is a localised artefact of the Python script's tolerance policy. Specifically:

1. Python's [`compute_a198683.py`](../../computations/python/compute_a198683.py) deduplicates with `mp.almosteq(z1, z2, rel_eps=cmp_tol, abs_eps=cmp_tol)` where `cmp_tol = 10^-(dps/2)`. Because `abs_eps` is set equal to `rel_eps` (and therefore to a fixed positive constant), the *absolute*-tolerance branch of `almosteq` declares **any** two values smaller in magnitude than `cmp_tol` to be equal, regardless of their actual structure.

2. At `n = 12` the bulk of the candidates produced by `(I)^(huge n=11 exponent)` and related splits have computed magnitudes far below `10^-130`. They are mathematically distinct but the `abs_eps` floor of `almosteq` lumps them into a single equivalence class.

3. Setting `abs_eps = 0` in the same Python script at the `n = 12` stage *only* — leaving the lower-level dedup untouched — raises the reported count from `2919` to `2925`, recovering **six of the seven** missing classes.

4. The remaining single-class gap (between Python with `abs_eps = 0` at `n = 12` and Wolfram with `Equal`) is small and consistent with secondary tolerance choices at lower levels and with the still-special-cased "overflow" candidate; this report does not certify which of `2925`, `2926`, or `2927` is the true count, only that the *bulk* of the discrepancy is explained by the `abs_eps` policy.

Neither side of the historical OEIS disagreement is therefore a "wrong wrap" certification. The Wolfram side is closer to the true count because it avoids the `abs_eps` artefact, but it is also not a proof-quality computation — both numbers come from heuristic equality predicates evaluated at finite precision. The exploratory reports under [`exploratory/`](../exploratory/README.md) describe the interval-arithmetic certification strategy that would be needed to settle the value rigorously.

## Quick reproduction

Run the original script and then the diagnostic that varies `abs_eps`:

```powershell
python .\src\Lean\Oeis\A198683\computations\python\compute_a198683.py --dps 260 --n 12
python .\src\Lean\Oeis\A198683\computations\python\diagnose_tol.py --dps 260
```

Expected output: the original script reports `a12 = 2919` (stable across `--dps 160..260`); `diagnose_tol.py` shows that swapping `abs_eps = rel_eps` for `abs_eps = 0` raises the count from `2919` to `2925` at every precision setting, while tightening `abs_eps` (down to `rel_eps * 10^-100`) does **not** change the count. The effect is therefore not a precision artefact — it is the existence of the floor itself.

Check that the lower-level counts are unaffected:

```powershell
python .\src\Lean\Oeis\A198683\computations\python\diagnose_levels.py --dps 180 --n-max 11
```

Both `abs_eps = rel_eps` and `abs_eps = 0` reproduce the OEIS-accepted counts `1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152` exactly; the `abs_eps` artefact only manifests at `n = 12`, because that is the first level where many candidate magnitudes fall well below `abs_eps`.

To extract the structural cases that drive the discrepancy:

```powershell
python .\src\Lean\Oeis\A198683\computations\python\diagnose_dedup.py --dps 260 --canonical-tol-frac 3
python .\src\Lean\Oeis\A198683\computations\python\diagnose_pairs.py --dps 260
```

## The deduplication policies in detail

### Python (the 2919 side)

The `n = 12` dedup uses `_dedupe_mpc`:

```python
def _dedupe_mpc(values, *, bucket_rel, cmp_tol):
    def key(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))
    buckets = defaultdict(list)
    out = []
    for z in values:
        k = key(z)
        for idx in buckets[k]:
            if mp.almosteq(z, out[idx], rel_eps=cmp_tol, abs_eps=cmp_tol):
                break
        else:
            buckets[k].append(len(out))
            out.append(z)
    return out
```

with `cmp_tol = 10^-(dps/2)`. Two complex values are merged when

```text
|z1 - z2| <= max(abs_eps, rel_eps * max(|z1|, |z2|))
```

`mpmath.almosteq` therefore treats every pair with `|z1| <= cmp_tol` and `|z2| <= cmp_tol` as equal: their difference is bounded above by `|z1| + |z2| <= 2 cmp_tol`, which falls inside the `abs_eps` ball.

This is harmless for moderate values, but at `n = 12` it collapses a structurally rich neighbourhood of "near-zero" candidates.

### Wolfram (the 2926 side)

The Wolfram recurrence in [`computations/wolfram/a198683-n12-check__2026-05-20.wl`](../../computations/wolfram/a198683-n12-check__2026-05-20.wl) uses

```wolfram
Union[..., SameTest -> Equal]
```

`Equal` for inexact complex numbers in Wolfram uses precision-aware comparison: it returns `True` only when the two numbers are indistinguishable at the working precision. It does not introduce an artificial absolute-tolerance floor, so two genuinely-distinct but extremely tiny values stay separate.

## Where the seven classes come from

The diagnostic [`diagnose_dedup.py`](../../computations/python/diagnose_dedup.py) re-runs both the Python value-space dedup and a canonical-form dedup that uses

```text
v1 = v2  iff  e1 - e2 = 2 pi i k  for some integer k
```

(written equivalently as a comparison of `(Re(e), Im(e) mod 2 pi)` on the level-12 exponent `e = b * Log(a)`, so the huge value `exp(e)` never has to be materialised).

At `dps = 260`, only three of the Python equivalence classes get split by that canonical form. They are visible in [`diagnose_pairs.py`](../../computations/python/diagnose_pairs.py) output:

### Class A — "near 0" cluster (`s1` class 128, 8 candidates)

Eight candidates with `Re(e)` ranging from `-1325` to `-3.6 * 10^9`. Each computed `|exp(e)|` is far below `10^-1000`, well inside the `abs_eps` ball. Within the cluster, the pair `(idx=2207, idx=3777)` has exponents that are **exactly** equal at the displayed precision (their structural difference cancels), so the canonical form correctly merges them; the other six are pairwise distinct.

Python merges all 8 into one class (one canonical merge plus six spurious merges). Wolfram keeps seven of them apart.

This single cluster accounts for **six** of the seven missing classes between `2919` and `2926`.

| Source candidate | Split `(k, ia, ib)` | `Re(e)` magnitude | `Im(e)` magnitude |
|---|---|---|---|
| `idx=129`  | `(1, 0, 129)`  | `~5*10^5`  | `~10^5`     |
| `idx=151`  | `(1, 0, 151)`  | `~3*10^3`  | `~10^4`     |
| `idx=644`  | `(1, 0, 644)`  | `~4*10^9`  | `~10^10`    |
| `idx=1061` | `(1, 0, 1061)` | `~4*10^5`  | `~2*10^5`   |
| `idx=1079` | `(1, 0, 1079)` | `~10^3`    | `~10^3`     |
| `idx=2053` | `(4, 0, 65)`   | `~10^3`    | `~3*10^3`   |
| `idx=2207` | `(4, 2, 65)`   | `~6*10^2`  | `~10^-258`  |
| `idx=3777` | `(10, 252, 0)` | `~6*10^2`  | `~10^-258`  |

Indices `2207` and `3777` agree on `Re(e)` and `Im(e)` to all displayed digits; their canonical-form classes merge. The other six candidates have pairwise `|dRe(e)|` ranging from `~3*10^2` to `~3*10^9` and `dIm mod 2pi` ranging across the full `(-pi, pi]` interval — there is no structural reason for any of them to coincide.

### Class B — "near `e^{-pi/2}`" cluster (`s1` class 560, 14 candidates)

All 14 candidates have `Re(e)` numerically indistinguishable from `-pi/2` and `Im(e)` of order `10^-261` to `10^-263`. So `exp(e)` is computed as a value indistinguishable from `e^{-pi/2} = i^i ≈ 0.207879...` at the working precision.

This is the structurally interesting case: many parenthesizations of twelve copies of `i` evaluate to `i^i` because the OEIS comment's "islands of associativity" (sub-trees that reduce to positive-real intermediates) give exact algebraic coincidences. Whether all 14 are truly mathematically equal to `i^i`, or whether some lie infinitesimally to one side of `e^{-pi/2}`, is exactly the kind of question the proof-quality interval evaluator in [`exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md) is designed to settle.

The canonical-form diagnostic (which is itself heuristic at this magnitude) splits the 14 into a small number of sub-classes that are visible in `diagnose_pairs.py` but does not yield a definitive count. This cluster is therefore a candidate for *part* of the residual 2925 → 2926 gap, but the diagnostic in this report does not assign blame here.

### Class C — "near 1" cluster (`s1` class 25, 3 candidates)

Three candidates with `Re(e)` and `Im(e)` smaller than `10^-1300`. Their `exp(e)` is computed as `≈ 1`. Two of them (`idx=1404`, `idx=4239`) share `Re(e)` exactly and differ only in tiny imaginary noise; the third (`idx=25`) has different real and imaginary parts. The canonical form splits this class into `{25}` and `{1404, 4239}`.

## What `2925` vs `2926` vs `2927` actually mean

| Variant | `a(12)` |
|---|---:|
| Python `compute_a198683.py` (default `abs_eps = rel_eps`) | `2919` |
| Python with `abs_eps = 0` at the `n = 12` dedup stage | `2925` |
| Wolfram `Equal` recurrence | `2926` |
| Canonical-exponent dedup with relaxed tolerance (`diagnose_dedup.py`) | `2927` |

These four numbers are *all* heuristics. They differ by at most eight classes out of 5139 candidates, all concentrated in three structurally-degenerate regions of the candidate space (near `0`, near `i^i`, and near `1`). None of the four is a proof.

The OEIS entry's historical "2919 or 2926" alternative is therefore a snapshot of the same three-cluster ambiguity expressed by two different tolerance policies. Settling the value rigorously requires the interval-arithmetic certification strategy described in [`exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md) (interval `(rho, theta)` propagation with bounded wrap integers) or a more compact symbolic-algebraic argument that the relevant sub-trees do or do not reduce to one of the special values `0`, `1`, or `i^i`.

## What to add to the corpus README, briefly

The current [`README.md`](../../README.md) says the disagreement is "about equality certification for a small number of candidate classes". That is correct but unspecific. A more concrete statement, supported by the diagnostics:

> The Python/`mpmath` script and the Wolfram recurrence agree on the OEIS lower terms and on the `5139` candidate powers at `n = 12`. The 7-class gap is explained as follows. Python uses `mpmath.almosteq(rel_eps, abs_eps)` with `abs_eps` set to a fixed positive constant; this declares **any** two values smaller in magnitude than `abs_eps` to be equal, lumping together an eight-element cluster of structurally-distinct "near-zero" candidates (six spurious merges). Setting `abs_eps = 0` in the same script raises the count from `2919` to `2925`. The remaining `2925` vs `2926` gap lives in two further small clusters near `i^i` and `1`, where the answer depends on whether tiny imaginary residuals are interpreted as numerical noise (Python's almosteq under any tolerance) or as genuine non-equalities (Wolfram's `Equal`). Neither implementation is a proof; the rigorous certification described in `exploratory/A198683-report-2.md` would be needed to settle the value.

## Files added or referenced by this diagnostic

- [`computations/python/compute_a198683.py`](../../computations/python/compute_a198683.py) — original Python recurrence (reports `2919`).
- [`computations/wolfram/a198683-n12-check__2026-05-20.wl`](../../computations/wolfram/a198683-n12-check__2026-05-20.wl) — Wolfram recurrence (reports `2926`).
- [`computations/python/diagnose_dedup.py`](../../computations/python/diagnose_dedup.py) — runs both the value-space dedup and a canonical-exponent dedup, prints the partition refinement.
- [`computations/python/diagnose_pairs.py`](../../computations/python/diagnose_pairs.py) — prints per-candidate exponent data for the three disputed clusters.
- [`computations/python/diagnose_tol.py`](../../computations/python/diagnose_tol.py) — sweeps `(rel_eps, abs_eps)` at the `n = 12` stage; shows the `2919 -> 2925` jump on `abs_eps = 0`.
- [`computations/python/diagnose_naive.py`](../../computations/python/diagnose_naive.py) — naive `O(N^2)` canonical-exponent dedup; useful as a structural cross-check (and as a witness that strict canonical-form comparison without interval arithmetic over-splits).
- [`computations/python/diagnose_levels.py`](../../computations/python/diagnose_levels.py) — recomputes `|V[n]|` for `n <= 11` under both `abs_eps` policies; shows the artefact is localised to `n = 12`.

## What this report does not claim

- It does **not** declare `2926` (or any other number) to be the true value of `A198683(12)`.
- It does **not** rule out that some pair in clusters B or C is mathematically equal even though the canonical-form heuristic separates them.
- It does **not** replace the rigorous interval-arithmetic certification described in `exploratory/A198683-report-2.md`.

It only identifies, as concretely as the local artefacts allow, *where* the historical `2919` vs `2926` disagreement actually lives, so future work can target the right clusters with the right tools.
