"""
Compute OEIS A198683(n): the number of distinct values taken by i^i^...^i
with n i's and all parenthesizations, where ^ is the *principal value*
complex power:

    a ^ b := exp(b * Log(a)),

and Log is the principal complex log (branch cut along negative reals,
imaginary part in (-pi, pi]).

This script is a historical finite-precision diagnostic. It reproduces the
known counts for n<=11 and the old low-precision A198683(12)=2919 plateau, but
it does not certify A198683(12). The n=12 deduplication is numerical
(`almosteq` on rounded bigfloats), so the reported count depends on the chosen
working precision (`mp.mp.dps`); reruns above the original precision window
change the n=12 count (stabilising around 2924 between --dps 2000 and 8000,
still below the Wolfram 2926). Use the root-cause reports under
Oeis/A198683/reports/ before treating this script's output as evidence.

Key engineering points:

1. We use dynamic programming on sets of *distinct* subexpression values,
   so n=12 requires only ~5k exponentiations rather than Catalan(11)=58786.
2. We use mpmath's principal-branch complex log/power.
3. We deduplicate numerically using scale-invariant bucketing + almosteq; this
   is the known weak point for n=12.
4. For n=12, exactly one candidate value becomes so tiny (double-exponential
   scale) that mpmath cannot materialize exp(e). For counting purposes we
   treat it as a separate value, keyed by the exponent e=b*log(a).

Run examples (PowerShell):

    python .\\src\\Lean\\Oeis\\A198683\\computations\\python\\compute_a198683.py --dps 180 --n 12
    python .\\src\\Lean\\Oeis\\A198683\\computations\\python\\compute_a198683.py --dps 260 --n 12
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import sys
from typing import Iterable, List, Tuple

import mpmath as mp


@dataclass(frozen=True)
class A12Result:
    dps: int
    a11: int
    candidate_total: int
    success_total: int
    overflow_total: int
    uniq_success: int
    uniq_overflow: int
    a12: int
    overflow_exponent_sample: mp.mpc | None


def _setup_precision(dps: int) -> Tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


def _dedupe_mpc(values: Iterable[mp.mpc], *, bucket_rel: mp.mpf, cmp_tol: mp.mpf) -> List[mp.mpc]:
    def key(z: mp.mpc) -> Tuple[int, int]:
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    buckets: dict[Tuple[int, int], list[int]] = defaultdict(list)
    out: list[mp.mpc] = []
    for z in values:
        k = key(z)
        for idx in buckets[k]:
            if mp.almosteq(z, out[idx], rel_eps=cmp_tol, abs_eps=cmp_tol):
                break
        else:
            buckets[k].append(len(out))
            out.append(z)
    return out


def _dedupe_pairs(
    pairs: Iterable[Tuple[mp.mpf, mp.mpf]],
    *,
    bucket_rel: mp.mpf,
    cmp_tol: mp.mpf,
) -> List[Tuple[mp.mpf, mp.mpf]]:
    def key(x: mp.mpf, y: mp.mpf) -> Tuple[int, int]:
        sx = max(1, abs(x))
        sy = max(1, abs(y))
        stepx = sx * bucket_rel
        stepy = sy * bucket_rel
        return (int(mp.nint(x / stepx)), int(mp.nint(y / stepy)))

    buckets: dict[Tuple[int, int], list[int]] = defaultdict(list)
    out: list[Tuple[mp.mpf, mp.mpf]] = []
    for x, y in pairs:
        k = key(x, y)
        for idx in buckets[k]:
            x2, y2 = out[idx]
            if mp.almosteq(x, x2, rel_eps=cmp_tol, abs_eps=cmp_tol) and mp.almosteq(
                y, y2, rel_eps=cmp_tol, abs_eps=cmp_tol
            ):
                break
        else:
            buckets[k].append(len(out))
            out.append((x, y))
    return out


def compute_values_upto_11(*, dps: int) -> dict[int, List[mp.mpc]]:
    bucket_rel, cmp_tol = _setup_precision(dps)
    I = mp.mpc(0, 1)

    values: dict[int, List[mp.mpc]] = {1: [I]}
    for n in range(2, 12):
        cand: list[mp.mpc] = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = _dedupe_mpc(cand, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    return values


def compute_a12(*, dps: int, overflow_digits_limit: int = 10_000) -> A12Result:
    bucket_rel, cmp_tol = _setup_precision(dps)

    values = compute_values_upto_11(dps=dps)
    a11 = len(values[11])

    # Precompute logs for bases.
    logs: dict[int, List[mp.mpc]] = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}

    def log10_abs(x: mp.mpf) -> mp.mpf:
        ax = abs(x)
        if ax == 0:
            return mp.ninf
        return mp.log10(ax)

    success: list[mp.mpc] = []
    overflow_e: list[Tuple[mp.mpf, mp.mpf]] = []
    overflow_exponent_sample: mp.mpc | None = None

    digits_limit = mp.mpf(overflow_digits_limit)

    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for la in left_logs:
            for b in right:
                e = b * la
                er = mp.re(e)
                if log10_abs(er) > digits_limit:
                    overflow_e.append((mp.re(e), mp.im(e)))
                    if overflow_exponent_sample is None:
                        overflow_exponent_sample = e
                    continue
                try:
                    success.append(mp.exp(e))
                except OverflowError:
                    overflow_e.append((mp.re(e), mp.im(e)))
                    if overflow_exponent_sample is None:
                        overflow_exponent_sample = e

    uniq_success = _dedupe_mpc(success, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    uniq_overflow = _dedupe_pairs(overflow_e, bucket_rel=bucket_rel, cmp_tol=cmp_tol)

    return A12Result(
        dps=dps,
        a11=a11,
        candidate_total=len(success) + len(overflow_e),
        success_total=len(success),
        overflow_total=len(overflow_e),
        uniq_success=len(uniq_success),
        uniq_overflow=len(uniq_overflow),
        a12=len(uniq_success) + len(uniq_overflow),
        overflow_exponent_sample=overflow_exponent_sample,
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=180)
    ap.add_argument("--n", type=int, default=12, choices=[11, 12])
    ap.add_argument("--overflow-digits-limit", type=int, default=10_000)
    args = ap.parse_args()

    if hasattr(sys, "set_int_max_str_digits"):
        # High-precision runs can trigger CPython's int<->str digit limit when
        # formatting enormous intermediate magnitudes for diagnostics. This
        # script never converts untrusted user input, so disable the guardrail
        # for reproducible research output.
        sys.set_int_max_str_digits(0)

    if args.n == 11:
        values = compute_values_upto_11(dps=args.dps)
        counts = [len(values[i]) for i in range(1, 12)]
        print({"dps": args.dps, "counts_1_to_11": counts})
        return 0

    r = compute_a12(dps=args.dps, overflow_digits_limit=args.overflow_digits_limit)
    try:
        overflow_sample = mp.nstr(r.overflow_exponent_sample, 50) if r.overflow_exponent_sample else None
    except ValueError:
        overflow_sample = "<mp.nstr failed (see CPython int_max_str_digits)>"
    out = {
        "dps": r.dps,
        "a11": r.a11,
        "candidate_total": r.candidate_total,
        "success_total": r.success_total,
        "overflow_total": r.overflow_total,
        "uniq_success": r.uniq_success,
        "uniq_overflow": r.uniq_overflow,
        "a12": r.a12,
        "overflow_exponent_sample": overflow_sample,
    }
    print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
