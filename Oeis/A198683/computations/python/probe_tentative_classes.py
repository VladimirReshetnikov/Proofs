"""
Probe each of the four tentative classes at multiple precisions to
determine which one splits as the dps increases. The hypothesis being
tested: which tentative class splits into 2 sub-classes to account for
the strict-vs-Wolfram +1 (2925 -> 2926).

For each candidate index in the tentative classes, recompute its
exponent e = b * log(a) at dps in {260, 400, 800} and report Re(e),
Im(e) reduced mod 2pi, and the wrap integer. If two candidates in the
same strict class converge to identical (Re, Im_reduced) as precision
rises, they are algebraically equal. If their difference is stable in
magnitude as precision rises, they are algebraically distinct.
"""

from __future__ import annotations

import sys
from collections import defaultdict
from typing import Dict, List, Tuple

import mpmath as mp


def setup_precision(dps: int) -> Tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


def dedupe_mpc(values, *, bucket_rel, cmp_tol, abs_eps):
    def key(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    buckets: dict = defaultdict(list)
    out = []
    for z in values:
        k = key(z)
        found = False
        for idx in buckets[k]:
            if mp.almosteq(z, out[idx], rel_eps=cmp_tol, abs_eps=abs_eps):
                found = True
                break
        if not found:
            buckets[k].append(len(out))
            out.append(z)
    return out


def compute_values_upto_11(*, dps):
    bucket_rel, cmp_tol = setup_precision(dps)
    I = mp.mpc(0, 1)
    values = {1: [I]}
    for n in range(2, 12):
        cand = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = dedupe_mpc(cand, bucket_rel=bucket_rel, cmp_tol=cmp_tol, abs_eps=cmp_tol)
    return values


def reduce_im_mod_2pi(im: mp.mpf, dps: int) -> Tuple[mp.mpf, str]:
    if im == 0:
        return mp.mpf(0), "0"
    log10_abs = mp.log10(abs(im))
    if log10_abs > dps - 50:
        return mp.mpf(0), "too_huge"
    two_pi = 2 * mp.pi
    raw = mp.fmod(im + mp.pi, two_pi)
    if raw < 0:
        raw += two_pi
    return raw - mp.pi, "ok"


def compute_e_for_split(k: int, ia: int, ib: int, *, dps: int) -> mp.mpc:
    """Compute e = b * log(a) where a = V[k][ia] and b = V[12-k][ib]."""
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    setup_precision(dps)
    values = compute_values_upto_11(dps=dps)
    a = values[k][ia]
    b = values[12 - k][ib]
    return b * mp.log(a)


# Tentative candidates from the strict-policy partition at dps=260.
TENTATIVE_CANDIDATES = {
    "cluster A doubleton {2207, 3777}": [
        (2207, 4, 2, 65),
        (3777, 10, 252, 0),
    ],
    "cluster A overflow {57}": [
        (57, 1, 0, 57),
    ],
    "cluster B near-i^i (14)": [
        (562, 1, 0, 562),
        (1901, 3, 1, 100),
        (2161, 4, 2, 19),
        (2378, 5, 4, 23),
        (2574, 6, 7, 12),
        (2581, 6, 8, 4),
        (2603, 6, 9, 11),
        (2847, 7, 23, 4),
        (3035, 8, 38, 1),
        (3057, 8, 45, 2),
        (3058, 8, 46, 0),
        (3352, 9, 100, 1),
        (3731, 10, 206, 0),
        (4549, 11, 562, 0),
    ],
    "cluster C near-1 {25, 1404, 4239}": [
        (25, 1, 0, 25),
        (1404, 2, 0, 252),
        (4239, 11, 252, 0),
    ],
}


def main() -> int:
    # We compute V[1..11] once per dps, then evaluate e for all candidates.
    # Naively redoing V[1..11] inside compute_e_for_split for every candidate
    # would explode wall-clock; cache per-dps.

    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    test_dps = [260, 500, 1000]
    cache: Dict[int, dict] = {}
    for dps in test_dps:
        print(f"Computing V[1..11] at dps={dps} ...", flush=True)
        setup_precision(dps)
        cache[dps] = compute_values_upto_11(dps=dps)

    print()
    print("===== Tentative-class probe =====")
    print()

    for label, candidates in TENTATIVE_CANDIDATES.items():
        print(f"--- {label} ---")
        for idx, k, ia, ib in candidates:
            print(f"  idx={idx}  (k={k}, ia={ia}, ib={ib})")
            for dps in test_dps:
                setup_precision(dps)
                values = cache[dps]
                a = values[k][ia]
                b = values[12 - k][ib]
                e = b * mp.log(a)
                re_e = mp.re(e)
                im_e = mp.im(e)
                im_red, status = reduce_im_mod_2pi(im_e, dps)
                print(
                    f"    dps={dps:>4}: Re(e)={mp.nstr(re_e, 10):<30s} "
                    f"Im_red={mp.nstr(im_red, 10):<25s} "
                    f"wrap_status={status}"
                )
        print()

    # Cluster B: pairwise differences for a representative subset.
    print("===== Cluster B pairwise (Re, Im_red) differences =====")
    print()
    cluster_b_pairs = [
        ("562 vs 2161", (1, 0, 562), (4, 2, 19)),
        ("562 vs 3057", (1, 0, 562), (8, 45, 2)),
        ("2161 vs 3057", (4, 2, 19), (8, 45, 2)),
        ("562 vs 4549", (1, 0, 562), (11, 562, 0)),
    ]
    for label, split_a, split_b in cluster_b_pairs:
        print(f"--- {label} ---")
        for dps in test_dps:
            setup_precision(dps)
            values = cache[dps]
            k1, ia1, ib1 = split_a
            k2, ia2, ib2 = split_b
            e1 = values[12 - k1][ib1] * mp.log(values[k1][ia1])
            e2 = values[12 - k2][ib2] * mp.log(values[k2][ia2])
            diff_re = mp.re(e1) - mp.re(e2)
            diff_im = mp.im(e1) - mp.im(e2)
            print(
                f"  dps={dps:>4}: diff_Re={mp.nstr(diff_re, 10):<30s} "
                f"diff_Im={mp.nstr(diff_im, 10):<30s}"
            )
        print()

    # Cluster A doubleton: pairwise differences.
    print("===== Cluster A doubleton {2207, 3777} pairwise diff =====")
    print()
    for dps in test_dps:
        setup_precision(dps)
        values = cache[dps]
        e1 = values[8][65] * mp.log(values[4][2])      # idx 2207
        e2 = values[2][0] * mp.log(values[10][252])    # idx 3777
        diff_re = mp.re(e1) - mp.re(e2)
        diff_im = mp.im(e1) - mp.im(e2)
        print(
            f"  dps={dps:>4}: diff_Re={mp.nstr(diff_re, 10):<30s} "
            f"diff_Im={mp.nstr(diff_im, 10):<30s}"
        )
    print()

    # Specifically for cluster C, compute pairwise differences.
    print("===== Cluster C pairwise Re(e) differences =====")
    print()
    cluster_c_pairs = [
        ("25 vs 1404", (1, 0, 25), (2, 0, 252)),
        ("25 vs 4239", (1, 0, 25), (11, 252, 0)),
        ("1404 vs 4239", (2, 0, 252), (11, 252, 0)),
    ]
    for label, split_a, split_b in cluster_c_pairs:
        print(f"--- {label} ---")
        for dps in test_dps:
            setup_precision(dps)
            values = cache[dps]
            k1, ia1, ib1 = split_a
            k2, ia2, ib2 = split_b
            e1 = values[12 - k1][ib1] * mp.log(values[k1][ia1])
            e2 = values[12 - k2][ib2] * mp.log(values[k2][ia2])
            diff_re = mp.re(e1) - mp.re(e2)
            diff_im = mp.im(e1) - mp.im(e2)
            print(
                f"  dps={dps:>4}: diff_Re={mp.nstr(diff_re, 10):<30s} "
                f"diff_Im={mp.nstr(diff_im, 10):<30s}"
            )
        print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
