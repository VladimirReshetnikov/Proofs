"""Check whether removing the abs_eps floor at lower levels (n<=11) changes
the number of distinct values reported. The OEIS-accepted sequence requires
|V[n]| for n <= 11 to be 1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import mpmath as mp


def _dedupe(values, *, bucket_rel, rel_eps, abs_eps):
    def key(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))
    buckets = defaultdict(list)
    out = []
    for z in values:
        k = key(z)
        merged = False
        for idx in buckets[k]:
            if mp.almosteq(z, out[idx], rel_eps=rel_eps, abs_eps=abs_eps):
                merged = True
                break
        if not merged:
            buckets[k].append(len(out))
            out.append(z)
    return out


def compute_values(*, dps, abs_eps_zero, n_max):
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(dps // 3))
    rel_eps = mp.mpf(10) ** (-(dps // 2))
    abs_eps = mp.mpf(0) if abs_eps_zero else rel_eps
    I = mp.mpc(0, 1)
    values = {1: [I]}
    for n in range(2, n_max + 1):
        cand = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = _dedupe(cand, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=abs_eps)
    return values


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=180)
    ap.add_argument("--n-max", type=int, default=10,
                    help="limit n to keep runtime tractable; default 10")
    args = ap.parse_args()

    print(f"dps={args.dps}")
    print(f"OEIS reference a(1..11) = 1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152")
    print()

    for abs_eps_zero in [False, True]:
        label = "abs_eps=0" if abs_eps_zero else "abs_eps=rel_eps"
        values = compute_values(dps=args.dps, abs_eps_zero=abs_eps_zero, n_max=args.n_max)
        counts = [len(values[n]) for n in range(1, args.n_max + 1)]
        print(f"{label:>20}  counts[1..{args.n_max}] = {counts}")


if __name__ == "__main__":
    main()
