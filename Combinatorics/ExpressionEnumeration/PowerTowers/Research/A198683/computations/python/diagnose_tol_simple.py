"""Streamlined tolerance probe: compare default Python dedup vs abs_eps=0 at
all levels, at a fixed precision. Reports class counts only.
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


def compute_values_upto_11(*, bucket_rel, rel_eps, abs_eps):
    I = mp.mpc(0, 1)
    values = {1: [I]}
    for n in range(2, 12):
        cand = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = _dedupe(cand, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=abs_eps)
    return values


def compute_a12(values, logs, *, bucket_rel, rel_eps, abs_eps, special_overflow):
    digits_limit = mp.mpf(10_000)
    succ = []
    over = []
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for la in left_logs:
            for b in right:
                e = b * la
                er = mp.re(e)
                ar = abs(er)
                log10_er = mp.ninf if ar == 0 else mp.log10(ar)
                if special_overflow and log10_er > digits_limit:
                    over.append(e)
                    continue
                try:
                    succ.append(mp.exp(e))
                except OverflowError:
                    if special_overflow:
                        over.append(e)
    def key_z(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))
    buckets = defaultdict(list)
    classes_succ = []
    for z in succ:
        k = key_z(z)
        merged = False
        for ci in buckets[k]:
            if mp.almosteq(z, classes_succ[ci], rel_eps=rel_eps, abs_eps=abs_eps):
                merged = True
                break
        if not merged:
            buckets[k].append(len(classes_succ))
            classes_succ.append(z)
    def key_xy(x, y):
        sx = max(1, abs(x))
        sy = max(1, abs(y))
        return (int(mp.nint(x / (sx * bucket_rel))), int(mp.nint(y / (sy * bucket_rel))))
    over_buckets = defaultdict(list)
    classes_over = []
    for e in over:
        k = key_xy(mp.re(e), mp.im(e))
        merged = False
        for ci in over_buckets[k]:
            x2, y2 = classes_over[ci]
            if mp.almosteq(mp.re(e), x2, rel_eps=rel_eps, abs_eps=abs_eps) and \
               mp.almosteq(mp.im(e), y2, rel_eps=rel_eps, abs_eps=abs_eps):
                merged = True
                break
        if not merged:
            over_buckets[k].append(len(classes_over))
            classes_over.append((mp.re(e), mp.im(e)))
    return len(classes_succ), len(classes_over)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=260)
    args = ap.parse_args()
    dps = args.dps
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(dps // 3))
    rel_eps = mp.mpf(10) ** (-(dps // 2))

    print(f"dps={dps}, rel_eps=abs_eps=10^-{dps // 2} (default)\n")

    print("Variant A: abs_eps = rel_eps at all levels (default script behavior)")
    values_a = compute_values_upto_11(bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=rel_eps)
    logs_a = {n: [mp.log(z) for z in values_a[n]] for n in range(1, 12)}
    a, b = compute_a12(values_a, logs_a, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=rel_eps, special_overflow=True)
    print(f"  |V[10]|={len(values_a[10])}, |V[11]|={len(values_a[11])}, n_succ={a}, n_over={b}, a12={a+b}")

    print()
    print("Variant B: abs_eps = 0 at all levels (relative-only tolerance)")
    values_b = compute_values_upto_11(bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=mp.mpf(0))
    logs_b = {n: [mp.log(z) for z in values_b[n]] for n in range(1, 12)}
    a, b = compute_a12(values_b, logs_b, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=mp.mpf(0), special_overflow=True)
    print(f"  |V[10]|={len(values_b[10])}, |V[11]|={len(values_b[11])}, n_succ={a}, n_over={b}, a12={a+b}")

    print()
    print("Variant C: abs_eps = 0, no special overflow handling (drop overflowed candidates)")
    a, b = compute_a12(values_b, logs_b, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=mp.mpf(0), special_overflow=False)
    print(f"  |V[10]|={len(values_b[10])}, |V[11]|={len(values_b[11])}, n_succ={a}, n_over={b}, a12={a+b}")


if __name__ == "__main__":
    main()
