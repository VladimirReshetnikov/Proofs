"""Sweep the (rel_eps, abs_eps) tolerance pair at ALL levels (n<=11 and the
n=12 stage) to isolate where the abs_eps floor causes spurious merges.

Also probe how the special "overflow" candidate is treated by re-running
the n=12 stage with and without that special handling.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import mpmath as mp


def _dedupe_mpc_with_tols(values, *, bucket_rel, rel_eps, abs_eps):
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
        values[n] = _dedupe_mpc_with_tols(cand, bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=abs_eps)
    return values


def compute_a12(values, logs, *, bucket_rel, rel_eps, abs_eps, special_overflow):
    digits_limit = mp.mpf(10_000)
    succ = []
    over = []
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
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
                    else:
                        # Don't count this candidate at all in non-special mode
                        # (matches "naive WL-style" behaviour where overflow
                        # would just drop the value out).
                        pass
    # Dedup successes
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
    # Dedup overflow by exponent
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
    print(f"dps={dps}")
    print()
    print(f"{'rel_eps':>10}  {'abs_eps':>10}  {'special_overflow':>18}  {'|V[10]|':>8}  {'|V[11]|':>8}  {'n_succ':>7}  {'n_over':>6}  {'a12':>6}")

    for exp_re in [dps // 2, dps // 3, dps // 4, dps // 5]:
        rel_eps = mp.mpf(10) ** (-exp_re)
        for abs_label, abs_eps in [
            (f"10^-{exp_re}", rel_eps),
            ("0", mp.mpf(0)),
        ]:
            values = compute_values_upto_11(bucket_rel=bucket_rel, rel_eps=rel_eps, abs_eps=abs_eps)
            v10 = len(values[10])
            v11 = len(values[11])
            logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}
            for special_overflow in [True, False]:
                n_succ, n_over = compute_a12(values, logs, bucket_rel=bucket_rel,
                                              rel_eps=rel_eps, abs_eps=abs_eps,
                                              special_overflow=special_overflow)
                a12 = n_succ + n_over
                print(f"  10^-{exp_re:<6}  {abs_label:>10}  {str(special_overflow):>18}  {v10:>8}  {v11:>8}  {n_succ:>7}  {n_over:>6}  {a12:>6}")


if __name__ == "__main__":
    main()
