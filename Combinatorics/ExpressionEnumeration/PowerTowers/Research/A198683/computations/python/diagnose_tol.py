"""Sweep the (rel_eps, abs_eps) tolerance pair used by Python's almosteq
dedup at the n=12 stage and report how A198683(12) changes.

Hypothesis: at dps=260, the original script uses rel_eps = abs_eps = 10^-130.
This abs_eps floor lumps together candidate values whose magnitude is far
below 10^-130 (i.e., exp(e) for Re(e) << -300 ln(10) ~ -700). At n=12 those
"near-zero" candidates are numerically distinct (Re(e) values range from
-1325 to -3.6e9, so |exp(e)| spans many decades) but Python's almosteq
declares them all equal via |z1 - z2| <= abs_eps.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import mpmath as mp


def _setup_precision(dps):
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


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


def compute_values_upto_11(*, dps):
    bucket_rel, cmp_tol = _setup_precision(dps)
    I = mp.mpc(0, 1)
    values = {1: [I]}
    for n in range(2, 12):
        cand = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = _dedupe_mpc_with_tols(cand, bucket_rel=bucket_rel, rel_eps=cmp_tol, abs_eps=cmp_tol)
    return values


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=260)
    args = ap.parse_args()

    dps = args.dps
    bucket_rel, cmp_tol = _setup_precision(dps)
    print(f"dps={dps}, default cmp_tol = 10^-{dps // 2}")

    values = compute_values_upto_11(dps=dps)
    logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}
    print(f"|values[11]| = {len(values[11])}")

    # Build n=12 candidates as (k, ia, ib, e).
    cands = []
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
                e = b * la
                cands.append((k, ia, ib, e))

    print(f"raw candidates: {len(cands)}")
    print()
    print(f"{'rel_eps':>15}  {'abs_eps':>15}  {'#classes_succ':>15}  {'#overflow':>12}  {'a12':>6}")

    digits_limit = mp.mpf(10_000)

    for exp_rel_eps in [dps // 2, dps // 3, dps // 4]:
        for exp_abs_eps_label, abs_eps_expr in [
            ("rel_eps", None),   # abs_eps = rel_eps (original)
            ("rel_eps*1e-50", -50),  # additional tightening
            ("rel_eps*1e-100", -100),
            ("0", "zero"),  # no abs floor
        ]:
            rel_eps = mp.mpf(10) ** (-exp_rel_eps)
            if abs_eps_expr is None:
                abs_eps = rel_eps
            elif abs_eps_expr == "zero":
                abs_eps = mp.mpf(0)
            else:
                abs_eps = rel_eps * mp.mpf(10) ** abs_eps_expr

            succ = []
            over = []
            for idx, (_, _, _, e) in enumerate(cands):
                er = mp.re(e)
                ar = abs(er)
                log10_er = mp.ninf if ar == 0 else mp.log10(ar)
                if log10_er > digits_limit:
                    over.append((idx, e))
                else:
                    try:
                        z = mp.exp(e)
                        succ.append((idx, z))
                    except OverflowError:
                        over.append((idx, e))

            # dedup successes with these tolerances
            def key_z(z):
                s = max(1, abs(z))
                step = s * bucket_rel
                return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

            buckets = defaultdict(list)
            classes_succ = []  # list of representative z
            for idx, z in succ:
                k = key_z(z)
                merged = False
                for ci in buckets[k]:
                    if mp.almosteq(z, classes_succ[ci], rel_eps=rel_eps, abs_eps=abs_eps):
                        merged = True
                        break
                if not merged:
                    buckets[k].append(len(classes_succ))
                    classes_succ.append(z)

            n_succ = len(classes_succ)
            n_over = 1 if over else 0
            a12 = n_succ + n_over
            print(f"  10^-{exp_rel_eps:>4}  {exp_abs_eps_label:>15}  {n_succ:>15}  {n_over:>12}  {a12:>6}")


if __name__ == "__main__":
    main()
