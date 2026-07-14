"""Print detailed exponent data for candidate indices that participate in
disputed equality classes between strategy 1 (almosteq) and strategy 2
(canonical i^Z mod 4) dedup. Includes the actual Re(e), Im(e) and the
i^Z canonical form.

Also report the symmetric "expression family" each candidate sits in:
the split index k and the left subexpression index ia.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from typing import List, Tuple

import mpmath as mp


def _setup_precision(dps: int) -> Tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


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


def compute_values_upto_11(*, dps: int):
    bucket_rel, cmp_tol = _setup_precision(dps)
    I = mp.mpc(0, 1)
    values = {1: [I]}
    for n in range(2, 12):
        cand = []
        for k in range(1, n):
            for a in values[k]:
                for b in values[n - k]:
                    cand.append(mp.power(a, b))
        values[n] = _dedupe_mpc(cand, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    return values


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=260)
    args = ap.parse_args()

    dps = args.dps
    bucket_rel, cmp_tol = _setup_precision(dps)
    values = compute_values_upto_11(dps=dps)
    logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}
    PI = mp.pi

    # Build n=12 candidates as (split_k, ia, ib, e); value = exp(e).
    cands = []
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
                e = b * la
                cands.append((k, ia, ib, e))

    print(f"raw candidates: {len(cands)}")
    # Recompute the value-space class membership (replicate strategy 1).
    succ = []  # (idx, exp(e))
    over = []  # (idx, e)
    digits_limit = mp.mpf(10_000)
    for idx, (_, _, _, e) in enumerate(cands):
        er = mp.re(e)
        ar = abs(er)
        log10_er = mp.ninf if ar == 0 else mp.log10(ar)
        if log10_er > digits_limit:
            over.append((idx, e))
        else:
            try:
                succ.append((idx, mp.exp(e)))
            except OverflowError:
                over.append((idx, e))

    def key_z(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    classes = []  # list of list[idx]
    reps = []    # list of representative z (or representative e for overflow)
    bucket = defaultdict(list)
    s1_map = [-1] * len(cands)

    for idx, z in succ:
        k = key_z(z)
        merged = False
        for ci in bucket[k]:
            if mp.almosteq(z, reps[ci], rel_eps=cmp_tol, abs_eps=cmp_tol):
                classes[ci].append(idx)
                s1_map[idx] = ci
                merged = True
                break
        if not merged:
            bucket[k].append(len(classes))
            s1_map[idx] = len(classes)
            classes.append([idx])
            reps.append(z)

    # overflow is its own class
    if over:
        overflow_class_id = len(classes)
        for idx, e in over:
            s1_map[idx] = overflow_class_id
        classes.append([idx for idx, _ in over])
        reps.append(("overflow", over[0][1]))

    print(f"strategy 1 classes: {len(classes)}")

    # For each candidate, the canonical Z = -2 i e / pi reduced mod 4 in Re.
    def canon_z(e):
        U = mp.re(e); V = mp.im(e)
        ReZ = 2 * V / PI
        ImZ = -2 * U / PI
        ReZmod = ReZ - 4 * mp.floor(ReZ / 4)
        return (ReZmod, ImZ)

    # Inspect specific s1 classes that the previous diagnostic flagged.
    targets = [25, 128, 560]

    # Strategy 2 (canonical) re-run inline so we can label each candidate.
    canon_tol = mp.mpf(10) ** (-(dps // 3))
    log10_step = mp.mpf("0.5")
    canon_buckets = defaultdict(list)
    canon_classes = []
    canon_reps = []
    s2_map = [-1] * len(cands)

    def key_zw(rez, imz):
        mag_imz = abs(imz)
        if mag_imz == 0:
            mag_bin = 0
        else:
            mag_bin = int(mp.floor(mp.log10(mag_imz) / log10_step))
        sign_imz = 0 if imz == 0 else (1 if imz > 0 else -1)
        re_bin = int(mp.nint(rez / bucket_rel))
        return (sign_imz, mag_bin, re_bin)

    for idx, (_, _, _, e) in enumerate(cands):
        rezmod, imz = canon_z(e)
        k = key_zw(rezmod, imz)
        boundary_keys = [k]
        if rezmod < bucket_rel * 10:
            boundary_keys.append(key_zw(rezmod + 4, imz))
        if (4 - rezmod) < bucket_rel * 10:
            boundary_keys.append(key_zw(rezmod - 4, imz))
        merged = False
        for bk in boundary_keys:
            for cls_idx in canon_buckets[bk]:
                rezr, imzr = canon_reps[cls_idx]
                drez = rezmod - rezr
                drez = drez - 4 * mp.floor((drez + 2) / 4)
                dimz = imz - imzr
                rscale = max(mp.mpf(1), abs(rezr), abs(rezmod))
                iscale = max(mp.mpf(1), abs(imzr), abs(imz))
                if abs(drez) <= canon_tol * rscale and abs(dimz) <= canon_tol * iscale:
                    canon_classes[cls_idx].append(idx)
                    s2_map[idx] = cls_idx
                    merged = True
                    break
            if merged:
                break
        if not merged:
            canon_buckets[k].append(len(canon_classes))
            s2_map[idx] = len(canon_classes)
            canon_classes.append([idx])
            canon_reps.append((rezmod, imz))

    print(f"strategy 2 classes: {len(canon_classes)}")

    print()
    print("=== Detailed inspection of disputed s1 classes ===")
    for ci in targets:
        cls = classes[ci]
        print(f"\n--- s1 class {ci} ({len(cls)} elements) ---")
        # Group candidates by s2 class
        by_s2 = defaultdict(list)
        for idx in cls:
            by_s2[s2_map[idx]].append(idx)
        for s2ci in sorted(by_s2.keys()):
            idxs = by_s2[s2ci]
            print(f"  -> s2 class {s2ci} ({len(idxs)} elements): {idxs}")
        for idx in cls:
            k, ia, ib, e = cands[idx]
            rezmod, imz = canon_z(e)
            print(f"  idx={idx} (k={k},ia={ia},ib={ib}) s2={s2_map[idx]}  Re(e)={mp.nstr(mp.re(e), 30)}  Im(e)={mp.nstr(mp.im(e), 30)}  ReZmod={mp.nstr(rezmod, 30)}  ImZ={mp.nstr(imz, 30)}")
        zs = []
        for idx in cls:
            k, ia, ib, e = cands[idx]
            cz = canon_z(e)
            zs.append((idx, k, ia, ib, e, cz))

        # For each pair, compute |Re(e1) - Re(e2)| and (Im(e1)-Im(e2)) mod 2pi
        n = len(zs)
        print(f"  pairwise (i,j) -- delta_Re_e, delta_Im_e mod 2pi (reduced to [-pi, pi])")
        for i in range(n):
            for j in range(i+1, n):
                _, _, _, _, ei, _ = zs[i]
                _, _, _, _, ej, _ = zs[j]
                dRe = mp.re(ei) - mp.re(ej)
                dIm = mp.im(ei) - mp.im(ej)
                # reduce dIm to (-pi, pi]
                dIm_mod = dIm - 2*PI*mp.nint(dIm/(2*PI))
                # k value
                kk = mp.nint(dIm/(2*PI))
                idxi = zs[i][0]; idxj = zs[j][0]
                print(f"    ({idxi},{idxj}): |dRe|={mp.nstr(abs(dRe), 12)}  dIm mod 2pi={mp.nstr(dIm_mod, 12)}  (k_wrap={int(kk)})")


if __name__ == "__main__":
    main()
