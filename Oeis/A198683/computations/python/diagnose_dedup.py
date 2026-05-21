"""Diagnostic for A198683(12): isolate which candidates Python's almosteq
dedup treats as equal but Wolfram's Equal treats as distinct.

Builds candidates the same way as compute_a198683.py up through n=11, then
generates the 5139 n=12 candidates as principal-branch exponents
    e = b * Log(a)  (so the value is exp(e), never materialised)

and dedups by two independent strategies:

1. value-space almosteq (same logic as compute_a198683.py)
2. canonical i^Z form: write each value as exp(e) = i^Z where
       Z = -2 i e / pi = (2 Im(e) / pi) + i (-2 Re(e) / pi),
   so two candidates are equal iff Re(Z1) - Re(Z2) in 4 Z and
   Im(Z1) - Im(Z2) = 0. Re(Z) is reduced modulo 4 to [0, 4) and
   then dedup uses a tight tolerance.

The script reports counts under each strategy and prints the index pairs
that strategy 1 merges but strategy 2 does not (the candidates Python
treats as duplicates that the i^Z canonical form would split apart), and
vice versa.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from typing import Iterable, List, Tuple

import mpmath as mp


def _setup_precision(dps: int) -> Tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


def _dedupe_mpc(values: Iterable[mp.mpc], *, bucket_rel, cmp_tol) -> List[mp.mpc]:
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
    ap.add_argument("--dps", type=int, default=180)
    ap.add_argument("--canonical-tol-frac", type=int, default=3,
                    help="canonical tolerance = 10^-(dps/canonical_tol_frac); default dps/3")
    args = ap.parse_args()

    dps = args.dps
    bucket_rel, cmp_tol = _setup_precision(dps)
    values = compute_values_upto_11(dps=dps)
    logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}

    PI = mp.pi

    # Build all 5139 n=12 candidates as (provenance, e) where value = exp(e),
    # AND track an identifying (k, ia, ib) split tag for traceback.
    cands = []  # list of (split_k, ia, ib, e)
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
                e = b * la
                cands.append((k, ia, ib, e))

    print(f"raw candidates: {len(cands)}")

    # Strategy 1: value-space dedup, with overflow special-case (matches the
    # original 2919 script).
    success = []  # list of (idx, exp(e))
    overflow = []  # list of (idx, e)
    digits_limit = mp.mpf(10_000)

    for idx, (_, _, _, e) in enumerate(cands):
        er = mp.re(e)
        ar = abs(er)
        if ar == 0:
            log10_er = mp.ninf
        else:
            log10_er = mp.log10(ar)
        if log10_er > digits_limit:
            overflow.append((idx, e))
            continue
        try:
            success.append((idx, mp.exp(e)))
        except OverflowError:
            overflow.append((idx, e))

    # Dedup successes with almosteq + bucketing.
    def key_z(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    succ_buckets = defaultdict(list)
    succ_classes = []  # list[list[int]] of candidate indices
    succ_reps = []     # representative z values

    for idx, z in success:
        k = key_z(z)
        merged = False
        for cls_idx in succ_buckets[k]:
            if mp.almosteq(z, succ_reps[cls_idx], rel_eps=cmp_tol, abs_eps=cmp_tol):
                succ_classes[cls_idx].append(idx)
                merged = True
                break
        if not merged:
            succ_buckets[k].append(len(succ_classes))
            succ_classes.append([idx])
            succ_reps.append(z)

    # Dedup overflow by (Re(e), Im(e)) almosteq.
    def key_xy(x, y):
        sx = max(1, abs(x))
        sy = max(1, abs(y))
        return (int(mp.nint(x / (sx * bucket_rel))), int(mp.nint(y / (sy * bucket_rel))))

    over_buckets = defaultdict(list)
    over_classes = []
    over_reps = []
    for idx, e in overflow:
        k = key_xy(mp.re(e), mp.im(e))
        merged = False
        for cls_idx in over_buckets[k]:
            x2, y2 = over_reps[cls_idx]
            if mp.almosteq(mp.re(e), x2, rel_eps=cmp_tol, abs_eps=cmp_tol) and mp.almosteq(mp.im(e), y2, rel_eps=cmp_tol, abs_eps=cmp_tol):
                over_classes[cls_idx].append(idx)
                merged = True
                break
        if not merged:
            over_buckets[k].append(len(over_classes))
            over_classes.append([idx])
            over_reps.append((mp.re(e), mp.im(e)))

    a12_strat1 = len(succ_classes) + len(over_classes)
    print(f"strategy 1 (almosteq + overflow): {a12_strat1} classes "
          f"(success={len(succ_classes)}, overflow={len(over_classes)})")

    # Strategy 2: canonical i^Z form. For each candidate, Z = -2 i e / pi.
    # Reduce Re(Z) mod 4 to [0, 4). Then dedup by (Re(Z) mod 4, Im(Z)) with
    # tight relative tolerance.
    canon_tol = mp.mpf(10) ** (-(dps // args.canonical_tol_frac))
    print(f"canonical tolerance: 10^-{dps // args.canonical_tol_frac}")

    canon = []  # list of (idx, ReZmod4, ImZ)
    for idx, (_, _, _, e) in enumerate(cands):
        U = mp.re(e)
        V = mp.im(e)
        ReZ = 2 * V / PI
        ImZ = -2 * U / PI
        ReZmod = ReZ - 4 * mp.floor(ReZ / 4)
        canon.append((idx, ReZmod, ImZ))

    # Bucket on (ReZmod, ImZ) at a coarse step proportional to the per-element
    # scale, then do a tight pairwise check.
    canon_buckets = defaultdict(list)
    canon_classes = []
    canon_reps = []

    # Bucket key: use log-scale magnitude bin for Im(Z) so huge values do not
    # collapse into a single bucket, plus a fine bin within Re(Z) mod 4.
    log10_step = mp.mpf("0.5")  # coarse magnitude bin (half a decade)

    def key_zw(rez, imz):
        mag_imz = abs(imz)
        if mag_imz == 0:
            mag_bin = 0
        else:
            mag_bin = int(mp.floor(mp.log10(mag_imz) / log10_step))
        # sign-aware sign bin
        sign_imz = 0 if imz == 0 else (1 if imz > 0 else -1)
        # Within bucket, use rounded relative position for Im and a fine bin
        # for Re mod 4.
        re_bin = int(mp.nint(rez / bucket_rel))  # bucket_rel = 10^-(dps/3)
        return (sign_imz, mag_bin, re_bin)

    for idx, rezmod, imz in canon:
        k = key_zw(rezmod, imz)
        # also consider wraparound near 0 / 4 boundary in real part by trying
        # the adjacent re_bins corresponding to rezmod+4 and rezmod-4
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
                # bring drez into [-2, 2]
                drez = drez - 4 * mp.floor((drez + 2) / 4)
                dimz = imz - imzr
                rscale = max(mp.mpf(1), abs(rezr), abs(rezmod))
                iscale = max(mp.mpf(1), abs(imzr), abs(imz))
                if abs(drez) <= canon_tol * rscale and abs(dimz) <= canon_tol * iscale:
                    canon_classes[cls_idx].append(idx)
                    merged = True
                    break
            if merged:
                break
        if not merged:
            canon_buckets[k].append(len(canon_classes))
            canon_classes.append([idx])
            canon_reps.append((rezmod, imz))

    print(f"strategy 2 (canonical i^Z mod 4): {len(canon_classes)} classes")

    # Compute Strategy 1 partition (as a set of frozensets over candidate idxs).
    def partition_from_classes(classes):
        return [frozenset(c) for c in classes]

    # Strategy 1 partition includes overflow_classes too.
    s1 = partition_from_classes(succ_classes) + partition_from_classes(over_classes)
    s2 = partition_from_classes(canon_classes)

    # Map: cand idx -> class index in each
    map1 = [-1] * len(cands)
    for ci, cls in enumerate(s1):
        for idx in cls:
            map1[idx] = ci
    map2 = [-1] * len(cands)
    for ci, cls in enumerate(s2):
        for idx in cls:
            map2[idx] = ci

    # For each pair of candidates, identify "merge disagreements".
    # Specifically: classes in s1 that are unions of multiple classes in s2 ->
    # Python merges these together, canonical form keeps them separate.
    s1_split_by_s2 = []  # list of (s1_class, [s2_class_ids])
    for ci, cls in enumerate(s1):
        sub = defaultdict(list)
        for idx in cls:
            sub[map2[idx]].append(idx)
        if len(sub) > 1:
            s1_split_by_s2.append((ci, dict(sub)))

    s2_split_by_s1 = []
    for ci, cls in enumerate(s2):
        sub = defaultdict(list)
        for idx in cls:
            sub[map1[idx]].append(idx)
        if len(sub) > 1:
            s2_split_by_s1.append((ci, dict(sub)))

    print()
    print(f"s1 classes that span multiple s2 classes: {len(s1_split_by_s2)}")
    for s1_ci, sub in s1_split_by_s2[:20]:
        sizes = sorted(len(v) for v in sub.values())
        print(f"  s1 class {s1_ci}: split into s2 sub-classes with sizes {sizes}")
        # print first idx in each sub
        for s2_ci, idxs in sub.items():
            i0 = idxs[0]
            k, ia, ib, e = cands[i0]
            print(f"    s2 class {s2_ci}: first idx {i0} -> split (k={k}, ia={ia}, ib={ib}); |Re(e)|~10^{mp.nstr(mp.log10(max(mp.mpf(1), abs(mp.re(e)))), 6)}, |Im(e)|~10^{mp.nstr(mp.log10(max(mp.mpf(1), abs(mp.im(e)))), 6)}")

    print()
    print(f"s2 classes that span multiple s1 classes: {len(s2_split_by_s1)}")
    for s2_ci, sub in s2_split_by_s1[:20]:
        sizes = sorted(len(v) for v in sub.values())
        print(f"  s2 class {s2_ci}: split into s1 sub-classes with sizes {sizes}")
        for s1_ci, idxs in sub.items():
            i0 = idxs[0]
            k, ia, ib, e = cands[i0]
            print(f"    s1 class {s1_ci}: first idx {i0} -> split (k={k}, ia={ia}, ib={ib}); |Re(e)|~10^{mp.nstr(mp.log10(max(mp.mpf(1), abs(mp.re(e)))), 6)}, |Im(e)|~10^{mp.nstr(mp.log10(max(mp.mpf(1), abs(mp.im(e)))), 6)}")


if __name__ == "__main__":
    main()
