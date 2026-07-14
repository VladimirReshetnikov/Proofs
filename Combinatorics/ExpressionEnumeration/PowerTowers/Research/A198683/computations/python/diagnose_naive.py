"""Naive O(N^2) canonical-form dedup of A198683(12) candidates.

For each candidate, compute the exponent e such that value = exp(e). Two
candidates are equal iff e1 - e2 = 2 pi i k for some integer k, i.e.,
Re(e1) == Re(e2) AND (Im(e1) - Im(e2)) / (2 pi) is an integer.

Uses union-find with explicit pair-by-pair comparison at high precision.
Tolerance is taken relative to the magnitude of the operands.

Prints the count of equivalence classes and (optionally) a list of all
non-singleton classes with their candidate indices.

Also reruns the Python almosteq value-space dedup so the diagnostic is
self-contained, plus reports the partition refinement between the two
strategies.
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
        values[n] = _dedupe_mpc(cand, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    return values


class UF:
    def __init__(self, n):
        self.p = list(range(n))
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb
            return True
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=260)
    ap.add_argument("--strict-tol-frac", type=int, default=3,
                    help="strict tolerance = 10^-(dps/strict_tol_frac); default dps/3")
    ap.add_argument("--print-classes", type=int, default=20,
                    help="print up to this many non-singleton equivalence classes")
    args = ap.parse_args()

    dps = args.dps
    bucket_rel, cmp_tol = _setup_precision(dps)
    values = compute_values_upto_11(dps=dps)
    logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}
    PI = mp.pi
    TWOPI = 2 * PI

    cands = []
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
                e = b * la
                cands.append((k, ia, ib, e))

    n = len(cands)
    print(f"raw candidates: {n}")

    # Strategy 1 (almosteq + overflow, replicated)
    succ = []
    over = []
    digits_limit = mp.mpf(10_000)
    for idx, (_, _, _, e) in enumerate(cands):
        er = mp.re(e)
        ar = abs(er)
        log10_er = mp.ninf if ar == 0 else mp.log10(ar)
        if log10_er > digits_limit:
            over.append(idx)
        else:
            try:
                z = mp.exp(e)
                succ.append((idx, z))
            except OverflowError:
                over.append(idx)

    uf1 = UF(n)
    succ_buckets = defaultdict(list)
    def key_z(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))
    succ_reps = {}  # cls_root -> z value
    for idx, z in succ:
        k = key_z(z)
        merged = False
        for cls_root in succ_buckets[k]:
            zr = succ_reps[cls_root]
            if mp.almosteq(z, zr, rel_eps=cmp_tol, abs_eps=cmp_tol):
                uf1.union(idx, cls_root)
                merged = True
                break
        if not merged:
            succ_buckets[k].append(idx)
            succ_reps[idx] = z
    # All overflow candidates merged together (in original script)
    if over:
        root = over[0]
        for o in over[1:]:
            uf1.union(o, root)

    # Strategy 3 (naive O(N^2) canonical exponent comparison).
    strict_tol = mp.mpf(10) ** (-(dps // args.strict_tol_frac))
    uf3 = UF(n)
    # Bucket by approximate (Re(e), Im(e) mod 2pi) at coarse scale to avoid
    # O(N^2) cost in practice.
    # Two values equal iff Re(e1)=Re(e2) AND Im(e1)-Im(e2) in 2pi Z.
    # Equivalently, both Re(e) and Im(e) mod 2pi are equal.
    # Build naive bucket on rounded (Re(e), Im(e) mod 2pi).
    def im_mod_2pi(e):
        v = mp.im(e)
        return v - TWOPI * mp.nint(v / TWOPI)

    # Compute (re, im_mod) for each candidate.
    keys = []  # list of (idx, re, im_mod)
    for idx, (_, _, _, e) in enumerate(cands):
        rr = mp.re(e)
        im_mod = im_mod_2pi(e)
        keys.append((idx, rr, im_mod))

    # Coarse buckets on (sign(re), floor(log10|re|/0.5)*0.5, sign(im_mod), floor(log10|im_mod|/0.5)*0.5).
    coarse = defaultdict(list)
    def coarse_key(rr, im):
        def part(v):
            av = abs(v)
            if av == 0:
                return (0, 0)
            sg = 1 if v > 0 else -1
            mb = int(mp.floor(mp.log10(av) / mp.mpf("0.5")))
            return (sg, mb)
        return (part(rr), part(im))

    for idx, rr, im_mod in keys:
        coarse[coarse_key(rr, im_mod)].append(idx)

    # Inside each coarse bucket, do all-pairs comparison.
    def equal_e(e1, e2):
        # |Re(e1) - Re(e2)| <= strict_tol * max(1, |Re(e1)|, |Re(e2)|)
        # AND |Im(e1) - Im(e2) - 2 pi k| <= strict_tol * max(1, |Im(e1)|, |Im(e2)|, 2 pi |k|) for some integer k
        re1 = mp.re(e1); re2 = mp.re(e2)
        dre = re1 - re2
        rscale = max(mp.mpf(1), abs(re1), abs(re2))
        if abs(dre) > strict_tol * rscale:
            return False
        di = mp.im(e1) - mp.im(e2)
        k = mp.nint(di / TWOPI)
        rem = di - TWOPI * k
        iscale = max(mp.mpf(1), abs(mp.im(e1)), abs(mp.im(e2)), TWOPI * abs(k))
        if abs(rem) > strict_tol * iscale:
            return False
        return True

    for bk, idxs in coarse.items():
        m = len(idxs)
        if m < 2:
            continue
        for i in range(m):
            for j in range(i+1, m):
                a = idxs[i]; b = idxs[j]
                if uf3.find(a) == uf3.find(b):
                    continue
                if equal_e(cands[a][3], cands[b][3]):
                    uf3.union(a, b)
    # Across buckets that differ only by 2pi wrap: handle by also iterating
    # adjacent im buckets explicitly.
    # For safety, also do a global pass on tiny |re| and |im| values which
    # are most prone to coarse misses.
    tiny_idxs = []
    for idx, rr, im_mod in keys:
        if abs(rr) < mp.mpf(10) ** (-50) and abs(im_mod) < mp.mpf(10) ** (-50):
            tiny_idxs.append(idx)
    print(f"tiny candidates (|Re|,|Im_mod| < 1e-50): {len(tiny_idxs)}")
    for i in range(len(tiny_idxs)):
        for j in range(i+1, len(tiny_idxs)):
            a = tiny_idxs[i]; b = tiny_idxs[j]
            if uf3.find(a) == uf3.find(b):
                continue
            if equal_e(cands[a][3], cands[b][3]):
                uf3.union(a, b)

    # Class counts.
    def classes_from_uf(uf):
        groups = defaultdict(list)
        for i in range(n):
            groups[uf.find(i)].append(i)
        return list(groups.values())

    cls1 = classes_from_uf(uf1)
    cls3 = classes_from_uf(uf3)

    print(f"strategy 1 (almosteq+overflow): {len(cls1)} classes")
    print(f"strategy 3 (naive canonical e):  {len(cls3)} classes")

    # Compute partition refinement.
    map1 = [-1] * n
    for ci, cls in enumerate(cls1):
        for idx in cls:
            map1[idx] = ci
    map3 = [-1] * n
    for ci, cls in enumerate(cls3):
        for idx in cls:
            map3[idx] = ci

    s1_split_by_s3 = []
    for ci, cls in enumerate(cls1):
        sub = defaultdict(list)
        for idx in cls:
            sub[map3[idx]].append(idx)
        if len(sub) > 1:
            s1_split_by_s3.append((ci, dict(sub)))

    s3_split_by_s1 = []
    for ci, cls in enumerate(cls3):
        sub = defaultdict(list)
        for idx in cls:
            sub[map1[idx]].append(idx)
        if len(sub) > 1:
            s3_split_by_s1.append((ci, dict(sub)))

    print(f"\ns1 classes split by s3: {len(s1_split_by_s3)}")
    for s1_ci, sub in s1_split_by_s3:
        sizes = sorted(len(v) for v in sub.values())
        print(f"  s1 class {s1_ci} ({len(cls1[s1_ci])} elems) -> sizes {sizes}")
        for s3_ci, idxs in sub.items():
            i0 = idxs[0]
            k, ia, ib, e = cands[i0]
            print(f"    s3 class {s3_ci} ({len(idxs)} elems): first idx {i0} k={k} ia={ia} ib={ib}")

    print(f"\ns3 classes split by s1: {len(s3_split_by_s1)}")
    for s3_ci, sub in s3_split_by_s1:
        sizes = sorted(len(v) for v in sub.values())
        print(f"  s3 class {s3_ci} ({len(cls3[s3_ci])} elems) -> sizes {sizes}")
        for s1_ci, idxs in sub.items():
            i0 = idxs[0]
            k, ia, ib, e = cands[i0]
            print(f"    s1 class {s1_ci} ({len(idxs)} elems): first idx {i0} k={k} ia={ia} ib={ib}")


if __name__ == "__main__":
    main()
