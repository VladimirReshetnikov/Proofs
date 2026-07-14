"""Trace the dynamic-programming representative expression for A198683.

The n=12 candidate TSV is generated from a dynamic-programming list of
deduplicated values.  This helper re-runs the same numerical recurrence while
carrying one representative expression string per retained value, then prints
the requested `values[n][index]` entry.

This is a diagnostic and provenance tool, not a proof certificate.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterable

import mpmath as mp


@dataclass(frozen=True)
class Representative:
    value: mp.mpc
    expr: str


def setup_precision(dps: int) -> tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


def dedupe(
    reps: Iterable[Representative], *, bucket_rel: mp.mpf, cmp_tol: mp.mpf
) -> list[Representative]:
    def key(z: mp.mpc) -> tuple[int, int]:
        scale = max(1, abs(z))
        step = scale * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    buckets: dict[tuple[int, int], list[int]] = defaultdict(list)
    out: list[Representative] = []
    for rep in reps:
        k = key(rep.value)
        for idx in buckets[k]:
            if mp.almosteq(rep.value, out[idx].value, rel_eps=cmp_tol, abs_eps=cmp_tol):
                break
        else:
            buckets[k].append(len(out))
            out.append(rep)
    return out


def compute_representatives(max_n: int, *, dps: int) -> dict[int, list[Representative]]:
    bucket_rel, cmp_tol = setup_precision(dps)
    values: dict[int, list[Representative]] = {1: [Representative(mp.mpc(0, 1), "i")]}
    for n in range(2, max_n + 1):
        candidates: list[Representative] = []
        for k in range(1, n):
            for left in values[k]:
                for right in values[n - k]:
                    candidates.append(
                        Representative(
                            mp.power(left.value, right.value),
                            f"({left.expr}^{right.expr})",
                        )
                    )
        values[n] = dedupe(candidates, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    return values


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--index", type=int, required=True, help="0-based retained-value index")
    parser.add_argument("--dps", type=int, default=260)
    args = parser.parse_args()

    values = compute_representatives(args.n, dps=args.dps)
    for n in range(1, args.n + 1):
        print(f"n={n}: {len(values[n])} retained values")

    rep = values[args.n][args.index]
    print()
    print(f"values[{args.n}][{args.index}]")
    print(f"expr: {rep.expr}")
    print(f"Re: {mp.nstr(mp.re(rep.value), 50)}")
    print(f"Im: {mp.nstr(mp.im(rep.value), 50)}")
    print(f"log10 |Im|: {mp.nstr(mp.log10(abs(mp.im(rep.value))), 50)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
