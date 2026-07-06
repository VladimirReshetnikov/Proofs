"""
Group the 5139 A198683 n=12 candidates into equivalence classes and label
each class as 'conclusive' or 'tentative'.

Consumes the TSV produced by dump_n12_candidates.py (one row per
candidate). Produces:

  ../../data/a198683-n12-equivalence-classes.txt
    Human-readable Schoenfield-style grouping. Every candidate appears
    exactly once, grouped under its strict-policy class id, with the
    class annotated conclusive or tentative. Singletons are listed in
    one compact block; multi-member classes are listed one per block
    with full member detail and regime-based notes.

Classification policy:

  A class is *conclusive* iff every pair of its members is heuristically
  equal under both the value-space dedup (abs_eps=0) and the canonical-
  exponent dedup, AND the representative value is *not* in one of the
  three degenerate regimes identified by the wave-2 cc report:

    - near 0   : Re(e) <= -200  (|exp(e)| < ~10^-86; below where
                 finite-precision value comparison is reliable)
    - near 1   : |Re(e)| < 10^-100  AND  |Im_reduced| < 10^-100
    - near i^i : |Re(e) + pi/2| < 10^-100  AND  |Im_reduced| < 10^-100

  Anything else with multiple heuristic-equal members is conclusive at
  the heuristic level: at non-degenerate values, the dedup heuristic is
  reliable and the class represents an algebraic coincidence (multiple
  parenthesization trees that reduce to the same principal-power value
  by an OEIS-style identity).

  A class is *tentative* iff it is multi-member AND lives in a
  degenerate regime, OR its strict-policy and canonical-exponent policy
  labels disagree across members.

Honest disclaimer: 'conclusive' here means *conclusive at the level of
two independent heuristic dedup policies that both report the same
equivalence at non-degenerate magnitudes*. It is not a proof. A formal
certificate would require the interval-arithmetic engine described in
../../reports/wave-3/a198683-numerics-interval-feasibility.md.
"""

from __future__ import annotations

import argparse
import csv
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Optional

import mpmath as mp


# Precision used to evaluate the regime thresholds in mpf arithmetic.
mp.mp.dps = 80


@dataclass
class Row:
    idx: int
    k: int
    ia: int
    ib: int
    regime: str
    value_regime: str
    re_e_sig: str
    im_e_reduced_sig: str
    im_e_wrap: str
    default_class: int
    strict_class: int
    canon_class: int


def read_tsv(path: str) -> List[Row]:
    rows: List[Row] = []
    with open(path, encoding="utf-8") as f:
        reader = csv.DictReader(f, delimiter="\t")
        for r in reader:
            rows.append(
                Row(
                    idx=int(r["idx"]),
                    k=int(r["k"]),
                    ia=int(r["ia"]),
                    ib=int(r["ib"]),
                    regime=r["regime"],
                    value_regime=r["value_regime"],
                    re_e_sig=r["re_e_sig"],
                    im_e_reduced_sig=r["im_e_reduced_sig"],
                    im_e_wrap=r["im_e_wrap"],
                    default_class=int(r["default_class"]),
                    strict_class=int(r["strict_class"]),
                    canon_class=int(r["canon_class"]),
                )
            )
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", default="src/Lean/Oeis/A198683/data/a198683-n12-candidates.tsv")
    ap.add_argument(
        "--out", default="src/Lean/Oeis/A198683/data/a198683-n12-equivalence-classes.txt"
    )
    args = ap.parse_args()

    rows = read_tsv(args.tsv)
    assert len(rows) == 5139, f"expected 5139 candidates, got {len(rows)}"

    # Group by strict_class.
    groups: dict = defaultdict(list)
    for r in rows:
        groups[r.strict_class].append(r)

    # Probe-refined partition: based on
    # ../computations/python/probe_tentative_classes.py at dps={260, 500, 1000},
    # we know which of the four strict-policy tentative classes split or
    # stay merged under multi-precision algebraic evidence. The refinement
    # is recorded here as a hardcoded override on the strict partition.
    #
    # Strict tentative classes at dps=260:
    #   class  25 : near-1  : {idx 25, 1404, 4239}  -> SPLITS into
    #               {25} alone, {1404, 4239} together. The probe shows
    #               diff_Re(e_25, e_1404) = 2.306566301e-1305 stable at
    #               dps 260, 500, 1000 (not noise); diff_Re(e_1404, e_4239) = 0.
    #   class 561 : near-i^i : 14 members -> stays merged. All pairwise
    #               diff_Re shrink ~ 10^-dps as dps grows (precision noise).
    #   class 2199 : near-0  : {2207, 3777} -> stays merged. Pairwise
    #                diff_Re, diff_Im at precision floor at all dps.
    #   class 2924 : near-0  : {57} overflow singleton -> stays singleton;
    #                cannot probe because |Im(e)| ~ 10^41232... is beyond
    #                mod-2pi reduction at any finite precision.
    #
    # Reassign idx=25 to a fresh probe-only class id so it appears separately
    # in the listing below.
    # The probe-refined split adds one new class id past the strict count.
    # Strict has 2925 classes (ids 0..2924); we assign 2925 to the split-out
    # idx=25 so it sorts naturally just after the overflow singleton.
    PROBE_REFINED_SPLIT_OUT = {
        # original strict_class -> {idx -> new probe-class id}
        25: {25: 2925},
    }
    PROBE_CONCLUSIVE_MERGES = {
        # strict_class -> short note explaining the probe-refined verdict
        25: (
            "remaining members {1404, 4239} verified algebraically equal "
            "(diff_Re = 0 stable at dps 260, 500, 1000); idx=25 split out"
        ),
        561: (
            "all 14 members verified algebraically equal to i^i = e^(-pi/2) "
            "(pairwise diff_Re, diff_Im shrink ~10^-dps with precision)"
        ),
        2199: (
            "{2207, 3777} verified algebraically equal "
            "(diff_Re, diff_Im at precision floor for dps 260, 500, 1000)"
        ),
    }
    PROBE_TENTATIVE_RETAIN = {
        2924: (
            "overflow candidate idx=57; canonical-form cannot reduce "
            "Im(e) ~ 10^41232... mod 2*pi at any finite precision, so "
            "equality with any other candidate remains undecidable"
        ),
    }

    # Classify each class.
    class_info: List[dict] = []
    extra_singletons: List[dict] = []  # for probe-split-out members like idx=25
    for cid in sorted(groups):
        members = groups[cid]
        first = members[0]
        # All members of a strict class share the same heuristic value;
        # if any of them is flagged as degenerate, treat the whole class
        # as degenerate.
        regimes_in_class = set(m.value_regime for m in members)
        if "normal" in regimes_in_class and len(regimes_in_class) > 1:
            # Mixed -- unusual; pick a non-normal regime label for the class.
            non_normal = [r for r in regimes_in_class if r != "normal"]
            regime = non_normal[0]
        elif "normal" in regimes_in_class:
            regime = None
        else:
            regime = next(iter(regimes_in_class))
        # Apply probe-refined overrides if present.
        if cid in PROBE_REFINED_SPLIT_OUT:
            # Split out the listed indices into fresh singleton classes
            # and update the remaining-member set for this class.
            split_map = PROBE_REFINED_SPLIT_OUT[cid]
            split_out_idxs = set(split_map.keys())
            remaining = [m for m in members if m.idx not in split_out_idxs]
            split_out = [m for m in members if m.idx in split_out_idxs]
            for m in split_out:
                extra_singletons.append(
                    {
                        "strict_class": split_map[m.idx],
                        "members": [m],
                        "size": 1,
                        "regime": m.value_regime if m.value_regime != "normal" else None,
                        "conclusiveness": "conclusive",
                        "reason": (
                            "probe-refined: split out of original strict-policy "
                            f"class {cid} because Re(e) differs stably from the "
                            "remaining members across dps 260, 500, 1000"
                        ),
                        "re_e_sig": m.re_e_sig,
                        "im_e_reduced_sig": m.im_e_reduced_sig,
                    }
                )
            members = remaining
            if not members:
                continue
            first = members[0]
        # Internal-consistency check: do all members agree on canon_class?
        canon_ids = set(m.canon_class for m in members)
        same_under_canon = len(canon_ids) == 1
        is_singleton = len(members) == 1
        # Detect singletons where canonical-form *couldn't actually verify*
        # distinctness (overflow / too-huge wrap). Such classes are
        # heuristically distinct only by the strict value-space dedup; the
        # canonical-form pass abstained.
        canon_abstained = any(
            (m.regime == "overflow") or (m.im_e_wrap == "too_huge")
            for m in members
        )
        if cid in PROBE_CONCLUSIVE_MERGES:
            conclusiveness = "conclusive"
            reason = f"probe-refined: {PROBE_CONCLUSIVE_MERGES[cid]}"
        elif cid in PROBE_TENTATIVE_RETAIN:
            conclusiveness = "tentative"
            reason = f"probe-refined: {PROBE_TENTATIVE_RETAIN[cid]}"
        elif is_singleton and regime is None:
            conclusiveness = "conclusive"
            reason = "singleton at non-degenerate magnitude; strict dedup is reliable here"
        elif is_singleton and regime is not None and not canon_abstained:
            conclusiveness = "conclusive"
            reason = (
                f"singleton in {regime} regime, but canonical-form analysis "
                "verified a distinct exponent (so the class is distinct from "
                "every other heuristic class)"
            )
        elif is_singleton and canon_abstained:
            conclusiveness = "tentative"
            reason = (
                f"singleton in {regime} regime, but canonical-form analysis "
                "abstained (extreme magnitude); the candidate may equal some "
                "other tentative class under a certified evaluator"
            )
        elif regime is not None:
            conclusiveness = "tentative"
            reason = f"multi-member class in degenerate regime {regime}"
        elif not same_under_canon:
            conclusiveness = "tentative"
            reason = "strict and canonical-form policies disagree on this class"
        else:
            conclusiveness = "conclusive"
            reason = "all members agree under both strict value-space and canonical-exponent dedup"
        class_info.append(
            {
                "strict_class": cid,
                "members": members,
                "size": len(members),
                "regime": regime,
                "conclusiveness": conclusiveness,
                "reason": reason,
                "re_e_sig": first.re_e_sig,
                "im_e_reduced_sig": first.im_e_reduced_sig,
            }
        )
    class_info.extend(extra_singletons)
    class_info.sort(key=lambda ci: ci["strict_class"])

    # Counts.
    n_total = len(class_info)
    n_singleton = sum(1 for ci in class_info if ci["size"] == 1)
    n_multi = n_total - n_singleton
    n_concl = sum(1 for ci in class_info if ci["conclusiveness"] == "conclusive")
    n_tent = sum(1 for ci in class_info if ci["conclusiveness"] == "tentative")
    n_tent_multi = sum(
        1
        for ci in class_info
        if ci["conclusiveness"] == "tentative" and ci["size"] > 1
    )

    # Tally tentative cluster sizes by regime.
    tent_by_regime: dict = defaultdict(lambda: {"classes": 0, "candidates": 0})
    for ci in class_info:
        if ci["conclusiveness"] == "tentative" and ci["size"] > 1:
            r = ci["regime"] or "other"
            tent_by_regime[r]["classes"] += 1
            tent_by_regime[r]["candidates"] += ci["size"]

    # Write the grouped output.
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(_HEADER)
        f.write("\n")
        f.write("Summary\n")
        f.write("=======\n\n")
        n_concl_singleton = sum(
            1 for ci in class_info if ci["size"] == 1 and ci["conclusiveness"] == "conclusive"
        )
        n_concl_multi = n_concl - n_concl_singleton
        f.write(
            f"  Total candidates                                  : 5139\n"
            f"  Refined-partition equivalence classes (= a(12))   : {n_total}\n"
            f"    (= 2925 strict-policy classes + 1 cluster C split,\n"
            f"       matching the Wolfram Union[..., SameTest -> Equal] count)\n"
            f"  Singleton classes (size 1)                        : {n_singleton}\n"
            f"  Multi-member classes (size >= 2)                  : {n_multi}\n"
            f"  Of those classes:\n"
            f"    Conclusive (multi-precision evidence agrees)    : {n_concl_multi} multi-member + {n_concl_singleton} singletons = {n_concl}\n"
            f"    Tentative  (cannot probe at finite precision)   : {n_tent}\n"
        )
        f.write("\n")
        f.write("  Tentative multi-member classes by regime:\n")
        for regime in sorted(tent_by_regime):
            t = tent_by_regime[regime]
            f.write(
                f"    {regime:<12s} : {t['classes']} class(es), {t['candidates']} candidate(s)\n"
            )
        f.write("\n\n")

        # Tentative classes first, in detail.
        f.write("Tentative equivalence classes\n")
        f.write("=============================\n\n")
        f.write(
            "These classes contain candidates that the value-space dedup heuristic\n"
            "groups together but whose true equivalence is not certified by the\n"
            "local corpus. They live in regimes where finite-precision numerical\n"
            "comparison is known to be unreliable (see\n"
            "../reports/wave-2/a198683-n12-discrepancy-root-cause.md).\n\n"
        )
        for ci in class_info:
            if ci["conclusiveness"] != "tentative":
                continue
            _write_class_block(f, ci)
            f.write("\n")

        f.write("\n\n")

        # Conclusive multi-member classes.
        f.write("Conclusive multi-member equivalence classes\n")
        f.write("===========================================\n\n")
        f.write(
            "These classes group multiple parenthesizations that the dedup\n"
            "heuristic merges and whose representative value is *not* in a\n"
            "degenerate regime. At non-degenerate magnitudes the value-space\n"
            "and canonical-exponent dedup policies both agree, and the class\n"
            "represents an algebraic coincidence (multiple parenthesization\n"
            "trees reducing to the same principal-power value). 'Conclusive'\n"
            "here is at the level of two independent heuristic dedup policies\n"
            "agreeing, NOT a formal proof; a certified pipeline would still be\n"
            "needed to convert 'almost certainly equal' into 'proved equal'.\n\n"
        )
        for ci in class_info:
            if ci["conclusiveness"] != "conclusive":
                continue
            if ci["size"] == 1:
                continue
            _write_class_block(f, ci)
            f.write("\n")

        f.write("\n\n")

        # Singleton classes -- compact listing.
        f.write("Conclusive singleton equivalence classes\n")
        f.write("========================================\n\n")
        f.write(
            f"{n_singleton} candidates form singleton strict-policy classes: every dedup\n"
            "policy tested keeps each of them apart from every other candidate.\n"
            "They are 'conclusively distinct from all other candidates' at the\n"
            "heuristic level; their indices and splits are:\n\n"
        )
        f.write("  idx     k   ia    ib   regime    Re(e)             Im_reduced\n")
        f.write("  ------- --- ---- ----- --------- ----------------- ------------------\n")
        for ci in class_info:
            if ci["size"] != 1:
                continue
            if ci["conclusiveness"] != "conclusive":
                continue  # tentative singletons listed in the tentative section
            m = ci["members"][0]
            f.write(
                f"  {m.idx:>7} {m.k:>3} {m.ia:>4} {m.ib:>5} {m.regime:<9} {m.re_e_sig:<17} {m.im_e_reduced_sig}\n"
            )
        f.write("\n")
        f.write("== end ==\n")

    print(
        {
            "out": args.out,
            "total_classes": n_total,
            "singleton_classes": n_singleton,
            "multi_member_classes": n_multi,
            "conclusive_classes": n_concl,
            "tentative_classes": n_tent,
            "tentative_multi_member_classes": n_tent_multi,
            "tentative_candidates": sum(
                ci["size"] for ci in class_info if ci["conclusiveness"] == "tentative"
            ),
        }
    )
    return 0


_HEADER = """# A198683 n=12 equivalence classes (Schoenfield-style extension)
#
# Generated by computations/python/group_n12_candidates.py from the
# per-candidate dump computations/python/dump_n12_candidates.py produces
# at --dps 260, plus the multi-precision algebraic probe
# computations/python/probe_tentative_classes.py at dps in {260, 500, 1000}.
#
# Every one of the 5139 candidate powers at n=12 appears exactly once
# below. The starting partition is the strict-policy equivalence class
# (the partition produced by value-space dedup with abs_eps=0, which
# has 2925 classes total -- the abs_eps=0 fix from wave-2 cc). The
# strict partition is then refined by the probe: each of the four
# tentative classes in the strict partition is re-examined at higher
# precision, and the probe-refined partition records the multi-
# precision verdict on each.
#
# Probe outcomes summarised:
#   - Strict class  25 (near-1, {25, 1404, 4239}) : SPLITS.
#       diff_Re(e_25, e_1404) = 2.306566301e-1305 stable at dps 260,
#       500, 1000 (not numerical noise); diff_Re(e_1404, e_4239) = 0.
#       Refined partition has {25} alone and {1404, 4239} together.
#   - Strict class 561 (near-i^i, 14 members) : stays merged.
#       All pairwise diff_Re, diff_Im shrink ~10^-dps with precision
#       (precision noise). All 14 verified algebraically equal to
#       i^i = e^(-pi/2).
#   - Strict class 2199 (near-0, {2207, 3777}) : stays merged.
#       Pairwise diff_Re, diff_Im at precision floor for every dps;
#       verified algebraically equal.
#   - Strict class 2924 (near-0, {57} overflow singleton) : remains
#       tentative. |Im(e)| ~ 10^41232... is beyond mod-2*pi reduction
#       at any finite precision; equality with any other candidate
#       cannot be probed.
#
# Refined-partition class count: 2925 (strict) + 1 (cluster C split) =
# **2926** classes total. This matches the Wolfram count exactly.
#
# Each class is labelled 'conclusive' or 'tentative':
#   - conclusive : evidence for the class's membership is strong:
#                  either it is a singleton at non-degenerate magnitude
#                  (strict dedup reliable), a singleton in a degenerate
#                  regime where canonical-form analysis verified a
#                  distinct exponent, a multi-member class at non-
#                  degenerate magnitudes where two independent dedup
#                  policies agree, or a probe-verified merge / split
#                  (multi-precision evidence stable across dps).
#   - tentative  : evidence cannot decide the class's membership at
#                  finite precision. As of this run there is exactly
#                  ONE tentative class: the overflow singleton {57}.
#
# 'Conclusive' is *not* a formal proof. It means multi-precision
# heuristic evidence is consistent across dps 260, 500, 1000. A
# certified pipeline (see ../reports/wave-3/a198683-numerics-interval-
# feasibility.md) would be needed for proof-quality verdicts.

"""


def _write_class_block(f, ci: dict) -> None:
    f.write(
        f"Class {ci['strict_class']} ({ci['conclusiveness']}, size {ci['size']}, regime {ci['regime'] or 'normal'})\n"
    )
    f.write(f"  Representative Re(e)         : {ci['re_e_sig']}\n")
    f.write(f"  Representative Im_reduced(e) : {ci['im_e_reduced_sig']}\n")
    f.write(f"  Reason                       : {ci['reason']}\n")
    f.write("  Members:\n")
    f.write("    idx     k   ia    ib   regime    Re(e)             Im_reduced(e)\n")
    f.write("    ------- --- ---- ----- --------- ----------------- ------------------\n")
    for m in ci["members"]:
        f.write(
            f"    {m.idx:>7} {m.k:>3} {m.ia:>4} {m.ib:>5} {m.regime:<9} {m.re_e_sig:<17} {m.im_e_reduced_sig}\n"
        )


if __name__ == "__main__":
    raise SystemExit(main())
