"""
Dump every A198683 n=12 candidate power with its (k, ia, ib) split and
equivalence-class labels under three heuristic deduplication policies.

This script is a wave-3 companion to compute_a198683.py. It enumerates the
same 5139 candidates that script computes at n=12 -- one per ordered pair
(left-value, right-value) where left has k copies of i, right has 12-k
copies of i, both drawn from the deduped lower-level sets V[k] and V[12-k]
-- and assigns each candidate three policy labels:

1. default_class    : value-space dedup with mpmath.almosteq(abs_eps=rel_eps),
                      exactly as compute_a198683.py runs by default. This is
                      the policy whose total is 2919.
2. strict_class     : value-space dedup with abs_eps=0. This is the policy
                      whose total is 2925 (per the wave-2 cc analysis), and
                      it is the policy used to *split* the near-zero cluster
                      into its component classes.
3. canon_class      : canonical-exponent dedup. Two candidates are merged iff
                      Re(e_1) == Re(e_2) and (Im(e_1) - Im(e_2)) mod 2pi == 0,
                      all checked at the working precision. This is the
                      policy used by the diagnose_dedup.py script in this
                      directory; cc's report notes it can over-split at
                      extreme magnitudes (near i^i in particular).

The "settled" partition is the join of the three policies: two candidates
are *settled-equivalent* iff every policy puts them in the same class. A
candidate that ends up alone in its strict class (size 1) is settled-
distinct from every other candidate at this evidence level. A multi-
candidate class under the strict policy that is *not* further split by the
canonical-exponent policy is a *tentative* class -- its members are
heuristically equal under both value-space and canonical-form analyses
but no proof-quality certificate exists in the corpus to confirm equality.

Output format: tab-separated CSV with one row per candidate.

Columns:
  idx           : 0-based candidate index, matching the order
                  compute_a198683.py enumerates candidates.
  k             : left-operand size, 1 <= k <= 11.
  ia            : 0-based index of the left operand in V[k].
  ib            : 0-based index of the right operand in V[12-k].
  regime        : 'success' (mpmath could materialise exp(e)) or
                  'overflow' (it could not -- e's real part is too large).
  re_e_sig      : Re(e) in scientific notation with 6 significant digits.
                  e = b * log(a) is the level-12 exponent before exp(e).
  im_e_sig      : Im(e), reduced to (-pi, pi], in scientific notation with
                  6 significant digits. The pre-reduction value would be
                  astronomical for large k.
  im_e_wrap     : floor((Im(e) + pi) / (2*pi)), the wrap integer that the
                  canonical-form reduction subtracted from Im(e). Reported
                  as 'n/a' if Im(e) is below the dedup tolerance.
  default_class : 0-based class id under the default-tolerance value-space
                  dedup.
  strict_class  : 0-based class id under the abs_eps=0 value-space dedup.
  canon_class   : 0-based class id under the canonical-exponent dedup.

Each class id space is a fresh 0-based numbering; matching ids across
different policy columns are unrelated.

Run:

    python dump_n12_candidates.py --dps 260

The default --dps 260 matches the wave-1 / wave-2 documented runs so that
the (k, ia, ib) splits in this dump match the indices cited in
../../reports/wave-2/a198683-n12-discrepancy-root-cause.md.
"""

from __future__ import annotations

import argparse
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable, List, Optional, Tuple

import mpmath as mp


# ----------------------------------------------------------------------
# Lower-level value sets (copied from compute_a198683.py so this script
# can run standalone).
# ----------------------------------------------------------------------


def _setup_precision(dps: int) -> Tuple[mp.mpf, mp.mpf]:
    mp.mp.dps = dps
    bucket_rel = mp.mpf(10) ** (-(mp.mp.dps // 3))
    cmp_tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
    return bucket_rel, cmp_tol


def _dedupe_mpc(values, *, bucket_rel, cmp_tol, abs_eps):
    """Value-space dedup with explicit abs_eps. Returns (deduped_list, class_ids).

    class_ids[i] is the class label assigned to values[i].
    """
    def key(z):
        s = max(1, abs(z))
        step = s * bucket_rel
        return (int(mp.nint(mp.re(z) / step)), int(mp.nint(mp.im(z) / step)))

    buckets: dict = defaultdict(list)  # bucket -> list of (deduped-idx, representative)
    out = []
    class_ids = []
    for z in values:
        k = key(z)
        assigned = None
        for idx in buckets[k]:
            if mp.almosteq(z, out[idx], rel_eps=cmp_tol, abs_eps=abs_eps):
                assigned = idx
                break
        if assigned is None:
            assigned = len(out)
            buckets[k].append(assigned)
            out.append(z)
        class_ids.append(assigned)
    return out, class_ids


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
        deduped, _ = _dedupe_mpc(cand, bucket_rel=bucket_rel, cmp_tol=cmp_tol, abs_eps=cmp_tol)
        values[n] = deduped
    return values


# ----------------------------------------------------------------------
# n=12 candidate enumeration with full per-candidate bookkeeping.
# ----------------------------------------------------------------------


@dataclass
class Candidate:
    idx: int
    k: int
    ia: int
    ib: int
    e: mp.mpc                     # The level-12 exponent, b * log(a).
    z: Optional[mp.mpc]           # exp(e) if materialisable, else None.
    regime: str                   # 'success' or 'overflow'.
    default_class: int = -1
    strict_class: int = -1
    canon_class: int = -1         # canonical-exponent, abs_eps = cmp_tol
    canon_strict_class: int = -1  # canonical-exponent, abs_eps = 0


def enumerate_candidates(*, dps: int, overflow_digits_limit: int = 10_000) -> List[Candidate]:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    _setup_precision(dps)
    values = compute_values_upto_11(dps=dps)
    logs = {n: [mp.log(z) for z in values[n]] for n in range(1, 12)}

    digits_limit = mp.mpf(overflow_digits_limit)

    cands: List[Candidate] = []
    idx = 0
    for k in range(1, 12):
        left_logs = logs[k]
        right = values[12 - k]
        for ia, la in enumerate(left_logs):
            for ib, b in enumerate(right):
                e = b * la
                er = mp.re(e)
                if er == 0:
                    log10er = mp.mpf(0)
                else:
                    log10er = mp.log10(abs(er))
                regime = "success"
                z: Optional[mp.mpc] = None
                if log10er > digits_limit:
                    regime = "overflow"
                else:
                    try:
                        z = mp.exp(e)
                    except OverflowError:
                        regime = "overflow"
                        z = None
                cands.append(Candidate(idx=idx, k=k, ia=ia, ib=ib, e=e, z=z, regime=regime))
                idx += 1
    assert len(cands) == 5139, f"unexpected candidate total {len(cands)}"
    return cands


# ----------------------------------------------------------------------
# Three dedup policies over the same candidate list.
# ----------------------------------------------------------------------


def label_default(cands: List[Candidate], *, bucket_rel, cmp_tol) -> None:
    """Default-tolerance value-space dedup. Mirrors compute_a198683.py exactly."""
    successes = [c for c in cands if c.regime == "success"]
    overflows = [c for c in cands if c.regime == "overflow"]

    _, success_ids = _dedupe_mpc(
        [c.z for c in successes],
        bucket_rel=bucket_rel,
        cmp_tol=cmp_tol,
        abs_eps=cmp_tol,
    )
    for c, cid in zip(successes, success_ids):
        c.default_class = cid

    # Overflow candidates dedupe on (Re(e), Im(e)) pairs; in this corpus there
    # is exactly one overflow candidate, but for completeness we follow
    # compute_a198683.py's _dedupe_pairs logic.
    n_success_classes = (max(success_ids) + 1) if success_ids else 0

    def pair_key(x, y):
        sx = max(1, abs(x))
        sy = max(1, abs(y))
        stepx = sx * bucket_rel
        stepy = sy * bucket_rel
        return (int(mp.nint(x / stepx)), int(mp.nint(y / stepy)))

    overflow_buckets: dict = defaultdict(list)
    overflow_reps: List[Tuple] = []
    for c in overflows:
        x, y = mp.re(c.e), mp.im(c.e)
        k = pair_key(x, y)
        assigned = None
        for idx in overflow_buckets[k]:
            x2, y2 = overflow_reps[idx]
            if (
                mp.almosteq(x, x2, rel_eps=cmp_tol, abs_eps=cmp_tol)
                and mp.almosteq(y, y2, rel_eps=cmp_tol, abs_eps=cmp_tol)
            ):
                assigned = idx
                break
        if assigned is None:
            assigned = len(overflow_reps)
            overflow_buckets[k].append(assigned)
            overflow_reps.append((x, y))
        c.default_class = n_success_classes + assigned


def label_strict(cands: List[Candidate], *, bucket_rel, cmp_tol) -> None:
    """Same value-space dedup but with abs_eps=0."""
    successes = [c for c in cands if c.regime == "success"]
    overflows = [c for c in cands if c.regime == "overflow"]

    _, success_ids = _dedupe_mpc(
        [c.z for c in successes],
        bucket_rel=bucket_rel,
        cmp_tol=cmp_tol,
        abs_eps=mp.mpf(0),
    )
    for c, cid in zip(successes, success_ids):
        c.strict_class = cid

    n_success_classes = (max(success_ids) + 1) if success_ids else 0

    def pair_key(x, y):
        sx = max(1, abs(x))
        sy = max(1, abs(y))
        stepx = sx * bucket_rel
        stepy = sy * bucket_rel
        return (int(mp.nint(x / stepx)), int(mp.nint(y / stepy)))

    overflow_buckets: dict = defaultdict(list)
    overflow_reps: List[Tuple] = []
    for c in overflows:
        x, y = mp.re(c.e), mp.im(c.e)
        k = pair_key(x, y)
        assigned = None
        for idx in overflow_buckets[k]:
            x2, y2 = overflow_reps[idx]
            if (
                mp.almosteq(x, x2, rel_eps=cmp_tol, abs_eps=mp.mpf(0))
                and mp.almosteq(y, y2, rel_eps=cmp_tol, abs_eps=mp.mpf(0))
            ):
                assigned = idx
                break
        if assigned is None:
            assigned = len(overflow_reps)
            overflow_buckets[k].append(assigned)
            overflow_reps.append((x, y))
        c.strict_class = n_success_classes + assigned


def reduce_im_mod_2pi(im: mp.mpf) -> Tuple[mp.mpf, str]:
    """Reduce im into (-pi, pi].

    Returns (reduced, wrap_repr). reduced is an mpf in (-pi, pi].
    wrap_repr is a string description of the wrap integer:
        - the exact integer as a string for moderate magnitudes,
        - 'huge:<order>' for magnitudes beyond what is meaningful at
          the current working precision,
        - 'too_huge' if |im| is so large that even mp.fmod cannot
          produce a meaningful residue.

    For the canonical-form dedup we only need `reduced`; the wrap
    string is diagnostic.
    """
    if im == 0:
        return mp.mpf(0), "0"
    two_pi = 2 * mp.pi
    # mp.fmod keeps the result bounded by 2pi without materialising the wrap.
    # First shift by pi so the result lands in (-pi, pi] after adjusting.
    log10_abs = mp.log10(abs(im))
    # mp.fmod's relative error scales with |im| / |2pi| at working precision.
    # For dps decimal digits of precision, the residue is meaningful only
    # while |im| << 10^dps. We guard at dps - 50 digits of headroom.
    safety_threshold = mp.mp.dps - 50
    if log10_abs > safety_threshold:
        return mp.mpf(0), "too_huge"
    raw = mp.fmod(im + mp.pi, two_pi)
    # mp.fmod returns a value with sign of (im+pi); normalise to [0, 2pi).
    if raw < 0:
        raw += two_pi
    reduced = raw - mp.pi  # now in (-pi, pi].
    # Compute a coarse description of the wrap integer for diagnostics.
    if log10_abs <= 30:
        # Safe to materialise as Python int.
        wrap_mpf = (im - reduced) / two_pi
        wrap_str = str(int(wrap_mpf))
    else:
        wrap_str = f"huge:1e{int(log10_abs)}"
    return reduced, wrap_str


def label_canonical(cands: List[Candidate], *, cmp_tol, abs_eps=None, target: str = "canon_class") -> None:
    """Canonical-exponent dedup.

    Two candidates are merged iff Re(e_1) == Re(e_2) (with relative
    tolerance ``cmp_tol`` and absolute floor ``abs_eps``) AND
    (Im(e_1) - Im(e_2)) reduces to 0 modulo 2pi at the same tolerance.

    The bucket key on (Re(e), Im(e) mod 2pi) keeps comparisons O(1) on
    average.

    With ``abs_eps=cmp_tol`` (the default), two exponents whose
    difference is smaller than ``cmp_tol`` get merged regardless of
    structure -- this is the value-space analogue of the wave-2 cc
    artefact, but applied to exponents rather than materialised values.

    With ``abs_eps=0`` the absolute-tolerance floor is removed: two
    exponents are merged only if their difference is small *relative*
    to their magnitudes. This separates the cluster-C 'near 1'
    candidates whose Re(e) values are 6.78e-2487 vs -2.31e-1305 (huge
    relative difference, tiny absolute difference).
    """
    if abs_eps is None:
        abs_eps = cmp_tol
    # Use cmp_tol as both bucket step (in log space) and equality tolerance.
    re_step = cmp_tol
    im_step = cmp_tol

    def key(re_, im_reduced):
        sre = max(1, abs(re_))
        sim = max(1, abs(im_reduced))
        stepr = sre * re_step
        stepi = sim * im_step
        return (int(mp.nint(re_ / stepr)), int(mp.nint(im_reduced / stepi)))

    reduced_cache: List[Tuple[mp.mpf, str]] = []
    for c in cands:
        red, wrap = reduce_im_mod_2pi(mp.im(c.e))
        reduced_cache.append((red, wrap))

    buckets: dict = defaultdict(list)  # bk -> [canon_class_id, ...]
    reps: dict = {}                    # canon_class_id -> (Re, Im_reduced)
    n_classes = 0
    for i, c in enumerate(cands):
        re_ = mp.re(c.e)
        im_red, wrap_str = reduced_cache[i]
        # Candidates whose Im(e) is beyond meaningful reduction at this
        # precision get a unique canonical class -- the reduction cannot
        # decide their equivalence at finite precision, so we cannot merge.
        if wrap_str == "too_huge" or c.regime == "overflow":
            setattr(c, target, n_classes)
            n_classes += 1
            continue
        bk = key(re_, im_red)
        assigned = None
        for cid in buckets[bk]:
            re_rep, im_rep = reps[cid]
            if not mp.almosteq(re_, re_rep, rel_eps=cmp_tol, abs_eps=abs_eps):
                continue
            # Im comparison must close the (Im_1 - Im_2) mod 2pi gap.
            diff = im_red - im_rep
            diff_mod, _ = reduce_im_mod_2pi(diff)
            if mp.almosteq(diff_mod, 0, rel_eps=cmp_tol, abs_eps=abs_eps):
                assigned = cid
                break
        if assigned is None:
            assigned = n_classes
            n_classes += 1
            buckets[bk].append(assigned)
            reps[assigned] = (re_, im_red)
        setattr(c, target, assigned)


# ----------------------------------------------------------------------
# Output.
# ----------------------------------------------------------------------


def format_mpf(x: mp.mpf, digits: int = 6) -> str:
    """Format an mpf as scientific notation with `digits` significant digits."""
    if x == 0:
        return "0"
    return mp.nstr(x, digits, strip_zeros=False)


def classify_regime(re_e: mp.mpf, im_red: mp.mpf, regime: str) -> str:
    """Classify a candidate's value regime at full working precision.

    The thresholds match the wave-2 cc analysis's three structurally-
    degenerate clusters; anything else is 'normal' (the dedup heuristic
    is reliable there).
    """
    # Overflow candidates are inherently in the "near-0 or near-infinity"
    # extreme regime; mpmath cannot materialise exp(e). cc treats the
    # single overflow candidate as a near-zero cluster member, so we
    # report it as near-0.
    if regime == "overflow":
        return "near-0"
    # near 0: exp(e) is exponentially small.
    if re_e < mp.mpf(-200):
        return "near-0"
    # near 1: |e| very small.
    if abs(re_e) < mp.mpf("1e-100") and abs(im_red) < mp.mpf("1e-100"):
        return "near-1"
    # near i^i: Re(e) ~ -pi/2, Im(e) ~ 0.
    if abs(re_e + mp.pi / 2) < mp.mpf("1e-100") and abs(im_red) < mp.mpf("1e-100"):
        return "near-i^i"
    return "normal"


def write_csv(cands: List[Candidate], path: str) -> None:
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(
            "idx\tk\tia\tib\tregime\tvalue_regime\tre_e_sig\tim_e_reduced_sig\tim_e_wrap\tdefault_class\tstrict_class\tcanon_class\tcanon_strict_class\n"
        )
        for c in cands:
            re_e = mp.re(c.e)
            im_e = mp.im(c.e)
            im_red, wrap_str = reduce_im_mod_2pi(im_e)
            value_regime = classify_regime(re_e, im_red, c.regime)
            f.write(
                "\t".join(
                    [
                        str(c.idx),
                        str(c.k),
                        str(c.ia),
                        str(c.ib),
                        c.regime,
                        value_regime,
                        format_mpf(re_e, 6),
                        format_mpf(im_red, 6),
                        wrap_str,
                        str(c.default_class),
                        str(c.strict_class),
                        str(c.canon_class),
                        str(c.canon_strict_class),
                    ]
                )
                + "\n"
            )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=260)
    ap.add_argument("--out", type=str, default="dump_n12_candidates.tsv")
    args = ap.parse_args()

    bucket_rel, cmp_tol = _setup_precision(args.dps)
    cands = enumerate_candidates(dps=args.dps)

    label_default(cands, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    label_strict(cands, bucket_rel=bucket_rel, cmp_tol=cmp_tol)
    label_canonical(cands, cmp_tol=cmp_tol, abs_eps=cmp_tol, target="canon_class")
    label_canonical(cands, cmp_tol=cmp_tol, abs_eps=mp.mpf(0), target="canon_strict_class")

    write_csv(cands, args.out)

    # Diagnostic summary.
    default_classes = max(c.default_class for c in cands) + 1
    strict_classes = max(c.strict_class for c in cands) + 1
    canon_classes = max(c.canon_class for c in cands) + 1
    canon_strict_classes = max(c.canon_strict_class for c in cands) + 1
    print(
        {
            "dps": args.dps,
            "candidate_total": len(cands),
            "default_classes": default_classes,
            "strict_classes": strict_classes,
            "canon_classes": canon_classes,
            "canon_strict_classes": canon_strict_classes,
            "out": args.out,
        }
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
