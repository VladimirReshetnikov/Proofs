"""Diagnose the A198683 n=12 overflow singleton's log-modulus gap.

This script reads the retained per-candidate TSV:

    src/Lean/Oeis/A198683/data/a198683-n12-candidates.tsv

and reports the candidates with the most negative displayed Re(e), where
e = b * Log(a) is the level-12 exponent.  It is a reproducibility helper for
the wave-3 overflow magnitude note; it does not recompute the candidates and
is not a proof certificate.
"""

from __future__ import annotations

import argparse
import csv
import re
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path


DEFAULT_TSV = Path("src/Lean/Oeis/A198683/data/a198683-n12-candidates.tsv")


@dataclass(frozen=True)
class ReSignature:
    idx: int
    text: str
    sign: int
    mantissa: Decimal
    exponent: int
    regime: str
    value_regime: str
    strict_class: int


_SCI_RE = re.compile(r"([+-]?)(?:(\d+(?:\.\d*)?)|(?:\.\d+))(?:[eE]([+-]?\d+))?")


def parse_sci(text: str) -> tuple[int, Decimal, int]:
    """Parse a decimal/scientific display string without materialising 10^huge."""

    match = _SCI_RE.fullmatch(text.strip())
    if match is None:
        raise ValueError(f"cannot parse numeric signature {text!r}")
    sign = -1 if match.group(1) == "-" else 1
    mantissa = Decimal(match.group(2))
    exponent = int(match.group(3) or 0)
    return sign, mantissa, exponent


def load_signatures(path: Path) -> list[ReSignature]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = csv.DictReader(stream, delimiter="\t")
        out: list[ReSignature] = []
        for row in rows:
            sign, mantissa, exponent = parse_sci(row["re_e_sig"])
            out.append(
                ReSignature(
                    idx=int(row["idx"]),
                    text=row["re_e_sig"],
                    sign=sign,
                    mantissa=mantissa,
                    exponent=exponent,
                    regime=row["regime"],
                    value_regime=row["value_regime"],
                    strict_class=int(row["strict_class"]),
                )
            )
        return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tsv", type=Path, default=DEFAULT_TSV)
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument("--huge-exponent-threshold", type=int, default=10_000)
    args = parser.parse_args()

    signatures = load_signatures(args.tsv)
    negative = [sig for sig in signatures if sig.sign < 0]
    negative.sort(key=lambda sig: (-sig.exponent, -sig.mantissa))

    print("Most negative displayed Re(e) signatures:")
    for sig in negative[: args.top]:
        print(
            f"  idx={sig.idx:<5d} Re(e)={sig.text:<48s} "
            f"regime={sig.regime:<8s} value_regime={sig.value_regime:<8s} "
            f"strict_class={sig.strict_class}"
        )

    huge = [
        sig
        for sig in negative
        if sig.exponent > args.huge_exponent_threshold
    ]
    print()
    print(
        "negative Re(e) signatures with scientific exponent > "
        f"{args.huge_exponent_threshold}: {len(huge)}"
    )
    for sig in huge:
        print(
            f"  idx={sig.idx}, exponent_digits={len(str(sig.exponent))}, "
            f"exponent_prefix={str(sig.exponent)[:50]}"
        )

    overflow = [sig for sig in signatures if sig.regime == "overflow"]
    print()
    print(f"overflow rows: {len(overflow)}")
    for sig in overflow:
        print(f"  idx={sig.idx}, Re(e)={sig.text}, strict_class={sig.strict_class}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
