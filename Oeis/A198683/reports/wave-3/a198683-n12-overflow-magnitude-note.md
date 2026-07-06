# A198683(12): overflow singleton magnitude note

- Status: Diagnostic note; not a certificate
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: Re-examine the retained `n = 12` overflow singleton `{57}` and identify a smaller certification target
- Created (UTC): 2026-07-06
- Repository HEAD: 4394ec8068f9d82c50fc15f656eb67835943025b

## Summary

The retained probe-refined `n = 12` table has one class still marked
tentative: strict class `2924`, the overflow singleton `{57}`. The reason
given in
[`../../data/a198683-n12-equivalence-classes.txt`](../../data/a198683-n12-equivalence-classes.txt)
is that `|Im(e)| ~ 10^41232...` cannot be reduced modulo `2π` at finite
precision, where `e = b Log(a)` is the level-12 exponent and the value is
`exp(e)`.

That phase-reduction obstruction is real, but it may be unnecessary for
this singleton. Equality of two nonzero complex numbers implies equality
of their moduli, hence equality of `Re(e)` for their principal-exponential
representatives. In the retained TSV signatures, candidate `57` is
separated from every other candidate by an enormous log-modulus gap:

```text
idx 57   Re(e) = -3.22389e+41232950809707420597749203381002924
idx 644  Re(e) = -3.62423e+9       (next most negative retained signature)
idx 129  Re(e) = -512261.
idx 1061 Re(e) = -349750.
idx 151  Re(e) = -2616.50
idx 1079 Re(e) = -1325.61
idx 2053 Re(e) = -963.733
idx 2207 Re(e) = -624.572
idx 3777 Re(e) = -624.572
```

Among the `5139` TSV rows, candidate `57` is the only row whose displayed
negative `Re(e)` has scientific exponent greater than `10000`; it is also
the only row marked `regime = overflow`.

This observation is reproducible with:

```powershell
python .\src\Lean\Oeis\A198683\computations\python\diagnose_overflow_magnitude.py --top 12
```

The dynamic-programming representative behind candidate `57` can be traced
with:

```powershell
python .\src\Lean\Oeis\A198683\computations\python\trace_dp_expression.py --n 11 --index 57 --dps 260
```

This reports the retained `values[11][57]` representative as

```text
(i^(i^(i^(((i^i)^i)^(i^((i^i)^(i^i)))))))
```

with displayed imaginary part

```text
2.0523942547869173541776347332204601020523469760352e+41232950809707420597749203381002924.
```

Since candidate `57` at `n = 12` is the split `(k=1, ia=0, ib=57)`,
its exponent is `e = values[11][57] Log(i) = values[11][57] * iπ/2`.
The enormous positive imaginary part above is therefore exactly the source
of the enormous negative `Re(e_57)`.

## Certification target

A proof-quality pipeline can settle the overflow singleton without reducing
its astronomical imaginary part modulo `2π` if it proves the following two
real-interval facts for the `5139` candidate exponents:

```text
Re(e_57) < -10^10000
for every j != 57, Re(e_j) > -10^10
```

Those two inequalities imply `|exp(e_57)| < exp(-10^10000)` while every
other candidate has modulus greater than `exp(-10^10)`, so candidate `57`
cannot equal any other candidate. This would replace an impossible-looking
phase-reduction problem with a large but ordinary real-interval bound.

The thresholds above are deliberately loose. The retained signatures
suggest a gap of roughly

```text
10^41232950809707420597749203381002924  versus  10^9.
```

Any certified bounds with many orders of magnitude between them would be
enough.

## What this does not prove

This note does not prove `A198683(12) = 2926`. It reads the retained TSV
signatures and identifies a simpler certification obligation for the one
class currently labelled tentative in the probe-refined file. The other
`2925` refined classes are still only as strong as the local
multi-precision evidence and algebraic-probe annotations behind them.

In particular, a formal settlement still needs either:

- a certified arithmetic pipeline for all equality and inequality decisions
  in the `5139`-candidate partition, or
- a symbolic proof that the retained conclusive merges and splits are
  mathematically correct.

The practical takeaway is narrower: the overflow singleton should be
handled by certified log-modulus comparison first, before spending effort
on astronomical argument reduction.
