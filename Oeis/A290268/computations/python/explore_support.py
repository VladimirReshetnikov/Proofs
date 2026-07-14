# -*- coding: utf-8 -*-
# A290268: number of terms in fully expanded n-th derivative of x^(x^2).
# Model: n-th derivative = sum over (j,k) of c[n][(j,k)] * x^(x^2+j) * log(x)^k
# Recurrence: differentiating x^(x^2+j) log^k x gives
#   2 x^(x^2+j+1) log^(k+1) x  + x^(x^2+j+1) log^k x + j x^(x^2+j-1) log^k x + k x^(x^2+j-1) log^(k-1) x
from collections import defaultdict
import sys

N = 66

levels = []
c = {(0, 0): 1}
levels.append(dict(c))
for n in range(N):
    d = defaultdict(int)
    for (j, k), v in c.items():
        d[(j + 1, k + 1)] += 2 * v
        d[(j + 1, k)] += v
        if j != 0:
            d[(j - 1, k)] += j * v
        if k != 0:
            d[(j - 1, k - 1)] += k * v
    c = {p: v for p, v in d.items() if v != 0}
    levels.append(dict(c))

# OEIS data for validation
oeis = [1,2,5,8,13,18,25,31,41,49,61,71,85,97,113,126,145,160,181,198,221,
        240,265,285,313,335,365,389,421,447,481,508,545,574,613,644,685,718,
        761,795,841,877,925,963,1013,1053,1105,1146,1201,1244,1301,1346,1405,1452]

print("== counts vs OEIS ==")
ok = True
for n in range(len(oeis)):
    got = len(levels[n])
    if got != oeis[n]:
        ok = False
        print(f"MISMATCH n={n}: got {got}, oeis {oeis[n]}")
print("all match" if ok else "MISMATCHES!", f"(checked {len(oeis)} terms)")

# closed form check: a(n) = n^2/2 + n + 1 - (n mod 2)*(1/2 + floor((n+1)/8))
print("== closed form check up to N ==")
ok = True
for n in range(N + 1):
    cf = n * n // 2 + n + 1 - (n % 2) * ((n + 1) // 8) - (n % 2) * 0  # careful with 1/2
    # n odd: n^2/2 + n + 1 - 1/2 - floor((n+1)/8) = (n^2+2n+1)/2 - floor((n+1)/8)
    if n % 2 == 0:
        cf = n * n // 2 + n + 1
    else:
        cf = (n + 1) ** 2 // 2 - (n + 1) // 8
    if len(levels[n]) != cf:
        ok = False
        print(f"closed-form MISMATCH n={n}: got {len(levels[n])}, cf {cf}")
print("closed form matches all computed" if ok else "CF MISMATCHES!")

# Support structure: for each n, for each j column present, which k's are nonzero,
# compared to the "full" range 0..(n+j)/2. Report holes and truncations.
print("== support structure ==")
for n in range(0, 26):
    lv = levels[n]
    js = sorted({j for (j, k) in lv}, reverse=True)
    desc = []
    for j in js:
        ks = sorted(k for (jj, k) in lv if jj == j)
        maxfull = (n + j) // 2
        full = list(range(0, maxfull + 1))
        if ks == full:
            desc.append(f"j={j}:full(0..{maxfull})")
        else:
            missing = sorted(set(full) - set(ks))
            extra = sorted(set(ks) - set(full))
            desc.append(f"j={j}:ks={ks} (full would be 0..{maxfull}, missing {missing}, extra {extra})")
    print(f"n={n}: jmin={js[-1]}, count={len(lv)}")
    for dsc in desc:
        print("   ", dsc)

# Look specifically at holes for larger n (only report non-full columns)
print("== non-full columns for n up to 40 ==")
for n in range(0, 41):
    lv = levels[n]
    js = sorted({j for (j, k) in lv}, reverse=True)
    jmin = js[-1]
    anomalies = []
    for j in js:
        ks = sorted(k for (jj, k) in lv if jj == j)
        maxfull = (n + j) // 2
        full = list(range(0, maxfull + 1))
        if ks != full:
            missing = sorted(set(full) - set(ks))
            anomalies.append((j, ks, missing))
    print(f"n={n}: jmin={jmin}, expected full j-range would be n..-n step -2; anomalies:")
    for j, ks, missing in anomalies:
        print(f"    j={j}: present {ks}, missing {missing}")
