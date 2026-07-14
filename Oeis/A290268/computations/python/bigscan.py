# -*- coding: utf-8 -*-
# Extended sporadic-zero scan for gamma(k,D,M) = [w^M](2+w)^k ((1+w)^2 log(1+w))^D.
# The x^x analog has a sporadic zero (A008296(8,5)); confirm the x^2 family has none
# in a much larger range than previously scanned.
from fractions import Fraction

WMAX = 400
DMAX = 14
KMAX = 20

log1p = [Fraction(0)] + [Fraction((-1) ** (i + 1), i) for i in range(1, WMAX + 1)]
phi = [Fraction(0)] * (WMAX + 1)
for i in range(WMAX + 1):
    s = log1p[i]
    if i >= 1:
        s += 2 * log1p[i - 1]
    if i >= 2:
        s += log1p[i - 2]
    phi[i] = s

def mulser(a, b):
    r = [Fraction(0)] * (WMAX + 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for jj in range(WMAX + 1 - i):
            bj = b[jj]
            if bj:
                r[i + jj] += ai * bj
    return r

anomalies = []
cur = [Fraction(0)] * (WMAX + 1)
cur[0] = Fraction(1)
phipow = cur
for D in range(0, DMAX + 1):
    if D > 0:
        phipow = mulser(phipow, phi)
    g = phipow[:]
    for k in range(0, KMAX + 1):
        if k > 0:
            g = [2 * g[i] + (g[i - 1] if i >= 1 else 0) for i in range(WMAX + 1)]
        # scan zeros for this (k, D)
        for M in range(D, WMAX + 1):
            iszero = (g[M] == 0)
            expected = (D == 0 and M > k) or (D >= 1 and M == k + 4 * D + 1 and (k + D) % 2 == 0)
            if iszero != expected:
                anomalies.append((k, D, M, iszero))
                print("ANOMALY", k, D, M, "zero" if iszero else "nonzero-but-expected-zero")
    print(f"D={D} done")
print(f"TOTAL ANOMALIES: {len(anomalies)} over k<=20, D<=14, M<=400")
