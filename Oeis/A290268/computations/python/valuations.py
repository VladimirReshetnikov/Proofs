# -*- coding: utf-8 -*-
# Deeper structure hunting for gamma(k,D,M) = [w^M](2+w)^k ((1+w)^2 log(1+w))^D
# 1. D=1: gamma(k,1,M) is a rational function of M: compute numerator polys N_k(M), factor.
# 2. v_2 / v_3 valuation patterns of gamma in the tail region.
from fractions import Fraction
from math import factorial

WMAX = 200
log1p = [Fraction(0)] + [Fraction((-1) ** (i + 1), i) for i in range(1, WMAX + 1)]
phi = [Fraction(0)] * (WMAX + 1)
for i in range(WMAX + 1):
    s = log1p[i]
    if i >= 1:
        s += 2 * log1p[i - 1]
    if i >= 2:
        s += log1p[i - 2]
    phi[i] = s

def mulser(a, b, cap=WMAX):
    r = [Fraction(0)] * (cap + 1)
    for i, ai in enumerate(a):
        if ai == 0 or i > cap:
            continue
        for jj, bj in enumerate(b):
            if i + jj > cap:
                break
            if bj:
                r[i + jj] += ai * bj
    return r

DMAX = 8
KMAX = 8
phipow = [[Fraction(0)] * (WMAX + 1) for _ in range(DMAX + 1)]
phipow[0][0] = Fraction(1)
for Dv in range(1, DMAX + 1):
    phipow[Dv] = mulser(phipow[Dv - 1], phi)

gamma = {}
for Dv in range(DMAX + 1):
    cur = phipow[Dv][:]
    gamma[(0, Dv)] = cur
    for kv in range(1, KMAX + 1):
        nxt = [Fraction(0)] * (WMAX + 1)
        for i in range(WMAX + 1):
            nxt[i] = 2 * cur[i] + (cur[i - 1] if i >= 1 else 0)
        gamma[(kv, Dv)] = nxt
        cur = nxt

# ---------- 1. D=1 numerator polynomials ----------
# gamma(k,1,M) = 2*(-1)^(M+1) * N_k(M) / (M(M-1)...(M-k-2))   [conjectured shape]
# Interpolate N_k from data, print coefficients and integer roots.
print("== D=1 numerators ==")
def lagrange_interp(pts):
    # pts: list of (x, y) Fractions; returns poly coeffs (ascending)
    n = len(pts)
    coeffs = [Fraction(0)] * n
    for i, (xi, yi) in enumerate(pts):
        # basis poly
        num = [Fraction(1)]
        den = Fraction(1)
        for jj, (xj, _) in enumerate(pts):
            if jj == i:
                continue
            num = [ (num[t - 1] if t >= 1 else 0) - xj * (num[t] if t < len(num) else 0) for t in range(len(num) + 1) ]
            den *= (xi - xj)
        for t in range(len(num)):
            coeffs[t] += yi * num[t] / den
    return coeffs

for kv in range(0, KMAX + 1):
    pts = []
    for M in range(kv + 20, kv + 20 + kv + 1):  # k+1 sample points in the tail
        g = gamma[(kv, 1)][M]
        denom_prod = Fraction(1)
        for s in range(kv + 3):
            denom_prod *= (M - s)
        N = g * denom_prod / (2 * (-1) ** (M + 1))
        pts.append((Fraction(M), N))
    coeffs = lagrange_interp(pts)
    # verify on other points
    ok = True
    for M in list(range(kv + 4, kv + 12)) + [150, 190]:
        g = gamma[(kv, 1)][M]
        denom_prod = Fraction(1)
        for s in range(kv + 3):
            denom_prod *= (M - s)
        N = g * denom_prod / (2 * (-1) ** (M + 1))
        val = sum(c * Fraction(M) ** t for t, c in enumerate(coeffs))
        if val != N:
            ok = False
    # integer roots in range
    roots = []
    for M in range(0, 200):
        val = sum(c * Fraction(M) ** t for t, c in enumerate(coeffs))
        if val == 0:
            roots.append(M)
    print(f"k={kv}: N_k coeffs (asc) = {[str(c) for c in coeffs]}, verified={ok}, integer roots in [0,200): {roots}")

# ---------- 2. valuation patterns ----------
def v_p(fr, p):
    if fr == 0:
        return None
    num, den = fr.numerator, fr.denominator
    v = 0
    while num % p == 0:
        num //= p; v += 1
    while den % p == 0:
        den //= p; v -= 1
    return v

print("== v_2(gamma) along M for sample (k,D) [tail region] ==")
for (kv, Dv) in [(0,1),(0,2),(0,3),(1,2),(2,3),(0,4),(1,4),(3,5)]:
    lo = kv + 2 * Dv + 1
    vals = []
    for M in range(lo, lo + 40):
        v = v_p(gamma[(kv, Dv)][M], 2)
        vals.append('Z' if v is None else v)
    print(f"k={kv} D={Dv}: v2 from M={lo}: {vals}")

print("== v_2 of integer c_n(j,k) = n!/(k!D!) gamma in negative region: pattern? ==")
# c integer v2 = v2(n!) - v2(k!) - v2(D!) + v2(gamma), n = M + k
for (kv, Dv) in [(0,1),(0,2),(1,2),(0,3)]:
    lo = kv + 2 * Dv + 1
    vals = []
    for M in range(lo, lo + 30):
        g = gamma[(kv, Dv)][M]
        n = M + kv
        if g == 0:
            vals.append('Z')
            continue
        cint = Fraction(factorial(n), factorial(kv) * factorial(Dv)) * g
        assert cint.denominator == 1
        vals.append(v_p(cint, 2))
    print(f"k={kv} D={Dv}: v2(c) from M={lo}: {vals}")
