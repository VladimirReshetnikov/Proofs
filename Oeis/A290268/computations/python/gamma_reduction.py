# -*- coding: utf-8 -*-
# Verify the reduction c_n(j,k) = n!/(k! D!) * [w^M] (2+w)^k phi(w)^D,
#   phi(w) = (1+w)^2 log(1+w),  D = (n+j)/2 - k,  M = n - k.
# Then study the zero set / signs / 2-adic valuations of
#   gamma(k,D,M) = [w^M] (2+w)^k phi(w)^D.
from fractions import Fraction
from collections import defaultdict
from math import factorial

WMAX = 140

# phi coefficients: phi = (1+w)^2 log(1+w)
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
        for jj, bj in enumerate(b):
            if i + jj > WMAX:
                break
            if bj:
                r[i + jj] += ai * bj
    return r

# phi^D for D = 0..DMAX
DMAX = 9
KMAX = 9
phipow = [[Fraction(0)] * (WMAX + 1) for _ in range(DMAX + 1)]
phipow[0][0] = Fraction(1)
for Dv in range(1, DMAX + 1):
    phipow[Dv] = mulser(phipow[Dv - 1], phi)

# (2+w)^k phi^D table: gamma[k][D] = series
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

# --- 1. verify the reduction against the lattice recurrence ---
N = 40
c = {(0, 0): 1}
levels = [dict(c)]
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

bad = 0
checked = 0
for n in range(0, N + 1):
    for j in range(-n, n + 1):
        if (n + j) % 2 != 0:
            continue
        for k in range(0, (n + j) // 2 + 1):
            Dv = (n + j) // 2 - k
            M = n - k
            if Dv > DMAX or (-j) > 0 and False:
                continue
            if Dv > DMAX or M > WMAX or (min(j, 0) != 0 and False):
                continue
            kk = k
            if kk > KMAX:
                continue
            g = gamma[(kk, Dv)][M] if M <= WMAX else None
            pred = Fraction(factorial(n), factorial(k) * factorial(Dv)) * g
            actual = levels[n].get((j, k), 0)
            checked += 1
            if pred != actual:
                bad += 1
                if bad < 10:
                    print("REDUCTION MISMATCH", n, j, k, "pred", pred, "actual", actual)
print(f"reduction check: {checked} points checked, {bad} mismatches")

# --- 2. zero set of gamma on the grid ---
print("== zero set of gamma(k,D,M), D>=1, M in [D, WMAX] ==")
anom = 0
for kv in range(KMAX + 1):
    for Dv in range(1, DMAX + 1):
        ser = gamma[(kv, Dv)]
        for M in range(Dv, WMAX + 1):
            iszero = (ser[M] == 0)
            hole = (M == kv + 4 * Dv + 1) and ((kv + Dv) % 2 == 0)
            if iszero != hole:
                anom += 1
                if anom < 30:
                    print(f"  ANOMALY k={kv} D={Dv} M={M}: zero={iszero} holepred={hole}")
print(f"zero-set anomalies: {anom}")

# --- 3. sign structure ---
# For each (k,D), print sign string over M = D .. k+4D+12, marking regions.
print("== sign strings (region: . = bulk M<=k+2D, | at hole line M=k+4D+1) ==")
def signch(x):
    return '+' if x > 0 else ('-' if x < 0 else '0')
for Dv in range(1, 7):
    for kv in range(0, 7):
        ser = gamma[(kv, Dv)]
        lo, hi = Dv, min(kv + 4 * Dv + 14, WMAX)
        s = ''
        for M in range(lo, hi + 1):
            ch = signch(ser[M])
            if M == kv + 2 * Dv:
                ch += ']'   # end of bulk
            if M == kv + 4 * Dv + 1:
                ch += '!'   # hole line
            s += ch
        print(f"k={kv} D={Dv}: M={lo}..{hi}: {s}")

# --- 4. deep tail sign check: does sign(gamma) == (-1)^(M-D) hold for M >= k+4D+2 ? ---
print("== tail sign pattern check ==")
bad2 = 0
for kv in range(KMAX + 1):
    for Dv in range(1, DMAX + 1):
        ser = gamma[(kv, Dv)]
        for M in range(kv + 4 * Dv + 2, WMAX + 1):
            want = 1 if (M - Dv) % 2 == 0 else -1
            got = 1 if ser[M] > 0 else (-1 if ser[M] < 0 else 0)
            if got != want:
                bad2 += 1
                if bad2 < 20:
                    print(f"  tail sign fail k={kv} D={Dv} M={M}: got {got} want {want}")
print(f"tail sign fails: {bad2}")

# --- 5. sign in intermediate band k+2D+1 <= M <= k+4D+1 ---
print("== intermediate band signs, organized by r = M-k-2D (1..2D+1) ==")
for Dv in range(1, 8):
    for kv in range(0, 8):
        ser = gamma[(kv, Dv)]
        row = []
        for r in range(1, 2 * Dv + 2):
            M = kv + 2 * Dv + r
            row.append(signch(ser[M]))
        print(f"D={Dv} k={kv}: r=1..{2*Dv+1}: {''.join(row)}")

# --- 6. bulk positivity check ---
bad3 = 0
for kv in range(KMAX + 1):
    for Dv in range(0, DMAX + 1):
        ser = gamma[(kv, Dv)]
        for M in range(Dv, kv + 2 * Dv + 1):
            if ser[M] <= 0:
                bad3 += 1
                if bad3 < 20:
                    print(f"  bulk nonpositive k={kv} D={Dv} M={M}: {ser[M]}")
print(f"bulk nonpositive count: {bad3}")
