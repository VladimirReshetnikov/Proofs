# A290268: number of terms in the expanded n-th derivative of x^(x^2)

[A290268](https://oeis.org/A290268) counts the terms of the fully expanded
n-th derivative of `x^(x^2)`. The entry conjectures (Reshetnikov 2017; restated
by Luschny 2017) that the sequence has generating function

```text
(1 + x + 2x^2 + 2x^3 + 2x^4 + 2x^5 + 2x^6 + x^7 + 2x^8 + x^9)
/ ((1 - x)(1 - x^2)(1 - x^8)),
```

equivalently that `a` satisfies the order-12 linear recurrence with signature
`{0, 2, 0, -1, 0, 0, 0, 1, 0, -2, 0, 1}`, equivalently the closed form

```text
a(2m)     = 2m^2 + 2m + 1,
a(2m - 1) = 2m^2 - floor(m/4).
```

This directory retains the investigation notes and the exact Python generators
behind the Lean development in `LeanProofs/A290268*.lean`.

## The exact model

Every derivative of `x^(x^2)` is an integer combination of the functions
`x^(x^2+j) * log(x)^k`. Writing

```text
(d/dx)^n x^(x^2) = sum_{j,k} c_n(j,k) * x^(x^2+j) * log(x)^k,
```

differentiating term-by-term gives the exact lattice recurrence

```text
c_0(j,k)     = [j = 0][k = 0],
c_{n+1}(j,k) = 2 c_n(j-1,k-1) + c_n(j-1,k) + (j+1) c_n(j+1,k) + (k+1) c_n(j+1,k+1),
```

and `a(n) = #{(j,k) : c_n(j,k) != 0}`. The support of `c_n` lies in
`{|j| <= n, j == n (mod 2), 0 <= k <= (n+j)/2}`. The recurrence reproduces the
worked example in the OEIS entry and the published data (`a(0..53)` checked,
and the closed form above checked against the model through `n = 66`).

## Generating-function reduction

Taylor expansion `sum_n z^n/n! (d/dx)^n x^(x^2) = (x+z)^((x+z)^2)` gives, for
`Q_n := x^(-x^2) (d/dx)^n x^(x^2)` viewed as a polynomial in `x^{±1}` and
`t = log x`:

```text
sum_n Q_n z^n / n! = exp((2xz + z^2) t) * (1 + z/x)^((x+z)^2).
```

Setting `w = z/x`, one finds `(1+z/x)^((x+z)^2) = exp(x^2 * phi(w))` with

```text
phi(w) = (1+w)^2 log(1+w) = w + (3/2)w^2 + sum_{m>=3} 2(-1)^(m+1) w^m / ((m-2)(m-1)m).
```

Both `x z t` (from the first factor, per power of `t`) and every monomial of
`x^2 phi(z/x)` carry equal weight 1 for the *depth* statistic
`D := (n+j)/2 - k`, which yields the key exact reduction

```text
c_n(j,k) = n! / (k! D!) * gamma(k, D, M),      D = (n+j)/2 - k,  M = n - k,
gamma(k,D,M) := [w^M] (2+w)^k * phi(w)^D.
```

(Verified exactly for all 3200 support-window points with `n <= 40`,
`k <= 9`, `D <= 9`.)

## Support characterization (conjectural, verified through n = 66)

The zero set of `gamma` on the lattice `k >= 0`, `D >= 0`, `M >= D` appears to
be exactly:

* `D = 0` and `M > k` (degree bound: `phi^0 (2+w)^k` has degree `k`), and
* the **hole line** `M = k + 4D + 1` with `k + D` even, `D >= 1`.

Translated back, `supp(c_n)` is:

* columns `j >= 0`: all `0 <= k <= (n+j)/2` (all coefficients positive);
* columns `j = -r < 0`: all `0 <= k <= (n-r)/2 - 1` **except** the single hole
  `k = (n - 2r + 1)/2`, present exactly when `r >= 3` and `n == r (mod 4)`.

Counting this set reproduces the conjectured closed form exactly: columns
`j >= 0` give `sum` of full ranges, negative columns give the `2m^2` totals,
and the holes account for the `floor(m/4)` correction (`floor((n+1)/8)` in the
OEIS form), whose period-8 behaviour is now explained by the congruence
`n == r (mod 4)` along `r = 3, 5, 7, ...`.

## The hole theorem (proved)

The exact vanishing on the hole line is a parity symmetry. Substituting
`w = e^u - 1` (so `log(1+w) = u`, `phi = u e^{2u}`) converts coefficient
extraction to a residue: with `B(u) := u/(e^u - 1)`,

```text
gamma(k,D,M) = [u^M] Ghat(u),   Ghat := (1+e^u)^k * u^D * e^{(2D+1)u} * B(u)^{M+1}.
```

Under `u -> -u`: `(1+e^{-u})^k = e^{-ku}(1+e^u)^k`, `B(-u) = e^u B(u)`, so

```text
Ghat(-u) = (-1)^D * e^{(M - k - 4D - 1)u} * Ghat(u).
```

On the line `M = k + 4D + 1` the exponential factor disappears, `Ghat` has pure
parity `(-1)^D`, and `[u^M] Ghat = 0` whenever `M - D` is odd, i.e. whenever
`k + D` is even. This is exactly the observed hole condition, including the
period-4 congruence. The change-of-variables lemma needed for `[u^M]` reduces,
for monomials `w^L`, to the classical residue identity
`[u^s](e^u (u/(e^u-1))^{s+1}) = 0` for `s >= 1`, which follows from
`s e^u/(e^u-1)^{s+1} = -d/du (e^u-1)^{-s}` — all provable in formal power
series over ℚ, no analysis required.

## What remains open: nonvanishing

The remaining content of the conjecture is that `gamma(k,D,M) != 0` everywhere
else in the region `D >= 1`, `M >= D`:

1. **Bulk positivity** (`M <= k + 2D`, i.e. `j >= 0`): all checked values are
   strictly positive.
2. **Negative region** (`M > k + 2D`, off the hole line): all checked values
   are nonzero (grid `k, D <= 9`, `M <= 140`), with sign *mostly*
   `(-1)^(M-D)`-alternating in the far tail but with sporadic non-alternating
   sign "wobbles" at moderate `M` (e.g. `k=2, D=5`), which never pass through
   zero. Any naive sign-induction along the recurrences therefore fails, and
   the following routes were checked and ruled out empirically:
   * clean 2-adic/3-adic valuation formulas for `gamma` (valuations are
     erratic in exactly the wobble zones);
   * eventually-strict alternation at a uniform distance from the hole line.
3. For `D = 1`, `gamma(k,1,M)` is an explicit rational function of `M`:
   `gamma(k,1,M) = 2(-1)^(M+1) N_k(M) / (M(M-1)...(M-k-2))` with `N_k` monic of
   degree `k` in `M`, e.g. `N_0 = 1`, `N_1 = M - 6`, `N_2 = M^2 - 13M + 48`,
   `N_3 = (M-8)(M^2 - 13M + 60)`. The claim for `D = 1` is that `N_k` has no
   integer roots `M >= k+3` besides `M = k+5` for odd `k`.
4. In Nørlund language `gamma(0,D,M) = B_{M-D}^{(M+1)}(2D+1)/(M-D)!`, so the
   negative region is a nonvanishing statement about higher-order Bernoulli
   (Nørlund) polynomials at odd integer arguments; the hole line is the
   reflection point `x = (a - ...)/2`-symmetry of `B_n^{(a)}(x)`.

The Lean development therefore (i) proves everything except nonvanishing
unconditionally, (ii) states the nonvanishing as an explicit hypothesis, and
(iii) verifies the conjecture exactly on the published OEIS range by kernel
computation.

## Contents

* `computations/python/explore_support.py` — lattice model, OEIS/closed-form
  comparison, support-shape and anomaly tables.
* `computations/python/gamma_reduction.py` — exact verification of the
  `c_n(j,k) = n!/(k!D!) gamma(k,D,M)` reduction, the zero-set scan, sign
  tables, and bulk-positivity scan.
* `computations/python/valuations.py` — `D = 1` numerator interpolation and
  p-adic valuation scans (negative results retained deliberately).
