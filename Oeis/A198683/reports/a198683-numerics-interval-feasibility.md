# A198683(12) certification feasibility via `src/Numerics/python`

- Status: Feasibility study
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: Determine whether the `src/Numerics/python` (`numerics`) package can serve as the sound real-line interval-arithmetic engine for a certified evaluation of `A198683(12)`, and identify what would have to be added on top
- Created (UTC): 2026-05-21T03:59:13Z
- Repository HEAD: f17b75114d0553b54fde626b9d9e325cf0f9eb4a

## Summary

`src/Numerics/python` is a strong **structural fit** for the certified-arithmetic
core that
[`exploratory/A198683-report-2.md`](exploratory/A198683-report-2.md) calls for,
and a **partial fit** for the full A198683(12) pipeline. It already provides
the hardest-to-build piece — sound interval arithmetic with outward rounding,
tower-shaped magnitudes (representing values up to roughly `10^^h(top)` for
canonical `h >= 1` and arbitrary `top`), and from-scratch transcendentals on
the positive real line. With it the magnitude side `rho` of every A198683
intermediate value is already handled, including the astronomical
`|i^C| ~ 4.10 * 10^(4.12 * 10^33)` regime documented in the OEIS entry at
`n = 11`.

What `numerics` does **not** provide is the argument-side machinery: there is
no `pi` constant, no `sin` / `cos` / `atan2`, no complex type, and no branch /
wrap bookkeeping. The package is deliberately a real-line library — see
`numerics/__init__.py` and `numerics/transcendentals.py`. To run the
`(rho, theta)`-interval pipeline described in `A198683-report-2.md` we would
need to extend the engine with three additions (`pi`, sin/cos on bounded
intervals, complex-interval wrapper) and then write the A198683 application
layer on top.

The extensions are well-scoped and naturally fit the existing
proposal-driven architecture. The application layer is the larger piece of
work but is straightforwardly bounded: roughly the same DP recurrence as
[`computations/python/compute_a198683.py`](../computations/python/compute_a198683.py),
with the per-value representation upgraded from `mpmath.mpc` to a
certified-interval polar form and with `mp.almosteq` replaced by the tri-valued
`numerics.equal` (whose `Undefined` branch drives adaptive precision instead of
the silent merges that produced the historical `2919` artefact diagnosed by
the two existing root-cause reports
[`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
and
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)).

**Recommendation**: pursue this path. It is the most direct route from the
current heuristic state to a certificate, and it builds on infrastructure
already designed around exactly the soundness contract A198683(12) needs. The
biggest single risk is the cost of `sin` / `cos` at astronomical arguments
(argument-reduction precision), which is sidestepped almost entirely by
adopting the `i^Z` canonical form from `A198683-report-2.md` §3 — see §5.3 of
this report.

## 1. What the certification target requires

This section paraphrases
[`exploratory/A198683-report-2.md`](exploratory/A198683-report-2.md) §2–§4
in terms of the primitive operations a certified engine has to expose.

### 1.1 Per-value representation

Every intermediate value `v` produced by some parenthesisation of `k <= 12`
copies of `i` is held as a **polar interval pair**:

- `rho_v` — an enclosure of `|v|`, with `rho_v.lo >= 0`.
- `theta_v` — an enclosure of `arg(v) in (-pi, pi]` (the principal branch).

Both endpoints are exact rationals; both intervals contain the true
mathematical value; widening is outward.

Magnitudes range from sub-`10^(-1300)` (the "near-zero" cluster diagnosed by
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md))
to roughly `10^(10^34)` (the OEIS-comment `n = 11` example). The representation
must accommodate at least this dynamic range, and at `n = 12` the upper bound
can stack one further level.

### 1.2 Primitive operations the engine must expose

For the DP recurrence `v = L ^ R` over polar intervals:

1. `ln_interval(rho_L)` — log of a positive real interval (`rho_L` may be
   tower-scaled).
2. `mul_complex_interval(R, log_L)` — complex interval multiplication.
   `R` is itself a polar pair; `log_L = ln(rho_L) + i * theta_L` is a complex
   rectangle whose imaginary part is `theta_L` and whose real part is
   `ln(rho_L)`.
3. `exp_complex_interval(E)` — complex exp on the resulting `E = U + i V`:
   `rho_new = exp(U)`, `theta_new = (V mod 2pi)` projected into `(-pi, pi]`.
   The `exp(U)` factor needs a tower-output capable `exp` on a real interval
   `U` that may itself be tower-scaled.
4. `argument_reduction(V)` — bring the imaginary part of `E` into the
   principal branch by subtracting an integer multiple of `2 pi`. The
   integer wrap count `k` must be known exactly.
5. **Equality predicate** that returns three-valued
   `EQUAL / NOT_EQUAL / UNDETERMINED` and drives adaptive precision.

### 1.3 Equality testing

`A198683-report-2.md` §3 reduces equality of two outcomes `N1 = i^Z1`,
`N2 = i^Z2` to integer detection on `Re(Z1) - Re(Z2)` modulo `4` plus
zero-detection on `Im(Z1) - Im(Z2)`. Both reduce to interval primitives:

- `Re(dZ) in 4 * Z` iff the interval `Re(dZ)/4` contains an integer and is
  short enough that it contains only one.
- `Im(dZ) == 0` iff the interval `Im(dZ)` contains `0` and is short enough
  that the surrounding context (no other algebraic candidate near zero)
  permits the certificate.

Both checks are classic uses of interval arithmetic: refine precision until
either the integer is uniquely captured or excluded.

## 2. What `numerics` provides today

Inventory drawn from `src/Numerics/python/numerics/__init__.py` and confirmed
against module-level docstrings and the implementation plan
(`src/Numerics/python/implementation-plan.md`).

### 2.1 Number types

| Type | File | Role |
|------|------|------|
| `ExactInteger`, `ExactRational` | `exact.py` | Exact rationals on the real line. |
| `GroundReal` | `ground_real.py` | Single exact rational in scientific-notation form `mantissa * 10^decimal_exponent`, with mantissa and exponent as arbitrary-precision Python `int`. |
| `TowerPoint` | `tower.py` | Out-of-band magnitudes as `(sign, polarity, height, top)`, where `top` is itself a `GroundReal`. Represents `sign * (10^^h(top))^polarity`. |
| `Interval` | `interval.py` | Closed `[lo, hi]` interval over the `Point = GroundReal | TowerPoint` union, with `compare_points(lo, hi) <= 0`. |
| `Undefined` | `undefined.py` | Absorbing element for domain failures and irreducible epistemic uncertainty. |

The three structural shapes `GroundInterval`, `TowerBall`, `GeneralHull` are
factory constructors that return `Interval` (see `interval.py` §1.43 and
round 9aj note). `TowerBall` is precisely the canonical-form interval
analogue of a `TowerPoint`, with `top_lo <= top_hi`.

### 2.2 Arithmetic surface (`arithmetic.py`)

The dispatcher in `numerics/arithmetic.py` exposes (with signatures
`(Real, ...) -> Real` returning the appropriate arm of the taxonomy):

- Elementary: `add`, `sub`, `mul`, `div`, `neg`, `abs_`.
- Powers and roots: `pow_`. (Square root is intentionally deferred.)
- Transcendentals: `exp`, `log`, `log2`, `log10`, `log_base`.
- Helpers used by SEIR-style log-domain addition: `logaddexp`, `logsumexp`.
- Comparisons: tri-valued `equal`, `not_equal`, `less`, `less_equal`,
  `greater`, `greater_equal`; representation-identity `same`, `not_same`.
- Aggregate: `minimum`, `maximum`, `median`, `median_deviation`.
- Precision plumbing: `widen_precision`, `with_working_precision`.

All operations are dispatched over the full `Real` taxonomy and return
`Interval` outputs for `Interval` inputs, with outward rounding consistent
with the soundness contract spelled out in
`src/Numerics/python/README.md` and the v1 proposal at
`src/Numerics/docs/proposals/proposal.md` §8.1.

### 2.3 Tower-regime status

Per `implementation-plan.md` (changelog through 2026-05):

- **M2a complete**: basic types, ground arithmetic, `neg` / `abs`,
  `log` at heights 1 and 2, `exp` at height 1.
- **M2b-beta-1 through M2b-beta-7 complete** modulo a few deferred
  close-magnitudes h >= 2 SEIR edge cases.
- **M3 (endpoint discipline) substantively complete**.

In practical terms: log, exp, mul, div, add, sub on tower-shaped intervals
are real for the regimes A198683(12) needs. The closest-magnitude
add/sub edge cases the plan still calls out as deferred are exactly the
"cancellation straddle" cases the report-2 strategy already handles by
refinement.

### 2.4 Transcendentals (`transcendentals.py`)

Implemented from scratch via the geometric `atanh`-series construction:

- `exp(GroundReal)`, `expm1(GroundReal)`.
- `ln(GroundReal)`, `log1p(GroundReal)`.

The `arithmetic.py` dispatcher lifts these to the `Real` taxonomy and routes
huge / tiny inputs through the tower regime via the unified log-domain
combiner.

### 2.5 Constants (`constants.py`)

Only `ln2_bounds(target_bits)` and `ln10_bounds(target_bits)`. The
module docstring explicitly notes that `pi`, `log10(e)`, and additional
constants "will land as the operations that need them are added."

### 2.6 Equality predicate (the key fit)

`numerics.equal(a, b, ctx)` is tri-valued. From
`arithmetic.py:6682` (paraphrased):

- Returns `True` iff both operands pin down to the same exact rational.
- Returns `False` iff their value-sets are provably disjoint.
- Returns `Undefined` otherwise (overlapping, touching, or at least one
  operand is `Undefined`).

This is exactly the semantics the A198683 dedup loop needs:
`Undefined` is the cue to refine precision, not the cue to silently merge.
The `mp.almosteq(abs_eps = rel_eps)` policy diagnosed by
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
has no counterpart in the `numerics` surface — there is no operation that
declares two distinct values equal because both are small.

### 2.7 Context (`context.py`)

Working precision is a per-context, immutable field
`working_precision_digits` (default `80` decimal digits) plus `guard_digits`
(default `20`). The ground band is `decimal_exponent in [-2^52, +2^52]`
(default), which already covers the entire range of representable magnitudes
the OEIS comment cites at `n = 11`. The cap `max_integer_digits = 1_000_000`
governs how large an exact integer the engine will materialise before
degrading to an `Interval` at working precision.

## 3. Gap analysis

| Requirement (from §1) | `numerics` today | Gap | Difficulty to close |
|---|---|---|---|
| Real interval at arbitrary precision | `Interval`, `GroundInterval` | None | n/a |
| Outward rounding, soundness contract | Built in | None | n/a |
| Tower-shaped magnitudes | `TowerPoint`, `TowerBall`, h >= 3 reachable via the M2b-beta-5 plan | None for the cases A198683(12) hits | n/a |
| `ln(positive real interval)` including tower-scaled | `log` dispatcher + `transcendentals.ln` | None | n/a |
| `exp(real interval)` including tower-scaled | `exp` dispatcher + `transcendentals.exp` | None | n/a |
| `pi` constant with rational bounds | Missing | Need `constants.pi_bounds(target_bits)` and (downstream) `pi_over_2_bounds`, `two_pi_bounds` | Small (~150 LOC + tests; Machin-style series mirroring `ln10_bounds`) |
| `sin`, `cos` on a bounded `GroundInterval` | Missing | Need Taylor-series implementation with explicit truncation bound | Moderate (~400-600 LOC + property tests; structurally parallel to `exp` / `expm1`) |
| `atan2(y, x)` or `arg(complex)` | Missing | Optional — only needed if we ever leave the `Z`-form representation. Avoidable per §5.3. | n/a if §5.3 is adopted |
| Complex-interval type | Missing | Need a thin wrapper `ComplexInterval = (re: Interval, im: Interval)` with the four arithmetic operations, complex `exp`, complex `log` | Moderate (~300-500 LOC; pure composition over `Interval`) |
| Wrap-integer / branch tracking | Missing | Application-layer: a `(Z_re_interval, Z_im_interval, wrap_int)` triple per value, with a mod-4 reducer on `Z_re` | Small (~200 LOC) |
| Tri-valued equality driven adaptive precision | `numerics.equal` is tri-valued | None on the engine side; need application-layer adaptive-precision loop | Small (the loop is ~50-100 LOC) |
| Argument reduction `(V mod 2 pi)` at huge V | Would need pi to ~log10|V| digits | Avoidable: use `i^Z` canonical form, where the only periodicity is mod 4 on `Re(Z)`. See §5.3. | n/a if §5.3 is adopted |

The structural gaps reduce to **three engine additions** and **one
application layer**. None of the additions require relaxing the soundness
contract; all of them have direct precedent in the existing
proposal-and-batch architecture.

## 4. Why `numerics` is the right substrate

Several properties of the package make it a better fit than the practical
alternatives (extending the `mpmath` script, or porting to Arb / Wolfram).

1. **Soundness contract first.** `numerics` exists to bracket real numbers
   honestly. Every operation widens outward; no operation silently merges or
   drops a "tiny" component. This is the contract the A198683(12) certificate
   has to live on top of. `mpmath` does not provide it; the `2919` artefact is
   a direct consequence.
2. **`Undefined` instead of "true with tolerance".** `numerics.equal` will
   never return `True` for two distinct mathematical values because it cannot
   prove disjointness. It will return `Undefined`. The dedup loop has a hard
   contract: if it ever sees `Undefined`, it must refine. There is no
   `abs_eps` knob that quietly collapses near-zero clusters.
3. **Tower magnitudes are first-class.** `TowerPoint` and `TowerBall` are
   designed for exactly the `10^^h(top)` regime A198683 produces at `n >= 11`.
   The "overflow bucket" special-case in
   [`compute_a198683.py`](../computations/python/compute_a198683.py) becomes
   unnecessary: an unmaterialisable mpmath complex magnitude is just a tower
   interval to `numerics`.
4. **Per-context precision and adaptive widening.**
   `numerics.with_working_precision` and `numerics.widen_precision` make the
   "refine until decided" outer loop a one-liner per candidate pair. The
   default `80` decimal digits is comparable to what
   `compute_a198683.py` uses today (`mp.dps = 220` was the historical
   plateau; `numerics` would start at `80` and grow on demand).
5. **In-repo, in-language.** No subprocess to a Wolfram kernel, no
   third-party C bindings, no opaque "magic" in the equality engine. Every
   line of every conclusion is auditable from `src/Numerics/python` and
   `src/Oeis/A198683/computations/python/`. The certificate is
   self-contained.
6. **The remaining work matches the package's existing roadmap.** A `pi`
   constant is already telegraphed in `constants.py`'s module docstring.
   `sin` / `cos` are the obvious next transcendentals after `exp` and `ln`.
   A complex-interval wrapper is a natural v2 milestone. Doing this work
   in service of A198683(12) advances the package in a direction it was
   already heading.

## 5. Proposed architecture

### 5.1 Layer split

```
+---------------------------------------------------------------+
| Application: src/Oeis/A198683/computations/python/            |
|   a198683_certified.py                                        |
|     - PolarValue, Outcome representation                      |
|     - DP recurrence (mirrors the existing script)             |
|     - Tri-valued dedup loop with adaptive precision           |
+---------------------------------------------------------------+
| Application-internal helpers                                  |
|   - ComplexInterval wrapper                                   |
|   - Mod-4 reducer on Re(Z)                                    |
|   - i^Z canonical form bookkeeping                            |
+---------------------------------------------------------------+
| Engine extensions, contributed back to src/Numerics/python    |
|   - numerics.constants.pi_bounds, pi_over_2_bounds            |
|   - numerics.transcendentals.sin / cos (GroundReal level)     |
|   - numerics.arithmetic.sin / cos dispatch                    |
+---------------------------------------------------------------+
| Existing numerics package (unchanged for our purposes)        |
|   - Interval, TowerBall, GeneralHull                          |
|   - exp, ln, mul, div, add, sub, log_base                     |
|   - equal (tri-valued), pow_                                  |
+---------------------------------------------------------------+
```

### 5.2 Per-value representation (`i^Z` canonical form)

Each value `v = i^Z` is stored as

```text
Z = Z_re_interval + i * Z_im_interval        # both numerics.Interval
```

with `Z_re_interval` reduced into a canonical residue band such as `[0, 4)`
modulo `4`. The materialised polar form `(rho, theta)` is recoverable on
demand but not stored:

```text
rho   = exp(-pi/2 * Z_im_interval)
theta = (pi/2 * Z_re_interval) reduced to (-pi, pi]
```

The DP recurrence becomes:

```
combine(L = i^Z_L, R = i^Z_R) -> i^Z_new

Z_new = i * exp(Z_R * i * pi/2) * Z_L
      = i * complex_exp(Z_R * (i * pi / 2)) * Z_L

complex_exp(a + i*b) = exp(a) * (cos(b) + i*sin(b))
```

The only `pi` factor that resists cancellation is the
`Z_R * (i * pi / 2)` argument to `complex_exp`. After mod-4 reduction on
`Re(Z_R)` (exact integer arithmetic — no `pi` needed for the reduction
itself), the resulting argument lives in a bounded ground-band rectangle of
real width `<= 2 pi` and imaginary part `<= pi * |Im(Z_R)|`. Trigonometric
arguments are then bounded and `sin` / `cos` Taylor series converge with
tight remainder bounds.

### 5.3 Why `i^Z` form sidesteps astronomical argument reduction

Done naively in `(rho, theta)` form, computing `theta_new = V mod 2 pi` for
a huge `V = R . Log(L)` requires representing `pi` to roughly
`log10(|V|) + working_precision` digits — at the `n = 11` magnitudes this is
already on the order of `10^33` digits of `pi`, which is hopelessly
infeasible.

In `i^Z` form the only argument reduction is **mod 4 on the real part of a
complex interval**, which is exact integer subtraction. No digit of `pi` is
needed at the reduction step. `pi` enters only at the final `sin` / `cos`
evaluation, where the argument is a ground-band interval of width `<= pi`.

This is the analogue, at the algebraic level, of the
classical Payne-Hanek argument-reduction trick — but here we can afford
to be more aggressive because the periodicity is integer (mod 4) rather
than transcendental (mod `2 pi`).

### 5.4 Tri-valued dedup loop

Pseudocode for the per-level dedup at `n = 12`:

```python
def dedup(values, *, ctx):
    representatives = []
    for v in values:
        merged = False
        for r in representatives:
            verdict = certified_equal(v, r, ctx)
            if verdict is True:
                merged = True
                break
            if verdict is Undefined:
                # Refine and retry — bounded loop, see below.
                verdict = refine_and_decide(v, r, start_ctx=ctx)
                if verdict is True:
                    merged = True
                    break
                if verdict is Undefined:
                    # Genuinely undecidable at the engine's algebraic
                    # reach; report the cluster, do not merge silently.
                    raise UndecidableCluster(v, r)
        if not merged:
            representatives.append(v)
    return representatives
```

`refine_and_decide` doubles `working_precision_digits` and recomputes `v`,
`r`, and the equality predicate, up to a configurable cap. Genuinely
undecidable clusters (the "near `i^i`" and "near `1`" residues identified by
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md))
surface explicitly rather than being collapsed.

For each `UndecidableCluster`, the operator chooses:

1. Inject a known algebraic identity (e.g., the `i^i = e^(-pi/2)` collisions
   that come from "islands of associativity" — see the OEIS comments and
   the discussion in `A198683-report-2.md`).
2. Increase the working-precision cap.
3. Record the cluster as residual and report a conditional certificate
   (`a(12) in {2926, 2927}` etc.).

Either way, the historical mistake — silent merge of distinct values — is
structurally impossible.

### 5.5 What the certified `compute_a198683.py` looks like

The control flow is unchanged from the existing script. The only
substantive changes are:

| Existing | Certified |
|---|---|
| `from mpmath import mpc, mp; mp.dps = 220` | `from numerics import Interval, with_working_precision, equal, log, exp, pow_` |
| `def _pow(a: mpc, b: mpc) -> mpc:` | `def _pow(a: PolarValue, b: PolarValue) -> PolarValue:` |
| `def _dedupe_mpc(values, *, bucket_rel, cmp_tol):` | `def _dedupe_certified(values, *, ctx):` |
| `if mp.almosteq(z1, z2, rel_eps=cmp_tol, abs_eps=cmp_tol):` | `verdict = equal(z1, z2, ctx); ...` |
| Special "overflow bucket" for one tiny `n = 12` candidate | None — tower-shaped intervals absorb it naturally |

The recurrence over `{V[n]}` and the candidate-generation loop survive
verbatim.

## 6. Implementation phases and sizing

Sizes given in lines of code (LoC) added or changed and in counts of
functions / tests, per the repository's velocity-independent estimate
convention (see `CLAUDE.md`).

### Phase A — `numerics` engine extensions (contribute back upstream)

1. `numerics.constants.pi_bounds(target_bits)` and
   `pi_over_2_bounds`, `two_pi_bounds`. Implementation via Machin-like
   formula `pi/4 = 4 * atan(1/5) - atan(1/239)` using the existing
   atanh-style series infrastructure. ~150 LoC + ~30 LoC of tests.
2. `numerics.transcendentals.sin(GroundReal)`, `cos(GroundReal)` with
   explicit truncation-error bounds, exposed via the dispatcher as
   `numerics.sin`, `numerics.cos`. ~400-600 LoC + ~100 LoC of tests.
3. `tan`, `atan`, `atan2` — optional; not needed for the `i^Z` form path.
   Skip unless a separate workstream needs them.

### Phase B — Application layer in `src/Oeis/A198683/computations/python/`

4. `complex_interval.py` — `ComplexInterval` dataclass with `add`, `sub`,
   `mul`, `div`, `complex_exp`, `complex_log`. ~300-500 LoC + ~150 LoC of
   property tests.
5. `z_form.py` — `ZValue` representation, mod-4 reducer on `Re(Z)`,
   converters to `(rho, theta)` for display. ~200 LoC + ~80 LoC of tests.
6. `certified_equal.py` — tri-valued equality on `ZValue` driven by
   `numerics.equal`. ~120 LoC + ~80 LoC of tests.
7. `a198683_certified.py` — the recurrence + dedup loop. Largely a port of
   the existing `compute_a198683.py` with the `_pow` and `_dedupe`
   replacements from §5.5. ~400-600 LoC + ~150 LoC of tests.

### Phase C — Validation

8. Reproduce all OEIS-accepted terms `a(1) ... a(11)` from the certified
   pipeline. This is the smoke test: any disagreement here invalidates an
   engine extension before reaching `n = 12`.
9. Cross-check the certified pipeline against the existing Wolfram
   recurrence on `n <= 11` and on the 5139 `n = 12` candidate powers, to
   establish that the candidate-generation phase matches.
10. Run the certified dedup at `n = 12`. Expected outcomes (none of which
    are pre-decided):
    - A definite integer count, with every pair-wise verdict either `True`
      (cluster) or `False` (disjoint).
    - Or one or more `UndecidableCluster` events, each surfacing the
      candidate pair and the precision cap that was reached. Resolve each
      by raising the cap or by an algebraic identity per §5.4.

### Phase D — Reporting

11. Produce a result report under `src/Oeis/A198683/reports/` recording
    the certified value, the working precision required at each cluster,
    the engine commit hash, and an audit trail of the equality verdicts.
    Cross-link from the existing root-cause reports.

## 7. Risks and open questions

### 7.1 Cost of `sin` / `cos` at the bounded arguments after `i^Z` reduction

The arguments to `sin` / `cos` after mod-4 reduction live in a bounded
ground-band rectangle. Taylor series converges in `O(working_precision /
log(arg_width))` terms; for a bound `arg_width <= pi` and `working_precision
= 80` decimal digits, the truncation point is around 80-100 terms. The
per-term cost is one rational multiplication; total cost per `sin` call is
small enough that the dominant cost is the surrounding interval bookkeeping,
not the trig evaluation. Risk: low.

### 7.2 The "overflow bucket" candidate in the existing script

`compute_a198683.py` special-cases one `n = 12` candidate that mpmath cannot
materialise as a finite complex. In the certified pipeline this is just a
tower-shaped magnitude; no special-case is needed. We should verify that
the candidate is in fact materialisable as a `TowerBall` at the chosen
height ceiling. The OEIS comment puts the `n = 11` upper bound near
`10^(10^33)`, well inside the default ground-band-emax via tower height 2;
`n = 12` may push to height 3, which is covered by M2b-beta-5 in the
implementation plan. Risk: low to moderate, contingent on M2b-beta-5
landing.

### 7.3 Residual undecidable clusters

The two existing root-cause reports already predict that the
"near `i^i`" and "near `1`" clusters cannot be settled by any finite-precision
interval engine without an extra ingredient — either an algebraic-identity
oracle (e.g., proving that a specific sub-tree algebraically equals
`i^i = exp(-pi/2)`) or symbolic simplification. The certified pipeline
exposes these as `UndecidableCluster` events; it does not resolve them
single-handedly. Risk: this is by design and is the explicit boundary of
the approach. The deliverable is either:

- A complete certificate (no `UndecidableCluster` events), or
- A conditional certificate `a(12) in S` for a small explicit set `S`,
  plus the precise list of pairs whose equality is still open.

The current historical conflict `a(12) in {2919, 2926}` would already shrink
to a much sharper statement.

### 7.4 Performance

The existing `compute_a198683.py` runs through `n = 12` in seconds at
`dps = 220`. The certified pipeline will be slower per operation
(`Fraction`-backed `numerics.add` is significantly heavier than
`mpmath.mpc` addition) but operates on the same `5139`-candidate set and
the same recurrence. Order-of-magnitude expectation: the certified
pipeline completes in minutes at the same working precision. The
adaptive-precision refinement loop dominates for the small number of
near-collision clusters that demand higher precision. Risk: tolerable; if
it becomes binding, the engine extensions (Phase A) are themselves an
optimisation surface.

### 7.5 Test infrastructure for cross-verification

`numerics` already runs a Wolfram differential test
(`tests/test_wolfram_differential.py`). The A198683 certified pipeline
should add a similar cross-check that compares its `n <= 11` candidate
values against the Wolfram recurrence. This both verifies the engine and
provides regression coverage in case future `numerics` changes shift
endpoints. Risk: low.

### 7.6 Engine surface stability

`numerics` is at v1 and the implementation plan is still active. Adding
`sin` / `cos` / `pi` upstream is structurally aligned, but coordination
with the package owner is advisable so the API names (`numerics.sin` vs
`numerics.trig.sin`, `pi_bounds` vs `pi`, etc.) match the eventual
proposal-level design. Risk: low, but a courtesy ADR or design-review
exchange in `src/Numerics/python/docs/` is appropriate before Phase A
lands.

## 8. Verdict

`src/Numerics/python` is the right tool for the job. It supplies the
hardest infrastructure piece — sound, outward-rounded interval arithmetic
over a real-line representation that natively spans the magnitudes
A198683(12) produces — and its tri-valued equality predicate is exactly the
hook that the silent-merge artefact (root cause: `mp.almosteq`'s `abs_eps`
floor; see
[`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md))
cannot survive.

The missing pieces are well-scoped: `pi`, `sin`, `cos`, a complex-interval
wrapper, and a `Z`-form bookkeeping layer. Together these are a few
thousand lines of new code, all of it in the proposal-driven style the
package already follows, none of it requiring a soundness compromise.

If pursued, the realistic outcome is either:

- A clean certificate `a(12) = N` with a full audit trail of pair-wise
  verdicts, or
- A sharp conditional `a(12) in S` with `|S|` small (likely 1-3), plus
  the explicit list of structurally-degenerate clusters that need an
  algebraic-identity argument (the same ones the two existing root-cause
  reports already flag).

Either outcome would replace the historical "either `2919` or `2926`" note
with the strongest standalone evidence the local corpus has produced, and
would do so without depending on Wolfram's symbolic equality engine.

## 9. References

- [`exploratory/A198683-report-2.md`](exploratory/A198683-report-2.md)
  — the certification strategy this report operationalises.
- [`a198683-n12-contradiction-root-cause__9e7681d48134.md`](a198683-n12-contradiction-root-cause__9e7681d48134.md)
  — the precision-sweep root-cause analysis.
- [`a198683-n12-discrepancy-root-cause.md`](a198683-n12-discrepancy-root-cause.md)
  — the tolerance-policy root-cause analysis, including the structural
  diagnosis of the `near-zero`, `near-i^i`, and `near-1` clusters that
  the certified pipeline must either resolve or report as undecidable.
- [`../computations/python/compute_a198683.py`](../computations/python/compute_a198683.py)
  — the existing heuristic Python pipeline that the certified pipeline
  replaces.
- `src/Numerics/python/README.md` — `numerics` package overview and
  soundness contract.
- `src/Numerics/python/implementation-plan.md` — engine roadmap and
  changelog; confirms M2 / M3 completion status.
- `src/Numerics/python/numerics/arithmetic.py` — dispatcher entry points,
  including the tri-valued `equal` (line ~6682).
- `src/Numerics/python/numerics/constants.py` — module docstring
  acknowledges `pi` as future work.
- `src/Numerics/python/numerics/transcendentals.py` — `exp`, `expm1`,
  `ln`, `log1p` only; no trig.
- `src/Numerics/python/docs/m2b-tower-arithmetic-spec.md` — tower-regime
  arithmetic spec; confirms `TowerBall` semantics and the SEIR-style
  endpoint algorithms the magnitude side of A198683 will exercise.
