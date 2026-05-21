# A198683(12) Contradiction Root Cause

- Status: Root-cause analysis
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, and future agents
- Scope: Explain why the local A198683 reports reached `2919` and `2926` for `A198683(12)`
- Created (UTC): 2026-05-21T02:15:49Z
- Repository HEAD: 9e45d165358c99eb3554980b4a9de38a77536bcb

## Summary

The local disagreement is not a recurrence disagreement. Both result reports use
the same dynamic-programming recurrence over distinct lower-level values, both
reproduce the accepted OEIS terms through `n=11`, and both generate `5139`
candidate powers at `n=12`.

The root cause is the Python/mpmath report's finite-precision equality
heuristic. Its `2919` result comes from numerical clustering of final complex
approximations using scale-relative buckets and `mp.almosteq`; that clustering
mistakes very close, unresolved candidates for equal candidates. The apparent
stability reported for `160..260` decimal digits is only a low-precision
plateau, not a certificate.

The Wolfram report's `2926` result is the strongest recorded local computation:
it uses the OEIS-style exact Wolfram Language recurrence and `Union[..., SameTest
-> Equal]`. It is still a computer-algebra result rather than a standalone proof
certificate independent of Wolfram's equality engine.

## Evidence from rerunning the Python computation

The historical Python report claimed that `2919` was stable across `160`, `180`,
`220`, and `260` decimal digits. Rerunning the same script beyond that precision
invalidates the claim:

| Command shape | Result |
|---|---:|
| `--dps 180 --n 12` | `2919` |
| `--dps 260 --n 12` | `2919` |
| `--dps 320 --n 12` | `2919` |
| `--dps 500 --n 12` | `2919` |
| `--dps 800 --n 12` | `2920` |
| `--dps 1000 --n 12` | `2921` |
| `--dps 1200 --n 12` | `2922` |
| `--dps 1500 --n 12` | `2922` |
| `--dps 2000 --n 12` | `2922` |
| `--dps 3000 --n 12` | `2924` |

The count drifting upward as precision increases is the diagnostic signature:
some candidates merged at low precision separate when the approximations carry
more information. A true exact equality count should not move this way under
increased working precision.

A second check reused the same generated `n=12` approximations and tightened the
final comparison tolerance. At `2000` decimal digits, increasing the comparison
strictness moved the total from `2922` to `2924`. At `3000` decimal digits,
strict tolerances again stabilized at `2924` for the tested window. This confirms
that the old `2919` result depends on the numerical merge policy, not just on the
set recurrence.

## Why the Python method is insufficient

The script in `../computations/python/compute_a198683.py` represents ordinary
candidates as `mpmath` complex bigfloats and then deduplicates those approximate
values:

```text
bucket key on approximate Re/Im, then mp.almosteq(...)
```

That is useful as a smoke test, but it cannot certify equality for A198683(12).
The difficult cases are not ordinary close floating-point comparisons:

- Principal complex power repeatedly reduces arguments modulo `2 Pi`, so each
  internal node contains a discrete branch/wrap decision.
- By `n=11`, OEIS already records magnitudes with decimal exponents around
  `4.1e34`; branch and equality decisions at `n=12` can need absolute
  information far beyond a few hundred decimal digits.
- The Python script compares final materialized values rather than preserving a
  proof object for every principal-log branch decision and every equality or
  inequality.
- Matching the accepted counts through `n=11` is a necessary smoke test, but it
  does not prove the chosen representatives and near-collision decisions are
  adequate for `n=12`.

The special "overflow bucket" in the Python script is not the source of the
seven-class conflict. The script consistently reports exactly one unmaterialized
candidate. The observed drift comes from the ordinary materialized candidates
being merged too aggressively.

## How to read the preserved reports

- `a198683-n12-python-mpmath-2919.md` is now best read as a historical
  finite-precision experiment. It found a low-precision plateau, but the plateau
  is false evidence for an exact count.
- `a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md` is the strongest
  local evidence for `2926`. Its result depends on Wolfram Language exact
  expression evaluation and `Equal`, not on numeric clustering.
- The exploratory reports correctly identify the hard part: the value is not
  settled by enumerating parenthesizations, but by certifying branch choices and
  equality/inequality for a small number of near-collision classes.

## Current conclusion

The contradiction should be documented as follows:

```text
2919 is invalidated as a finite-precision mpmath deduplication artifact.
2926 is the strongest recorded local result, coming from the exact Wolfram recurrence.
A formal independent certificate would still be needed to make the repository
claim completely independent of Wolfram's symbolic equality engine.
```

This is stricter than the previous neutral index wording. The corpus should
preserve the conflicting reports, but readers should no longer treat `2919` and
`2926` as equally supported by the local evidence.

## Reproducibility notes from this root-cause pass

The Python drift evidence above was reproduced locally from the current
`src/Oeis/A198683/computations/python/compute_a198683.py` script. In the same
session, the historical Wolfram command and a direct `wolframscript -file` run
did not complete within a `604` second timeout. That timeout does not explain
the contradiction; it only means the historical `2926` Wolfram run remains a
recorded result rather than a freshly reproduced result from this pass.
