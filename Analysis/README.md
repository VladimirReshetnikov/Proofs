# Analysis

Exact analytic identities in paired Lean and Coq developments.

- [`TrigonometricIdentities/`](TrigonometricIdentities/) contains the
  eleven-term arctangent-square identity and the golden-ratio sine identity.
- [`ExponentialIdentities/`](ExponentialIdentities/) contains the exact floor
  certificate for the five-level tiny-exponent tower.

The Coq developments are mathematical ports rather than generated
translations. The tiny-exponent proof uses `coq-interval`; the trigonometric
proof derives the exact constants needed by the identity.
