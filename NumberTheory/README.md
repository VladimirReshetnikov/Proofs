# Number Theory

- [`DiophantineEquations/`](DiophantineEquations/) contains FLT for exponent
  four. Lean imports mathlib's unconditional theorem; the Coq wrapper exposes
  the remaining classical descent step explicitly because no modern library
  theorem is available there.
- [`IntegerSums/`](IntegerSums/) proves the exact floor-square-root summation
  identity.
- [`RationalEnumeration/`](RationalEnumeration/) proves that the rational
  floor orbit enumerates every nonnegative rational exactly once.
- [`RiemannHypothesis/PAStatement/`](RiemannHypothesis/PAStatement/) defines a
  first-order PA sentence for the Mertens/Littlewood arithmetic criterion. It
  formalizes the statement, not yet its analytic equivalence with RH.
