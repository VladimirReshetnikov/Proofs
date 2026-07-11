/-
  PAHF.lean

  Peano arithmetic and hereditary finite sets.

  This facade exports the complete Lean formalization of the classical
  deductive bi-interpretability route between Peano arithmetic and the
  finite-generation hereditary-finite-set theory `HFFinAx_s`:

  * interpret hereditary finite sets in arithmetic by Ackermann's bit coding;
  * interpret arithmetic in hereditary finite sets by the finite von Neumann
    ordinals;
  * transfer first-order theorems in both directions;
  * prove both composite translations equivalent to the identity on sentences.

  The public certificate is `paHFFinDeductiveBiInterpretation`, and
  `PA_biinterpretable_with_HFFin` states its existence.  The extra
  finite-generation schema is essential: the foundation-style theory `HFAx_s`
  alone also has infinite models.  The reusable semantic layer additionally
  exposes the standard Ackermann model and its explicit round-trip isomorphisms.
-/

import SetTheory.PAHF.AckermannHFCore
import SetTheory.PAHF.PASyntax
import SetTheory.PAHF.ProofCalculus
import SetTheory.PAHF.RiemannHypothesis
import SetTheory.PAHF.Interpretation
import SetTheory.PAHF.RoundTrip
import SetTheory.PAHF.HFRoundTrip
