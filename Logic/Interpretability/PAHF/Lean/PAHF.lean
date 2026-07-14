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

import PAHF.AckermannHFCore
import PAHF.PASyntax
import PAHF.ProofCalculus
import PAHF.Interpretation
import PAHF.RawSemantics
import PAHF.RoundTrip
import PAHF.HFRoundTrip
