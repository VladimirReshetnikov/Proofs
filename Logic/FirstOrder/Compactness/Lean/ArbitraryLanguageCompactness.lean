import Mathlib.ModelTheory.Satisfiability

/-!
# Compactness for an arbitrary first-order language

This is the literal signature-polymorphic form of the compactness theorem:
for any first-order language (with symbol types in arbitrary universes) and
any set of sentences, satisfiability is equivalent to satisfiability of every
finite subset.  Mathlib proves the result semantically by an ultraproduct; the
repository gives it a stable, audited headline alongside its independent
from-scratch proof for the local binary-relation language.
-/

namespace LeanProofs.FirstOrderCompactness

universe u v

/-- **First-order compactness theorem, arbitrary-language form.** -/
theorem arbitrary_language_compactness
    {L : FirstOrder.Language.{u, v}} {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable

end LeanProofs.FirstOrderCompactness
