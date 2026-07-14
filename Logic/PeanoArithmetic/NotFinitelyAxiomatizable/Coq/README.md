# Coq status: finite-axiomatizability reduction

This folder does **not** yet contain an unconditional proof that first-order
Peano arithmetic is not finitely axiomatizable.

[`FiniteBasisReduction.v`](FiniteBasisReduction.v) formalizes the
standard deductive notion (a finite list of sentences with exactly PA's
sentence consequences) and proves that any such list can be replaced by one
finite list of genuine PA axioms. It then reduces the requested result to the
explicit proposition `PAInductionFragmentStrictness`: every finite PA fragment
fails to derive some further sealed induction instance.

That strictness theorem is not assumed as an axiom. Proving it requires
metamathematics absent from the current repository, such as an arithmetized
second-incompleteness argument or a formal strict hierarchy of induction
fragments. The existing `PA.Model` cannot fill the gap: by construction it
already carries induction for every meta-level predicate and therefore cannot
serve as a countermodel to a finite induction fragment.

Build and audit from the repository root:

```powershell
coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/FiniteBasisReduction.v

coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/Audit.v
```
