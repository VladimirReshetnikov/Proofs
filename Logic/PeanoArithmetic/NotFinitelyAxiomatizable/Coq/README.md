# Coq status: finite-axiomatizability reduction

This folder does **not** yet contain an unconditional proof that first-order
Peano arithmetic is not finitely axiomatizable.

[`FiniteBasisReduction.v`](FiniteBasisReduction.v) formalizes the
standard deductive notion (a finite list of sentences with exactly PA's
sentence consequences) and proves that any such list can be replaced by one
finite list of genuine PA axioms. It proves standard-model consistency for
every such fragment and reduces the requested result to the exact proposition
`PAFiniteFragmentStrictness`: every finite PA fragment fails to derive some
PA-provable sentence. It also proves the classical converse, so this
separation proposition is equivalent to PA's non-finite-axiomatizability, not
just sufficient for it. `PAInductionFragmentStrictness` is retained as the
stronger Ryll--Nardzewski conclusion.

[`HierarchyReduction.v`](HierarchyReduction.v) defines positive structural
ranks for PA terms and formulas and the canonical theory `PARankFragment n`:
the six base axioms plus induction for formulas of rank at most `n`.  It
machine-checks that every finite list of genuine PA axioms is contained in one
such fragment.  Consequently it is enough to prove
`PARankFragmentStrictness`, saying that every canonical fragment misses a
further induction instance; this proposition implies both
`PAFiniteFragmentStrictness` and the headline non-finite-axiomatizability
statement.  It is an explicit premise, not an axiom.

The same module defines a law-free `RawPAModel` containing only a carrier and
interpretations of `0`, successor, addition, and multiplication.  It proves
the repository's natural-deduction calculus sound for this raw semantics,
without constructing a `PA.Model` or assuming any arithmetic law.  Therefore
`PA_rank_fragment_separation_of_raw_countermodel` turns any raw model of
`PARankFragment n` that falsifies a genuine PA axiom into the corresponding
syntactic separation.  `rank_fragment_strictness_of_raw_countermodels`
packages a family of such models into `PARankFragmentStrictness`.

The semantic interface is instantiated unconditionally at rank zero.
`two_chain_raw_model` consists of two disjoint successor chains, with zero at
the root of the first; its addition and multiplication satisfy the displayed
recursion equations.  It validates all six non-induction axioms, hence all of
`PARankFragment 0`, but falsifies induction for
`x = 0 \/ exists y, x = S y` at the second chain's root.  Therefore
`PA_rank_zero_fragment_misses_zero_or_successor_induction` and
`PA_rank_zero_fragment_strict` are proved outright, not left as premises.

`finite_fragment_strictness_of_mostowski` also verifies the exact fixed-base
argument: for `T = Base ++ Delta`, local PA reflection supplies `Con(T)` and
Goedel II prevents `T` from proving that same sentence, hence weakening rules
out a `Delta`-proof. Reflection and instantiated Goedel II remain explicit
premises, not axioms. Formalizing them requires metamathematics absent from the
current repository. The existing `PA.Model` cannot fill the gap: by
construction it already carries induction for every meta-level predicate and
therefore cannot serve as a countermodel to a finite induction fragment.

Build and audit from the repository root:

```powershell
coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/FiniteBasisReduction.v

coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/HierarchyReduction.v

coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/Audit.v
```
