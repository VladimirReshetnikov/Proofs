# Coq proof of PA non-finite axiomatizability

This directory contains the independent Coq development of the
Ryll-Nardzewski finite-Skolem-hull proof.  It uses the repository's PA syntax,
natural-deduction calculus, completeness theorem, and PA-in-HF interpretation.
The target statement uses the deductive notion of finite axiomatization: a
finite list of arithmetic sentences having exactly PA's sentence consequences
in the original language.  `TraceContractRealization.v` proves the
unconditional headline theorem
`PATraceContractRealization.peano_arithmetic_not_finitely_axiomatizable`.

## Construction

The proof is organized around a strict separation between the ambient model
and the eventual countermodel.

- `HierarchyReduction.v` defines the finite, cofinal hierarchy
  `PARankFragment n` and the law-free `RawPAModel` semantics used by the
  countermodels.
- `NonstandardHFFin.v` applies first-order compactness to relativized
  hereditary-finite-set theory.  A looped marker names an ordinal above every
  standard numeral; PA-in-HF yields an ambient raw arithmetic algebra which
  satisfies every sealed PA axiom.
- `FiniteSkolemHull.v`, `CanonicalSelector.v`, and `CanonicalSelectorPA.v`
  close the distinguished nonstandard element under arithmetic and canonical
  least/default witnesses.  They prove bounded-rank elementarity and transfer
  the requested rank fragment.  No `PA.Model` is built for the hull: full PA
  remains an ambient-model hypothesis only.
- `SkolemProgramCode.v` gives finite Skolem programs injective polynomial codes
  whose recursive child codes are strictly smaller than their parents.
- `FiniteBetaCoding.v` proves external finite beta coding in any raw model of
  PA and, crucially, constructs beta parameters denoted by Skolem programs, so
  both parameters belong to the hull.
- `ProgramTrace.v` defines one fixed first-order beta-table evaluator.  It
  dispatches over the finite rank-bounded formula enumeration rather than
  interpreting coded PA syntax.  Every recursive lookup carries an explicit
  child-code bound.  Its zero default is enabled only when no genuine output
  satisfies a constructor case.
- `TotalProgramRows.v` gives an exhaustive total row decoder for every
  standard natural-number code, proves round trips for genuine programs, and
  builds the finite canonical beta table through an arbitrary target.
- `StandardTraceRows.v` performs semantic inversion and standard-code
  normalization for arbitrary satisfying rows.
- `CanonicalTotalRows.v` selects the canonical genuine row, or the guarded
  zero row, supplied by the total decoder at every standard code.
- `StandardTraceFunctionality.v` uses strong induction on standard codes to
  compare independently chosen beta tables, not merely two entries in one
  table, and proves functionality of the fixed trace evaluator.
- `TotalTraceEvaluator.v` constructs closure-preserving canonical beta tables
  in the hull and proves evaluator totality at every standard code.
- `EvaluatorCutContract.v` is evaluator-independent.  Once standard codes
  enumerate the carrier functionally, it defines “not covered by codes below
  this bound.”  A pigeonhole argument shows that this formula defines exactly
  the standard elements.  It contains zero and is successor-closed, while the
  distinguished nonstandard seed is outside it, so a genuine sealed PA
  induction axiom fails.
- `TraceContractRealization.v` combines totality and cross-table functionality
  with the evaluator-cut contract, constructs a countermodel for every
  `PARankFragment n`, and passes that family to the finite-basis reduction in
  `FiniteBasisReduction.v`.

The construction contains no project-local `Axiom`, `Admitted`, or admitted
obligation.  `Audit.v` checks the public theorem surface and prints assumptions
for the critical results; `coqchk` independently rechecks the compiled object
and its imported dependency closure.

## Module order

The focused development is compiled in this order:

```text
FiniteBasisReduction.v
HierarchyReduction.v
FiniteSkolemHull.v
CanonicalSelector.v
CanonicalSelectorPA.v
SkolemProgramCode.v
FiniteBetaCoding.v
NonstandardHFFin.v
EvaluatorCutContract.v
ProgramTrace.v
TotalProgramRows.v
StandardTraceRows.v
CanonicalTotalRows.v
StandardTraceFunctionality.v
TotalTraceEvaluator.v
TraceContractRealization.v
Audit.v
```

Every module is registered in the repository-root `_CoqProject`;
`coq_makefile` derives the authoritative dependency graph from those sources.

## Verification

From the repository root, the complete Coq workspace can be rebuilt with:

```powershell
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

For focused compilation, use the same logical mappings as `_CoqProject`:

```powershell
$q = @(
  '-Q', 'Logic/FirstOrder/Coq', 'FirstOrder',
  '-Q', 'Logic/Interpretability/PAHF/Coq', 'PAHF',
  '-Q', 'Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq',
        'PAFiniteBasisReduction'
)

coqc @q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/Audit.v
```

With the preceding dependencies compiled, the final realization can be
recompiled and its complete imported object closure kernel-checked directly:

```powershell
coqc @q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/TraceContractRealization.v
coqchk @q PAFiniteBasisReduction.TraceContractRealization `
  PAFiniteBasisReduction.Audit
```

Both focused commands pass for the module containing
`PATraceContractRealization.peano_arithmetic_not_finitely_axiomatizable`.
