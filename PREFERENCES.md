# Preferences

- Created (UTC): 2026-07-10T03:39:14Z
- Repository HEAD: d0b8e70c90a3abf3e76e94f95ae828be2f336b91

Inferred and explicitly stated user/project preferences for this proof repository.
See also the nearest project `README.md` for corpus-specific conventions.

## Formalization architecture

- **Carve reusable modules out of research formalizations.** When a proof
  development accumulates general-purpose infrastructure, split it into
  theory-independent modules with a clean import DAG and separate it from the
  research-specific content. State genericity boundaries precisely rather than
  overselling them. Mechanical refactors of proven code should preserve proof
  bodies verbatim where practical so the proof assistant can cheaply re-certify
  the move.

- **One lexical canon for the power-tower OEIS family.** A000081, A002845,
  A198683, and A199812 are all defined from the shared lexical syntax
  `LeanProofs.PowTower.Expr`; they differ only in the interpretation of the atom
  and binary exponentiation node. The lexical `valueSet`/`valueCard` is the
  canonical definition. Every computation-facing presentation enters proofs
  through a Lean-proved equivalence back to that canon. Infrastructure reusable
  by two or more sequences belongs in `LeanProofs/PowTower.lean`, and executable
  backends must be proved correct rather than trusted through `implemented_by`.

## Mathematical research

- **Try symbolic proof before numerical evidence.** For Wolfram-supported
  identity work, simplify the difference symbolically with `FunctionExpand`,
  `ComplexExpand`, and `FullSimplify` before using numerics or PSLQ.

- **Verify candidate identities robustly.** When symbolic simplification does
  not close an identity, test the difference with `PossibleZeroQ` under raised
  `$MaxExtraPrecision` (at least 100), and independently cross-check difficult
  cases before treating a numerical result as proof evidence.

- **Use canaries in integer-relation searches.** Include an unrelated constant,
  preferably `ChampernowneNumber[]`, in every PSLQ basis. A candidate relation
  must have zero canary coefficient and should recur across permutations,
  scalings, and working precisions before it is trusted as a discovery lead.

## Documentation and notation

- Use `ℜ` and `ℑ` for real and imaginary parts in prose, and `\Re` and
  `\Im` in LaTeX. Wolfram Language code continues to use the heads `Re` and
  `Im`.
- Current-state documents describe the repository as it exists now. Historical
  commands and paths remain unchanged in explicitly dated reports and captured
  agent logs.
