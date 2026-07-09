# Wave-5 Reports

- Status: Informational index
- Audience: Maintainers, OEIS contributors, future agents
- Scope: The Lean decision-tree certificate for `A198683(12)` and the proved
  near-`1` split
- Created (UTC): 2026-07-08T22:15:25Z
- Repository HEAD: 0609c247be9ff7cb059d0df42aedefc4c4a6de2d

Wave-5 is the formalization step after the wave-4 checkpoint: the residual
`a(12)` uncertainty is packaged into named Lean hypotheses with a proved
decision tree, and the near-`1` split — one of the two structural
uncertainties — is proved outright, exposing and repairing two faulty
endpoint constants in the process.

| Report | What it records |
|--------|-----------------|
| [`a198683-n12-decision-tree-and-near-one-split.md`](a198683-n12-decision-tree-and-near-one-split.md) | The `N12PartitionWitness` decision tree, the proved `nearOneSplit`, the two refuted-and-repaired ladder constants, and the remaining road to `a(12) = 2926` |
| [`a198683-formalization-status-and-remaining-work.md`](a198683-formalization-status-and-remaining-work.md) | The honest ledger: exactly what is proved / conditional / data-certified / heuristic, and the measured remaining work for each goal (`a(8) = 77` pilot through the OEIS-grade `a(12)` artifact) |

The live Lean modules this wave documents:

- [`LeanProofs/A198683N12Certificate.lean`](../../../../LeanProofs/A198683N12Certificate.lean)
- [`LeanProofs/A198683N12Endpoints.lean`](../../../../LeanProofs/A198683N12Endpoints.lean)
