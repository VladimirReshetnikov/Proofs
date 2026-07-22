(** Assumption audit for the compact-selector induction cases. *)

From BoundedPAConsistency Require Import
  RawCodedCompactSelectorInductionCases.

Import PABoundedRawCodedCompactSelectorInductionCases.

Print Assumptions PA_BProv_compactSelectorInductionZeroFormula.
Print Assumptions
  raw_codedPAProofOf_compactSelectorInductionZeroFormula.
Print Assumptions raw_compactSelectorInductionStep_exact.
