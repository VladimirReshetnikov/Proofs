(** Assumption audit for the compact selector scope certificates. *)

From BoundedPAConsistency Require Import RawCodedCompactSelectorScopes.

Import PABoundedRawCodedCompactSelectorScopes.

Print Assumptions
  compactRestrictedPAConsistencyFormulaCodeGraph_scoped_two.
Print Assumptions standardFormulaScoped_codedPAProofOfTermAt.
Print Assumptions compactSelectorPackageFormula_scoped_one.
