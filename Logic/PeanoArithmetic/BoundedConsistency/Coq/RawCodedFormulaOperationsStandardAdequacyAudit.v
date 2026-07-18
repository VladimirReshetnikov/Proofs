(** Assumption audit for the standard formula-operation interface. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperationsStandardAdequacy.

Import PA.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.

Check standardFormulaShift.
Check standardFormulaSingleSubstitution.
Check standardFormulaShift_zero_one.
Check standardFormulaSingleSubstitution_zero.

Check raw_standardFormulaShift_atom.
Check raw_standardFormulaSubstitution_atom.

Print Assumptions standardFormulaShift_zero_one.
Print Assumptions standardFormulaSingleSubstitution_zero.
Print Assumptions raw_standardFormulaShift_atom.
Print Assumptions raw_standardFormulaSubstitution_atom.
