(** Public surface and assumption audit for selector-package induction. *)

From BoundedPAConsistency Require Import
  RawCodedPASelectorPackageInduction.

Import PABoundedRawCodedPASelectorPackageInduction.

Check selectorPackageFormula.
Check RawSelectorPackageAt.
Check raw_sat_selectorPackageFormula_iff.
Check RawSelectorPackageBase.
Check RawSelectorPackageSuccessorClosed.
Check raw_selectorPackages_all_of_base_and_successor.
Check RawSelectorPackageBaseInAllModels.
Check RawSelectorPackageSuccessorClosedInAllModels.
Check raw_restrictedPAConsistencyCompiler_of_package_induction.

(** The final theorem remains conditional on the two displayed construction
    laws; this audit must not be read as discharging either law. *)
Print Assumptions raw_sat_selectorPackageFormula_iff.
Print Assumptions raw_selectorPackages_all_of_base_and_successor.
Print Assumptions raw_restrictedPAConsistencyCompiler_of_package_induction.
