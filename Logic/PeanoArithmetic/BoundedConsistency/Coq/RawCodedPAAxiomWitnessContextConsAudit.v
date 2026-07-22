(** Assumption audit for witnessed PA-context extension. *)

From BoundedPAConsistency Require Import
  RawCodedPAAxiomWitnessContextCons.

Import PABoundedRawCodedPAAxiomWitnessContextCons.

Check raw_codedPAAxiomWitnessContext_cons.
Print Assumptions raw_codedPAAxiomWitnessContext_cons.
