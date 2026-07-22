(** Public surface and assumption audit for ordinary PA leaf certificates. *)

From BoundedPAConsistency Require Import RawCodedPAProofLeafCertificates.

Import PABoundedRawCodedPAProofLeafCertificates.

Check raw_codedPAAxiomWitnessContext_empty.
Check rawProofLemCertificate.
Check raw_codedPAProofOf_lem.
Check raw_codedPAProvability_lem.

Print Assumptions raw_codedPAAxiomWitnessContext_empty.
Print Assumptions raw_codedPAProofOf_lem.
Print Assumptions raw_codedPAProvability_lem.
