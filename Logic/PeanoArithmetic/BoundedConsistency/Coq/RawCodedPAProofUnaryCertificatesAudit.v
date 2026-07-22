(** Public surface and assumption audit for unary PA-proof certificates. *)

From BoundedPAConsistency Require Import RawCodedPAProofUnaryCertificates.

Import PABoundedRawCodedPAProofUnaryCertificates.

Check rawProofBotECertificate.
Check raw_codedPAProofOf_botE_from_fields.
Check raw_codedPAProofOf_botE.
Check raw_codedPAProvability_botE.

Print Assumptions raw_codedPAProofOf_botE_from_fields.
Print Assumptions raw_codedPAProofOf_botE.
Print Assumptions raw_codedPAProvability_botE.
