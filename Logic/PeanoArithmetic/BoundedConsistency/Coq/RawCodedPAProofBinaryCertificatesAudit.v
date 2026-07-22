(** Public surface and assumption audit for binary PA-proof certificates. *)

From BoundedPAConsistency Require Import RawCodedPAProofBinaryCertificates.

Import PABoundedRawCodedPAProofBinaryCertificates.

Check rawProofImpECertificate.
Check raw_codedPAProofOf_impE_from_fields.

Print Assumptions raw_codedPAProofOf_impE_from_fields.
