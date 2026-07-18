(** Public surface and kernel-assumption audit for the coded checker formula.

    Notice what is intentionally absent: there is no declaration of type

      Formula.BProv Formula.Ax_s [] (NoRestrictedPAProofFormula n).

    Standard-model truth, even for every metatheoretic [n], is not an
    object-language PA derivation. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof
  CodedCheckerComputability CodedCheckerStructuralComputability
  CodedCheckerDecisionComputability CodedCheckerFormula.

Import PA.
Import PABoundedCodedProof.
Import PABoundedCodedDecoderComputability.
Import PABoundedCodedCheckerStructuralComputability.
Import PABoundedCodedCheckerDecisionComputability.
Import PABoundedCodedCheckerFormula.

Check term_decodeRestrictedPAProof.
Check term_checkRestrictedPAProofCode.
Check restrictedProofFlag.
Check one_eq_restrictedProofFlag.
Check RestrictedPAProofFormula.
Check RestrictedPAProofFormula_spec.
Check NoRestrictedPAProofFormula.
Check NoRestrictedPAProofFormula_spec.
Check NoRestrictedPAProofFormula_standard_true.

Print Assumptions term_decodeRestrictedPAProof.
Print Assumptions term_checkRestrictedPAProofCode.
Print Assumptions one_eq_restrictedProofFlag.
Print Assumptions RestrictedPAProofFormula_spec.
Print Assumptions NoRestrictedPAProofFormula_spec.
Print Assumptions NoRestrictedPAProofFormula_standard_true.
