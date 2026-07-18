(** Public surface and kernel-assumption audit for [CodedProof]. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof.

Import PA.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.

Check RawProof.
Check rawContext.
Check rawConclusion.
Check rawProofValidb.
Check rawProofValidb_spec.
Check rawProofValidb_prov.
Check rawOfProvTree.
Check rawProofValidb_rawOfProvTree.
Check rawProofOccurrenceRank.
Check rawProofOccurrenceRank_rawOfProvTree.
Check rawProofAllBoundedb_rawOfProvTree.
Check contextCode.
Check decodeContext_contextCode.
Check rawProofCode.
Check decodeRawProof.
Check decodeRawProof_rawProofCode.
Check rawProofCode_injective.
Check checkRawProofCode.
Check provTreeCode.
Check checkRawProofCode_provTreeCode.
Check checkRawProofCode_sound.
Check PAAxiomWitness.
Check witnessedAxiom.
Check witnessedAxiom_is_Ax_s.
Check Ax_s_has_witness.
Check decodeAxiomWitness_axiomWitnessCode.
Check decodeAxiomWitnessList_axiomWitnessListCode.
Check restrictedPAProofCode.
Check decodeRestrictedPAProof.
Check decodeRestrictedPAProof_restrictedPAProofCode.
Check checkRestrictedPAProofCode.
Check checkRestrictedPAProofCode_provTreeCode.
Check RestrictedBProv_has_checked_code.
Check checkRestrictedPAProofCode_BProv_sound.
Check checkedRestrictedPA_consistent_standard.

Print Assumptions rawProofValidb_spec.
Print Assumptions rawProofValidb_prov.
Print Assumptions rawProofValidb_rawOfProvTree.
Print Assumptions rawProofOccurrenceRank_rawOfProvTree.
Print Assumptions rawProofAllBoundedb_rawOfProvTree.
Print Assumptions decodeRawProof_rawProofCode.
Print Assumptions rawProofCode_injective.
Print Assumptions checkRawProofCode_provTreeCode.
Print Assumptions checkRawProofCode_sound.
Print Assumptions witnessedAxiom_is_Ax_s.
Print Assumptions Ax_s_has_witness.
Print Assumptions decodeAxiomWitness_axiomWitnessCode.
Print Assumptions decodeRestrictedPAProof_restrictedPAProofCode.
Print Assumptions checkRestrictedPAProofCode_provTreeCode.
Print Assumptions RestrictedBProv_has_checked_code.
Print Assumptions checkRestrictedPAProofCode_BProv_sound.
Print Assumptions checkedRestrictedPA_consistent_standard.
