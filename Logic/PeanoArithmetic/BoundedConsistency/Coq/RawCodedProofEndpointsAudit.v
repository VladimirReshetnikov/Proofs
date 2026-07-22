(** Assumption audit for arithmetic raw-proof endpoint exposure. *)

From BoundedPAConsistency Require Import RawCodedProofEndpoints.

Import PABoundedRawCodedProofEndpoints.

Check proofEndpointCasesTermAt.
Check RawProofEndpointCases.
Check raw_sat_proofEndpointCasesTermAt_iff.

Check proofEndpointTermAt.
Check RawProofEndpoint.
Check raw_sat_proofEndpointTermAt_iff.
Check raw_proofEndpoint_constructor.

Print Assumptions raw_sat_proofEndpointCasesTermAt_iff.
Print Assumptions raw_sat_proofEndpointTermAt_iff.
Print Assumptions raw_proofEndpoint_constructor.
