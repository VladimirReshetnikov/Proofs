(*
  Coq counterpart shim for LeanProofs/A198683N12Endpoints.lean.

  The endpoint estimates themselves are represented in Coq by the existing
  complex-instantiated certificate stack:
    A198683N12Bounds.v
    A198683N12ComplexTowers.v
    A198683N12CertificateC.v

  This file gives the merged Lean endpoint module its own Coq import surface
  and re-exports the headline near-one split and A198683(12) consequences.
*)

From LeanProofsCoq Require Import A198683N12ComplexTowers.
From LeanProofsCoq Require Import A198683N12CertificateC.

Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A198683N12Endpoints.

Module Tw := LeanProofsCoq.A198683N12ComplexTowers.LeanProofs.A198683N12ComplexTowers.
Module CertC := LeanProofsCoq.A198683N12CertificateC.LeanProofs.A198683N12CertificateC.

Definition N12PartitionWitnessC : Type := CertC.N12PartitionWitnessC.
Definition OverflowIsolatedC : N12PartitionWitnessC -> Prop :=
  CertC.OverflowIsolatedC.
Definition A198683CountC : nat -> Prop := CertC.A198683CountC.

Theorem nearOneSplit :
  Tw.nearOne25C <> Tw.nearOne1404C.
Proof. exact Tw.nearOne25C_ne_nearOne1404C. Qed.

Theorem a198683_twelve_mem_of_witness :
  forall (w : N12PartitionWitnessC) (n : nat),
  A198683CountC n -> n = 2925 \/ n = 2926.
Proof. exact CertC.a198683_twelve_mem_of_witness. Qed.

Theorem a198683_twelve_eq_2926_of_overflowIsolated :
  forall (w : N12PartitionWitnessC),
  OverflowIsolatedC w ->
  forall n, A198683CountC n -> n = 2926.
Proof. exact CertC.a198683_twelve_eq_2926_of_overflowIsolated. Qed.

Theorem a198683_twelve_eq_2925_of_overflowCollision :
  forall (w : N12PartitionWitnessC),
  ~ OverflowIsolatedC w ->
  forall n, A198683CountC n -> n = 2925.
Proof. exact CertC.a198683_twelve_eq_2925_of_overflowCollision. Qed.

End A198683N12Endpoints.
End LeanProofs.
