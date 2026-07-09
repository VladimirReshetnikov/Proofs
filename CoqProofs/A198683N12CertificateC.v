(*
  The A198683(12) decision tree instantiated at the complex numbers.

  This is the Coq counterpart of the headline layer of Lean's
  LeanProofs/A198683N12Certificate.lean + A198683N12Endpoints.lean: the
  generic decision-tree module (A198683N12Certificate.v) is instantiated at
  V := Coquelicot's C, with the lexical evaluator interpreting the shared
  PowTower syntax by principal complex powers (evalC := eval Ci principalPow,
  mirroring Lean's IPowExpr.eval := PowTower.Expr.eval Complex.I
  principalPow), and with the three distinguished class values pinned to the
  concrete towers of A198683N12ComplexTowers.v.

  Because the near-1 split is PROVED on the Coq side too
  (nearOne25C_ne_nearOne1404C, riding the interval-certified norm
  separation of A198683N12Bounds.v), the headline theorems need only the
  wide partition witness:

  - a198683_twelve_mem_of_witness : any witness confines the distinct count
    of the n = 12 principal-power values to {2925, 2926};
  - a198683_twelve_eq_2926_of_overflowIsolated : the overflow no-miracles
    hypothesis pins the expected value 2926;
  - a198683_twelve_eq_2925_of_overflowCollision : its failure forces 2925.

  The count is expressed through the relational spec
  A198683Count n := DistinctCount (map evalC (parenthesizations 12)) n
  (exists and is unique for every evaluator); a witness of the count plays
  the role of Lean's a198683 12.
*)

From Coquelicot Require Import Complex.
From LeanProofsCoq Require Import PowTower.
From LeanProofsCoq Require Import A198683Complex.
From LeanProofsCoq Require Import A198683N12ComplexTowers.
From LeanProofsCoq Require Import A198683N12Certificate.

Module LeanProofs.
Module A198683N12CertificateC.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.
Module Cx := LeanProofsCoq.A198683Complex.LeanProofs.A198683Complex.
Module Tw := LeanProofsCoq.A198683N12ComplexTowers.LeanProofs.A198683N12ComplexTowers.
Module Cert := LeanProofsCoq.A198683N12Certificate.LeanProofs.A198683N12Certificate.

(* Principal-power evaluation of the shared lexical syntax. *)
Definition evalC : PT.Expr -> C := PT.eval Ci Cx.principalPow.

(* The complex-instantiated witness type: 2926 class representatives with
   cover, separation outside the two structurally uncertain comparisons,
   and the three distinguished classes pinned to the concrete towers. *)
Definition N12PartitionWitnessC : Type :=
  Cert.N12PartitionWitness C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C.

(* The no-miracles hypothesis for the overflow class, at C. *)
Definition OverflowIsolatedC (w : N12PartitionWitnessC) : Prop :=
  Cert.OverflowIsolated C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C w.

(* "The distinct count of the n = 12 principal-power values is n." *)
Definition A198683CountC (n : nat) : Prop :=
  Cert.A198683Count C evalC n.

Theorem a198683CountC_exists : exists n, A198683CountC n.
Proof. exact (Cert.a198683Count_exists C evalC). Qed.

Theorem a198683CountC_unique : forall n m,
  A198683CountC n -> A198683CountC m -> n = m.
Proof. exact (Cert.a198683Count_unique C evalC). Qed.

(* ------------------------------------------------------------------ *)
(* The headline theorems: the near-1 split is proved, so any witness   *)
(* alone confines the count, and the overflow question decides it.     *)
(* ------------------------------------------------------------------ *)

Theorem a198683_twelve_mem_of_witness :
  forall (w : N12PartitionWitnessC) (n : nat),
  A198683CountC n -> n = 2925 \/ n = 2926.
Proof.
  intros w n Hc.
  exact (Cert.a198683_twelve_mem_of_split C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C w
    Tw.nearOne25C_ne_nearOne1404C n Hc).
Qed.

Theorem a198683_twelve_eq_2926_of_overflowIsolated :
  forall (w : N12PartitionWitnessC),
  OverflowIsolatedC w ->
  forall n, A198683CountC n -> n = 2926.
Proof.
  intros w hiso n Hc.
  exact (Cert.a198683_twelve_eq_2926 C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C w
    Tw.nearOne25C_ne_nearOne1404C hiso n Hc).
Qed.

Theorem a198683_twelve_eq_2925_of_overflowCollision :
  forall (w : N12PartitionWitnessC),
  ~ OverflowIsolatedC w ->
  forall n, A198683CountC n -> n = 2925.
Proof.
  intros w hcol n Hc.
  exact (Cert.a198683_twelve_eq_2925_of_overflowCollision C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C w
    Tw.nearOne25C_ne_nearOne1404C hcol n Hc).
Qed.

(* The three-valued membership without the proved split, for reference. *)
Theorem a198683_twelve_mem :
  forall (w : N12PartitionWitnessC) (n : nat),
  A198683CountC n -> n = 2924 \/ n = 2925 \/ n = 2926.
Proof.
  intros w n Hc.
  exact (Cert.a198683_twelve_mem C evalC
    Tw.nearOne25C Tw.nearOne1404C Tw.overflowCandidate12C w n Hc).
Qed.

End A198683N12CertificateC.
End LeanProofs.
