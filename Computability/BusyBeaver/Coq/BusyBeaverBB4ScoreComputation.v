(* ===================================================================== *)
(*  Computation-only four-state score certificate.                        *)
(*                                                                       *)
(*  Keeping the VM conversion in this minimal module is operationally    *)
(*  important: Rocq compiles the scored q200 enumeration once, and all   *)
(*  semantic proofs consume the resulting equality from a cached [.vo].  *)
(* ===================================================================== *)

From Stdlib Require Import List.
Import ListNotations.

From CoqBB4 Require Import BB4_Deciders_Pipeline.
From BusyBeaver Require Import BusyBeaverBB4Score.

Module BusyBeaverBB4ScoreComputation.

Module S := BusyBeaverBB4Score.

Definition score_q_0 : S.ScoreQueue := S.root_score_q_upd1_simplified.

Definition score_q_suc (q : S.ScoreQueue) : S.ScoreQueue :=
  S.score_upds q decider_all 13.

Definition score_q_200 : S.ScoreQueue :=
  Nat.iter 200 score_q_suc score_q_0.

(** [vm_cast_no_check] asks Rocq's VM evaluator to establish the conversion
    below.  Despite the historical name, the cast is checked when [Qed]
    closes the proof.  It does not use native OCaml compilation or widen the
    trusted boundary beyond Rocq's kernel/VM.  This minimal form compiled in
    181 seconds in the isolated benchmark on the pinned development. *)
Lemma score_q_200_empty :
  score_q_200 = (([], []), true).
Proof.
  vm_cast_no_check (eq_refl ((([], []), true) : S.ScoreQueue)).
Qed.

End BusyBeaverBB4ScoreComputation.
