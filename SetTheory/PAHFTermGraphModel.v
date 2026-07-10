(* ===================================================================== *)
(*  PAHFTermGraphModel.v                                                *)
(*                                                                       *)
(*  Arbitrary-model transport for PA term graphs.  These small lemmas are *)
(*  the semantic plumbing needed by the direct PA-to-HFFin proof         *)
(*  translation; keeping them here avoids duplicating slot arithmetic in *)
(*  every translated proof rule.                                        *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia.
From SetTheory Require Import Fol PAHF PAHFInterpretations.

Lemma Sat_termGraphAt_shift_front :
  forall (V : Type) (mem : V -> V -> Prop)
    (t : PA.term) rho out (e : nat -> V) d,
  Sat V mem e (termGraphAt rho out t) ->
  Sat V mem (scons V d e)
    (termGraphAt (fun n => S (rho n)) (S out) t).
Proof.
  intros V mem t rho out e d h.
  assert (hrename :
    rename S (termGraphAt rho out t) =
      termGraphAt (fun n => S (rho n)) (S out) t).
  {
    apply termGraphAt_rename.
  }
  rewrite <- hrename.
  apply (proj2 (Sat_rename V mem (termGraphAt rho out t)
    S (scons V d e))).
  apply (proj1 (Sat_ext V mem (termGraphAt rho out t)
    e (fun n => scons V d e (S n))
    (fun n => eq_refl))).
  exact h.
Qed.

Lemma Sat_termGraphAt_shift_front_inv :
  forall (V : Type) (mem : V -> V -> Prop)
    (t : PA.term) rho out (e : nat -> V) d,
  Sat V mem (scons V d e)
    (termGraphAt (fun n => S (rho n)) (S out) t) ->
  Sat V mem e (termGraphAt rho out t).
Proof.
  intros V mem t rho out e d h.
  assert (hrename :
    rename S (termGraphAt rho out t) =
      termGraphAt (fun n => S (rho n)) (S out) t).
  { apply termGraphAt_rename. }
  rewrite <- hrename in h.
  apply (proj2 (Sat_ext V mem (termGraphAt rho out t)
    e (fun n => scons V d e (S n))
    (fun n => eq_refl))).
  exact (proj1 (Sat_rename V mem (termGraphAt rho out t)
    S (scons V d e)) h).
Qed.

Definition insertAfterOutputMap (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S k)
  end.

Lemma Sat_termGraphAt_insert_after_output :
  forall (V : Type) (mem : V -> V -> Prop)
    (t : PA.term) rho (e : nat -> V) outValue d,
  Sat V mem (scons V outValue e)
    (termGraphAt (fun n => S (rho n)) 0 t) ->
  Sat V mem (scons V outValue (scons V d e))
    (termGraphAt (fun n => S (S (rho n))) 0 t).
Proof.
  intros V mem t rho e outValue d h.
  assert (hrename :
    rename insertAfterOutputMap
      (termGraphAt (fun n => S (rho n)) 0 t) =
    termGraphAt (fun n => S (S (rho n))) 0 t).
  {
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n. reflexivity.
  }
  rewrite <- hrename.
  apply (proj2 (Sat_rename V mem
    (termGraphAt (fun n => S (rho n)) 0 t)
    insertAfterOutputMap (scons V outValue (scons V d e)))).
  apply (proj1 (Sat_ext V mem
    (termGraphAt (fun n => S (rho n)) 0 t)
    (scons V outValue e)
    (fun n => scons V outValue (scons V d e)
      (insertAfterOutputMap n))
    (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
  exact h.
Qed.

Lemma Sat_termGraphAt_insert_after_output_inv :
  forall (V : Type) (mem : V -> V -> Prop)
    (t : PA.term) rho (e : nat -> V) outValue d,
  Sat V mem (scons V outValue (scons V d e))
    (termGraphAt (fun n => S (S (rho n))) 0 t) ->
  Sat V mem (scons V outValue e)
    (termGraphAt (fun n => S (rho n)) 0 t).
Proof.
  intros V mem t rho e outValue d h.
  assert (hrename :
    rename insertAfterOutputMap
      (termGraphAt (fun n => S (rho n)) 0 t) =
    termGraphAt (fun n => S (S (rho n))) 0 t).
  {
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n. reflexivity.
  }
  rewrite <- hrename in h.
  apply (proj2 (Sat_ext V mem
    (termGraphAt (fun n => S (rho n)) 0 t)
    (scons V outValue e)
    (fun n => scons V outValue (scons V d e)
      (insertAfterOutputMap n))
    (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
  exact (proj1 (Sat_rename V mem
    (termGraphAt (fun n => S (rho n)) 0 t)
    insertAfterOutputMap (scons V outValue (scons V d e))) h).
Qed.
