(* ===================================================================== *)
(*  BusyBeaverMathlib.v                                                  *)
(*                                                                       *)
(*  Coq counterpart of the Lean mathlib-facing BusyBeaver bridge.        *)
(*  Lean's file connects SetTheory.BusyBeaver to mathlib's Turing        *)
(*  machine and partial-recursive-code library; this Coq development has *)
(*  no such dependency.  The low-level compiler connection is therefore  *)
(*  exposed as an explicit record, while the reusable finite tape/counting*)
(*  lemmas and the domination consequence are proved directly.           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List ZArith.
From SetTheory Require Import BusyBeaver.
Import ListNotations.

Module BB := BusyBeaver.

Module BusyBeaverMathlib.

Theorem list_length_le_of_nodup_subset :
  forall (A : Type) (xs ys : list A),
    NoDup xs -> (forall x, In x xs -> In x ys) ->
    length xs <= length ys.
Proof.
  intros A xs ys hxs hsub.
  apply NoDup_incl_length; [exact hxs | ].
  intros x hx.
  exact (hsub x hx).
Qed.

Theorem tape_mem_of_read_true : forall tape pos,
  BB.Tape.read tape pos = true -> In pos tape.
Proof.
  intros tape pos h.
  unfold BB.Tape.read in h.
  destruct (in_dec Z.eq_dec pos tape) as [hin | hnot].
  - exact hin.
  - discriminate.
Qed.

Theorem positions_length_le_tape_length_of_read_true :
  forall positions tape,
    NoDup positions ->
    NoDup tape ->
    (forall pos, In pos positions -> BB.Tape.read tape pos = true) ->
    length positions <= length tape.
Proof.
  intros positions tape hPositions _hTape hRead.
  apply list_length_le_of_nodup_subset.
  - exact hPositions.
  - intros pos hpos.
    apply tape_mem_of_read_true.
    exact (hRead pos hpos).
Qed.

Definition rado_positions_of_nat_offsets (head : Z)
    (offsets : list nat) : BB.tape :=
  map (fun n => (head + Z.of_nat n)%Z) offsets.

Theorem nat_offset_position_injective : forall head,
  forall a b,
    (head + Z.of_nat a = head + Z.of_nat b)%Z -> a = b.
Proof.
  intros head a b h.
  apply Nat2Z.inj.
  lia.
Qed.

Theorem rado_positions_of_nat_offsets_nodup :
  forall head offsets,
    NoDup offsets -> NoDup (rado_positions_of_nat_offsets head offsets).
Proof.
  intros head offsets h.
  unfold rado_positions_of_nat_offsets.
  induction offsets as [|a rest IH].
  - constructor.
  - inversion h as [|? ? hnot hrest]; subst.
    simpl.
    constructor.
    + intro hin.
      apply in_map_iff in hin.
      destruct hin as [b [hb hbin]].
      apply hnot.
      assert (a = b).
      {
        apply (nat_offset_position_injective head).
        symmetry. exact hb.
      }
      subst b.
      exact hbin.
    + apply IH.
      exact hrest.
Qed.

Theorem rado_positions_of_nat_offsets_length :
  forall head offsets,
    length (rado_positions_of_nat_offsets head offsets) = length offsets.
Proof.
  intros head offsets.
  unfold rado_positions_of_nat_offsets.
  apply length_map.
Qed.

Theorem rado_positions_of_nat_offsets_read_true :
  forall head offsets tape,
    (forall n, In n offsets ->
      BB.Tape.read tape (head + Z.of_nat n)%Z = true) ->
    forall pos,
      In pos (rado_positions_of_nat_offsets head offsets) ->
      BB.Tape.read tape pos = true.
Proof.
  intros head offsets tape hRead pos hpos.
  unfold rado_positions_of_nat_offsets in hpos.
  apply in_map_iff in hpos.
  destruct hpos as [n [hpos hn]].
  rewrite <- hpos.
  exact (hRead n hn).
Qed.

Record SupportedCompilerBridge
    (TotalRecursive : (nat -> nat) -> Prop) : Type := {
  bridge_threshold : forall f, TotalRecursive f -> nat;
  bridge_realizes_lower_bound :
    forall f (hf : TotalRecursive f) n,
      bridge_threshold f hf <= n ->
      exists score, f n <= score /\ BB.AttainableScoreAtMost n score
}.

Theorem supportedCompilerBridge_has_lowerBoundCompiler :
  forall TotalRecursive,
    SupportedCompilerBridge TotalRecursive ->
    BB.HasEventuallyAtMostLowerBoundCompiler TotalRecursive.
Proof.
  intros TotalRecursive hBridge f hf.
  exists (bridge_threshold TotalRecursive hBridge f hf).
  intros n hn.
  exact (bridge_realizes_lower_bound TotalRecursive hBridge f hf n hn).
Qed.

Theorem sigma_eventually_dominates_every_supported_total_recursive :
  forall Sigma,
    BB.IsSigma Sigma ->
    forall TotalRecursive,
      SupportedCompilerBridge TotalRecursive ->
      forall f, TotalRecursive f -> BB.EventuallyDominates Sigma f.
Proof.
  intros Sigma hSigma TotalRecursive hBridge f hf.
  apply BB.eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    with (TotalRecursive := TotalRecursive).
  - exact hSigma.
  - apply supportedCompilerBridge_has_lowerBoundCompiler.
    exact hBridge.
  - exact hf.
Qed.

End BusyBeaverMathlib.
