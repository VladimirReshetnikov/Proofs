(* ===================================================================== *)
(*  PAHFOrdinalCodeTermOperations.v                                     *)
(*                                                                       *)
(*  Constructor normal forms for PA composite term graphs.              *)
(*                                                                       *)
(*  Binder/slot-map normalization is separated from the arithmetic       *)
(*  inductions.  Addition and multiplication therefore expose one small  *)
(*  translated-HF operation core after their recursive operand graphs.   *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFOrdinalCode
  PAHFRoundTripEquality PAHFOrdinalCodeTermCompatibility
  PAHFTranslatedOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* --------------------------------------------------------------------- *)
(*  Successor                                                            *)
(* --------------------------------------------------------------------- *)

Lemma compositeTermGraphAt_succ : forall codedOut codedMap t,
  compositeTermGraphAt codedOut codedMap (tSucc t) =
    pEx (pAnd
      (compositeTermGraphAt 0 (fun n => codedMap n + 1) t)
      (hfAdjoinGraphTermAt
        (tVar (codedOut + 1)) (tVar 0) (tVar 0))).
Proof.
  intros codedOut codedMap t.
  assert (hterm :
      hfFormulaAt (hfUpVarMap (codedTermSlotMap codedOut codedMap))
        (termGraphAt (fun n => S n + 1) 0 t) =
      compositeTermGraphAt 0 (fun n => codedMap n + 1) t).
  {
    set (graph := termGraphAt S 0 t).
    assert (hgraph : Fol.rename (Fol.up S) graph =
        termGraphAt (fun n => S n + 1) 0 t).
    {
      unfold graph.
      rewrite termGraphAt_rename.
      apply termGraphAt_map_ext.
      intro n.
      unfold Fol.up.
      replace (S n + 1) with (S (S n)) by lia.
      reflexivity.
    }
    unfold compositeTermGraphAt.
    rewrite <- hgraph.
    rewrite hfFormulaAt_source_rename.
    unfold graph.
    apply hfFormulaAt_ext.
    intros [|n]; cbn [hfUpVarMap codedTermSlotMap Fol.up]; lia.
  }
  assert (hsucc :
      hfFormulaAt (hfUpVarMap (codedTermSlotMap codedOut codedMap))
        (HF_succAt 1 0) =
      hfAdjoinGraphTermAt
        (tVar (codedOut + 1)) (tVar 0) (tVar 0)).
  {
    unfold hfAdjoinGraphTermAt, HF_succAt, HF_adjoinAt, fIff, iffForm.
    cbn [hfFormulaAt hfUpVarMap codedTermSlotMap Term.rename].
    repeat rewrite hfMemTermAt_var.
    replace (codedOut + 1) with (S codedOut) by lia.
    reflexivity.
  }
  unfold compositeTermGraphAt at 1.
  cbn [termGraphAt hfFormulaAt].
  rewrite hterm.
  replace (0 + 1) with 1 by lia.
  rewrite hsucc.
  reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(*  Addition                                                             *)
(* --------------------------------------------------------------------- *)

Definition addLeftShift (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => k + 3
  end.

Definition addRightShift (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => k + 3
  end.

Lemma hfFormulaAt_add_left_termGraph_eq_composite : forall
    codedOut codedMap t,
  hfFormulaAt
      (hfUpVarMap (hfUpVarMap
        (codedTermSlotMap codedOut codedMap)))
      (termGraphAt (fun n => S n + 2) 1 t) =
    compositeTermGraphAt 1 (fun n => codedMap n + 2) t.
Proof.
  intros codedOut codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename addLeftShift graph =
      termGraphAt (fun n => S n + 2) 1 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n.
    unfold addLeftShift.
    lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n].
  - reflexivity.
  - cbn [addLeftShift].
    replace (n + 3) with (S (S (S n))) by lia.
    cbn [hfUpVarMap codedTermSlotMap].
    lia.
Qed.

Lemma hfFormulaAt_add_right_termGraph_eq_composite : forall
    codedOut codedMap t,
  hfFormulaAt
      (hfUpVarMap (hfUpVarMap
        (codedTermSlotMap codedOut codedMap)))
      (termGraphAt (fun n => S n + 2) 0 t) =
    compositeTermGraphAt 0 (fun n => codedMap n + 2) t.
Proof.
  intros codedOut codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename addRightShift graph =
      termGraphAt (fun n => S n + 2) 0 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n.
    unfold addRightShift.
    lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n].
  - reflexivity.
  - cbn [addRightShift].
    replace (n + 3) with (S (S (S n))) by lia.
    cbn [hfUpVarMap codedTermSlotMap].
    lia.
Qed.

Definition compositeAddGraphAt
    (codedOut : nat) (codedMap : nat -> nat) : formula :=
  hfFormulaAt
    (hfUpVarMap (hfUpVarMap
      (codedTermSlotMap codedOut codedMap)))
    (addGraphAt 2 1 0).

Definition compositeAddCoreSlotMap (codedOut n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S k) => codedOut + k + 2
  end.

Definition compositeAddCoreAt (codedOut : nat) : formula :=
  hfFormulaAt (compositeAddCoreSlotMap codedOut)
    (addGraphAt 2 1 0).

Lemma compositeAddGraphAt_eq_core : forall codedOut codedMap,
  compositeAddGraphAt codedOut codedMap =
    compositeAddCoreAt codedOut.
Proof.
  intros codedOut codedMap.
  unfold compositeAddGraphAt, compositeAddCoreAt.
  apply hfFormulaAt_ext_free.
  intros n hn.
  destruct (addGraphAt_free n 2 1 0 hn) as [-> | [-> | ->]];
    cbn [hfUpVarMap codedTermSlotMap compositeAddCoreSlotMap]; lia.
Qed.

Lemma compositeTermGraphAt_add_normalForm : forall
    codedOut codedMap left right,
  compositeTermGraphAt codedOut codedMap (tAdd left right) =
    pEx (pEx
      (pAnd
        (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
        (pAnd
          (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
          (compositeAddCoreAt codedOut)))).
Proof.
  intros codedOut codedMap left right.
  rewrite <- (compositeAddGraphAt_eq_core codedOut codedMap).
  unfold compositeTermGraphAt at 1.
  unfold compositeAddGraphAt.
  cbn [termGraphAt hfFormulaAt].
  rewrite hfFormulaAt_add_left_termGraph_eq_composite.
  rewrite hfFormulaAt_add_right_termGraph_eq_composite.
  reflexivity.
Qed.

(** Arithmetic kernel left after both recursive operand graphs have been
    normalized. *)
Definition PAOrdinalCodeAddCoreCompatibility : Prop :=
  forall (G : list formula) (leftRaw rightRaw : term) (codedOut : nat),
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (tVar 1)) ->
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (tVar 0)) ->
    BProv Ax_s G
      (iffForm
        (compositeAddCoreAt codedOut)
        (ordinalCodeGraphTermAt
          (tAdd leftRaw rightRaw) (tVar (codedOut + 2)))).

(* --------------------------------------------------------------------- *)
(*  Multiplication                                                       *)
(* --------------------------------------------------------------------- *)

Definition mulLeftShift (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => k + 4
  end.

Definition mulRightShift (n : nat) : nat :=
  match n with
  | 0 => 2
  | S k => k + 4
  end.

Lemma hfFormulaAt_mul_left_termGraph_eq_composite : forall
    codedOut codedMap t,
  hfFormulaAt
      (hfUpVarMap (hfUpVarMap (hfUpVarMap
        (codedTermSlotMap codedOut codedMap))))
      (termGraphAt (fun n => S n + 3) 1 t) =
    compositeTermGraphAt 1 (fun n => codedMap n + 3) t.
Proof.
  intros codedOut codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename mulLeftShift graph =
      termGraphAt (fun n => S n + 3) 1 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n.
    unfold mulLeftShift.
    lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n].
  - reflexivity.
  - cbn [mulLeftShift].
    replace (n + 4) with (S (S (S (S n)))) by lia.
    cbn [hfUpVarMap codedTermSlotMap].
    lia.
Qed.

Lemma hfFormulaAt_mul_right_termGraph_eq_composite : forall
    codedOut codedMap t,
  hfFormulaAt
      (hfUpVarMap (hfUpVarMap (hfUpVarMap
        (codedTermSlotMap codedOut codedMap))))
      (termGraphAt (fun n => S n + 3) 2 t) =
    compositeTermGraphAt 2 (fun n => codedMap n + 3) t.
Proof.
  intros codedOut codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename mulRightShift graph =
      termGraphAt (fun n => S n + 3) 2 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n.
    unfold mulRightShift.
    lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n].
  - reflexivity.
  - cbn [mulRightShift].
    replace (n + 4) with (S (S (S (S n)))) by lia.
    cbn [hfUpVarMap codedTermSlotMap].
    lia.
Qed.

Definition compositeMulGraphAt
    (codedOut : nat) (codedMap : nat -> nat) : formula :=
  hfFormulaAt
    (hfUpVarMap (hfUpVarMap (hfUpVarMap
      (codedTermSlotMap codedOut codedMap))))
    (fAnd (fEq 0 3) mulGraph).

Definition compositeMulCoreSlotMap (codedOut n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | S (S (S k)) => codedOut + k + 3
  end.

Definition compositeMulCoreAt (codedOut : nat) : formula :=
  hfFormulaAt (compositeMulCoreSlotMap codedOut)
    (fAnd (fEq 0 3) mulGraph).

Lemma compositeMulGraphAt_eq_core : forall codedOut codedMap,
  compositeMulGraphAt codedOut codedMap =
    compositeMulCoreAt codedOut.
Proof.
  intros codedOut codedMap.
  unfold compositeMulGraphAt, compositeMulCoreAt.
  apply hfFormulaAt_ext_free.
  intros n hn.
  simpl in hn.
  destruct hn as [heq | hmul].
  - destruct heq as [-> | ->];
      cbn [hfUpVarMap codedTermSlotMap compositeMulCoreSlotMap]; lia.
  - destruct (mulGraph_free n hmul) as [-> | [-> | ->]];
      cbn [hfUpVarMap codedTermSlotMap compositeMulCoreSlotMap]; lia.
Qed.

Lemma compositeTermGraphAt_mul_normalForm : forall
    codedOut codedMap left right,
  compositeTermGraphAt codedOut codedMap (tMul left right) =
    pEx (pEx (pEx
      (pAnd
        (compositeTermGraphAt 1 (fun n => codedMap n + 3) left)
        (pAnd
          (compositeTermGraphAt 2 (fun n => codedMap n + 3) right)
          (compositeMulCoreAt codedOut))))).
Proof.
  intros codedOut codedMap left right.
  rewrite <- (compositeMulGraphAt_eq_core codedOut codedMap).
  unfold compositeTermGraphAt at 1.
  unfold compositeMulGraphAt.
  cbn [termGraphAt hfFormulaAt].
  rewrite hfFormulaAt_mul_left_termGraph_eq_composite.
  rewrite hfFormulaAt_mul_right_termGraph_eq_composite.
  reflexivity.
Qed.

(** Arithmetic kernel left after both recursive operand graphs have been
    normalized. *)
Definition PAOrdinalCodeMulOpenCoreCompatibility : Prop :=
  forall (G : list formula) (leftRaw rightRaw : term) (codedOut : nat),
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (tVar 1)) ->
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (tVar 2)) ->
    BProv Ax_s G
      (iffForm
        (compositeMulCoreAt codedOut)
        (ordinalCodeGraphTermAt
          (tMul leftRaw rightRaw) (tVar (codedOut + 3)))).

(** The same core with its local output existentially bound.  Before the
    binder, the operand codes are slots zero and one and the external output
    is slot [codedOut + 2].  This is the form needed to reconstruct a
    multiplication term graph from its target ordinal-code graph. *)
Definition PAOrdinalCodeMulBoundCoreCompatibility : Prop :=
  forall (G : list formula) (leftRaw rightRaw : term) (codedOut : nat),
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (tVar 0)) ->
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (tVar 1)) ->
    BProv Ax_s G
      (iffForm
        (pEx (compositeMulCoreAt codedOut))
        (ordinalCodeGraphTermAt
          (tMul leftRaw rightRaw) (tVar (codedOut + 2)))).

Record PAOrdinalCodeMulCoreProofs : Prop := {
  pa_mul_open_core : PAOrdinalCodeMulOpenCoreCompatibility;
  pa_mul_bound_core : PAOrdinalCodeMulBoundCoreCompatibility
}.
