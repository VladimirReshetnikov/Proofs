(* ===================================================================== *)
(*  PAHFRoundTripQuantifiers.v                                          *)
(*                                                                       *)
(*  Quantifier constructors for the PA -> HF -> PA round trip.          *)
(*                                                                       *)
(*  The proof is purely syntactic once the ordinal-code graph supplies  *)
(*  totality and range.  Those are kept in one small explicit interface: *)
(*  neither standard-model reflection nor an unproved arithmetic fact is *)
(*  hidden in the logical bookkeeping below.                            *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFProofCalculus
  PAHFOrdinalCode PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Normal forms of the two composite quantifiers. *)

Lemma hfFormulaAt_domain_up_eq_codedOrdinalDomain :
  forall codedMap,
    hfFormulaAt (hfUpVarMap codedMap) domainForm =
      codedOrdinalDomain.
Proof.
  intro codedMap.
  unfold codedOrdinalDomain, translateHFFormula.
  apply hfFormulaAt_ext_free.
  intros n hn.
  pose proof (domainForm_free n hn) as hn0.
  subst n.
  reflexivity.
Qed.

Lemma formulaAt_up_id : forall phi,
  formulaAt (upVarMap (fun n : nat => n)) phi =
    formulaAt (fun n : nat => n) phi.
Proof.
  intro phi.
  apply formulaAt_map_ext.
  intros [|n]; reflexivity.
Qed.

Lemma paCompositeAt_all_normalForm : forall codedMap phi,
  paCompositeAt codedMap (pAll phi) =
    pAll (pImp codedOrdinalDomain
      (paCompositeAt (hfUpVarMap codedMap) phi)).
Proof.
  intros codedMap phi.
  unfold paCompositeAt.
  change
    ((pAll (pImp
      (hfFormulaAt (hfUpVarMap codedMap) domainForm)
      (hfFormulaAt (hfUpVarMap codedMap)
        (formulaAt (upVarMap (fun n : nat => n)) phi)))) =
    pAll (pImp codedOrdinalDomain
      (hfFormulaAt (hfUpVarMap codedMap)
        (formulaAt (fun n : nat => n) phi)))).
  rewrite hfFormulaAt_domain_up_eq_codedOrdinalDomain.
  rewrite formulaAt_up_id.
  reflexivity.
Qed.

Lemma paCompositeAt_ex_normalForm : forall codedMap phi,
  paCompositeAt codedMap (pEx phi) =
    pEx (pAnd codedOrdinalDomain
      (paCompositeAt (hfUpVarMap codedMap) phi)).
Proof.
  intros codedMap phi.
  unfold paCompositeAt.
  change
    ((pEx (pAnd
      (hfFormulaAt (hfUpVarMap codedMap) domainForm)
      (hfFormulaAt (hfUpVarMap codedMap)
        (formulaAt (upVarMap (fun n : nat => n)) phi)))) =
    pEx (pAnd codedOrdinalDomain
      (hfFormulaAt (hfUpVarMap codedMap)
        (formulaAt (fun n : nat => n) phi)))).
  rewrite hfFormulaAt_domain_up_eq_codedOrdinalDomain.
  rewrite formulaAt_up_id.
  reflexivity.
Qed.

(** Slot maps after opening a range witness (raw in slot [0], code in
    slot [1]) or a totality witness (code in slot [0], raw in slot [1]). *)

Definition rangeRawMap (rawMap : nat -> nat) : nat -> nat :=
  fun n => match n with
           | 0 => 0
           | S k => rawMap k + 2
           end.

Definition rangeCodedMap (codedMap : nat -> nat) : nat -> nat :=
  fun n => match n with
           | 0 => 1
           | S k => codedMap k + 2
           end.

Definition totalRawMap (rawMap : nat -> nat) : nat -> nat :=
  fun n => match n with
           | 0 => 1
           | S k => rawMap k + 2
           end.

Definition totalCodedMap (codedMap : nat -> nat) : nat -> nat :=
  fun n => match n with
           | 0 => 0
           | S k => codedMap k + 2
           end.

Lemma rename_paCompositeAt : forall r codedMap phi,
  rename r (paCompositeAt codedMap phi) =
    paCompositeAt (fun n => r (codedMap n)) phi.
Proof.
  intros r codedMap phi.
  unfold paCompositeAt.
  apply rename_hfFormulaAt.
Qed.

Lemma rename_succ_paCompositeAt_up : forall codedMap phi,
  rename S (paCompositeAt (hfUpVarMap codedMap) phi) =
    paCompositeAt (rangeCodedMap codedMap) phi.
Proof.
  intros codedMap phi.
  rewrite rename_paCompositeAt.
  unfold paCompositeAt.
  apply hfFormulaAt_ext.
  intros [|n]; unfold rangeCodedMap, hfUpVarMap; simpl; lia.
Qed.

Lemma rename_succ_rawBody : forall rawMap phi,
  rename S (rename (up rawMap) phi) =
    rename (totalRawMap rawMap) phi.
Proof.
  intros rawMap phi.
  rewrite rename_comp.
  apply rename_ext.
  intros [|n]; unfold totalRawMap, up; simpl; lia.
Qed.

Lemma subst_instTerm_range_rawBody : forall rawMap phi,
  subst (instTerm (tVar 0))
    (rename (up S)
      (rename (up S) (rename (upVarMap rawMap) phi))) =
  rename (rangeRawMap rawMap) phi.
Proof.
  intros rawMap phi.
  rewrite subst_instTerm_var_zero_rename_up_succ.
  rewrite rename_comp.
  apply rename_ext.
  intros [|n]; unfold rangeRawMap, up, upVarMap; simpl; lia.
Qed.

Lemma subst_instTerm_total_codedBody : forall codedMap phi,
  subst (instTerm (tVar 0))
    (rename (up S)
      (rename (up S)
        (paCompositeAt (hfUpVarMap codedMap) phi))) =
  paCompositeAt (totalCodedMap codedMap) phi.
Proof.
  intros codedMap phi.
  rewrite subst_instTerm_var_zero_rename_up_succ.
  rewrite rename_paCompositeAt.
  unfold paCompositeAt.
  apply hfFormulaAt_ext.
  intros [|n]; unfold totalCodedMap, hfUpVarMap; simpl; lia.
Qed.

Lemma subst_instTerm_var_zero_codedOrdinalDomain :
  subst (instTerm (tVar 0)) codedOrdinalDomain =
    codedOrdinalDomain.
Proof.
  rewrite subst_instTerm_var.
  transitivity (rename (fun n : nat => n) codedOrdinalDomain).
  - apply rename_ext_free.
    intros n hn.
    pose proof (codedOrdinalDomain_free n hn) as hn0.
    subst n.
    reflexivity.
  - apply rename_id.
Qed.

Lemma subst_instTerm_total_codedOrdinalDomain :
  subst (instTerm (tVar 0))
    (rename (up S) (rename (up S) codedOrdinalDomain)) =
  codedOrdinalDomain.
Proof.
  rewrite subst_instTerm_var_zero_rename_up_succ.
  transitivity (rename (fun n : nat => n) codedOrdinalDomain).
  - apply rename_ext_free.
    intros n hn.
    pose proof (codedOrdinalDomain_free n hn) as hn0.
    subst n.
    reflexivity.
  - apply rename_id.
Qed.

(** The exact arithmetic frontier used by both quantifier constructors.
    Totality is already reduced elsewhere to Ackermann adjunction.  The
    range field says that the reverse-translated HF ordinal domain consists
    exactly of outputs of the ordinal-code graph. *)

Definition PAOrdinalCodeGraphRangeProof : Prop :=
  forall (G : list formula) (coded : term),
    BProv Ax_s G
      (iffForm
        (subst (instTerm coded) codedOrdinalDomain)
        (pEx (ordinalCodeGraphTermAt
          (tVar 0) (Term.rename S coded)))).

Record PAOrdinalCodeQuantifierProofs : Prop := {
  pa_quantifier_code_total : PAOrdinalCodeGraphTotalProof;
  pa_quantifier_code_range : PAOrdinalCodeGraphRangeProof
}.

Definition PAOrdinalCodeQuantifierProofs_of_total_and_range
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hrange : PAOrdinalCodeGraphRangeProof) :
  PAOrdinalCodeQuantifierProofs :=
  {| pa_quantifier_code_total := htotal;
     pa_quantifier_code_range := hrange |}.

Definition PAOrdinalCodeQuantifierProofs_of_adjoinExistence
    (hadjoin : PAHFAdjoinExistence)
    (hrange : PAOrdinalCodeGraphRangeProof) :
  PAOrdinalCodeQuantifierProofs :=
  PAOrdinalCodeQuantifierProofs_of_total_and_range
    (PAOrdinalCodeGraphTotalProof_of_adjoinExistence hadjoin)
    hrange.

Lemma BProv_Ax_s_ordinalCodeGraph_range_of_domain :
  forall (P : PAOrdinalCodeQuantifierProofs) G coded,
  BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain) ->
  BProv Ax_s G
    (pEx (ordinalCodeGraphTermAt
      (tVar 0) (Term.rename S coded))).
Proof.
  intros P G coded hdomain.
  pose proof (pa_quantifier_code_range P G coded) as hrange.
  pose proof (BProv_andE1 Ax_s G _ _ hrange) as hforward.
  exact (BProv_mp Ax_s G _ _ hforward hdomain).
Qed.

Lemma BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph :
  forall (P : PAOrdinalCodeQuantifierProofs) G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded) ->
  BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain).
Proof.
  intros P G raw coded hgraph.
  assert (hex : BProv Ax_s G
    (pEx (ordinalCodeGraphTermAt
      (tVar 0) (Term.rename S coded)))).
  {
    apply (BProv_exI Ax_s G _ raw).
    rewrite subst_ordinalCodeGraphTermAt.
    simpl.
    rewrite term_subst_instTerm_rename_succ.
    exact hgraph.
  }
  pose proof (pa_quantifier_code_range P G coded) as hrange.
  pose proof (BProv_andE2 Ax_s G _ _ hrange) as hreverse.
  exact (BProv_mp Ax_s G _ _ hreverse hex).
Qed.

(** Forward half of the universal constructor.  An arbitrary coded-domain
    value is opened by range, paired with its raw preimage, and fed to the
    induction hypothesis. *)

Lemma BProv_Ax_s_paCompositeAt_all_forward :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
  forall G rawMap codedMap,
  (forall n, Free n (pAll phi) ->
    BProv Ax_s G
      (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
  BProv Ax_s G
    (pImp (rename rawMap (pAll phi))
      (paCompositeAt codedMap (pAll phi))).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  set (rawBody := rename (upVarMap rawMap) phi).
  set (codedBody := paCompositeAt (hfUpVarMap codedMap) phi).
  set (rawAll := pAll rawBody).
  set (codedAll := pAll (pImp codedOrdinalDomain codedBody)).
  set (C0 := rawAll :: G).
  set (C1 := map (rename S) C0).
  set (C2 := codedOrdinalDomain :: C1).
  assert (hcodedBody : BProv Ax_s C2 codedBody).
  {
    assert (hdomain : BProv Ax_s C2 codedOrdinalDomain).
    {
      apply BProv_ass.
      unfold C2. simpl. now left.
    }
    assert (hdomainInst : BProv Ax_s C2
      (subst (instTerm (tVar 0)) codedOrdinalDomain)).
    {
      rewrite subst_instTerm_var_zero_codedOrdinalDomain.
      exact hdomain.
    }
    pose proof (BProv_Ax_s_ordinalCodeGraph_range_of_domain
      P C2 (tVar 0) hdomainInst) as hrange.
    set (graphBody := ordinalCodeGraphTermAt (tVar 0) (tVar 1)).
    assert (hrange' : BProv Ax_s C2 (pEx graphBody)).
    {
      unfold graphBody.
      simpl in hrange.
      exact hrange.
    }
    set (C3 := graphBody :: map (rename S) C2).
    assert (hopened : BProv Ax_s C3 (rename S codedBody)).
    {
      assert (hgraph : BProv Ax_s C3 (ordinalCodeGraphAt 0 1)).
      {
        assert (hass : BProv Ax_s C3 graphBody).
        {
          apply BProv_ass.
          unfold C3. simpl. now left.
        }
        unfold graphBody, ordinalCodeGraphAt in *.
        exact hass.
      }
      assert (hpaired : forall n, Free n phi ->
        BProv Ax_s C3
          (ordinalCodeGraphAt
            (rangeRawMap rawMap n)
            (rangeCodedMap codedMap n))).
      {
        intros [|n] hn.
        - unfold rangeRawMap, rangeCodedMap.
          exact hgraph.
        - pose proof (hcode n hn) as h0.
          pose proof (BProv_context_cons Ax_s G rawAll _ h0) as hC0.
          pose proof (BProv_iterRenameSucc_of_sentences
            Ax_s sentence_ax_s 2 C0 _ hC0) as hrenamed.
          pose proof (BProv_context_prefix Ax_s
            [graphBody; rename S codedOrdinalDomain]
            _ _ hrenamed) as hctx.
          cbn [iterRenameContextSucc iterRenameSucc] in hctx.
          unfold C3, C2, C1, C0 in hctx |- *.
          cbn [map] in hctx |- *.
          unfold rangeRawMap, rangeCodedMap.
          unfold ordinalCodeGraphAt in hctx |- *.
          rewrite !rename_ordinalCodeGraphTermAt in hctx.
          cbn [Term.rename] in hctx.
          replace (rawMap n + 2) with (S (S (rawMap n))) by lia.
          replace (codedMap n + 2) with (S (S (codedMap n))) by lia.
          exact hctx.
      }
      pose proof (ih C3 (rangeRawMap rawMap)
        (rangeCodedMap codedMap) hpaired) as hih.
      pose proof (BProv_andE1 Ax_s C3 _ _ hih) as hihForward.
      assert (hall0 : BProv Ax_s C0 rawAll).
      {
        apply BProv_ass.
        unfold C0. simpl. now left.
      }
      pose proof (BProv_iterRenameSucc_of_sentences
        Ax_s sentence_ax_s 2 C0 _ hall0) as hallRenamed.
      pose proof (BProv_context_prefix Ax_s
        [graphBody; rename S codedOrdinalDomain]
        _ _ hallRenamed) as hallCtx.
      cbn [iterRenameContextSucc iterRenameSucc] in hallCtx.
      assert (hallCtx' : BProv Ax_s C3
        (pAll (rename (up S) (rename (up S) rawBody)))).
      {
        unfold C3, C2, C1 in *.
        unfold rawAll in hallCtx.
        simpl in hallCtx.
        exact hallCtx.
      }
      pose proof (BProv_allE Ax_s C3 _ (tVar 0) hallCtx') as hrawInst.
      assert (hraw : BProv Ax_s C3
        (rename (rangeRawMap rawMap) phi)).
      {
        unfold rawBody in hrawInst.
        rewrite subst_instTerm_range_rawBody in hrawInst.
        exact hrawInst.
      }
      pose proof (BProv_mp Ax_s C3 _ _ hihForward hraw) as hcomp.
      unfold codedBody.
      rewrite rename_succ_paCompositeAt_up.
      exact hcomp.
    }
    apply (BProv_exE_of_sentences Ax_s C2 graphBody codedBody
      sentence_ax_s hrange').
    unfold C3 in hopened.
    exact hopened.
  }
  assert (himp : BProv Ax_s C1
    (pImp codedOrdinalDomain codedBody)).
  {
    apply BProv_impI.
    unfold C2 in hcodedBody.
    exact hcodedBody.
  }
  assert (hall : BProv Ax_s C0 codedAll).
  {
    unfold codedAll.
    apply BProv_allI_of_sentences; [exact sentence_ax_s |].
    unfold C1 in himp.
    exact himp.
  }
  assert (hmain : BProv Ax_s G (pImp rawAll codedAll)).
  {
    apply BProv_impI.
    unfold C0 in hall.
    exact hall.
  }
  assert (hup : rename (upVarMap rawMap) phi =
    rename (up rawMap) phi).
  {
    apply rename_ext.
    intros [|n]; reflexivity.
  }
  unfold rawAll, rawBody in hmain.
  rewrite hup in hmain.
  unfold codedAll, codedBody in hmain.
  rewrite <- paCompositeAt_all_normalForm in hmain.
  simpl in hmain.
  exact hmain.
Qed.

(** Reverse half of the universal constructor.  Totality supplies a code
    for the freshly bound raw value. *)

Lemma BProv_Ax_s_paCompositeAt_all_reverse :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
  forall G rawMap codedMap,
  (forall n, Free n (pAll phi) ->
    BProv Ax_s G
      (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
  BProv Ax_s G
    (pImp (paCompositeAt codedMap (pAll phi))
      (rename rawMap (pAll phi))).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  set (rawBody := rename (upVarMap rawMap) phi).
  set (codedBody := paCompositeAt (hfUpVarMap codedMap) phi).
  set (rawAll := pAll rawBody).
  set (codedAll := pAll (pImp codedOrdinalDomain codedBody)).
  set (C0 := codedAll :: G).
  set (C1 := map (rename S) C0).
  assert (hrawBody : BProv Ax_s C1 rawBody).
  {
    pose proof (pa_quantifier_code_total P C1 (tVar 0)) as htotal.
    set (graphBody := ordinalCodeGraphTermAt (tVar 1) (tVar 0)).
    assert (htotal' : BProv Ax_s C1 (pEx graphBody)).
    {
      unfold graphBody.
      simpl in htotal.
      exact htotal.
    }
    set (C2 := graphBody :: map (rename S) C1).
    assert (hopened : BProv Ax_s C2 (rename S rawBody)).
    {
      assert (hgraphTerm : BProv Ax_s C2
        (ordinalCodeGraphTermAt (tVar 1) (tVar 0))).
      {
        apply BProv_ass.
        unfold C2, graphBody. simpl. now left.
      }
      assert (hgraph : BProv Ax_s C2 (ordinalCodeGraphAt 1 0)).
      {
        unfold ordinalCodeGraphAt.
        exact hgraphTerm.
      }
      assert (hpaired : forall n, Free n phi ->
        BProv Ax_s C2
          (ordinalCodeGraphAt
            (totalRawMap rawMap n)
            (totalCodedMap codedMap n))).
      {
        intros [|n] hn.
        - unfold totalRawMap, totalCodedMap.
          exact hgraph.
        - pose proof (hcode n hn) as h0.
          pose proof (BProv_context_cons Ax_s G codedAll _ h0) as hC0.
          pose proof (BProv_iterRenameSucc_of_sentences
            Ax_s sentence_ax_s 2 C0 _ hC0) as hrenamed.
          pose proof (BProv_context_prefix Ax_s
            [graphBody] _ _ hrenamed) as hctx.
          cbn [iterRenameContextSucc iterRenameSucc] in hctx.
          unfold C2, C1, C0 in hctx |- *.
          cbn [map] in hctx |- *.
          unfold totalRawMap, totalCodedMap.
          unfold ordinalCodeGraphAt in hctx |- *.
          rewrite !rename_ordinalCodeGraphTermAt in hctx.
          cbn [Term.rename] in hctx.
          replace (rawMap n + 2) with (S (S (rawMap n))) by lia.
          replace (codedMap n + 2) with (S (S (codedMap n))) by lia.
          exact hctx.
      }
      pose proof (ih C2 (totalRawMap rawMap)
        (totalCodedMap codedMap) hpaired) as hih.
      pose proof (BProv_andE2 Ax_s C2 _ _ hih) as hihReverse.
      assert (hall0 : BProv Ax_s C0 codedAll).
      {
        apply BProv_ass.
        unfold C0. simpl. now left.
      }
      pose proof (BProv_iterRenameSucc_of_sentences
        Ax_s sentence_ax_s 2 C0 _ hall0) as hallRenamed.
      pose proof (BProv_context_prefix Ax_s
        [graphBody] _ _ hallRenamed) as hallCtx.
      cbn [iterRenameContextSucc iterRenameSucc] in hallCtx.
      assert (hallCtx' : BProv Ax_s C2
        (pAll (rename (up S) (rename (up S)
          (pImp codedOrdinalDomain codedBody))))).
      {
        unfold C2, C1 in *.
        unfold codedAll in hallCtx.
        simpl in hallCtx.
        exact hallCtx.
      }
      pose proof (BProv_allE Ax_s C2 _ (tVar 0) hallCtx')
        as hbodyInst.
      assert (hcodedImp : BProv Ax_s C2
        (pImp codedOrdinalDomain
          (paCompositeAt (totalCodedMap codedMap) phi))).
      {
        change (BProv Ax_s C2
          (subst (instTerm (tVar 0))
            (rename (up S) (rename (up S)
              (pImp codedOrdinalDomain codedBody)))))
          in hbodyInst.
        change (BProv Ax_s C2
          (pImp
            (subst (instTerm (tVar 0))
              (rename (up S) (rename (up S)
                codedOrdinalDomain)))
            (subst (instTerm (tVar 0))
              (rename (up S) (rename (up S) codedBody)))))
          in hbodyInst.
        rewrite subst_instTerm_total_codedOrdinalDomain in hbodyInst.
        unfold codedBody in hbodyInst.
        rewrite subst_instTerm_total_codedBody in hbodyInst.
        exact hbodyInst.
      }
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph
        P C2 (tVar 1) (tVar 0) hgraphTerm) as hdomainInst.
      assert (hdomain : BProv Ax_s C2 codedOrdinalDomain).
      {
        rewrite subst_instTerm_var_zero_codedOrdinalDomain in hdomainInst.
        exact hdomainInst.
      }
      pose proof (BProv_mp Ax_s C2 _ _ hcodedImp hdomain) as hcomp.
      pose proof (BProv_mp Ax_s C2 _ _ hihReverse hcomp) as hraw.
      unfold rawBody.
      rewrite rename_succ_rawBody.
      exact hraw.
    }
    apply (BProv_exE_of_sentences Ax_s C1 graphBody rawBody
      sentence_ax_s htotal').
    unfold C2 in hopened.
    exact hopened.
  }
  assert (hall : BProv Ax_s C0 rawAll).
  {
    unfold rawAll.
    apply BProv_allI_of_sentences; [exact sentence_ax_s |].
    unfold C1 in hrawBody.
    exact hrawBody.
  }
  assert (hmain : BProv Ax_s G (pImp codedAll rawAll)).
  {
    apply BProv_impI.
    unfold C0 in hall.
    exact hall.
  }
  assert (hup : rename (upVarMap rawMap) phi =
    rename (up rawMap) phi).
  {
    apply rename_ext.
    intros [|n]; reflexivity.
  }
  unfold rawAll, rawBody in hmain.
  rewrite hup in hmain.
  unfold codedAll, codedBody in hmain.
  rewrite <- paCompositeAt_all_normalForm in hmain.
  simpl in hmain.
  exact hmain.
Qed.

Lemma BProv_Ax_s_paCompositeAt_all_exact :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
    PACompositeFormulaExact (pAll phi).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  apply PAHFProofCalculus.BProv_PA_iffForm_intro.
  - exact (BProv_Ax_s_paCompositeAt_all_forward
      P phi ih G rawMap codedMap hcode).
  - exact (BProv_Ax_s_paCompositeAt_all_reverse
      P phi ih G rawMap codedMap hcode).
Qed.

(** Forward half of the existential constructor.  Opening a raw witness
    and applying graph totality produces the coded witness. *)

Lemma BProv_Ax_s_paCompositeAt_ex_forward :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
  forall G rawMap codedMap,
  (forall n, Free n (pEx phi) ->
    BProv Ax_s G
      (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
  BProv Ax_s G
    (pImp (rename rawMap (pEx phi))
      (paCompositeAt codedMap (pEx phi))).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  set (rawBody := rename (upVarMap rawMap) phi).
  set (codedBody := paCompositeAt (hfUpVarMap codedMap) phi).
  set (codedAnd := pAnd codedOrdinalDomain codedBody).
  set (rawEx := pEx rawBody).
  set (codedEx := pEx codedAnd).
  set (C0 := rawEx :: G).
  assert (hcodedEx : BProv Ax_s C0 codedEx).
  {
    assert (hrawEx : BProv Ax_s C0 rawEx).
    {
      apply BProv_ass.
      unfold C0. simpl. now left.
    }
    set (C1 := rawBody :: map (rename S) C0).
    assert (hrawOpened : BProv Ax_s C1 (rename S codedEx)).
    {
      pose proof (pa_quantifier_code_total P C1 (tVar 0)) as htotal.
      set (graphBody := ordinalCodeGraphTermAt (tVar 1) (tVar 0)).
      assert (htotal' : BProv Ax_s C1 (pEx graphBody)).
      {
        unfold graphBody.
        simpl in htotal.
        exact htotal.
      }
      set (C2 := graphBody :: map (rename S) C1).
      assert (hcodeOpened : BProv Ax_s C2
        (rename S (rename S codedEx))).
      {
        assert (hgraphTerm : BProv Ax_s C2
          (ordinalCodeGraphTermAt (tVar 1) (tVar 0))).
        {
          apply BProv_ass.
          unfold C2, graphBody. simpl. now left.
        }
        assert (hgraph : BProv Ax_s C2 (ordinalCodeGraphAt 1 0)).
        {
          unfold ordinalCodeGraphAt.
          exact hgraphTerm.
        }
        assert (hpaired : forall n, Free n phi ->
          BProv Ax_s C2
            (ordinalCodeGraphAt
              (totalRawMap rawMap n)
              (totalCodedMap codedMap n))).
        {
          intros [|n] hn.
          - unfold totalRawMap, totalCodedMap.
            exact hgraph.
          - pose proof (hcode n hn) as h0.
            pose proof (BProv_context_cons Ax_s G rawEx _ h0) as hC0.
            pose proof (BProv_lift_two_contexts_of_sentences
              Ax_s sentence_ax_s C0 rawBody graphBody _ hC0) as hctx.
            unfold C2, C1, C0 in hctx |- *.
            cbn [map] in hctx |- *.
            unfold totalRawMap, totalCodedMap.
            unfold ordinalCodeGraphAt in hctx |- *.
            rewrite !rename_ordinalCodeGraphTermAt in hctx.
            cbn [Term.rename] in hctx.
            replace (rawMap n + 2) with (S (S (rawMap n))) by lia.
            replace (codedMap n + 2) with (S (S (codedMap n))) by lia.
            exact hctx.
        }
        pose proof (ih C2 (totalRawMap rawMap)
          (totalCodedMap codedMap) hpaired) as hih.
        pose proof (BProv_andE1 Ax_s C2 _ _ hih) as hihForward.
        assert (hraw0 : BProv Ax_s C1 rawBody).
        {
          apply BProv_ass.
          unfold C1. simpl. now left.
        }
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C1 graphBody _ hraw0) as hrawCtx.
        assert (hraw : BProv Ax_s C2
          (rename (totalRawMap rawMap) phi)).
        {
          unfold C2 in hrawCtx.
          unfold rawBody in hrawCtx.
          rewrite rename_succ_rawBody in hrawCtx.
          exact hrawCtx.
        }
        pose proof (BProv_mp Ax_s C2 _ _ hihForward hraw) as hcomp.
        pose proof (BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph
          P C2 (tVar 1) (tVar 0) hgraphTerm) as hdomainInst.
        assert (hdomain : BProv Ax_s C2 codedOrdinalDomain).
        {
          rewrite subst_instTerm_var_zero_codedOrdinalDomain in hdomainInst.
          exact hdomainInst.
        }
        assert (hand : BProv Ax_s C2
          (pAnd codedOrdinalDomain
            (paCompositeAt (totalCodedMap codedMap) phi))).
        {
          exact (BProv_andI Ax_s C2 _ _ hdomain hcomp).
        }
        assert (hinst : BProv Ax_s C2
          (subst (instTerm (tVar 0))
            (rename (up S) (rename (up S) codedAnd)))).
        {
          change (BProv Ax_s C2
            (pAnd
              (subst (instTerm (tVar 0))
                (rename (up S) (rename (up S)
                  codedOrdinalDomain)))
              (subst (instTerm (tVar 0))
                (rename (up S) (rename (up S) codedBody))))).
          rewrite subst_instTerm_total_codedOrdinalDomain.
          unfold codedBody.
          rewrite subst_instTerm_total_codedBody.
          exact hand.
        }
        assert (hex : BProv Ax_s C2
          (pEx (rename (up S) (rename (up S) codedAnd)))).
        {
          exact (BProv_exI Ax_s C2 _ (tVar 0) hinst).
        }
        unfold codedEx.
        change (BProv Ax_s C2
          (pEx (rename (up S) (rename (up S) codedAnd)))).
        exact hex.
      }
      apply (BProv_exE_of_sentences Ax_s C1 graphBody
        (rename S codedEx) sentence_ax_s htotal').
      unfold C2 in hcodeOpened.
      exact hcodeOpened.
    }
    apply (BProv_exE_of_sentences Ax_s C0 rawBody codedEx
      sentence_ax_s hrawEx).
    unfold C1 in hrawOpened.
    exact hrawOpened.
  }
  assert (hmain : BProv Ax_s G (pImp rawEx codedEx)).
  {
    apply BProv_impI.
    unfold C0 in hcodedEx.
    exact hcodedEx.
  }
  assert (hup : rename (upVarMap rawMap) phi =
    rename (up rawMap) phi).
  {
    apply rename_ext.
    intros [|n]; reflexivity.
  }
  unfold rawEx, rawBody in hmain.
  rewrite hup in hmain.
  unfold codedEx, codedAnd, codedBody in hmain.
  rewrite <- paCompositeAt_ex_normalForm in hmain.
  simpl in hmain.
  exact hmain.
Qed.

(** Reverse half of the existential constructor.  Opening the coded
    witness and applying range supplies its raw preimage. *)

Lemma BProv_Ax_s_paCompositeAt_ex_reverse :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
  forall G rawMap codedMap,
  (forall n, Free n (pEx phi) ->
    BProv Ax_s G
      (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
  BProv Ax_s G
    (pImp (paCompositeAt codedMap (pEx phi))
      (rename rawMap (pEx phi))).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  set (rawBody := rename (upVarMap rawMap) phi).
  set (codedBody := paCompositeAt (hfUpVarMap codedMap) phi).
  set (codedAnd := pAnd codedOrdinalDomain codedBody).
  set (rawEx := pEx rawBody).
  set (codedEx := pEx codedAnd).
  set (C0 := codedEx :: G).
  assert (hrawEx : BProv Ax_s C0 rawEx).
  {
    assert (hcodedEx : BProv Ax_s C0 codedEx).
    {
      apply BProv_ass.
      unfold C0. simpl. now left.
    }
    set (C1 := codedAnd :: map (rename S) C0).
    assert (hcodedOpened : BProv Ax_s C1 (rename S rawEx)).
    {
      assert (hand : BProv Ax_s C1 codedAnd).
      {
        apply BProv_ass.
        unfold C1. simpl. now left.
      }
      assert (hdomain : BProv Ax_s C1 codedOrdinalDomain).
      {
        unfold codedAnd in hand.
        exact (BProv_andE1 Ax_s C1 _ _ hand).
      }
      assert (hdomainInst : BProv Ax_s C1
        (subst (instTerm (tVar 0)) codedOrdinalDomain)).
      {
        rewrite subst_instTerm_var_zero_codedOrdinalDomain.
        exact hdomain.
      }
      pose proof (BProv_Ax_s_ordinalCodeGraph_range_of_domain
        P C1 (tVar 0) hdomainInst) as hrange.
      set (graphBody := ordinalCodeGraphTermAt (tVar 0) (tVar 1)).
      assert (hrange' : BProv Ax_s C1 (pEx graphBody)).
      {
        unfold graphBody.
        simpl in hrange.
        exact hrange.
      }
      set (C2 := graphBody :: map (rename S) C1).
      assert (hrawOpened : BProv Ax_s C2
        (rename S (rename S rawEx))).
      {
        assert (hgraph : BProv Ax_s C2 (ordinalCodeGraphAt 0 1)).
        {
          assert (hass : BProv Ax_s C2 graphBody).
          {
            apply BProv_ass.
            unfold C2. simpl. now left.
          }
          unfold graphBody, ordinalCodeGraphAt in *.
          exact hass.
        }
        assert (hpaired : forall n, Free n phi ->
          BProv Ax_s C2
            (ordinalCodeGraphAt
              (rangeRawMap rawMap n)
              (rangeCodedMap codedMap n))).
        {
          intros [|n] hn.
          - unfold rangeRawMap, rangeCodedMap.
            exact hgraph.
          - pose proof (hcode n hn) as h0.
            pose proof (BProv_context_cons Ax_s G codedEx _ h0) as hC0.
            pose proof (BProv_lift_two_contexts_of_sentences
              Ax_s sentence_ax_s C0 codedAnd graphBody _ hC0) as hctx.
            unfold C2, C1, C0 in hctx |- *.
            cbn [map] in hctx |- *.
            unfold rangeRawMap, rangeCodedMap.
            unfold ordinalCodeGraphAt in hctx |- *.
            rewrite !rename_ordinalCodeGraphTermAt in hctx.
            cbn [Term.rename] in hctx.
            replace (rawMap n + 2) with (S (S (rawMap n))) by lia.
            replace (codedMap n + 2) with (S (S (codedMap n))) by lia.
            exact hctx.
        }
        pose proof (ih C2 (rangeRawMap rawMap)
          (rangeCodedMap codedMap) hpaired) as hih.
        pose proof (BProv_andE2 Ax_s C2 _ _ hih) as hihReverse.
        assert (hcoded : BProv Ax_s C1 codedBody).
        {
          unfold codedAnd in hand.
          exact (BProv_andE2 Ax_s C1 _ _ hand).
        }
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C1 graphBody _ hcoded) as hcodedCtx.
        assert (hcomp : BProv Ax_s C2
          (paCompositeAt (rangeCodedMap codedMap) phi)).
        {
          unfold C2 in hcodedCtx.
          unfold codedBody in hcodedCtx.
          rewrite rename_succ_paCompositeAt_up in hcodedCtx.
          exact hcodedCtx.
        }
        pose proof (BProv_mp Ax_s C2 _ _ hihReverse hcomp) as hraw.
        assert (hinst : BProv Ax_s C2
          (subst (instTerm (tVar 0))
            (rename (up S) (rename (up S) rawBody)))).
        {
          unfold rawBody.
          rewrite subst_instTerm_range_rawBody.
          exact hraw.
        }
        assert (hex : BProv Ax_s C2
          (pEx (rename (up S) (rename (up S) rawBody)))).
        {
          exact (BProv_exI Ax_s C2 _ (tVar 0) hinst).
        }
        unfold rawEx.
        change (BProv Ax_s C2
          (pEx (rename (up S) (rename (up S) rawBody)))).
        exact hex.
      }
      apply (BProv_exE_of_sentences Ax_s C1 graphBody
        (rename S rawEx) sentence_ax_s hrange').
      unfold C2 in hrawOpened.
      exact hrawOpened.
    }
    apply (BProv_exE_of_sentences Ax_s C0 codedAnd rawEx
      sentence_ax_s hcodedEx).
    unfold C1 in hcodedOpened.
    exact hcodedOpened.
  }
  assert (hmain : BProv Ax_s G (pImp codedEx rawEx)).
  {
    apply BProv_impI.
    unfold C0 in hrawEx.
    exact hrawEx.
  }
  assert (hup : rename (upVarMap rawMap) phi =
    rename (up rawMap) phi).
  {
    apply rename_ext.
    intros [|n]; reflexivity.
  }
  unfold rawEx, rawBody in hmain.
  rewrite hup in hmain.
  unfold codedEx, codedAnd, codedBody in hmain.
  rewrite <- paCompositeAt_ex_normalForm in hmain.
  simpl in hmain.
  exact hmain.
Qed.

Lemma BProv_Ax_s_paCompositeAt_ex_exact :
  forall (P : PAOrdinalCodeQuantifierProofs) phi,
  PACompositeFormulaExact phi ->
    PACompositeFormulaExact (pEx phi).
Proof.
  intros P phi ih G rawMap codedMap hcode.
  apply PAHFProofCalculus.BProv_PA_iffForm_intro.
  - exact (BProv_Ax_s_paCompositeAt_ex_forward
      P phi ih G rawMap codedMap hcode).
  - exact (BProv_Ax_s_paCompositeAt_ex_reverse
      P phi ih G rawMap codedMap hcode).
Qed.

(** The requested constructor fields, packaged independently of equality.
    This is the exact bridge consumed by [PACompositeConstructorProofs]. *)

Record PACompositeQuantifierConstructorProofs : Prop := {
  pa_quantifier_all_exact : forall phi,
    PACompositeFormulaExact phi ->
      PACompositeFormulaExact (pAll phi);
  pa_quantifier_ex_exact : forall phi,
    PACompositeFormulaExact phi ->
      PACompositeFormulaExact (pEx phi)
}.

Definition PACompositeQuantifierConstructorProofs_of_graph
    (P : PAOrdinalCodeQuantifierProofs) :
  PACompositeQuantifierConstructorProofs :=
  {| pa_quantifier_all_exact :=
       BProv_Ax_s_paCompositeAt_all_exact P;
     pa_quantifier_ex_exact :=
       BProv_Ax_s_paCompositeAt_ex_exact P |}.

Definition PACompositeConstructorProofs_of_eq_and_quantifiers
    (heq : forall left right,
      PACompositeFormulaExact (pEq left right))
    (P : PAOrdinalCodeQuantifierProofs) :
  PACompositeConstructorProofs :=
  {| pa_composite_eq_exact := heq;
     pa_composite_all_exact :=
       BProv_Ax_s_paCompositeAt_all_exact P;
     pa_composite_ex_exact :=
       BProv_Ax_s_paCompositeAt_ex_exact P |}.
