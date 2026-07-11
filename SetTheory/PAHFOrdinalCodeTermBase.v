(* ===================================================================== *)
(*  PAHFOrdinalCodeTermBase.v                                           *)
(*                                                                       *)
(*  Zero and successor constructors for the PA ordinal-code term graph. *)
(*                                                                       *)
(*  The zero constructor uses Ackermann membership extensionality.  The  *)
(*  successor constructor is reduced exactly to graph successor closure  *)
(*  and one-point Ackermann-adjoin existence.                            *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From SetTheory Require Import
  Fol Calculus PAHF PAHFOrdinalCode PAHFOrdinalCodeTotal
  PAHFOrdinalCodeTotalInduction PAHFOrdinalCodeRange
  PAHFRoundTripArithmetic
  PAHFOrdinalCodeTermCompatibility
  PAHFCompositeArithmetic PAHFOrdinalCodeFunctional
  PAHFOrdinalCodeTermOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* --------------------------------------------------------------------- *)
(* Empty-code normalization for the zero constructor.                    *)

Definition hfEmptyTermAt_base (setCode : term) : formula :=
  pAll (pImp
    (hfMemTermAt 0 (Term.rename S setCode))
    pBot).

Definition hfEmptyAt_base (setCode : nat) : formula :=
  hfEmptyTermAt_base (tVar setCode).

Lemma subst_hfEmptyTermAt_base : forall sigma setCode,
  subst sigma (hfEmptyTermAt_base setCode) =
    hfEmptyTermAt_base (Term.subst sigma setCode).
Proof.
  intros sigma setCode.
  unfold hfEmptyTermAt_base.
  cbn [subst].
  rewrite subst_up_hfMemTermAt_zero_rename_succ.
  reflexivity.
Qed.

Lemma rename_hfEmptyTermAt_base : forall r setCode,
  rename r (hfEmptyTermAt_base setCode) =
    hfEmptyTermAt_base (Term.rename r setCode).
Proof.
  intros r setCode.
  rewrite <- subst_var_rename.
  rewrite subst_hfEmptyTermAt_base.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_hfEmptyTermAt_base_not_mem : forall
    (B : formula -> Prop) G setCode query,
  BProv B G (hfEmptyTermAt_base setCode) ->
  BProv B G
    (pImp (hfMemTermAt query setCode) pBot).
Proof.
  intros B G setCode query hempty.
  unfold hfEmptyTermAt_base in hempty.
  pose proof (BProv_allE B G _ (tVar query) hempty) as hpoint.
  change (BProv B G
    (pImp
      (subst (instTerm (tVar query))
        (hfMemTermAt 0 (Term.rename S setCode)))
      pBot)) in hpoint.
  rewrite subst_instTerm_var_hfMemTermAt_zero_rename_succ in hpoint.
  exact hpoint.
Qed.

(** The closed Ackermann code zero satisfies the translated empty
    predicate. *)
Lemma BProv_Ax_s_hfEmptyTermAt_base_zero :
  BProv Ax_s [] (hfEmptyTermAt_base tZero).
Proof.
  pose proof (BProv_Ax_s_HF_empty_zero_body_of_member_bot
    BProv_Ax_s_HF_empty_zero_member_bot) as hraw.
  unfold hfEmptyTermAt_base.
  change (BProv Ax_s []
    (subst (instTerm tZero)
      (pAll (pImp (hfMemAt 0 1) pBot)))).
  exact hraw.
Qed.

(** Any two explicitly empty Ackermann codes have the same membership
    bits. *)
Lemma BProv_Ax_s_same_members_of_hfEmptyTermAt_base : forall
    G left right,
  BProv Ax_s G (hfEmptyTermAt_base left) ->
  BProv Ax_s G (hfEmptyTermAt_base right) ->
  BProv Ax_s G
    (pAll
      (iffForm
        (hfMemTermAt 0 (Term.rename S left))
        (hfMemTermAt 0 (Term.rename S right)))).
Proof.
  intros G left right hleft hright.
  set (Q := map (rename S) G).
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
    G _ hleft S) as hleftRenRaw.
  assert (hleftRen : BProv Ax_s Q
      (hfEmptyTermAt_base (Term.rename S left))).
  {
    unfold Q.
    rewrite rename_hfEmptyTermAt_base in hleftRenRaw.
    exact hleftRenRaw.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
    G _ hright S) as hrightRenRaw.
  assert (hrightRen : BProv Ax_s Q
      (hfEmptyTermAt_base (Term.rename S right))).
  {
    unfold Q.
    rewrite rename_hfEmptyTermAt_base in hrightRenRaw.
    exact hrightRenRaw.
  }
  set (leftMem := hfMemTermAt 0 (Term.rename S left)).
  set (rightMem := hfMemTermAt 0 (Term.rename S right)).
  assert (hforward : BProv Ax_s Q (pImp leftMem rightMem)).
  {
    set (C := leftMem :: Q).
    assert (hmem : BProv Ax_s C leftMem).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hnot : BProv Ax_s C (pImp leftMem pBot)).
    {
      apply (BProv_context_cons Ax_s Q leftMem).
      unfold leftMem.
      exact (BProv_hfEmptyTermAt_base_not_mem
        Ax_s Q (Term.rename S left) 0 hleftRen).
    }
    assert (hbot : BProv Ax_s C pBot).
    { exact (BProv_mp Ax_s C _ _ hnot hmem). }
    assert (hrightC : BProv Ax_s C rightMem).
    { exact (BProv_botE Ax_s C rightMem hbot). }
    unfold C in hrightC.
    exact (BProv_impI Ax_s Q leftMem rightMem hrightC).
  }
  assert (hreverse : BProv Ax_s Q (pImp rightMem leftMem)).
  {
    set (C := rightMem :: Q).
    assert (hmem : BProv Ax_s C rightMem).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hnot : BProv Ax_s C (pImp rightMem pBot)).
    {
      apply (BProv_context_cons Ax_s Q rightMem).
      unfold rightMem.
      exact (BProv_hfEmptyTermAt_base_not_mem
        Ax_s Q (Term.rename S right) 0 hrightRen).
    }
    assert (hbot : BProv Ax_s C pBot).
    { exact (BProv_mp Ax_s C _ _ hnot hmem). }
    assert (hleftC : BProv Ax_s C leftMem).
    { exact (BProv_botE Ax_s C leftMem hbot). }
    unfold C in hleftC.
    exact (BProv_impI Ax_s Q rightMem leftMem hleftC).
  }
  apply (BProv_allI_of_sentences Ax_s G _ sentence_ax_s).
  unfold iffForm.
  exact (BProv_andI Ax_s Q _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_eq_zero_of_hfEmptyTermAt_base : forall
    (hext : PAHFMembershipExtensionalityProof) G setCode,
  BProv Ax_s G (hfEmptyTermAt_base setCode) ->
  BProv Ax_s G (pEq setCode tZero).
Proof.
  intros hext G setCode hempty.
  apply (BProv_Ax_s_eq_of_hfSameMembersTermAt_of_extensionality
    hext G setCode tZero).
  exact (BProv_Ax_s_same_members_of_hfEmptyTermAt_base
    G setCode tZero hempty
    (BProv_weaken_nil Ax_s G _ BProv_Ax_s_hfEmptyTermAt_base_zero)).
Qed.

Lemma BProv_hfEmptyTermAt_base_of_eq_zero : forall
    (B : formula -> Prop) G setCode,
  BProv B G (pEq setCode tZero) ->
  BProv B G (hfEmptyTermAt_base tZero) ->
  BProv B G (hfEmptyTermAt_base setCode).
Proof.
  intros B G setCode heq hzero.
  set (context := hfEmptyTermAt_base (tVar 0)).
  assert (hzeroInst : BProv B G (subst (instTerm tZero) context)).
  {
    unfold context.
    rewrite subst_hfEmptyTermAt_base.
    simpl.
    exact hzero.
  }
  pose proof (BProv_eqElim B G tZero setCode context
    (BProv_eqSym B G _ _ heq) hzeroInst) as hset.
  unfold context in hset.
  rewrite subst_hfEmptyTermAt_base in hset.
  simpl in hset.
  exact hset.
Qed.

Lemma compositeTermGraphAt_zero_base : forall codedOut codedMap,
  compositeTermGraphAt codedOut codedMap tZero =
    hfEmptyAt_base codedOut.
Proof.
  intros codedOut codedMap.
  unfold compositeTermGraphAt, hfEmptyAt_base,
    hfEmptyTermAt_base, codedTermSlotMap.
  cbn [termGraphAt hfFormulaAt hfUpVarMap Term.rename].
  rewrite hfMemTermAt_var.
  reflexivity.
Qed.

(** Complete zero-constructor compatibility. *)
Theorem PAOrdinalCodeTermZeroCompatibility_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  PAOrdinalCodeTermZeroCompatibility.
Proof.
  intros hext G rawMap codedMap codedOut hcode.
  rewrite compositeTermGraphAt_zero_base.
  set (empty := hfEmptyAt_base codedOut).
  set (graph := ordinalCodeGraphTermAt tZero (tVar codedOut)).
  assert (hforward : BProv Ax_s G (pImp empty graph)).
  {
    set (C := empty :: G).
    assert (hempty : BProv Ax_s C empty).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (heq : BProv Ax_s C (pEq (tVar codedOut) tZero)).
    {
      unfold empty, hfEmptyAt_base in hempty.
      exact (BProv_Ax_s_eq_zero_of_hfEmptyTermAt_base
        hext C (tVar codedOut) hempty).
    }
    assert (hzero : BProv Ax_s C
        (ordinalCodeGraphTermAt tZero tZero)).
    {
      exact (BProv_weaken_nil Ax_s C _
        (BProv_Ax_s_ordinalCodeGraphTermAt_zero [])).
    }
    assert (hgraph : BProv Ax_s C graph).
    {
      unfold graph.
      exact (BProv_ordinalCodeGraphTermAt_congr_coded
        Ax_s C tZero tZero (tVar codedOut)
        (BProv_eqSym Ax_s C _ _ heq) hzero).
    }
    unfold C in hgraph.
    exact (BProv_impI Ax_s G empty graph hgraph).
  }
  assert (hreverse : BProv Ax_s G (pImp graph empty)).
  {
    set (C := graph :: G).
    assert (hgraph : BProv Ax_s C graph).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hzeroGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt tZero tZero)).
    {
      exact (BProv_weaken_nil Ax_s C _
        (BProv_Ax_s_ordinalCodeGraphTermAt_zero [])).
    }
    assert (heq : BProv Ax_s C (pEq (tVar codedOut) tZero)).
    {
      unfold graph in hgraph.
      exact (BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_extensionality
        hext C tZero (tVar codedOut) tZero hgraph hzeroGraph).
    }
    assert (hzeroEmpty : BProv Ax_s C (hfEmptyTermAt_base tZero)).
    {
      exact (BProv_weaken_nil Ax_s C _
        BProv_Ax_s_hfEmptyTermAt_base_zero).
    }
    assert (hempty : BProv Ax_s C empty).
    {
      unfold empty, hfEmptyAt_base.
      exact (BProv_hfEmptyTermAt_base_of_eq_zero
        Ax_s C (tVar codedOut) heq hzeroEmpty).
    }
    unfold C in hempty.
    exact (BProv_impI Ax_s G graph empty hempty).
  }
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(* --------------------------------------------------------------------- *)
(* Successor graph equivalence.                                          *)

(** Successor closure, coded-output functionality, and one-point adjoin
    existence strengthen the recurrence implication to an equivalence. *)
Lemma BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ_base :
  PAOrdinalCodeGraphSuccClosureProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAHFAdjoinExistence ->
  forall G raw pred codedOut,
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) ->
    BProv Ax_s G
      (iffForm
        (hfAdjoinGraphTermAt codedOut pred pred)
        (ordinalCodeGraphTermAt (tSucc raw) codedOut)).
Proof.
  intros hsucc hfunctional hadjoin G raw pred codedOut hpred.
  assert (hforward : BProv Ax_s G
      (pImp
        (hfAdjoinGraphTermAt codedOut pred pred)
        (ordinalCodeGraphTermAt (tSucc raw) codedOut))).
  {
    set (C := hfAdjoinGraphTermAt codedOut pred pred :: G).
    assert (hadjoinC : BProv Ax_s C
        (hfAdjoinGraphTermAt codedOut pred pred)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hpredC : BProv Ax_s C
        (ordinalCodeGraphTermAt raw pred)).
    { exact (BProv_context_cons Ax_s G _ _ hpred). }
    assert (hnext : BProv Ax_s C
        (ordinalCodeGraphTermAt (tSucc raw) codedOut)).
    { exact (hsucc C raw pred codedOut hpredC hadjoinC). }
    unfold C in hnext.
    exact (BProv_impI Ax_s G _ _ hnext).
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt (tSucc raw) codedOut)
        (hfAdjoinGraphTermAt codedOut pred pred))).
  {
    set (targetGraph := ordinalCodeGraphTermAt (tSucc raw) codedOut).
    set (C := targetGraph :: G).
    assert (htarget : BProv Ax_s C targetGraph).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hpredC : BProv Ax_s C
        (ordinalCodeGraphTermAt raw pred)).
    { exact (BProv_context_cons Ax_s G targetGraph _ hpred). }
    pose proof (hadjoin C pred pred) as hex.
    set (body := hfAdjoinGraphTermAt
      (tVar 0) (Term.rename S pred) (Term.rename S pred)).
    set (D := body :: map (rename S) C).
    assert (hinner : BProv Ax_s D
        (rename S (hfAdjoinGraphTermAt codedOut pred pred))).
    {
      assert (hadjoinD : BProv Ax_s D body).
      { apply BProv_ass. unfold D. simpl. now left. }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        C _ hpredC S) as hpredRen.
      assert (hpredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S raw) (Term.rename S pred))).
      {
        rewrite rename_ordinalCodeGraphTermAt in hpredRen.
        unfold D.
        exact (BProv_context_cons Ax_s (map (rename S) C)
          body _ hpredRen).
      }
      assert (hnew : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S raw)) (tVar 0))).
      {
        exact (hsucc D (Term.rename S raw) (Term.rename S pred)
          (tVar 0) hpredD hadjoinD).
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        C _ htarget S) as htargetRen.
      assert (htargetD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S raw))
            (Term.rename S codedOut))).
      {
        unfold targetGraph in htargetRen.
        rewrite rename_ordinalCodeGraphTermAt in htargetRen.
        cbn [Term.rename] in htargetRen.
        unfold D.
        exact (BProv_context_cons Ax_s (map (rename S) C)
          body _ htargetRen).
      }
      assert (heq : BProv Ax_s D
          (pEq (tVar 0) (Term.rename S codedOut))).
      {
        exact (hfunctional D
          (tSucc (Term.rename S raw))
          (tVar 0) (Term.rename S codedOut) hnew htargetD).
      }
      assert (htransport : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.rename S codedOut)
            (Term.rename S pred) (Term.rename S pred))).
      {
        exact (BProv_hfAdjoinGraphTermAt_congr_output
          Ax_s D (tVar 0) (Term.rename S codedOut)
          (Term.rename S pred) (Term.rename S pred)
          heq hadjoinD).
      }
      rewrite rename_hfAdjoinGraphTermAt.
      exact htransport.
    }
    assert (hresult : BProv Ax_s C
        (hfAdjoinGraphTermAt codedOut pred pred)).
    {
      unfold hfAdjoinExistsTermAt in hex.
      unfold body, D in hinner.
      exact (BProv_exE_of_sentences Ax_s C _ _
        sentence_ax_s hex hinner).
    }
    unfold C, targetGraph in hresult.
    exact (BProv_impI Ax_s G _ _ hresult).
  }
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(** Constructor-level successor compatibility after the recursive operand
    theorem has been instantiated at the fresh output slot. *)
Lemma BProv_Ax_s_term_graph_succ_of_shifted_operand_base :
  PAOrdinalCodeGraphSuccClosureProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAHFAdjoinExistence ->
  forall G t rawMap codedMap codedOut,
    BProv Ax_s (map (rename S) G)
      (iffForm
        (compositeTermGraphAt 0 (fun n => codedMap n + 1) t)
        (ordinalCodeGraphTermAt
          (Term.rename S (Term.rename rawMap t))
          (tVar 0))) ->
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap (tSucc t))
        (ordinalCodeGraphTermAt
          (Term.rename rawMap (tSucc t))
          (tVar codedOut))).
Proof.
  intros hsucc hfunctional hadjoin G t rawMap codedMap codedOut hoperand.
  set (raw := Term.rename rawMap t).
  set (composite := compositeTermGraphAt codedOut codedMap (tSucc t)).
  set (target := ordinalCodeGraphTermAt (tSucc raw) (tVar codedOut)).
  set (operandComposite :=
    compositeTermGraphAt 0 (fun n => codedMap n + 1) t).
  set (operandGraph := ordinalCodeGraphTermAt
    (Term.rename S raw) (tVar 0)).
  set (adjoinGraph := hfAdjoinGraphTermAt
    (tVar (codedOut + 1)) (tVar 0) (tVar 0)).
  set (body := pAnd operandComposite adjoinGraph).
  assert (hforward : BProv Ax_s G (pImp composite target)).
  {
    set (C := composite :: G).
    assert (hcomposite : BProv Ax_s C composite).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hex : BProv Ax_s C (pEx body)).
    {
      unfold composite in hcomposite.
      rewrite compositeTermGraphAt_succ in hcomposite.
      unfold body, operandComposite, adjoinGraph.
      exact hcomposite.
    }
    set (D := body :: map (rename S) C).
    assert (hinner : BProv Ax_s D (rename S target)).
    {
      assert (hbody : BProv Ax_s D body).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (hoperandComposite : BProv Ax_s D operandComposite).
      { unfold body in hbody. exact (BProv_andE1 Ax_s D _ _ hbody). }
      assert (hadjoinD : BProv Ax_s D adjoinGraph).
      { unfold body in hbody. exact (BProv_andE2 Ax_s D _ _ hbody). }
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        (rename S composite) _ hoperand) as hoperandCtx.
      pose proof (BProv_context_cons Ax_s
        (rename S composite :: map (rename S) G)
        body _ hoperandCtx) as hoperandCtx'.
      assert (hoperandD : BProv Ax_s D
          (iffForm operandComposite operandGraph)).
      {
        unfold D, C, raw, operandComposite, operandGraph.
        exact hoperandCtx'.
      }
      assert (hoperandForward : BProv Ax_s D
          (pImp operandComposite operandGraph)).
      { unfold iffForm in hoperandD; exact (BProv_andE1 Ax_s D _ _ hoperandD). }
      assert (hgraph : BProv Ax_s D operandGraph).
      { exact (BProv_mp Ax_s D _ _ hoperandForward hoperandComposite). }
      pose proof
        (BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ_base
          hsucc hfunctional hadjoin D
          (Term.rename S raw) (tVar 0) (tVar (codedOut + 1))
          hgraph) as hstep.
      assert (hstepForward : BProv Ax_s D
          (pImp adjoinGraph
            (ordinalCodeGraphTermAt
              (tSucc (Term.rename S raw))
              (tVar (codedOut + 1))))).
      {
        unfold iffForm in hstep.
        unfold adjoinGraph.
        exact (BProv_andE1 Ax_s D _ _ hstep).
      }
      pose proof (BProv_mp Ax_s D _ _ hstepForward hadjoinD) as hnext.
      unfold target, raw.
      rewrite rename_ordinalCodeGraphTermAt.
      cbn [Term.rename].
      replace (S codedOut) with (codedOut + 1) by lia.
      exact hnext.
    }
    assert (hresult : BProv Ax_s C target).
    {
      unfold D in hinner.
      exact (BProv_exE_of_sentences Ax_s C body target
        sentence_ax_s hex hinner).
    }
    unfold C in hresult.
    exact (BProv_impI Ax_s G composite target hresult).
  }
  assert (hreverse : BProv Ax_s G (pImp target composite)).
  {
    set (C := target :: G).
    assert (htarget : BProv Ax_s C target).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (htotal : BProv Ax_s C (pEx operandGraph)).
    {
      unfold operandGraph.
      exact ((PAOrdinalCodeGraphTotalProof_of_adjoinExistence hadjoin)
        C raw).
    }
    set (D := operandGraph :: map (rename S) C).
    assert (hinner : BProv Ax_s D (rename S composite)).
    {
      assert (hgraph : BProv Ax_s D operandGraph).
      { apply BProv_ass. unfold D. simpl. now left. }
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        (rename S target) _ hoperand) as hoperandCtx.
      pose proof (BProv_context_cons Ax_s
        (rename S target :: map (rename S) G)
        operandGraph _ hoperandCtx) as hoperandCtx'.
      assert (hoperandD : BProv Ax_s D
          (iffForm operandComposite operandGraph)).
      {
        unfold D, C, raw, operandComposite, operandGraph.
        exact hoperandCtx'.
      }
      assert (hoperandReverse : BProv Ax_s D
          (pImp operandGraph operandComposite)).
      { unfold iffForm in hoperandD; exact (BProv_andE2 Ax_s D _ _ hoperandD). }
      assert (hoperandComposite : BProv Ax_s D operandComposite).
      { exact (BProv_mp Ax_s D _ _ hoperandReverse hgraph). }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        C _ htarget S) as htargetRen.
      assert (htargetD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S raw))
            (tVar (codedOut + 1)))).
      {
        unfold target in htargetRen.
        rewrite rename_ordinalCodeGraphTermAt in htargetRen.
        cbn [Term.rename] in htargetRen.
        replace (S codedOut) with (codedOut + 1) in htargetRen by lia.
        unfold D.
        exact (BProv_context_cons Ax_s (map (rename S) C)
          operandGraph _ htargetRen).
      }
      pose proof
        (BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ_base
          hsucc hfunctional hadjoin D
          (Term.rename S raw) (tVar 0) (tVar (codedOut + 1))
          hgraph) as hstep.
      assert (hstepReverse : BProv Ax_s D
          (pImp
            (ordinalCodeGraphTermAt
              (tSucc (Term.rename S raw))
              (tVar (codedOut + 1)))
            adjoinGraph)).
      {
        unfold iffForm in hstep.
        unfold adjoinGraph.
        exact (BProv_andE2 Ax_s D _ _ hstep).
      }
      assert (hadjoinD : BProv Ax_s D adjoinGraph).
      { exact (BProv_mp Ax_s D _ _ hstepReverse htargetD). }
      assert (hbody : BProv Ax_s D body).
      {
        unfold body.
        exact (BProv_andI Ax_s D _ _ hoperandComposite hadjoinD).
      }
      unfold composite.
      rewrite compositeTermGraphAt_succ.
      apply (BProv_exI Ax_s D _ (tVar 0)).
      cbn [subst].
      rewrite !subst_instTerm_var_zero_rename_up_succ.
      unfold body, operandComposite, adjoinGraph in hbody.
      exact hbody.
    }
    assert (hresult : BProv Ax_s C composite).
    {
      unfold D in hinner.
      exact (BProv_exE_of_sentences Ax_s C operandGraph composite
        sentence_ax_s htotal hinner).
    }
    unfold C in hresult.
    exact (BProv_impI Ax_s G target composite hresult).
  }
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(** Successor preserves the complete polymorphic term-graph property. *)
Theorem PAOrdinalCodeTermSuccCompatibility_of_interfaces :
  PAOrdinalCodeGraphSuccClosureProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAHFAdjoinExistence ->
  PAOrdinalCodeTermSuccCompatibility.
Proof.
  intros hsucc hfunctional hadjoin t ih
    G rawMap codedMap codedOut hcode.
  set (rawMap1 := fun n => rawMap n + 1).
  set (codedMap1 := fun n => codedMap n + 1).
  assert (hcode1 : forall n, Term.Free n t ->
      BProv Ax_s (map (rename S) G)
        (ordinalCodeGraphAt (rawMap1 n) (codedMap1 n))).
  {
    intros n hn.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      G _ (hcode n hn) S) as hren.
    unfold ordinalCodeGraphAt in *.
    rewrite rename_ordinalCodeGraphTermAt in hren.
    cbn [Term.rename] in hren.
    unfold rawMap1, codedMap1.
    replace (S (rawMap n)) with (rawMap n + 1) in hren by lia.
    replace (S (codedMap n)) with (codedMap n + 1) in hren by lia.
    exact hren.
  }
  pose proof (ih (map (rename S) G)
    rawMap1 codedMap1 0 hcode1) as hoperand0.
  assert (hoperand : BProv Ax_s (map (rename S) G)
      (iffForm
        (compositeTermGraphAt 0 (fun n => codedMap n + 1) t)
        (ordinalCodeGraphTermAt
          (Term.rename S (Term.rename rawMap t))
          (tVar 0)))).
  {
    unfold rawMap1, codedMap1 in hoperand0.
    replace (Term.rename (fun n => rawMap n + 1) t) with
      (Term.rename S (Term.rename rawMap t)) in hoperand0.
    - exact hoperand0.
    - rewrite Term.rename_comp.
      apply Term.rename_ext.
      intro n.
      lia.
  }
  exact (BProv_Ax_s_term_graph_succ_of_shifted_operand_base
    hsucc hfunctional hadjoin
    G t rawMap codedMap codedOut hoperand).
Qed.

(** The complete zero/successor constructor kit, with exactly the three
    arithmetic interfaces still supplied by the surrounding assembly. *)
Definition PAOrdinalCodeTermBaseCompatibilityProofs_of_interfaces
    (hext : PAHFMembershipExtensionalityProof)
    (hsucc : PAOrdinalCodeGraphSuccClosureProof)
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeTermBaseCompatibilityProofs.
Proof.
  pose (hfunctional :=
    PAOrdinalCodeGraphFunctionalProof_of_extensionality hext).
  refine {| pa_term_graph_functional := hfunctional;
            pa_term_graph_zero :=
              PAOrdinalCodeTermZeroCompatibility_of_extensionality hext;
            pa_term_graph_succ := _ |}.
  exact (PAOrdinalCodeTermSuccCompatibility_of_interfaces
    hsucc hfunctional hadjoin).
Defined.

(** Convenient implication form for final certificate assembly. *)
Theorem PAOrdinalCodeTermBaseCompatibilityProofs_of_extensionality_succ_adjoin :
  PAHFMembershipExtensionalityProof ->
  PAOrdinalCodeGraphSuccClosureProof ->
  PAHFAdjoinExistence ->
  PAOrdinalCodeTermBaseCompatibilityProofs.
Proof.
  exact PAOrdinalCodeTermBaseCompatibilityProofs_of_interfaces.
Qed.
