(* ===================================================================== *)
(*  PAHFOrdinalCodeRangeArithmetic.v                                     *)
(*                                                                       *)
(*  Arithmetic certificates for the three local ordinal-code range laws. *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFOrdinalCode PAHFOrdinalCodeTotal PAHFOrdinalCodeTotalCapacity
  PAHFOrdinalCodeTotalInduction PAHFTranslatedHFFin PAHFMembershipTail
  PAHFOrdinalCodeTermCompatibility PAHFOrdinalCodeInjective
  PAHFRoundTripArithmetic PAHFRoundTripEquality PAHFRoundTripQuantifiers
  PAHFOrdinalCodeRange.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** The two elementary translated-HF domain facts needed by graph
    codomain induction. *)
Definition HF_zeroDomainSentence : form :=
  fAll (fImp (HF_emptyAt 0) (HF_ordinalLikeAt 0)).

Definition HF_domainSuccSentence : form :=
  fAll (fAll
    (fImp
      (HF_ordinalLikeAt 1)
      (fImp
        (HF_succAt 0 1)
        (HF_ordinalLikeAt 0)))).

Lemma HF_zeroDomainSentence_sentence :
  Fol.Sentence HF_zeroDomainSentence.
Proof.
  intros i hi.
  unfold HF_zeroDomainSentence, HF_emptyAt, HF_ordinalLikeAt,
    HF_transitiveAt, HF_memTotalOnAt in hi.
  simpl in hi. lia.
Qed.

Lemma HF_domainSuccSentence_sentence :
  Fol.Sentence HF_domainSuccSentence.
Proof.
  intros i hi.
  unfold HF_domainSuccSentence, HF_ordinalLikeAt,
    HF_transitiveAt, HF_memTotalOnAt, HF_succAt, HF_adjoinAt,
    fIff in hi.
  simpl in hi. lia.
Qed.

Lemma BProv_HFFin_zeroDomainSentence :
  Completeness.BProv HFFinAx_s [] HF_zeroDomainSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_zeroDomainSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros empty hempty.
    assert (hemptyEq : empty = foam_empty V M).
    {
      exact (proj1 (foam_HF_emptyAt_empty V M
        (scons V empty v) 0) hempty).
    }
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
      (scons V empty v) 0)).
    rewrite hemptyEq.
    apply foam_OrdinalLike_empty.
Qed.

Lemma BProv_HFFin_domainSuccSentence :
  Completeness.BProv HFFinAx_s [] HF_domainSuccSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_domainSuccSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros input output hinput hsucc.
    assert (hinput' : OrdinalLike (foam_mem V M) input).
    {
      exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
        (scons V output (scons V input v)) 1) hinput).
    }
    assert (hsucc' : output = foam_adjoin V M input input).
    {
      exact (proj1 (foam_HF_succAt_spec V M
        (scons V output (scons V input v)) 0 1) hsucc).
    }
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
      (scons V output (scons V input v)) 0)).
    exact (foam_OrdinalLike_adjoin_self V M input output hinput' hsucc').
Qed.

Definition zeroDomainPAFormula : formula :=
  pAll (pImp (hfEmptyTermAt (tVar 0)) codedOrdinalDomain).

Definition domainSuccPAFormula : formula :=
  pAll (pAll
    (pImp
      (rename S codedOrdinalDomain)
      (pImp
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
        codedOrdinalDomain))).

Lemma translateHFFormula_zeroDomainSentence :
  translateHFFormula HF_zeroDomainSentence = zeroDomainPAFormula.
Proof. reflexivity. Qed.

Lemma translateHFFormula_domainSuccSentence :
  translateHFFormula HF_domainSuccSentence = domainSuccPAFormula.
Proof. reflexivity. Qed.

Record PAOrdinalDomainClosureProofs : Prop := {
  pa_zero_domain : BProv Ax_s [] zeroDomainPAFormula;
  pa_domain_succ : BProv Ax_s [] domainSuccPAFormula
}.

Definition PAOrdinalDomainClosureProofs_of_translatedHFFin
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalDomainClosureProofs.
Proof.
  constructor.
  - rewrite <- translateHFFormula_zeroDomainSentence.
    apply (BProv_lift_translatedHFFinAx_to_PA
      (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
    apply BProv_translateHFFormula_of_BProv_HFFin.
    exact BProv_HFFin_zeroDomainSentence.
  - rewrite <- translateHFFormula_domainSuccSentence.
    apply (BProv_lift_translatedHFFinAx_to_PA
      (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
    apply BProv_translateHFFormula_of_BProv_HFFin.
    exact BProv_HFFin_domainSuccSentence.
Defined.

Lemma BProv_Ax_s_codedOrdinalDomain_zero : forall
    D : PAOrdinalDomainClosureProofs,
  BProv Ax_s [] (subst (instTerm tZero) codedOrdinalDomain).
Proof.
  intro D.
  pose proof (BProv_allE Ax_s [] _ tZero (pa_zero_domain D)) as hraw.
  assert (himp : BProv Ax_s []
      (pImp
        (hfEmptyTermAt tZero)
        (subst (instTerm tZero) codedOrdinalDomain))).
  {
    unfold zeroDomainPAFormula in hraw.
    cbn [subst] in hraw.
    rewrite subst_hfEmptyTermAt in hraw.
    simpl in hraw.
    exact hraw.
  }
  exact (BProv_mp Ax_s [] _ _ himp BProv_Ax_s_hfEmptyTermAt_zero).
Qed.

Lemma BProv_Ax_s_codedOrdinalDomain_adjoin_self : forall
    (D : PAOrdinalDomainClosureProofs) G pred current,
  BProv Ax_s G (subst (instTerm pred) codedOrdinalDomain) ->
  BProv Ax_s G (hfAdjoinGraphTermAt current pred pred) ->
  BProv Ax_s G (subst (instTerm current) codedOrdinalDomain).
Proof.
  intros D G pred current hpred hadjoin.
  assert (hall : BProv Ax_s G domainSuccPAFormula).
  { exact (BProv_weaken_nil Ax_s G _ (pa_domain_succ D)). }
  pose proof (BProv_allE Ax_s G _ pred hall) as hpredRaw.
  pose proof (BProv_allE Ax_s G _ current hpredRaw) as hcurrentRaw.
  assert (hpredNorm :
      subst (instTerm current)
        (subst (Term.upSubst (instTerm pred))
          (rename S codedOrdinalDomain)) =
      subst (instTerm pred) codedOrdinalDomain).
  {
    rewrite subst_rename_succ_up.
    rewrite subst_instTerm_rename_succ.
    reflexivity.
  }
  assert (hcurrentNorm :
      subst (instTerm current)
        (subst (Term.upSubst (instTerm pred)) codedOrdinalDomain) =
      subst (instTerm current) codedOrdinalDomain).
  { rewrite subst_up_inst_codedOrdinalDomain. reflexivity. }
  assert (himp : BProv Ax_s G
      (pImp
        (subst (instTerm pred) codedOrdinalDomain)
        (pImp
          (hfAdjoinGraphTermAt current pred pred)
          (subst (instTerm current) codedOrdinalDomain)))).
  {
    unfold domainSuccPAFormula in hcurrentRaw.
    cbn [subst] in hcurrentRaw.
    rewrite subst_hfAdjoinGraphTermAt in hcurrentRaw.
    rewrite hpredNorm, hcurrentNorm in hcurrentRaw.
    repeat rewrite Term.subst_rename_succ_up in hcurrentRaw.
    repeat rewrite term_subst_instTerm_rename_succ in hcurrentRaw.
    cbn [instTerm Term.subst Term.upSubst] in hcurrentRaw.
    rewrite subst_hfAdjoinGraphTermAt in hcurrentRaw.
    repeat rewrite Term.subst_rename_succ_up in hcurrentRaw.
    repeat rewrite term_subst_instTerm_rename_succ in hcurrentRaw.
    exact hcurrentRaw.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hpred) hadjoin).
Qed.

(** Every graph endpoint at a fixed raw input is in the coded ordinal
    domain. *)
Definition ordinalCodeCodomainTermAt (raw : term) : formula :=
  pAll
    (pImp
      (ordinalCodeGraphTermAt (Term.rename S raw) (tVar 0))
      codedOrdinalDomain).

Lemma subst_ordinalCodeCodomainTermAt : forall sigma raw,
  subst sigma (ordinalCodeCodomainTermAt raw) =
    ordinalCodeCodomainTermAt (Term.subst sigma raw).
Proof.
  intros sigma raw.
  assert (hdomain :
      subst (Term.upSubst sigma) codedOrdinalDomain =
      codedOrdinalDomain).
  {
    transitivity (subst (fun n => tVar n) codedOrdinalDomain).
    - apply subst_ext_free.
      intros n hn.
      pose proof (codedOrdinalDomain_free n hn) as hn0.
      subst n. reflexivity.
    - apply subst_id.
  }
  unfold ordinalCodeCodomainTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  rewrite Term.subst_rename_succ_up.
  rewrite hdomain.
  reflexivity.
Qed.

Lemma rename_ordinalCodeCodomainTermAt : forall r raw,
  rename r (ordinalCodeCodomainTermAt raw) =
    ordinalCodeCodomainTermAt (Term.rename r raw).
Proof.
  intros r raw.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeCodomainTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_Ax_s_ordinalCodeCodomainTermAt_zero : forall
    (D : PAOrdinalDomainClosureProofs) G,
  BProv Ax_s G (ordinalCodeCodomainTermAt tZero).
Proof.
  intros D G.
  set (graph := ordinalCodeGraphTermAt tZero (tVar 0)).
  set (Q := map (rename S) G).
  set (C := graph :: Q).
  assert (hbody : BProv Ax_s Q (pImp graph codedOrdinalDomain)).
  {
    assert (hgraph : BProv Ax_s C graph).
    { apply BProv_ass. unfold C. simpl. now left. }
    pose proof (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
      C (tVar 0) hgraph) as heq.
    assert (hdomainZero : BProv Ax_s C
        (subst (instTerm tZero) codedOrdinalDomain)).
    {
      exact (BProv_weaken_nil Ax_s C _
        (BProv_Ax_s_codedOrdinalDomain_zero D)).
    }
    pose proof (BProv_eqElim Ax_s C tZero (tVar 0)
      codedOrdinalDomain (BProv_eqSym Ax_s C _ _ heq)
      hdomainZero) as hdomainRaw.
    assert (hdomain : BProv Ax_s C codedOrdinalDomain).
    {
      rewrite subst_instTerm_var_zero_codedOrdinalDomain in hdomainRaw.
      exact hdomainRaw.
    }
    unfold C in hdomain.
    exact (BProv_impI Ax_s Q graph codedOrdinalDomain hdomain).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _ sentence_ax_s hbody)
    as hall.
  unfold ordinalCodeCodomainTermAt, graph, Q.
  simpl in hall.
  exact hall.
Qed.

Lemma subst_instTerm_var_one_codedOrdinalDomain :
  subst (instTerm (tVar 1)) codedOrdinalDomain =
    rename S codedOrdinalDomain.
Proof.
  rewrite subst_instTerm_var.
  apply rename_ext_free.
  intros n hn.
  pose proof (codedOrdinalDomain_free n hn) as hn0.
  subst n. reflexivity.
Qed.

Lemma BProv_Ax_s_ordinalCodeCodomainTermAt_succ : forall
    (D0 : PAOrdinalDomainClosureProofs) G raw,
  BProv Ax_s G (ordinalCodeCodomainTermAt raw) ->
  BProv Ax_s G (ordinalCodeCodomainTermAt (tSucc raw)).
Proof.
  intros D0 G raw hih.
  set (raw1 := Term.rename S raw).
  set (graph := ordinalCodeGraphTermAt (tSucc raw1) (tVar 0)).
  set (Q := map (rename S) G).
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hih S) as hihRaw.
  assert (hihQ : BProv Ax_s Q (ordinalCodeCodomainTermAt raw1)).
  {
    unfold Q, raw1.
    rewrite rename_ordinalCodeCodomainTermAt in hihRaw.
    exact hihRaw.
  }
  set (C := graph :: Q).
  assert (hbody : BProv Ax_s Q (pImp graph codedOrdinalDomain)).
  {
    assert (hgraph : BProv Ax_s C graph).
    { apply BProv_ass. unfold C. simpl. now left. }
    pose proof (BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
      C raw1 (tVar 0) hgraph) as hedge.
    set (raw2 := Term.rename S raw1).
    set (edgeBody :=
      pAnd
        (ordinalCodeGraphTermAt raw2 (tVar 0))
        (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))).
    set (E := edgeBody :: map (rename S) C).
    assert (hopened : BProv Ax_s E (rename S codedOrdinalDomain)).
    {
      assert (hedgeBody : BProv Ax_s E edgeBody).
      { apply BProv_ass. unfold E. simpl. now left. }
      assert (hpred : BProv Ax_s E
          (ordinalCodeGraphTermAt raw2 (tVar 0))).
      { unfold edgeBody in hedgeBody; exact (BProv_andE1 Ax_s E _ _ hedgeBody). }
      assert (hadjoin : BProv Ax_s E
          (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))).
      { unfold edgeBody in hedgeBody; exact (BProv_andE2 Ax_s E _ _ hedgeBody). }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s Q _
        hihQ S) as hihRen.
      pose proof (BProv_context_cons Ax_s (map (rename S) Q)
        (rename S graph) _ hihRen) as hgraphCtx.
      pose proof (BProv_context_cons Ax_s
        (rename S graph :: map (rename S) Q)
        edgeBody _ hgraphCtx) as hihE0.
      assert (hihE : BProv Ax_s E (ordinalCodeCodomainTermAt raw2)).
      {
        unfold E, C, raw1, raw2.
        rewrite rename_ordinalCodeCodomainTermAt in hihE0.
        exact hihE0.
      }
      pose proof (BProv_allE Ax_s E _ (tVar 0) hihE) as himpRaw.
      assert (himp : BProv Ax_s E
          (pImp
            (ordinalCodeGraphTermAt raw2 (tVar 0))
            codedOrdinalDomain)).
      {
        unfold ordinalCodeCodomainTermAt in himpRaw.
        cbn [subst] in himpRaw.
        rewrite subst_ordinalCodeGraphTermAt in himpRaw.
        rewrite subst_instTerm_var_zero_codedOrdinalDomain in himpRaw.
        simpl in himpRaw.
        repeat rewrite term_subst_instTerm_rename_succ in himpRaw.
        exact himpRaw.
      }
      assert (hpredDomain : BProv Ax_s E codedOrdinalDomain).
      { exact (BProv_mp Ax_s E _ _ himp hpred). }
      assert (hpredDomainInst : BProv Ax_s E
          (subst (instTerm (tVar 0)) codedOrdinalDomain)).
      {
        rewrite subst_instTerm_var_zero_codedOrdinalDomain.
        exact hpredDomain.
      }
      pose proof (BProv_Ax_s_codedOrdinalDomain_adjoin_self
        D0 E (tVar 0) (tVar 1)
        hpredDomainInst
        hadjoin) as hcurrentDomain.
      rewrite subst_instTerm_var_one_codedOrdinalDomain in hcurrentDomain.
      exact hcurrentDomain.
    }
    assert (hdomain : BProv Ax_s C codedOrdinalDomain).
    {
      apply (BProv_exE_of_sentences Ax_s C edgeBody codedOrdinalDomain
        sentence_ax_s).
      - unfold ordinalCodePredEdgeTermAt in hedge.
        unfold edgeBody, raw2.
        exact hedge.
      - unfold E in hopened. exact hopened.
    }
    unfold C in hdomain.
    exact (BProv_impI Ax_s Q graph codedOrdinalDomain hdomain).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _ sentence_ax_s hbody)
    as hall.
  unfold ordinalCodeCodomainTermAt, graph, raw1.
  simpl in hall.
  exact hall.
Qed.

Lemma BProv_Ax_s_all_ordinalCodeCodomain : forall
    D : PAOrdinalDomainClosureProofs,
  BProv Ax_s [] (pAll (ordinalCodeCodomainTermAt (tVar 0))).
Proof.
  intro D.
  set (phi := ordinalCodeCodomainTermAt (tVar 0)).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    pose proof (BProv_Ax_s_ordinalCodeCodomainTermAt_zero D []) as hbase.
    unfold phi.
    rewrite subst_ordinalCodeCodomainTermAt.
    simpl. exact hbase.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  {
    set (C := [phi]).
    assert (hih : BProv Ax_s C phi).
    { apply BProv_ass. unfold C. simpl. now left. }
    pose proof (BProv_Ax_s_ordinalCodeCodomainTermAt_succ
      D C (tVar 0) hih) as hnext.
    assert (hnextSub : BProv Ax_s C (subst substSuccVar phi)).
    {
      unfold phi.
      rewrite subst_ordinalCodeCodomainTermAt.
      simpl. exact hnext.
    }
    unfold C in hnextSub.
    exact (BProv_impI Ax_s [] phi _ hnextSub).
  }
  assert (hsucc : BProv Ax_s []
      (pAll (pImp phi (subst substSuccVar phi)))).
  { exact (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s hsuccImp). }
  unfold phi.
  exact (BProv_Ax_s_induction_rule []
    (ordinalCodeCodomainTermAt (tVar 0)) hzero hsucc).
Qed.

Lemma rename_subst_instTerm_codedOrdinalDomain : forall coded,
  rename S (subst (instTerm coded) codedOrdinalDomain) =
    subst (instTerm (Term.rename S coded)) codedOrdinalDomain.
Proof.
  intro coded.
  rewrite rename_subst.
  apply subst_ext_free.
  intros n hn.
  pose proof (codedOrdinalDomain_free n hn) as hn0.
  subst n. reflexivity.
Qed.

Definition PAOrdinalCodeGraphCodomainProof_of_domainClosure
    (D : PAOrdinalDomainClosureProofs) :
  PAOrdinalCodeGraphCodomainProof.
Proof.
  intros G coded hrange.
  set (graph := ordinalCodeGraphTermAt
    (tVar 0) (Term.rename S coded)).
  set (C := graph :: map (rename S) G).
  assert (hinner : BProv Ax_s C
      (rename S (subst (instTerm coded) codedOrdinalDomain))).
  {
    assert (hall : BProv Ax_s C
        (pAll (ordinalCodeCodomainTermAt (tVar 0)))).
    { exact (BProv_weaken_nil Ax_s C _ (BProv_Ax_s_all_ordinalCodeCodomain D)). }
    pose proof (BProv_allE Ax_s C _ (tVar 0) hall) as hrawPoint.
    assert (hpoint : BProv Ax_s C
        (ordinalCodeCodomainTermAt (tVar 0))).
    {
      rewrite subst_ordinalCodeCodomainTermAt in hrawPoint.
      simpl in hrawPoint. exact hrawPoint.
    }
    pose proof (BProv_allE Ax_s C _ (Term.rename S coded) hpoint)
      as himpRaw.
    assert (himp : BProv Ax_s C
        (pImp graph
          (subst (instTerm (Term.rename S coded))
            codedOrdinalDomain))).
    {
      unfold ordinalCodeCodomainTermAt in himpRaw.
      cbn [subst] in himpRaw.
      rewrite subst_ordinalCodeGraphTermAt in himpRaw.
      simpl in himpRaw.
      repeat rewrite term_subst_instTerm_rename_succ in himpRaw.
      unfold graph. exact himpRaw.
    }
    assert (hgraph : BProv Ax_s C graph).
    { apply BProv_ass. unfold C. simpl. now left. }
    pose proof (BProv_mp Ax_s C _ _ himp hgraph) as hdomain.
    rewrite rename_subst_instTerm_codedOrdinalDomain.
    exact hdomain.
  }
  apply (BProv_exE_of_sentences Ax_s G graph
    (subst (instTerm coded) codedOrdinalDomain) sentence_ax_s).
  - unfold ordinalCodeGraphRangeExistsTermAt in hrange.
    unfold graph. exact hrange.
  - unfold C in hinner. exact hinner.
Defined.

Definition PAOrdinalCodeGraphCodomainProof_of_TranslatedHFFinAxiomProofs
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalCodeGraphCodomainProof :=
  PAOrdinalCodeGraphCodomainProof_of_domainClosure
    (PAOrdinalDomainClosureProofs_of_translatedHFFin P).

(** The exact Ackermann-adjoin output functionality used by graph successor
    closure. *)
Definition PAHFAdjoinOutputFunctionalProof : Prop :=
  forall G new1 new2 oldCode elemCode,
    BProv Ax_s G (hfAdjoinGraphTermAt new1 oldCode elemCode) ->
    BProv Ax_s G (hfAdjoinGraphTermAt new2 oldCode elemCode) ->
    BProv Ax_s G (pEq new1 new2).

Lemma BProv_hfAdjoinGraphTermAt_congr_old : forall
    (B : formula -> Prop) G newCode old1 old2 elemCode,
  BProv B G (pEq old1 old2) ->
  BProv B G (hfAdjoinGraphTermAt newCode old1 elemCode) ->
  BProv B G (hfAdjoinGraphTermAt newCode old2 elemCode).
Proof.
  intros B G newCode old1 old2 elemCode heq hgraph.
  set (context := hfAdjoinGraphTermAt
    (Term.rename S newCode) (tVar 0) (Term.rename S elemCode)).
  assert (hinst : BProv B G (subst (instTerm old1) context)).
  {
    unfold context.
    rewrite subst_hfAdjoinGraphTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hgraph.
  }
  pose proof (BProv_eqElim B G old1 old2 context heq hinst) as hout.
  unfold context in hout.
  rewrite subst_hfAdjoinGraphTermAt in hout.
  simpl in hout.
  repeat rewrite term_subst_instTerm_rename_succ in hout.
  exact hout.
Qed.

Lemma BProv_hfAdjoinGraphTermAt_congr_elem : forall
    (B : formula -> Prop) G newCode oldCode elem1 elem2,
  BProv B G (pEq elem1 elem2) ->
  BProv B G (hfAdjoinGraphTermAt newCode oldCode elem1) ->
  BProv B G (hfAdjoinGraphTermAt newCode oldCode elem2).
Proof.
  intros B G newCode oldCode elem1 elem2 heq hgraph.
  set (context := hfAdjoinGraphTermAt
    (Term.rename S newCode) (Term.rename S oldCode) (tVar 0)).
  assert (hinst : BProv B G (subst (instTerm elem1) context)).
  {
    unfold context.
    rewrite subst_hfAdjoinGraphTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hgraph.
  }
  pose proof (BProv_eqElim B G elem1 elem2 context heq hinst) as hout.
  unfold context in hout.
  rewrite subst_hfAdjoinGraphTermAt in hout.
  simpl in hout.
  repeat rewrite term_subst_instTerm_rename_succ in hout.
  exact hout.
Qed.

Lemma BProv_Ax_s_hfAdjoinGraphTermAt_congr_inputs : forall
    G newCode old1 old2 elem1 elem2,
  BProv Ax_s G (pEq old1 old2) ->
  BProv Ax_s G (pEq elem1 elem2) ->
  BProv Ax_s G (hfAdjoinGraphTermAt newCode old1 elem1) ->
  BProv Ax_s G (hfAdjoinGraphTermAt newCode old2 elem2).
Proof.
  intros G newCode old1 old2 elem1 elem2 hold helem hgraph.
  apply (BProv_hfAdjoinGraphTermAt_congr_elem
    Ax_s G newCode old2 elem1 elem2 helem).
  exact (BProv_hfAdjoinGraphTermAt_congr_old
    Ax_s G newCode old1 old2 elem1 hold hgraph).
Qed.

(** Totality plus the two output-functionality laws force the independently
    selected successor graph endpoint to be the supplied Ackermann adjoin. *)
Definition PAOrdinalCodeGraphSuccClosureProof_of_functionality
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hgraphFunctional : PAOrdinalCodeGraphFunctionalProof)
    (hadjoinFunctional : PAHFAdjoinOutputFunctionalProof) :
  PAOrdinalCodeGraphSuccClosureProof.
Proof.
  intros G raw pred current hpred hadjoin.
  set (target := ordinalCodeGraphTermAt (tSucc raw) current).
  set (outGraph := ordinalCodeGraphTermAt
    (tSucc (Term.rename S raw)) (tVar 0)).
  assert (htotalEx : BProv Ax_s G (pEx outGraph)).
  {
    unfold outGraph.
    exact (htotal G (tSucc raw)).
  }
  set (C := outGraph :: map (rename S) G).
  assert (hinner : BProv Ax_s C (rename S target)).
  {
    assert (hout : BProv Ax_s C outGraph).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (raw1 := Term.rename S raw).
    pose proof (BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
      C raw1 (tVar 0) hout) as hedge.
    set (raw2 := Term.rename S raw1).
    set (pred2 := Term.rename (fun n => n + 2) pred).
    set (current2 := Term.rename (fun n => n + 2) current).
    set (edgeBody :=
      pAnd
        (ordinalCodeGraphTermAt raw2 (tVar 0))
        (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))).
    set (E := edgeBody :: map (rename S) C).
    assert (hopened : BProv Ax_s E
        (rename S (rename S target))).
    {
      assert (hedgeBody : BProv Ax_s E edgeBody).
      { apply BProv_ass. unfold E. simpl. now left. }
      assert (hedgePred : BProv Ax_s E
          (ordinalCodeGraphTermAt raw2 (tVar 0))).
      { unfold edgeBody in hedgeBody; exact (BProv_andE1 Ax_s E _ _ hedgeBody). }
      assert (hedgeAdjoin : BProv Ax_s E
          (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))).
      { unfold edgeBody in hedgeBody; exact (BProv_andE2 Ax_s E _ _ hedgeBody). }
      assert (lift2 : forall phi,
          BProv Ax_s G phi -> BProv Ax_s E (rename S (rename S phi))).
      {
        intros phi hphi.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
          hphi S) as hren1.
        pose proof (BProv_context_cons Ax_s (map (rename S) G)
          outGraph _ hren1) as houtCtx.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s C _
          houtCtx S) as hren2.
        pose proof (BProv_context_cons Ax_s (map (rename S) C)
          edgeBody _ hren2) as hedgeCtx.
        unfold E, C. exact hedgeCtx.
      }
      pose proof (lift2 _ hpred) as hpredRaw.
      assert (hpredE : BProv Ax_s E
          (ordinalCodeGraphTermAt raw2 pred2)).
      {
        rewrite !rename_ordinalCodeGraphTermAt in hpredRaw.
        unfold raw2, raw1, pred2.
        cbn [Term.rename] in hpredRaw.
        repeat rewrite Term.rename_comp in hpredRaw.
        replace (fun x : nat => S (S x)) with
          (fun x => x + 2) in hpredRaw
          by (apply functional_extensionality; intro x; lia).
        rewrite Term.rename_comp.
        replace (fun x : nat => S (S x)) with
          (fun x => x + 2)
          by (apply functional_extensionality; intro x; lia).
        exact hpredRaw.
      }
      pose proof (lift2 _ hadjoin) as hadjoinRaw.
      assert (hadjoinE : BProv Ax_s E
          (hfAdjoinGraphTermAt current2 pred2 pred2)).
      {
        rewrite !rename_hfAdjoinGraphTermAt in hadjoinRaw.
        unfold pred2, current2.
        cbn [Term.rename] in hadjoinRaw.
        repeat rewrite Term.rename_comp in hadjoinRaw.
        replace (fun x : nat => S (S x)) with
          (fun x => x + 2) in hadjoinRaw
          by (apply functional_extensionality; intro x; lia).
        exact hadjoinRaw.
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s C _
        hout S) as houtRen.
      pose proof (BProv_context_cons Ax_s (map (rename S) C)
        edgeBody _ houtRen) as houtE0.
      assert (houtE : BProv Ax_s E
          (ordinalCodeGraphTermAt (tSucc raw2) (tVar 1))).
      {
        unfold raw2.
        change (BProv Ax_s E
          (ordinalCodeGraphTermAt
            (Term.rename S (tSucc raw1))
            (Term.rename S (tVar 0)))).
        rewrite <- (rename_ordinalCodeGraphTermAt S
          (tSucc raw1) (tVar 0)).
        change (BProv Ax_s E (rename S outGraph)) in houtE0.
        exact houtE0.
      }
      assert (hpredEq : BProv Ax_s E (pEq pred2 (tVar 0))).
      {
        exact (hgraphFunctional E raw2 pred2 (tVar 0)
          hpredE hedgePred).
      }
      assert (hedgeAdjoin' : BProv Ax_s E
          (hfAdjoinGraphTermAt (tVar 1) pred2 pred2)).
      {
        exact (BProv_Ax_s_hfAdjoinGraphTermAt_congr_inputs
          E (tVar 1) (tVar 0) pred2 (tVar 0) pred2
          (BProv_eqSym Ax_s E _ _ hpredEq)
          (BProv_eqSym Ax_s E _ _ hpredEq) hedgeAdjoin).
      }
      assert (houtEq : BProv Ax_s E (pEq (tVar 1) current2)).
      {
        exact (hadjoinFunctional E (tVar 1) current2 pred2 pred2
          hedgeAdjoin' hadjoinE).
      }
      assert (hresult : BProv Ax_s E
          (ordinalCodeGraphTermAt (tSucc raw2) current2)).
      {
        exact (BProv_ordinalCodeGraphTermAt_congr_coded
          Ax_s E (tSucc raw2) (tVar 1) current2 houtEq houtE).
      }
      unfold target.
      rewrite !rename_ordinalCodeGraphTermAt.
      unfold raw2, raw1, current2.
      cbn [rename Term.rename].
      repeat rewrite Term.rename_comp.
      replace (fun x : nat => S (S x)) with
        (fun x => x + 2)
        by (apply functional_extensionality; intro x; lia).
      unfold raw2, raw1, current2 in hresult.
      rewrite Term.rename_comp in hresult.
      replace (fun x : nat => S (S x)) with
        (fun x => x + 2) in hresult
        by (apply functional_extensionality; intro x; lia).
      exact hresult.
    }
    apply (BProv_exE_of_sentences Ax_s C edgeBody (rename S target)
      sentence_ax_s).
    - unfold ordinalCodePredEdgeTermAt in hedge.
      unfold edgeBody, raw2.
      exact hedge.
    - unfold E in hopened. exact hopened.
  }
  apply (BProv_exE_of_sentences Ax_s G outGraph target
    sentence_ax_s htotalEx).
  unfold C in hinner. exact hinner.
Defined.

(** HFFin finite-ordinal predecessor decomposition. *)
Definition HF_ordinalCodeZeroCase : form :=
  fAll (fImp (HF_emptyAt 0) (fEq 1 0)).

Definition HF_ordinalCodeSuccBody : form :=
  fAnd (HF_ordinalLikeAt 0)
    (fAnd (fMem 0 1) (HF_succAt 1 0)).

Definition HF_ordinalCodeZeroOrSuccPoint : form :=
  fImp (HF_ordinalLikeAt 0)
    (fOr HF_ordinalCodeZeroCase (fEx HF_ordinalCodeSuccBody)).

Definition HF_ordinalCodeZeroOrSuccSentence : form :=
  fAll HF_ordinalCodeZeroOrSuccPoint.

Lemma HF_ordinalCodeZeroOrSuccSentence_sentence :
  Fol.Sentence HF_ordinalCodeZeroOrSuccSentence.
Proof.
  intros i hi.
  unfold HF_ordinalCodeZeroOrSuccSentence,
    HF_ordinalCodeZeroOrSuccPoint, HF_ordinalCodeZeroCase,
    HF_ordinalCodeSuccBody, HF_ordinalLikeAt, HF_transitiveAt,
    HF_memTotalOnAt, HF_emptyAt, HF_succAt, HF_adjoinAt,
    fIff in hi.
  simpl in hi. lia.
Qed.

Lemma BProv_HFFin_ordinalCodeZeroOrSuccSentence :
  Completeness.BProv HFFinAx_s [] HF_ordinalCodeZeroOrSuccSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_ordinalCodeZeroOrSuccSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros current hcurrent.
    assert (hordinal : OrdinalLike (foam_mem V M) current).
    {
      exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
        (scons V current v) 0) hcurrent).
    }
    destruct (fofam_OrdinalLike_empty_or_succ V M current hordinal)
      as [hempty | [pred [hpredMem hsucc]]].
    + left. intros empty hemptySat.
      assert (hemptyEq : empty = foam_empty V M).
      {
        exact (proj1 (foam_HF_emptyAt_empty V M
          (scons V empty (scons V current v)) 0) hemptySat).
      }
      rewrite hempty, hemptyEq. reflexivity.
    + right. exists pred.
      split.
      * apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V pred (scons V current v)) 0)).
        exact (OrdinalLike_of_mem V (foam_mem V M)
          current pred hordinal hpredMem).
      * split.
        -- exact hpredMem.
        -- apply (proj2 (foam_HF_succAt_spec V M
             (scons V pred (scons V current v)) 1 0)).
           exact hsucc.
Qed.

Definition ordinalCodeZeroCaseTermAt (current : term) : formula :=
  pAll (pImp
    (hfEmptyTermAt (tVar 0))
    (pEq (Term.rename S current) (tVar 0))).

Definition ordinalCodeMemSuccBodyTermAt (current : term) : formula :=
  pAnd codedOrdinalDomain
    (pAnd
      (hfMemTermAt 0 (Term.rename S current))
      (hfAdjoinGraphTermAt
        (Term.rename S current) (tVar 0) (tVar 0))).

Definition ordinalCodeMemZeroOrSuccTermAt (current : term) : formula :=
  pOr (ordinalCodeZeroCaseTermAt current)
    (pEx (ordinalCodeMemSuccBodyTermAt current)).

Definition ordinalCodeMemZeroOrSuccPoint : formula :=
  pImp codedOrdinalDomain
    (ordinalCodeMemZeroOrSuccTermAt (tVar 0)).

Lemma translateHFFormula_ordinalCodeZeroOrSuccSentence :
  translateHFFormula HF_ordinalCodeZeroOrSuccSentence =
    pAll ordinalCodeMemZeroOrSuccPoint.
Proof. reflexivity. Qed.

Lemma BProv_Ax_s_ordinalCodeMemZeroOrSuccSentence : forall
    P : TranslatedHFFinAxiomProofs,
  BProv Ax_s [] (pAll ordinalCodeMemZeroOrSuccPoint).
Proof.
  intro P.
  rewrite <- translateHFFormula_ordinalCodeZeroOrSuccSentence.
  apply (BProv_lift_translatedHFFinAx_to_PA
    (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
  apply BProv_translateHFFormula_of_BProv_HFFin.
  exact BProv_HFFin_ordinalCodeZeroOrSuccSentence.
Qed.

Lemma subst_up_inst_hfMemAt_zero_one : forall current,
  subst (Term.upSubst (instTerm current)) (hfMemAt 0 1) =
    hfMemTermAt 0 (Term.rename S current).
Proof.
  intro current.
  change (subst (Term.upSubst (instTerm current))
    (hfMemTermAt 0 (Term.rename S (tVar 0))) =
    hfMemTermAt 0 (Term.rename S current)).
  rewrite subst_up_hfMemTermAt_zero_rename_succ.
  simpl. reflexivity.
Qed.

Lemma subst_instTerm_ordinalCodeMemZeroOrSuccPoint : forall current,
  subst (instTerm current) ordinalCodeMemZeroOrSuccPoint =
    pImp
      (subst (instTerm current) codedOrdinalDomain)
      (ordinalCodeMemZeroOrSuccTermAt current).
Proof.
  intro current.
  unfold ordinalCodeMemZeroOrSuccPoint,
    ordinalCodeMemZeroOrSuccTermAt,
    ordinalCodeZeroCaseTermAt,
    ordinalCodeMemSuccBodyTermAt.
  cbn [subst].
  rewrite subst_hfEmptyTermAt.
  rewrite subst_up_inst_codedOrdinalDomain.
  rewrite subst_up_inst_hfMemAt_zero_one.
  rewrite subst_hfAdjoinGraphTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  repeat rewrite term_subst_instTerm_rename_succ.
  cbn [instTerm Term.subst Term.upSubst].
  repeat rewrite term_subst_instTerm_rename_succ.
  reflexivity.
Qed.

Lemma BProv_Ax_s_ordinalCodeMemZeroOrSuccTermAt_of_domain : forall
    (P : TranslatedHFFinAxiomProofs) G current,
  BProv Ax_s G (subst (instTerm current) codedOrdinalDomain) ->
  BProv Ax_s G (ordinalCodeMemZeroOrSuccTermAt current).
Proof.
  intros P G current hdomain.
  assert (hall : BProv Ax_s G (pAll ordinalCodeMemZeroOrSuccPoint)).
  {
    exact (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_ordinalCodeMemZeroOrSuccSentence P)).
  }
  pose proof (BProv_allE Ax_s G _ current hall) as hpointRaw.
  rewrite subst_instTerm_ordinalCodeMemZeroOrSuccPoint in hpointRaw.
  exact (BProv_mp Ax_s G _ _ hpointRaw hdomain).
Qed.

Lemma BProv_Ax_s_ltAt_of_hfMemAt : forall G elem set,
  BProv Ax_s G (hfMemAt elem set) ->
  BProv Ax_s G (ltAt elem set).
Proof.
  intros G elem set hmem.
  exact (BProv_Ax_s_ltAt_of_hfMemAt_of_all
    BProv_Ax_s_all_hfMembersBelowAt G elem set hmem).
Qed.

Lemma rename_up_succ_codedOrdinalDomain :
  rename (up S) codedOrdinalDomain = codedOrdinalDomain.
Proof.
  transitivity (rename (fun n : nat => n) codedOrdinalDomain).
  - apply rename_ext_free. intros n hn.
    pose proof (codedOrdinalDomain_free n hn) as hn0.
    subst n. reflexivity.
  - apply rename_id.
Qed.

Lemma BProv_Ax_s_ordinalCodeDomainZeroOrSuccAt_of_domain : forall
    (P : TranslatedHFFinAxiomProofs) G,
  BProv Ax_s G codedOrdinalDomain ->
  BProv Ax_s G
    (ordinalCodeDomainZeroOrSuccTermAt (tVar 0)).
Proof.
  intros P G hdomain.
  pose proof (BProv_Ax_s_ordinalCodeMemZeroOrSuccTermAt_of_domain
    P G (tVar 0)) as hcases0.
  assert (hdomainInst : BProv Ax_s G
      (subst (instTerm (tVar 0)) codedOrdinalDomain)).
  { rewrite subst_instTerm_var_zero_codedOrdinalDomain. exact hdomain. }
  specialize (hcases0 hdomainInst).
  set (zeroCase := ordinalCodeZeroCaseTermAt (tVar 0)).
  set (succBody := ordinalCodeMemSuccBodyTermAt (tVar 0)).
  set (succCase := pEx succBody).
  assert (hzero : BProv Ax_s (zeroCase :: G)
      (ordinalCodeDomainZeroOrSuccTermAt (tVar 0))).
  {
    set (Z := zeroCase :: G).
    assert (hall : BProv Ax_s Z zeroCase).
    { apply BProv_ass. unfold Z. simpl. now left. }
    pose proof (BProv_allE Ax_s Z _ tZero hall) as himpRaw.
    assert (himp : BProv Ax_s Z
        (pImp (hfEmptyTermAt tZero)
          (pEq (tVar 0) tZero))).
    {
      unfold zeroCase, ordinalCodeZeroCaseTermAt in himpRaw.
      cbn [subst] in himpRaw.
      rewrite subst_hfEmptyTermAt in himpRaw.
      simpl in himpRaw.
      exact himpRaw.
    }
    assert (hempty : BProv Ax_s Z (hfEmptyTermAt tZero)).
    { exact (BProv_weaken_nil Ax_s Z _ BProv_Ax_s_hfEmptyTermAt_zero). }
    pose proof (BProv_mp Ax_s Z _ _ himp hempty) as heq.
    unfold ordinalCodeDomainZeroOrSuccTermAt.
    exact (BProv_orI1 Ax_s Z _ _ heq).
  }
  set (Sctx := succCase :: G).
  assert (hsucc : BProv Ax_s Sctx
      (ordinalCodeDomainZeroOrSuccTermAt (tVar 0))).
  {
    assert (hex : BProv Ax_s Sctx (pEx succBody)).
    { apply BProv_ass. unfold Sctx, succCase. simpl. now left. }
    set (C := succBody :: map (rename S) Sctx).
    assert (hinner : BProv Ax_s C
        (rename S
          (ordinalCodeDomainZeroOrSuccTermAt (tVar 0)))).
    {
      assert (hbody : BProv Ax_s C succBody).
      { apply BProv_ass. unfold C. simpl. now left. }
      assert (hpredDomain : BProv Ax_s C codedOrdinalDomain).
      {
        unfold succBody, ordinalCodeMemSuccBodyTermAt in hbody.
        exact (BProv_andE1 Ax_s C _ _ hbody).
      }
      pose proof (BProv_andE2 Ax_s C _ _ hbody) as hrest.
      assert (hmem : BProv Ax_s C (hfMemAt 0 1)).
      {
        unfold succBody, ordinalCodeMemSuccBodyTermAt in hrest.
        change (BProv Ax_s C
          (pAnd (hfMemAt 0 1)
            (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0)))) in hrest.
        exact (BProv_andE1 Ax_s C _ _ hrest).
      }
      assert (hadjoin : BProv Ax_s C
          (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))).
      {
        unfold succBody, ordinalCodeMemSuccBodyTermAt in hrest.
        change (BProv Ax_s C
          (pAnd (hfMemAt 0 1)
            (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0)))) in hrest.
        exact (BProv_andE2 Ax_s C _ _ hrest).
      }
      pose proof (BProv_Ax_s_ltAt_of_hfMemAt C 0 1 hmem) as hlt.
      assert (hprod : BProv Ax_s C
          (ordinalCodeDomainSuccBodyTermAt (tVar 0))).
      {
        unfold ordinalCodeDomainSuccBodyTermAt.
        simpl.
        exact (BProv_andI Ax_s C _ _ hpredDomain
          (BProv_andI Ax_s C _ _ hlt hadjoin)).
      }
      assert (hexTarget : BProv Ax_s C
          (rename S
            (pEx (ordinalCodeDomainSuccBodyTermAt (tVar 0))))).
      {
        change (BProv Ax_s C
          (pEx (rename (up S)
            (ordinalCodeDomainSuccBodyTermAt (tVar 0))))).
        apply (BProv_exI Ax_s C _ (tVar 0)).
        unfold ordinalCodeDomainSuccBodyTermAt.
        cbn [rename].
        rewrite rename_up_succ_codedOrdinalDomain.
        cbn [subst].
        rewrite subst_instTerm_var_zero_codedOrdinalDomain.
        simpl.
        exact hprod.
      }
      unfold ordinalCodeDomainZeroOrSuccTermAt.
      cbn [rename].
      exact (BProv_orI2 Ax_s C _ _ hexTarget).
    }
    apply (BProv_exE_of_sentences Ax_s Sctx succBody
      (ordinalCodeDomainZeroOrSuccTermAt (tVar 0)) sentence_ax_s hex).
    unfold C in hinner. exact hinner.
  }
  exact (BProv_orE Ax_s G zeroCase succCase
    (ordinalCodeDomainZeroOrSuccTermAt (tVar 0))
    hcases0 hzero hsucc).
Qed.

Lemma subst_ordinalCodeDomainZeroOrSuccTermAt : forall sigma current,
  subst sigma (ordinalCodeDomainZeroOrSuccTermAt current) =
    ordinalCodeDomainZeroOrSuccTermAt (Term.subst sigma current).
Proof.
  intros sigma current.
  assert (hdomain :
      subst (Term.upSubst sigma) codedOrdinalDomain =
      codedOrdinalDomain).
  {
    transitivity (subst (fun n => tVar n) codedOrdinalDomain).
    - apply subst_ext_free. intros n hn.
      pose proof (codedOrdinalDomain_free n hn) as hn0.
      subst n. reflexivity.
    - apply subst_id.
  }
  unfold ordinalCodeDomainZeroOrSuccTermAt,
    ordinalCodeDomainSuccBodyTermAt.
  cbn [subst].
  rewrite subst_ltTermAt.
  rewrite subst_hfAdjoinGraphTermAt.
  rewrite hdomain.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma BProv_Ax_s_all_ordinalCodeDomainZeroOrSucc : forall
    P : TranslatedHFFinAxiomProofs,
  BProv Ax_s []
    (pAll
      (pImp codedOrdinalDomain
        (ordinalCodeDomainZeroOrSuccTermAt (tVar 0)))).
Proof.
  intro P.
  set (C := [codedOrdinalDomain]).
  assert (hdomain : BProv Ax_s C codedOrdinalDomain).
  { apply BProv_ass. unfold C. simpl. now left. }
  pose proof (BProv_Ax_s_ordinalCodeDomainZeroOrSuccAt_of_domain
    P C hdomain) as htarget.
  assert (himp : BProv Ax_s []
      (pImp codedOrdinalDomain
        (ordinalCodeDomainZeroOrSuccTermAt (tVar 0)))).
  { unfold C in htarget; exact (BProv_impI Ax_s [] _ _ htarget). }
  exact (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s himp).
Qed.

Definition PAOrdinalCodeDomainDecompositionProof_of_TranslatedHFFinAxiomProofs
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalCodeDomainDecompositionProof.
Proof.
  intros G current hdomain.
  assert (hall : BProv Ax_s G
      (pAll
        (pImp codedOrdinalDomain
          (ordinalCodeDomainZeroOrSuccTermAt (tVar 0))))).
  {
    exact (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_all_ordinalCodeDomainZeroOrSucc P)).
  }
  pose proof (BProv_allE Ax_s G _ current hall) as himpRaw.
  assert (himp : BProv Ax_s G
      (pImp
        (subst (instTerm current) codedOrdinalDomain)
        (ordinalCodeDomainZeroOrSuccTermAt current))).
  {
    cbn [subst] in himpRaw.
    rewrite subst_ordinalCodeDomainZeroOrSuccTermAt in himpRaw.
    simpl in himpRaw.
    exact himpRaw.
  }
  exact (BProv_mp Ax_s G _ _ himp hdomain).
Defined.

(** Assemble all three local range laws from their exact upstream
    certificates. *)
Definition OrdinalCodeGraphRangeLocalFacts_of_arithmetic
    (P : TranslatedHFFinAxiomProofs)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hgraphFunctional : PAOrdinalCodeGraphFunctionalProof)
    (hadjoinFunctional : PAHFAdjoinOutputFunctionalProof) :
  OrdinalCodeGraphRangeLocalFacts :=
  OrdinalCodeGraphRangeLocalFacts_of_components
    (PAOrdinalCodeDomainDecompositionProof_of_TranslatedHFFinAxiomProofs P)
    (PAOrdinalCodeGraphSuccClosureProof_of_functionality
      htotal hgraphFunctional hadjoinFunctional)
    (PAOrdinalCodeGraphCodomainProof_of_TranslatedHFFinAxiomProofs P).

Definition PAOrdinalCodeGraphRangeProof_of_arithmetic
    (P : TranslatedHFFinAxiomProofs)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hgraphFunctional : PAOrdinalCodeGraphFunctionalProof)
    (hadjoinFunctional : PAHFAdjoinOutputFunctionalProof) :
  PAOrdinalCodeGraphRangeProof :=
  PAOrdinalCodeGraphRangeProof_of_localFacts
    (OrdinalCodeGraphRangeLocalFacts_of_arithmetic
      P htotal hgraphFunctional hadjoinFunctional).

Definition PAOrdinalCodeGraphRangeProof_of_adjoin_and_functionality
    (P : TranslatedHFFinAxiomProofs)
    (hadjoin : PAHFAdjoinExistence)
    (hgraphFunctional : PAOrdinalCodeGraphFunctionalProof)
    (hadjoinFunctional : PAHFAdjoinOutputFunctionalProof) :
  PAOrdinalCodeGraphRangeProof :=
  PAOrdinalCodeGraphRangeProof_of_arithmetic P
    (PAOrdinalCodeGraphTotalProof_of_adjoinExistence hadjoin)
    hgraphFunctional hadjoinFunctional.
