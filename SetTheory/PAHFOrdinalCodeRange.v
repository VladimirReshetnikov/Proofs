(* ===================================================================== *)
(*  PAHFOrdinalCodeRange.v                                              *)
(*                                                                       *)
(*  Proof-theoretic reduction of the ordinal-code graph range theorem.   *)
(*                                                                       *)
(*  The generic strong-induction and binder plumbing is proved here.     *)
(*  The remaining mathematical content is isolated in three local laws: *)
(*  finite-ordinal predecessor decomposition, graph successor closure,   *)
(*  and graph codomain safety.                                           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFOrdinalCodeTotal PAHFOrdinalCodeTotalInduction PAHFTranslatedHFFin
  PAHFRoundTripArithmetic PAHFRoundTripQuantifiers.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Pure PA strong induction for an arbitrary formula whose current value
    is stored in slot zero. *)
Lemma BProv_Ax_s_all_of_strongStep : forall psi,
  (forall G,
    BProv Ax_s G (hfStrongBelowAt psi) ->
    BProv Ax_s G psi) ->
  BProv Ax_s [] (pAll psi).
Proof.
  intros psi hcurrent.
  set (below := hfStrongBelowAt psi).
  assert (hzero : BProv Ax_s [] (subst substZero below)).
  {
    unfold below.
    rewrite substZero_hfStrongBelowAt.
    set (lowLtZero := ltTermAt (tVar 0) tZero).
    assert (hbody : BProv Ax_s [] (pImp lowLtZero psi)).
    {
      set (D := [lowLtZero]).
      assert (hlt : BProv Ax_s D lowLtZero).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (hzeroLe : BProv Ax_s D (leTermAt tZero (tVar 0))).
      { exact (BProv_Ax_s_leTermAt_zero_left D (tVar 0)). }
      assert (hbot : BProv Ax_s D pBot).
      {
        exact (BProv_Ax_s_ltTermAt_leTermAt_bot D
          (tVar 0) tZero hlt hzeroLe).
      }
      assert (hpsi : BProv Ax_s D psi).
      { exact (BProv_botE Ax_s D psi hbot). }
      unfold D in hpsi.
      exact (BProv_impI Ax_s [] lowLtZero psi hpsi).
    }
    exact (BProv_allI_of_sentences Ax_s []
      (pImp lowLtZero psi) sentence_ax_s hbody).
  }
  assert (hsuccBody : BProv Ax_s [below]
      (subst substSuccVar below)).
  {
    set (Sctx := [below]).
    assert (hbelowS : BProv Ax_s Sctx below).
    { apply BProv_ass. unfold Sctx. simpl. now left. }
    assert (hpsiCurrent : BProv Ax_s Sctx psi).
    { apply hcurrent. unfold below in hbelowS. exact hbelowS. }
    set (lowLtSucc := ltTermAt (tVar 0) (tSucc (tVar 1))).
    set (psiAtLow := rename rSkipParam psi).
    assert (htarget : BProv Ax_s Sctx
        (pAll (pImp lowLtSucc psiAtLow))).
    {
      set (R := map (rename S) Sctx).
      assert (hbody : BProv Ax_s R (pImp lowLtSucc psiAtLow)).
      {
        set (D := lowLtSucc :: R).
        assert (hlt : BProv Ax_s D lowLtSucc).
        { apply BProv_ass. unfold D. simpl. now left. }
        assert (hcases : BProv Ax_s D
            (pOr (ltTermAt (tVar 0) (tVar 1))
                 (pEq (tVar 0) (tVar 1)))).
        {
          exact (BProv_Ax_s_ltTermAt_succ_right_cases D
            (tVar 0) (tVar 1) hlt).
        }
        assert (hbelowRen : BProv Ax_s R (rename S below)).
        {
          unfold R.
          exact (BProv_rename_of_sentences Ax_s sentence_ax_s Sctx
            below hbelowS S).
        }
        assert (hbelowBody : BProv Ax_s R
            (pImp (ltTermAt (tVar 0) (tVar 1)) psiAtLow)).
        {
          pose proof (BProv_allE_current_of_renamed R
            (pImp (ltAt 0 1) (rename rSkipParam psi))
            hbelowRen) as h.
          unfold below, hfStrongBelowAt in hbelowRen.
          rewrite ltTermAt_var.
          unfold psiAtLow.
          exact h.
        }
        assert (hstrict : BProv Ax_s
            (ltTermAt (tVar 0) (tVar 1) :: D) psiAtLow).
        {
          set (E := ltTermAt (tVar 0) (tVar 1) :: D).
          assert (hltPred : BProv Ax_s E
              (ltTermAt (tVar 0) (tVar 1))).
          { apply BProv_ass. unfold E. simpl. now left. }
          assert (hbelowE : BProv Ax_s E
              (pImp (ltTermAt (tVar 0) (tVar 1)) psiAtLow)).
          {
            unfold E, D.
            apply BProv_context_cons.
            apply BProv_context_cons.
            exact hbelowBody.
          }
          exact (BProv_mp Ax_s E
            (ltTermAt (tVar 0) (tVar 1)) psiAtLow
            hbelowE hltPred).
        }
        assert (hequal : BProv Ax_s
            (pEq (tVar 0) (tVar 1) :: D) psiAtLow).
        {
          set (E := pEq (tVar 0) (tVar 1) :: D).
          assert (heq : BProv Ax_s E (pEq (tVar 0) (tVar 1))).
          { apply BProv_ass. unfold E. simpl. now left. }
          assert (hpsiRen : BProv Ax_s R (rename S psi)).
          {
            unfold R.
            exact (BProv_rename_of_sentences Ax_s sentence_ax_s Sctx
              psi hpsiCurrent S).
          }
          assert (hpsiE : BProv Ax_s E (rename S psi)).
          {
            unfold E, D.
            apply BProv_context_cons.
            apply BProv_context_cons.
            exact hpsiRen.
          }
          unfold psiAtLow.
          exact (BProv_predicate_current_of_eq_previous E psi heq hpsiE).
        }
        assert (hpsi : BProv Ax_s D psiAtLow).
        {
          exact (BProv_orE Ax_s D
            (ltTermAt (tVar 0) (tVar 1))
            (pEq (tVar 0) (tVar 1)) psiAtLow
            hcases hstrict hequal).
        }
        unfold D in hpsi.
        exact (BProv_impI Ax_s R lowLtSucc psiAtLow hpsi).
      }
      unfold R in hbody.
      exact (BProv_allI_of_sentences Ax_s Sctx
        (pImp lowLtSucc psiAtLow) sentence_ax_s hbody).
    }
    unfold Sctx in htarget.
    unfold below.
    rewrite substSuccVar_hfStrongBelowAt.
    unfold lowLtSucc, psiAtLow in htarget.
    exact htarget.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp below (subst substSuccVar below))).
  {
    exact (BProv_impI Ax_s [] below
      (subst substSuccVar below) hsuccBody).
  }
  assert (hsucc : BProv Ax_s []
      (pAll (pImp below (subst substSuccVar below)))).
  {
    exact (BProv_allI_of_sentences Ax_s []
      (pImp below (subst substSuccVar below)) sentence_ax_s hsuccImp).
  }
  assert (hallBelow : BProv Ax_s [] (pAll below)).
  { exact (BProv_Ax_s_induction_rule [] below hzero hsucc). }
  assert (hallBelowRen : BProv Ax_s [] (rename S (pAll below))).
  {
    exact (BProv_rename_of_sentences Ax_s sentence_ax_s []
      (pAll below) hallBelow S).
  }
  assert (hbelow : BProv Ax_s [] below).
  { exact (BProv_allE_current_of_renamed [] below hallBelowRen). }
  assert (hpsi : BProv Ax_s [] psi).
  { apply hcurrent. unfold below in hbelow. exact hbelow. }
  exact (BProv_allI_of_sentences Ax_s [] psi sentence_ax_s hpsi).
Qed.

(** Pointwise range characterization at the current coded value in slot
    zero. *)
Definition ordinalCodeGraphRangePoint : formula :=
  iffForm codedOrdinalDomain (pEx (ordinalCodeGraphAt 0 1)).

(** Term-parametric existential range predicate. *)
Definition ordinalCodeGraphRangeExistsTermAt (coded : term) : formula :=
  pEx (ordinalCodeGraphTermAt (tVar 0) (Term.rename S coded)).

Lemma subst_instTerm_ordinalCodeGraphRangePoint : forall coded,
  subst (instTerm coded) ordinalCodeGraphRangePoint =
    iffForm
      (subst (instTerm coded) codedOrdinalDomain)
      (ordinalCodeGraphRangeExistsTermAt coded).
Proof.
  intro coded.
  unfold ordinalCodeGraphRangePoint,
    ordinalCodeGraphRangeExistsTermAt, ordinalCodeGraphAt, iffForm.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  cbn [Term.subst Term.upSubst Term.rename].
  reflexivity.
Qed.

Lemma rename_rSkipParam_ordinalCodeGraphRangePoint :
  rename rSkipParam ordinalCodeGraphRangePoint =
    ordinalCodeGraphRangePoint.
Proof.
  assert (hdomain : rename rSkipParam codedOrdinalDomain =
      codedOrdinalDomain).
  {
    transitivity (rename (fun n : nat => n) codedOrdinalDomain).
    - apply rename_ext_free. intros n hn.
      pose proof (codedOrdinalDomain_free n hn) as hn0.
      subst n. reflexivity.
    - apply rename_id.
  }
  unfold ordinalCodeGraphRangePoint, iffForm, ordinalCodeGraphAt.
  cbn [rename].
  rewrite hdomain, rename_ordinalCodeGraphTermAt.
  reflexivity.
Qed.

(** Binder body saying that the fresh predecessor in slot zero is an
    ordinal-like strict predecessor of [current], and that [current] is its
    HF successor. *)
Definition ordinalCodeDomainSuccBodyTermAt (current : term) : formula :=
  pAnd codedOrdinalDomain
    (pAnd
      (ltTermAt (tVar 0) (Term.rename S current))
      (hfAdjoinGraphTermAt
        (Term.rename S current) (tVar 0) (tVar 0))).

Definition ordinalCodeDomainZeroOrSuccTermAt (current : term) : formula :=
  pOr (pEq current tZero)
    (pEx (ordinalCodeDomainSuccBodyTermAt current)).

Definition OrdinalCodeGraphRangeStrongStep : Prop :=
  forall G,
    BProv Ax_s G (hfStrongBelowAt ordinalCodeGraphRangePoint) ->
    BProv Ax_s G ordinalCodeGraphRangePoint.

Record OrdinalCodeGraphRangeLocalFacts : Prop := {
  ocgr_domain_decompose : forall G current,
    BProv Ax_s G (subst (instTerm current) codedOrdinalDomain) ->
    BProv Ax_s G (ordinalCodeDomainZeroOrSuccTermAt current);
  ocgr_graph_succ : forall G raw pred current,
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) ->
    BProv Ax_s G (hfAdjoinGraphTermAt current pred pred) ->
    BProv Ax_s G (ordinalCodeGraphTermAt (tSucc raw) current);
  ocgr_graph_codomain : forall G coded,
    BProv Ax_s G (ordinalCodeGraphRangeExistsTermAt coded) ->
    BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain)
}.

Lemma BProv_ordinalCodeGraphRangePoint_of_strongBelow : forall G,
  BProv Ax_s G
    (rename S (hfStrongBelowAt ordinalCodeGraphRangePoint)) ->
  BProv Ax_s G (ltAt 0 1) ->
  BProv Ax_s G ordinalCodeGraphRangePoint.
Proof.
  intros G hbelow hlt.
  pose proof (BProv_allE_current_of_renamed G
    (pImp (ltAt 0 1)
      (rename rSkipParam ordinalCodeGraphRangePoint))
    hbelow) as himp.
  rewrite rename_rSkipParam_ordinalCodeGraphRangePoint in himp.
  exact (BProv_mp Ax_s G (ltAt 0 1)
    ordinalCodeGraphRangePoint himp hlt).
Qed.

(** The three local mathematical laws discharge the local strong-induction
    step.  All witness opening and De Bruijn transport is internal to this
    lemma. *)
Lemma OrdinalCodeGraphRangeStrongStep_of_localFacts :
  OrdinalCodeGraphRangeLocalFacts ->
  OrdinalCodeGraphRangeStrongStep.
Proof.
  intros F G hbelow.
  set (domain := codedOrdinalDomain).
  set (range := ordinalCodeGraphRangeExistsTermAt (tVar 0)).
  assert (hforward : BProv Ax_s G (pImp domain range)).
  {
    set (D := domain :: G).
    assert (hdomain : BProv Ax_s D domain).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hdecomp : BProv Ax_s D
        (ordinalCodeDomainZeroOrSuccTermAt (tVar 0))).
    {
      apply (ocgr_domain_decompose F D (tVar 0)).
      rewrite subst_instTerm_var_zero_codedOrdinalDomain.
      exact hdomain.
    }
    set (zeroCase := pEq (tVar 0) tZero).
    set (succBody := ordinalCodeDomainSuccBodyTermAt (tVar 0)).
    set (succCase := pEx succBody).
    assert (hzeroBranch : BProv Ax_s (zeroCase :: D) range).
    {
      set (Z := zeroCase :: D).
      assert (hzero : BProv Ax_s Z (pEq (tVar 0) tZero)).
      { apply BProv_ass. unfold Z, zeroCase. simpl. now left. }
      assert (hgraphZero : BProv Ax_s Z
          (ordinalCodeGraphTermAt tZero tZero)).
      { apply BProv_Ax_s_ordinalCodeGraphTermAt_zero. }
      set (graphContext := ordinalCodeGraphTermAt
        (Term.rename S tZero) (tVar 0)).
      assert (hgraphZeroInst : BProv Ax_s Z
          (subst (instTerm tZero) graphContext)).
      {
        unfold graphContext.
        rewrite subst_ordinalCodeGraphTermAt.
        simpl.
        exact hgraphZero.
      }
      assert (hgraphCurrent : BProv Ax_s Z
          (ordinalCodeGraphTermAt tZero (tVar 0))).
      {
        pose proof (BProv_eqElim Ax_s Z tZero (tVar 0)
          graphContext (BProv_eqSym Ax_s Z (tVar 0) tZero hzero)
          hgraphZeroInst) as htransport.
        unfold graphContext in htransport.
        rewrite subst_ordinalCodeGraphTermAt in htransport.
        simpl in htransport.
        exact htransport.
      }
      unfold range, ordinalCodeGraphRangeExistsTermAt.
      apply (BProv_exI Ax_s Z _ tZero).
      rewrite subst_ordinalCodeGraphTermAt.
      simpl.
      exact hgraphCurrent.
    }
    assert (hsuccBranch : BProv Ax_s (succCase :: D) range).
    {
      set (Sctx := succCase :: D).
      assert (hsuccEx : BProv Ax_s Sctx (pEx succBody)).
      {
        apply BProv_ass.
        unfold Sctx, succCase. simpl. now left.
      }
      set (C := succBody :: map (rename S) Sctx).
      assert (hinner : BProv Ax_s C (rename S range)).
      {
        assert (hsucc : BProv Ax_s C succBody).
        { apply BProv_ass. unfold C. simpl. now left. }
        assert (hpredDomain : BProv Ax_s C codedOrdinalDomain).
        {
          unfold succBody, ordinalCodeDomainSuccBodyTermAt in hsucc.
          exact (BProv_andE1 Ax_s C _ _ hsucc).
        }
        assert (hrest : BProv Ax_s C
            (pAnd
              (ltTermAt (tVar 0) (tVar 1))
              (hfAdjoinGraphTermAt
                (tVar 1) (tVar 0) (tVar 0)))).
        {
          unfold succBody, ordinalCodeDomainSuccBodyTermAt in hsucc.
          simpl in hsucc.
          exact (BProv_andE2 Ax_s C _ _ hsucc).
        }
        assert (hlt : BProv Ax_s C (ltAt 0 1)).
        {
          change (BProv Ax_s C (ltTermAt (tVar 0) (tVar 1))).
          exact (BProv_andE1 Ax_s C _ _ hrest).
        }
        assert (hadjoin : BProv Ax_s C
            (hfAdjoinGraphTermAt
              (tVar 1) (tVar 0) (tVar 0))).
        { exact (BProv_andE2 Ax_s C _ _ hrest). }
        assert (hbelowS : BProv Ax_s Sctx
            (hfStrongBelowAt ordinalCodeGraphRangePoint)).
        {
          unfold Sctx, D.
          apply BProv_context_cons.
          apply BProv_context_cons.
          exact hbelow.
        }
        assert (hbelowC : BProv Ax_s C
            (rename S
              (hfStrongBelowAt ordinalCodeGraphRangePoint))).
        {
          unfold C.
          exact (BProv_rename_succ_context_cons_of_sentences
            Ax_s sentence_ax_s Sctx succBody
            (hfStrongBelowAt ordinalCodeGraphRangePoint) hbelowS).
        }
        assert (hpredPoint : BProv Ax_s C
            ordinalCodeGraphRangePoint).
        {
          exact (BProv_ordinalCodeGraphRangePoint_of_strongBelow
            C hbelowC hlt).
        }
        assert (hpredForward : BProv Ax_s C
            (pImp codedOrdinalDomain
              (ordinalCodeGraphRangeExistsTermAt (tVar 0)))).
        {
          unfold ordinalCodeGraphRangePoint,
            ordinalCodeGraphRangeExistsTermAt,
            ordinalCodeGraphAt, iffForm in hpredPoint.
          simpl in hpredPoint.
          exact (BProv_andE1 Ax_s C _ _ hpredPoint).
        }
        assert (hpredRange : BProv Ax_s C
            (ordinalCodeGraphRangeExistsTermAt (tVar 0))).
        {
          exact (BProv_mp Ax_s C codedOrdinalDomain
            (ordinalCodeGraphRangeExistsTermAt (tVar 0))
            hpredForward hpredDomain).
        }
        set (graphBody := ordinalCodeGraphTermAt (tVar 0) (tVar 1)).
        set (E := graphBody :: map (rename S) C).
        assert (hgraphBody : BProv Ax_s E graphBody).
        { apply BProv_ass. unfold E. simpl. now left. }
        assert (hadjoinE : BProv Ax_s E
            (hfAdjoinGraphTermAt
              (tVar 2) (tVar 1) (tVar 1))).
        {
          pose proof (BProv_rename_succ_context_cons_of_sentences
            Ax_s sentence_ax_s C graphBody
            (hfAdjoinGraphTermAt (tVar 1) (tVar 0) (tVar 0))
            hadjoin) as hraw.
          rewrite rename_hfAdjoinGraphTermAt in hraw.
          simpl in hraw.
          unfold E.
          exact hraw.
        }
        assert (hnext : BProv Ax_s E
            (ordinalCodeGraphTermAt
              (tSucc (tVar 0)) (tVar 2))).
        {
          exact (ocgr_graph_succ F E
            (tVar 0) (tVar 1) (tVar 2)
            hgraphBody hadjoinE).
        }
        assert (htarget : BProv Ax_s E
            (rename S (rename S range))).
        {
          unfold range, ordinalCodeGraphRangeExistsTermAt.
          cbn [rename].
          apply (BProv_exI Ax_s E _ (tSucc (tVar 0))).
          exact hnext.
        }
        apply (BProv_exE_of_sentences Ax_s C graphBody
          (rename S range) sentence_ax_s).
        - unfold ordinalCodeGraphRangeExistsTermAt in hpredRange.
          unfold graphBody.
          exact hpredRange.
        - unfold E in htarget.
          exact htarget.
      }
      apply (BProv_exE_of_sentences Ax_s Sctx succBody range
        sentence_ax_s hsuccEx).
      unfold C in hinner.
      exact hinner.
    }
    assert (hrange : BProv Ax_s D range).
    {
      apply (BProv_orE Ax_s D zeroCase succCase range).
      - unfold zeroCase, succCase,
          ordinalCodeDomainZeroOrSuccTermAt in hdecomp.
        exact hdecomp.
      - exact hzeroBranch.
      - exact hsuccBranch.
    }
    unfold D, domain in hrange.
    exact (BProv_impI Ax_s G codedOrdinalDomain range hrange).
  }
  assert (hreverse : BProv Ax_s G (pImp range domain)).
  {
    set (D := range :: G).
    assert (hrange : BProv Ax_s D range).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hdomain : BProv Ax_s D domain).
    {
      unfold domain.
      apply (ocgr_graph_codomain F D (tVar 0)).
      unfold range in hrange.
      exact hrange.
    }
    unfold D in hdomain.
    exact (BProv_impI Ax_s G range domain hdomain).
  }
  unfold ordinalCodeGraphRangePoint, range, domain, iffForm.
  simpl.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(** A local strong-induction step yields the exact range field used by the
    quantified PA round-trip constructors, for arbitrary contexts and coded
    terms. *)
Lemma PAOrdinalCodeGraphRangeProof_of_strongStep :
  OrdinalCodeGraphRangeStrongStep ->
  PAOrdinalCodeGraphRangeProof.
Proof.
  intros hstep G coded.
  assert (hall : BProv Ax_s [] (pAll ordinalCodeGraphRangePoint)).
  {
    apply BProv_Ax_s_all_of_strongStep.
    exact hstep.
  }
  assert (hallG : BProv Ax_s G (pAll ordinalCodeGraphRangePoint)).
  { exact (BProv_weaken_nil Ax_s G _ hall). }
  pose proof (BProv_allE Ax_s G ordinalCodeGraphRangePoint
    coded hallG) as hinst.
  rewrite subst_instTerm_ordinalCodeGraphRangePoint in hinst.
  exact hinst.
Qed.

Theorem PAOrdinalCodeGraphRangeProof_of_localFacts :
  OrdinalCodeGraphRangeLocalFacts ->
  PAOrdinalCodeGraphRangeProof.
Proof.
  intro F.
  apply PAOrdinalCodeGraphRangeProof_of_strongStep.
  exact (OrdinalCodeGraphRangeStrongStep_of_localFacts F).
Qed.

(** Individually named residuals make the reduction convenient for modules
    which establish the arithmetic towers independently. *)
Definition PAOrdinalCodeDomainDecompositionProof : Prop :=
  forall G current,
    BProv Ax_s G (subst (instTerm current) codedOrdinalDomain) ->
    BProv Ax_s G (ordinalCodeDomainZeroOrSuccTermAt current).

Definition PAOrdinalCodeGraphSuccClosureProof : Prop :=
  forall G raw pred current,
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) ->
    BProv Ax_s G (hfAdjoinGraphTermAt current pred pred) ->
    BProv Ax_s G (ordinalCodeGraphTermAt (tSucc raw) current).

Definition PAOrdinalCodeGraphCodomainProof : Prop :=
  forall G coded,
    BProv Ax_s G (ordinalCodeGraphRangeExistsTermAt coded) ->
    BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain).

Definition OrdinalCodeGraphRangeLocalFacts_of_components
    (hdomain : PAOrdinalCodeDomainDecompositionProof)
    (hsucc : PAOrdinalCodeGraphSuccClosureProof)
    (hcodomain : PAOrdinalCodeGraphCodomainProof) :
  OrdinalCodeGraphRangeLocalFacts :=
  {| ocgr_domain_decompose := hdomain;
     ocgr_graph_succ := hsucc;
     ocgr_graph_codomain := hcodomain |}.

Theorem PAOrdinalCodeGraphRangeProof_of_components :
  PAOrdinalCodeDomainDecompositionProof ->
  PAOrdinalCodeGraphSuccClosureProof ->
  PAOrdinalCodeGraphCodomainProof ->
  PAOrdinalCodeGraphRangeProof.
Proof.
  intros hdomain hsucc hcodomain.
  apply PAOrdinalCodeGraphRangeProof_of_localFacts.
  exact (OrdinalCodeGraphRangeLocalFacts_of_components
    hdomain hsucc hcodomain).
Qed.
