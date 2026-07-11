(* ===================================================================== *)
(*  PAHFOrdinalCodeAddCore.v                                            *)
(*                                                                       *)
(*  Arithmetic core for reverse-translated HF addition.                 *)
(*                                                                       *)
(*  Closed HFFin operation laws are instantiated at arbitrary PA terms;  *)
(*  subsequent ordinal induction is kept behind explicit graph-law       *)
(*  interfaces so it composes with the independently proved graph tower. *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Logic.FunctionalExtensionality.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeInjective PAHFOrdinalCodeRange PAHFTranslatedOperations
  PAHFOrdinalCodeTermOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Exact successor edge used by the addition recursion.  The term-base
    module supplies this from graph successor closure, output functionality,
    and Ackermann-adjoin totality. *)
Definition PAOrdinalCodeSuccAdjoinCompatibility : Prop :=
  forall (G : list formula) (raw pred out : term),
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) ->
    BProv Ax_s G
      (iffForm
        (hfAdjoinGraphTermAt out pred pred)
        (ordinalCodeGraphTermAt (tSucc raw) out)).

Definition addTermSubst (out left right : term) (n : nat) : term :=
  match n with
  | 0 => right
  | 1 => left
  | 2 => out
  | S (S (S k)) => tVar (k + 3)
  end.

Definition hfAddGraphTermAt
    (out left right : term) : formula :=
  subst (addTermSubst out left right) (hfAddGraphAt 2 1 0).

Lemma hfAddGraphAt_eq_termAt : forall out left right,
  hfAddGraphAt out left right =
    hfAddGraphTermAt (tVar out) (tVar left) (tVar right).
Proof.
  intros out left right.
  set (r := fun n =>
    match n with
    | 0 => right
    | 1 => left
    | 2 => out
    | S (S (S k)) => k + 3
    end).
  assert (hsubst :
      addTermSubst (tVar out) (tVar left) (tVar right) =
      fun n => tVar (r n)).
  {
    apply functional_extensionality.
    intros [|[|[|n]]]; reflexivity.
  }
  assert (hsource : Fol.rename r (addGraphAt 2 1 0) =
      addGraphAt out left right).
  {
    rewrite rename_addGraphAt.
    unfold r.
    reflexivity.
  }
  unfold hfAddGraphTermAt, hfAddGraphAt.
  rewrite hsubst.
  rewrite subst_var_rename.
  rewrite rename_hfFormulaAt.
  rewrite <- hsource.
  rewrite hfFormulaAt_source_rename.
  reflexivity.
Qed.

Lemma subst_hfAddGraphTermAt : forall sigma out left right,
  subst sigma (hfAddGraphTermAt out left right) =
    hfAddGraphTermAt
      (Term.subst sigma out)
      (Term.subst sigma left)
      (Term.subst sigma right).
Proof.
  intros sigma out left right.
  unfold hfAddGraphTermAt.
  rewrite subst_comp.
  apply subst_ext_free.
  intros n hn.
  destruct (hfFormulaAt_free (addGraphAt 2 1 0)
    (fun n => n) n hn) as [m [hm ->]].
  destruct (addGraphAt_free m 2 1 0 hm) as [-> | [-> | ->]];
    reflexivity.
Qed.

Lemma rename_hfAddGraphTermAt : forall r out left right,
  rename r (hfAddGraphTermAt out left right) =
    hfAddGraphTermAt
      (Term.rename r out)
      (Term.rename r left)
      (Term.rename r right).
Proof.
  intros r out left right.
  rewrite <- subst_var_rename.
  rewrite subst_hfAddGraphTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma compositeAddCoreAt_eq_termAt : forall codedOut,
  compositeAddCoreAt codedOut =
    hfAddGraphTermAt
      (tVar (codedOut + 2)) (tVar 1) (tVar 0).
Proof.
  intro codedOut.
  rewrite <- hfAddGraphAt_eq_termAt.
  unfold compositeAddCoreAt, hfAddGraphAt.
  set (r := compositeAddCoreSlotMap codedOut).
  assert (hsource : Fol.rename r (addGraphAt 2 1 0) =
      addGraphAt (codedOut + 2) 1 0).
  {
    rewrite rename_addGraphAt.
    unfold r, compositeAddCoreSlotMap.
    replace (codedOut + 0 + 2) with (codedOut + 2) by lia.
    reflexivity.
  }
  rewrite <- hsource.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intro n. reflexivity.
Qed.

Lemma hfEmptyCodeAt_eq_termAt : forall slot,
  hfEmptyCodeAt slot = hfEmptyTermAt (tVar slot).
Proof.
  intro slot.
  unfold hfEmptyCodeAt, hfEmptyTermAt, HF_emptyAt.
  cbn [hfFormulaAt hfUpVarMap Term.rename].
  rewrite hfMemTermAt_var.
  reflexivity.
Qed.

Lemma addHFOrdinalLikeAt_eq_domainTermAt : forall slot,
  addHFOrdinalLikeAt slot =
    subst (instTerm (tVar slot)) codedOrdinalDomain.
Proof.
  intro slot.
  assert (hsource :
      Fol.rename (Fol.inst slot) domainForm = HF_ordinalLikeAt slot).
  {
    unfold domainForm, HF_ordinalLikeAt, HF_transitiveAt,
      HF_memTotalOnAt.
    cbn [Fol.rename Fol.up Fol.inst].
    reflexivity.
  }
  unfold addHFOrdinalLikeAt, codedOrdinalDomain, translateHFFormula.
  rewrite subst_instTerm_var.
  rewrite rename_hfFormulaAt.
  rewrite <- hsource.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intro n. reflexivity.
Qed.

Lemma subst_domainTermAt : forall sigma coded,
  subst sigma (subst (instTerm coded) codedOrdinalDomain) =
    subst (instTerm (Term.subst sigma coded)) codedOrdinalDomain.
Proof.
  intros sigma coded.
  rewrite subst_comp.
  apply subst_ext_free.
  intros n hn.
  pose proof (codedOrdinalDomain_free n hn) as ->.
  reflexivity.
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_zero_right : forall
    (P : TranslatedHFFinAxiomProofs) G out left right,
  BProv Ax_s G (hfEmptyTermAt right) ->
  BProv Ax_s G (pEq out left) ->
  BProv Ax_s G (hfAddGraphTermAt out left right).
Proof.
  intros P G out left right hright hout.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll
        (pImp
          (hfEmptyTermAt (tVar 1))
          (pImp
            (pEq (tVar 0) (tVar 2))
            (hfAddGraphTermAt (tVar 0) (tVar 2) (tVar 1)))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addZeroRightSentence P)) as h.
    repeat rewrite hfEmptyCodeAt_eq_termAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out hright0) as hout0.
  assert (himp : BProv Ax_s G
      (pImp (hfEmptyTermAt right)
        (pImp (pEq out left)
          (hfAddGraphTermAt out left right)))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout0.
    repeat rewrite subst_hfEmptyTermAt in hout0.
    repeat rewrite subst_hfAddGraphTermAt in hout0.
    repeat rewrite Term.subst_rename_succ_up in hout0.
    repeat rewrite term_subst_instTerm_rename_succ in hout0.
    cbn [Term.subst Term.upSubst instTerm] in hout0.
    repeat rewrite Term.subst_rename_succ_up in hout0.
    repeat rewrite term_subst_instTerm_rename_succ in hout0.
    exact hout0.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hright) hout).
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_succ_right : forall
    (P : TranslatedHFFinAxiomProofs) G
    outSucc out left rightSucc right,
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfAdjoinGraphTermAt rightSucc right right) ->
  BProv Ax_s G (hfAdjoinGraphTermAt outSucc out out) ->
  BProv Ax_s G (hfAddGraphTermAt out left right) ->
  BProv Ax_s G (hfAddGraphTermAt outSucc left rightSucc).
Proof.
  intros P G outSucc out left rightSucc right
    hrightDomain hrightSucc houtSucc hadd.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 3)) codedOrdinalDomain)
          (pImp
            (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))
            (pImp
              (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
              (pImp
                (hfAddGraphTermAt (tVar 1) (tVar 4) (tVar 3))
                (hfAddGraphTermAt (tVar 0) (tVar 4) (tVar 2)))))))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addSuccRightSentence P)) as h.
    rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ rightSucc hright0) as hrightSucc0.
  pose proof (BProv_allE Ax_s G _ out hrightSucc0) as hout0.
  pose proof (BProv_allE Ax_s G _ outSucc hout0) as houtSucc0.
  assert (himp : BProv Ax_s G
      (pImp (subst (instTerm right) codedOrdinalDomain)
        (pImp (hfAdjoinGraphTermAt rightSucc right right)
          (pImp (hfAdjoinGraphTermAt outSucc out out)
            (pImp (hfAddGraphTermAt out left right)
              (hfAddGraphTermAt outSucc left rightSucc)))))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in houtSucc0.
    repeat rewrite subst_domainTermAt in houtSucc0.
    repeat rewrite subst_hfAdjoinGraphTermAt in houtSucc0.
    repeat rewrite subst_hfAddGraphTermAt in houtSucc0.
    repeat rewrite Term.subst_rename_succ_up in houtSucc0.
    repeat rewrite term_subst_instTerm_rename_succ in houtSucc0.
    cbn [Term.subst Term.upSubst instTerm] in houtSucc0.
    repeat rewrite subst_domainTermAt in houtSucc0.
    repeat rewrite subst_hfAdjoinGraphTermAt in houtSucc0.
    repeat rewrite subst_hfAddGraphTermAt in houtSucc0.
    repeat rewrite Term.subst_rename_succ_up in houtSucc0.
    repeat rewrite term_subst_instTerm_rename_succ in houtSucc0.
    exact houtSucc0.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _
        (BProv_mp Ax_s G _ _ himp hrightDomain)
        hrightSucc) houtSucc) hadd).
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_functional : forall
    (P : TranslatedHFFinAxiomProofs) G out1 out2 left right,
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfAddGraphTermAt out1 left right) ->
  BProv Ax_s G (hfAddGraphTermAt out2 left right) ->
  BProv Ax_s G (pEq out1 out2).
Proof.
  intros P G out1 out2 left right hrightDomain hadd1 hadd2.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 2)) codedOrdinalDomain)
          (pImp
            (hfAddGraphTermAt (tVar 1) (tVar 3) (tVar 2))
            (pImp
              (hfAddGraphTermAt (tVar 0) (tVar 3) (tVar 2))
              (pEq (tVar 1) (tVar 0)))))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addFunctionalSentence P)) as h.
    rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out1 hright0) as hout1.
  pose proof (BProv_allE Ax_s G _ out2 hout1) as hout2.
  assert (himp : BProv Ax_s G
      (pImp (subst (instTerm right) codedOrdinalDomain)
        (pImp (hfAddGraphTermAt out1 left right)
          (pImp (hfAddGraphTermAt out2 left right)
            (pEq out1 out2))))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfAddGraphTermAt in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    cbn [Term.subst Term.upSubst instTerm] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfAddGraphTermAt in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    exact hout2.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _ himp hrightDomain) hadd1) hadd2).
Qed.

Lemma BProv_Ax_s_codedOrdinalDomain_of_graph : forall
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded) ->
  BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain).
Proof.
  intros hcodomain G raw coded hgraph.
  apply (hcodomain G coded).
  unfold ordinalCodeGraphRangeExistsTermAt.
  apply (BProv_exI Ax_s G _ raw).
  rewrite subst_ordinalCodeGraphTermAt.
  cbn [instTerm Term.subst].
  rewrite term_subst_instTerm_rename_succ.
  exact hgraph.
Qed.

Lemma BProv_Ax_s_hfEmptyTermAt_of_eq_zero : forall G t,
  BProv Ax_s G (pEq t tZero) ->
  BProv Ax_s G (hfEmptyTermAt t).
Proof.
  intros G t heq.
  set (context := hfEmptyTermAt (tVar 0)).
  assert (hzero : BProv Ax_s G
      (subst (instTerm tZero) context)).
  {
    unfold context.
    rewrite subst_hfEmptyTermAt.
    cbn [instTerm Term.subst].
    exact (BProv_weaken_nil Ax_s G _ BProv_Ax_s_hfEmptyTermAt_zero).
  }
  pose proof (BProv_eqElim Ax_s G tZero t context
    (BProv_eqSym Ax_s G _ _ heq) hzero) as htransport.
  unfold context in htransport.
  repeat rewrite subst_hfEmptyTermAt in htransport.
  cbn [instTerm Term.subst] in htransport.
  repeat rewrite term_subst_instTerm_rename_succ in htransport.
  exact htransport.
Qed.

(** Base case of ordinal-code addition.  The only HF fact needed here is
    addition by the empty code; output uniqueness on both graph sides turns
    that canonical witness into an equivalence for an arbitrary output. *)
Lemma BProv_Ax_s_ordinalCodeAddCore_zero : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    G leftRaw leftCode rightCode out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt tZero rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfAddGraphTermAt out leftCode rightCode)
      (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)).
Proof.
  intros P hcodomain hfunctional G leftRaw leftCode rightCode out
    hleft hright.
  pose proof
    (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
      G rightCode hright) as hrightEq.
  pose proof
    (BProv_Ax_s_hfEmptyTermAt_of_eq_zero G rightCode hrightEq)
    as hrightEmpty.
  pose proof
    (BProv_Ax_s_codedOrdinalDomain_of_graph
      hcodomain G tZero rightCode hright) as hrightDomain.
  assert (hbase : BProv Ax_s G
      (hfAddGraphTermAt leftCode leftCode rightCode)).
  {
    exact (BProv_Ax_s_hfAddGraphTermAt_zero_right
      P G leftCode leftCode rightCode hrightEmpty
      (BProv_eqRefl Ax_s G leftCode)).
  }
  pose proof (BProv_weaken_nil Ax_s G _
    (BProv_Ax_s_addZero_term leftRaw)) as haddZero.
  assert (hforward : BProv Ax_s G
      (pImp
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out))).
  {
    apply BProv_impI.
    set (C := hfAddGraphTermAt out leftCode rightCode :: G).
    assert (hadd : BProv Ax_s C
        (hfAddGraphTermAt out leftCode rightCode)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtEq : BProv Ax_s C (pEq out leftCode)).
    {
      exact (BProv_Ax_s_hfAddGraphTermAt_functional
        P C out leftCode leftCode rightCode
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ hrightDomain)
        hadd
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ hbase)).
    }
    assert (houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_coded
        Ax_s C leftRaw leftCode out
        (BProv_eqSym Ax_s C _ _ houtEq)
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ hleft)).
    }
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C leftRaw (tAdd leftRaw tZero) out
      (BProv_eqSym Ax_s C _ _
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ haddZero))
      houtGraph).
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)
        (hfAddGraphTermAt out leftCode rightCode))).
  {
    apply BProv_impI.
    set (C := ordinalCodeGraphTermAt (tAdd leftRaw tZero) out :: G).
    assert (htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C (tAdd leftRaw tZero) leftRaw out
        (BProv_context_cons Ax_s G
          (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ haddZero)
        htarget).
    }
    assert (houtEq : BProv Ax_s C (pEq out leftCode)).
    {
      exact (hfunctional C leftRaw out leftCode
        houtGraph
        (BProv_context_cons Ax_s G
          (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ hleft)).
    }
    exact (BProv_Ax_s_hfAddGraphTermAt_zero_right
      P C out leftCode rightCode
      (BProv_context_cons Ax_s G
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ hrightEmpty)
      houtEq).
  }
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.
