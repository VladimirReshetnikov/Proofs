(* ===================================================================== *)
(*  PAHFTranslatedHFFin.v                                                *)
(*                                                                       *)
(*  Deductive PA proof of the Ackermann translation of HF set induction. *)
(*  This module keeps the one genuinely arithmetic ingredient -- that    *)
(*  every Ackermann member has a smaller code -- explicit until its       *)
(*  standalone boundedness derivation is ported below this layer.         *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import PAHF.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Every Ackermann member of [set] has a strictly smaller numeric code. *)
Definition hfMembersBelowAt (set : nat) : formula :=
  pAll (pImp (hfMemAt 0 (S set)) (ltAt 0 (S set))).

(** Term-parametric set-code variant of [hfMembersBelowAt]. *)
Definition hfMembersBelowTermAt (setCode : term) : formula :=
  pAll
    (pImp
      (hfMemTermAt 0 (Term.rename S setCode))
      (ltTermAt (tVar 0) (Term.rename S setCode))).

(** Cumulative strong-induction invariant for membership boundedness. *)
Definition hfMembersBelowThroughTermAt (boundCode : term) : formula :=
  pAll
    (pImp
      (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
      (hfMembersBelowAt 0)).

Definition hfMembersBelowThroughAt (bound : nat) : formula :=
  hfMembersBelowThroughTermAt (tVar bound).

Lemma hfMembersBelowTermAt_var : forall set,
  hfMembersBelowTermAt (tVar set) = hfMembersBelowAt set.
Proof. intro set. reflexivity. Qed.

Lemma subst_instTerm_var_hfMembersBelowAt_body : forall elem set,
  subst (instTerm (tVar elem))
    (pImp (hfMemAt 0 (S set)) (ltAt 0 (S set))) =
  pImp (hfMemAt elem set) (ltAt elem set).
Proof.
  intros elem set. reflexivity.
Qed.

Lemma subst_instTerm_var_hfMembersBelowAt_zero : forall set,
  subst (instTerm (tVar set)) (hfMembersBelowAt 0) =
  hfMembersBelowAt set.
Proof.
  intro set. reflexivity.
Qed.

Lemma rename_hfMembersBelowTermAt_succ : forall setCode,
  rename S (hfMembersBelowTermAt setCode) =
  hfMembersBelowTermAt (Term.rename S setCode).
Proof.
  intro setCode.
  unfold hfMembersBelowTermAt, hfMemTermAt, betaTermAtConstIdx,
    betaTermAt, remTermAt, ltTermAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaDiv2BitAt, betaAtSuccIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt,
    eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma rename_hfMembersBelowThroughTermAt_succ : forall boundCode,
  rename S (hfMembersBelowThroughTermAt boundCode) =
  hfMembersBelowThroughTermAt (Term.rename S boundCode).
Proof.
  intro boundCode.
  unfold hfMembersBelowThroughTermAt, hfMembersBelowAt, hfMemAt,
    betaDiv2StepsThroughAt, betaDiv2StepWitnessAt, betaDiv2BitAt,
    betaAtSuccIdx, betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    ltTermAt, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma subst_instTerm_hfMembersBelowTermAt_var_zero : forall setCode,
  subst (instTerm setCode) (hfMembersBelowTermAt (tVar 0)) =
  hfMembersBelowTermAt setCode.
Proof.
  intro setCode.
  unfold hfMembersBelowTermAt, hfMemTermAt, betaTermAtConstIdx,
    betaTermAt, remTermAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaDiv2BitAt, betaAtSuccIdx, betaAt,
    remAt, ltAt, leAt, ltTermAt, div2StepAt, boolAt, zeroAt,
    oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

(** Transport the element slot of membership to an arbitrary proved term. *)
Lemma BProv_hfMemAt_of_elem_eq_term :
  forall (B : formula -> Prop) G elem set elemTerm,
  BProv B G (hfMemAt elem set) ->
  BProv B G (pEq (tVar elem) elemTerm) ->
  BProv B G (subst (instTerm elemTerm) (hfMemAt 0 (S set))).
Proof.
  intros B G elem set elemTerm hmem helem.
  assert (hmemSubst : BProv B G
      (subst (instTerm (tVar elem)) (hfMemAt 0 (S set)))).
  {
    rewrite subst_instTerm_var_hfMemAt_zero_succ.
    exact hmem.
  }
  exact (BProv_eqElim B G (tVar elem) elemTerm
    (hfMemAt 0 (S set)) helem hmemSubst).
Qed.

(** Project one boundedness instance from the cumulative invariant. *)
Lemma BProv_Ax_s_hfMembersBelowAt_of_throughTermAt :
  forall G boundCode set,
  BProv Ax_s G (hfMembersBelowThroughTermAt boundCode) ->
  BProv Ax_s G (leTermAt (tVar set) boundCode) ->
  BProv Ax_s G (hfMembersBelowAt set).
Proof.
  intros G boundCode set hthrough hle.
  assert (hlt : BProv Ax_s G
      (ltTermAt (tVar set) (tSucc boundCode))).
  {
    exact (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt G
      (tVar set) boundCode hle).
  }
  pose proof (BProv_allE Ax_s G
    (pImp
      (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
      (hfMembersBelowAt 0))
    (tVar set) hthrough) as himp.
  assert (hnorm :
      subst (instTerm (tVar set))
        (pImp
          (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
          (hfMembersBelowAt 0)) =
      pImp (ltTermAt (tVar set) (tSucc boundCode))
        (hfMembersBelowAt set)).
  {
    change (pImp
      (subst (instTerm (tVar set))
        (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode))))
      (subst (instTerm (tVar set)) (hfMembersBelowAt 0)) =
      pImp (ltTermAt (tVar set) (tSucc boundCode))
        (hfMembersBelowAt set)).
    rewrite subst_instTerm_var_hfMembersBelowAt_zero.
    f_equal.
    unfold ltTermAt.
    simpl.
    rewrite Term.rename_comp.
    rewrite term_subst_upSubst_instTerm_rename_two_succ.
    reflexivity.
  }
  rewrite hnorm in himp.
  exact (BProv_mp Ax_s G
    (ltTermAt (tVar set) (tSucc boundCode))
    (hfMembersBelowAt set) himp hlt).
Qed.

(** Transport the term-parametric boundedness predicate across set-code
    equality. *)
Lemma BProv_hfMembersBelowTermAt_of_set_eq_term :
  forall (B : formula -> Prop) G oldCode newCode,
  BProv B G (hfMembersBelowTermAt oldCode) ->
  BProv B G (pEq oldCode newCode) ->
  BProv B G (hfMembersBelowTermAt newCode).
Proof.
  intros B G oldCode newCode hold heq.
  assert (holdSubst : BProv B G
      (subst (instTerm oldCode)
        (hfMembersBelowTermAt (tVar 0)))).
  {
    rewrite subst_instTerm_hfMembersBelowTermAt_var_zero.
    exact hold.
  }
  pose proof (BProv_eqElim B G oldCode newCode
    (hfMembersBelowTermAt (tVar 0)) heq holdSubst) as hnew.
  rewrite subst_instTerm_hfMembersBelowTermAt_var_zero in hnew.
  exact hnew.
Qed.

(** Apply a one-code membership-bound invariant to a concrete member slot. *)
Lemma BProv_ltAt_of_hfMembersBelowAt :
  forall (B : formula -> Prop) G elem set,
  BProv B G (hfMembersBelowAt set) ->
  BProv B G (hfMemAt elem set) ->
  BProv B G (ltAt elem set).
Proof.
  intros B G elem set hall hmem.
  pose proof (BProv_allE B G
    (pImp (hfMemAt 0 (S set)) (ltAt 0 (S set)))
    (tVar elem) hall) as himp.
  rewrite subst_instTerm_var_hfMembersBelowAt_body in himp.
  exact (BProv_mp B G (hfMemAt elem set) (ltAt elem set) himp hmem).
Qed.

(** PA rendering of the hereditary premise in one translated HF induction
    instance. *)
Definition hfHereditaryAt (psi : formula) : formula :=
  pAll
    (pImp
      (pAll (pImp (hfMemAt 0 1) (rename rSkipParam psi)))
      psi).

(** Strong-induction accumulator: every code below the current code
    satisfies [psi]. *)
Definition hfStrongBelowAt (psi : formula) : formula :=
  pAll (pImp (ltAt 0 1) (rename rSkipParam psi)).

(** Renaming used by equality elimination in a context containing both a
    fresh candidate and the current induction bound. *)
Definition rInductionEq (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S (S k))
  end.

Lemma subst_previous_rInductionEq : forall psi,
  subst (instTerm (tVar 1)) (rename rInductionEq psi) =
  rename S psi.
Proof.
  intro psi.
  rewrite subst_instTerm_var, rename_comp.
  apply rename_ext.
  intros [|n]; reflexivity.
Qed.

Lemma subst_current_rInductionEq : forall psi,
  subst (instTerm (tVar 0)) (rename rInductionEq psi) =
  rename rSkipParam psi.
Proof.
  intro psi.
  rewrite subst_instTerm_var, rename_comp.
  apply rename_ext.
  intros [|n]; reflexivity.
Qed.

(** Instantiate a universally quantified formula after shifting its ambient
    parameters under the currently opened variable. *)
Lemma BProv_allE_current_of_renamed : forall G a,
  BProv Ax_s G (rename S (pAll a)) ->
  BProv Ax_s G a.
Proof.
  intros G a h.
  pose proof (BProv_allE Ax_s G (rename (Fol.up S) a) (tVar 0) h) as hinst.
  rewrite subst_instTerm_var_zero_rename_up_succ in hinst.
  exact hinst.
Qed.

(** Transport an arbitrary induction predicate from the preceding bound slot
    to the fresh candidate slot. *)
Lemma BProv_predicate_current_of_eq_previous : forall G psi,
  BProv Ax_s G (pEq (tVar 0) (tVar 1)) ->
  BProv Ax_s G (rename S psi) ->
  BProv Ax_s G (rename rSkipParam psi).
Proof.
  intros G psi heq hprevious.
  assert (hprevious' : BProv Ax_s G
      (subst (instTerm (tVar 1)) (rename rInductionEq psi))).
  { rewrite subst_previous_rInductionEq. exact hprevious. }
  pose proof (BProv_eqElim Ax_s G (tVar 1) (tVar 0)
    (rename rInductionEq psi) (BProv_eqSym Ax_s G _ _ heq)
    hprevious') as hcurrent.
  rewrite subst_current_rInductionEq in hcurrent.
  exact hcurrent.
Qed.

Lemma subst_up_zero_rename_rSkipParam : forall psi,
  subst (Term.upSubst substZero) (rename rSkipParam psi) = psi.
Proof.
  intro psi.
  rewrite subst_rename.
  transitivity (subst (fun n => tVar n) psi).
  - apply subst_ext. intros [|n]; reflexivity.
  - apply subst_id.
Qed.

Lemma subst_up_succ_rename_rSkipParam : forall psi,
  subst (Term.upSubst substSuccVar) (rename rSkipParam psi) =
  rename rSkipParam psi.
Proof.
  intro psi.
  rewrite subst_rename.
  rewrite <- subst_var_rename.
  apply subst_ext.
  intros [|n]; reflexivity.
Qed.

Lemma substZero_hfStrongBelowAt : forall psi,
  subst substZero (hfStrongBelowAt psi) =
  pAll (pImp (ltTermAt (tVar 0) tZero) psi).
Proof.
  intro psi.
  unfold hfStrongBelowAt, ltAt, leAt, ltTermAt.
  simpl.
  rewrite subst_up_zero_rename_rSkipParam.
  reflexivity.
Qed.

Lemma substSuccVar_hfStrongBelowAt : forall psi,
  subst substSuccVar (hfStrongBelowAt psi) =
  pAll
    (pImp
      (ltTermAt (tVar 0) (tSucc (tVar 1)))
      (rename rSkipParam psi)).
Proof.
  intro psi.
  unfold hfStrongBelowAt, ltAt, leAt, ltTermAt.
  simpl.
  rewrite subst_up_succ_rename_rSkipParam.
  reflexivity.
Qed.

(** PA rendering of the unsealed Ackermann translation of HF set induction. *)
Definition translatedHFInductionBody (psi : formula) : formula :=
  pImp (hfHereditaryAt psi) (pAll psi).

(** Membership implies code order, parametrized by the one global arithmetic
    theorem needed by the translated-induction proof. *)
Lemma BProv_Ax_s_ltAt_of_hfMemAt_of_all :
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)) ->
  forall G elem set,
  BProv Ax_s G (hfMemAt elem set) ->
  BProv Ax_s G (ltAt elem set).
Proof.
  intros hall G elem set hmem.
  pose proof (BProv_allE Ax_s [] (hfMembersBelowAt 0)
    (tVar set) hall) as hsetRaw.
  rewrite subst_instTerm_var_hfMembersBelowAt_zero in hsetRaw.
  pose proof (BProv_weaken_nil Ax_s G (hfMembersBelowAt set) hsetRaw)
    as hset.
  exact (BProv_ltAt_of_hfMembersBelowAt Ax_s G elem set hset hmem).
Qed.

(** The hereditary premise yields [psi] at the current code once the strong
    induction accumulator supplies [psi] for every smaller code. *)
Lemma BProv_Ax_s_predicate_of_renamed_hereditary_and_strongBelow :
  forall (hmembersBelow : BProv Ax_s [] (pAll (hfMembersBelowAt 0))) G psi,
  BProv Ax_s G (rename S (hfHereditaryAt psi)) ->
  BProv Ax_s G (hfStrongBelowAt psi) ->
  BProv Ax_s G psi.
Proof.
  intros hmembersBelow G psi hhereditary hbelow.
  set (memberImp := pImp (hfMemAt 0 1) (rename rSkipParam psi)).
  assert (hstep : BProv Ax_s G (pImp (pAll memberImp) psi)).
  {
    pose proof (BProv_allE_current_of_renamed G
      (pImp (pAll memberImp) psi) hhereditary) as h.
    unfold memberImp in h.
    exact h.
  }
  assert (hmemberBody :
      BProv Ax_s (map (rename S) G) memberImp).
  {
    set (D := hfMemAt 0 1 :: map (rename S) G).
    assert (hmem : BProv Ax_s D (hfMemAt 0 1)).
    { apply BProv_ass_head. }
    assert (hlt : BProv Ax_s D (ltAt 0 1)).
    {
      exact (BProv_Ax_s_ltAt_of_hfMemAt_of_all
        hmembersBelow D 0 1 hmem).
    }
    assert (hbelowRen : BProv Ax_s (map (rename S) G)
        (rename S (hfStrongBelowAt psi))).
    {
      exact (BProv_rename_of_sentences Ax_s sentence_ax_s G
        (hfStrongBelowAt psi) hbelow S).
    }
    assert (hbelowBody : BProv Ax_s (map (rename S) G)
        (pImp (ltAt 0 1) (rename rSkipParam psi))).
    {
      exact (BProv_allE_current_of_renamed (map (rename S) G)
        (pImp (ltAt 0 1) (rename rSkipParam psi)) hbelowRen).
    }
    assert (hbelowBodyD : BProv Ax_s D
        (pImp (ltAt 0 1) (rename rSkipParam psi))).
    {
      unfold D.
      apply BProv_context_cons.
      exact hbelowBody.
    }
    assert (hpsi : BProv Ax_s D (rename rSkipParam psi)).
    {
      exact (BProv_mp Ax_s D (ltAt 0 1) (rename rSkipParam psi)
        hbelowBodyD hlt).
    }
    unfold D in hpsi.
    unfold memberImp.
    exact (BProv_impI Ax_s (map (rename S) G)
      (hfMemAt 0 1) (rename rSkipParam psi) hpsi).
  }
  assert (hmembers : BProv Ax_s G (pAll memberImp)).
  {
    exact (BProv_allI_of_sentences Ax_s G memberImp
      sentence_ax_s hmemberBody).
  }
  exact (BProv_mp Ax_s G (pAll memberImp) psi hstep hmembers).
Qed.

(** Strong induction on the current code, retaining an arbitrary context of
    persistent premises.  The local rule receives those premises in the
    renamed form appropriate below the induction variable.  This common shell
    is shared by ordinal range, ordinary HF induction, and finite-generation
    induction; only their local current-code rules differ. *)
Lemma BProv_Ax_s_all_of_strongStep_under : forall premises psi,
  (forall G,
    (forall premise, In premise premises ->
      BProv Ax_s G (rename S premise)) ->
    BProv Ax_s G (hfStrongBelowAt psi) ->
    BProv Ax_s G psi) ->
  BProv Ax_s premises (pAll psi).
Proof.
  intros premises psi hcurrent.
  set (below := hfStrongBelowAt psi).
  assert (hzero : BProv Ax_s premises (subst substZero below)).
  {
    unfold below.
    rewrite substZero_hfStrongBelowAt.
    set (lowLtZero := ltTermAt (tVar 0) tZero).
    assert (hbody : BProv Ax_s (map (rename S) premises)
        (pImp lowLtZero psi)).
    {
      set (D := lowLtZero :: map (rename S) premises).
      assert (hlt : BProv Ax_s D lowLtZero).
      { apply BProv_ass_head. }
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
      exact (BProv_impI Ax_s (map (rename S) premises)
        lowLtZero psi hpsi).
    }
    exact (BProv_allI_of_sentences Ax_s premises
      (pImp lowLtZero psi) sentence_ax_s hbody).
  }
  assert (hsuccBody : BProv Ax_s
      (below :: map (rename S) premises)
      (subst substSuccVar below)).
  {
    set (Sctx := below :: map (rename S) premises).
    assert (hbelowS : BProv Ax_s Sctx below).
    { apply BProv_ass_head. }
    assert (hpremisesS : forall premise, In premise premises ->
        BProv Ax_s Sctx (rename S premise)).
    {
      intros premise hpremise.
      apply BProv_ass.
      unfold Sctx. simpl. right.
      apply in_map. exact hpremise.
    }
    assert (hpsiCurrent : BProv Ax_s Sctx psi).
    {
      apply (hcurrent Sctx hpremisesS).
      unfold below in hbelowS. exact hbelowS.
    }
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
        { apply BProv_ass_head. }
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
          { apply BProv_ass_head. }
          assert (hbelowE : BProv Ax_s E
              (pImp (ltTermAt (tVar 0) (tVar 1)) psiAtLow)).
          {
            unfold E, D.
            apply BProv_context_two.
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
          { apply BProv_ass_head. }
          assert (hpsiRen : BProv Ax_s R (rename S psi)).
          {
            unfold R.
            exact (BProv_rename_of_sentences Ax_s sentence_ax_s Sctx
              psi hpsiCurrent S).
          }
          assert (hpsiE : BProv Ax_s E (rename S psi)).
          {
            unfold E, D.
            apply BProv_context_two.
            exact hpsiRen.
          }
          unfold psiAtLow.
          exact (BProv_predicate_current_of_eq_previous
            E psi heq hpsiE).
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
  assert (hsuccImp : BProv Ax_s (map (rename S) premises)
      (pImp below (subst substSuccVar below))).
  {
    exact (BProv_impI Ax_s (map (rename S) premises) below
      (subst substSuccVar below) hsuccBody).
  }
  assert (hsucc : BProv Ax_s premises
      (pAll (pImp below (subst substSuccVar below)))).
  {
    exact (BProv_allI_of_sentences Ax_s premises
      (pImp below (subst substSuccVar below)) sentence_ax_s hsuccImp).
  }
  assert (hallBelow : BProv Ax_s premises (pAll below)).
  { exact (BProv_Ax_s_induction_rule premises below hzero hsucc). }
  set (Q := map (rename S) premises).
  assert (hpremisesQ : forall premise, In premise premises ->
      BProv Ax_s Q (rename S premise)).
  {
    intros premise hpremise.
    apply BProv_ass.
    unfold Q. apply in_map. exact hpremise.
  }
  assert (hallBelowRen : BProv Ax_s Q (rename S (pAll below))).
  {
    unfold Q.
    exact (BProv_rename_of_sentences Ax_s sentence_ax_s premises
      (pAll below) hallBelow S).
  }
  assert (hbelowQ : BProv Ax_s Q below).
  { exact (BProv_allE_current_of_renamed Q below hallBelowRen). }
  assert (hpsiBody : BProv Ax_s Q psi).
  {
    apply (hcurrent Q hpremisesQ).
    unfold below in hbelowQ. exact hbelowQ.
  }
  unfold Q in hpsiBody.
  exact (BProv_allI_of_sentences Ax_s premises psi
    sentence_ax_s hpsiBody).
Qed.

(** Ordinary PA induction on the cumulative strict-prefix predicate proves
    the unsealed translated HF set-induction body. *)
Lemma BProv_Ax_s_translatedHFInductionBody_of_all_hfMembersBelowAt :
  forall (hmembersBelow : BProv Ax_s [] (pAll (hfMembersBelowAt 0))) psi,
  BProv Ax_s [] (translatedHFInductionBody psi).
Proof.
  intros hmembersBelow psi.
  set (hereditary := hfHereditaryAt psi).
  assert (hallPsi : BProv Ax_s [hereditary] (pAll psi)).
  {
    apply (BProv_Ax_s_all_of_strongStep_under [hereditary] psi).
    intros G hpremises hbelow.
    apply (BProv_Ax_s_predicate_of_renamed_hereditary_and_strongBelow
      hmembersBelow G psi).
    - exact (hpremises hereditary (or_introl eq_refl)).
    - exact hbelow.
  }
  unfold translatedHFInductionBody.
  unfold hereditary in hallPsi.
  exact (BProv_impI Ax_s [] (hfHereditaryAt psi) (pAll psi) hallPsi).
Qed.

Lemma hfFormulaAt_HF_induction_form : forall phi,
  hfFormulaAt (fun n : nat => n) (HF_induction_form phi) =
  translatedHFInductionBody
    (hfFormulaAt (fun n : nat => n) phi).
Proof.
  intro phi.
  unfold HF_induction_form, translatedHFInductionBody, hfHereditaryAt.
  simpl.
  repeat rewrite hfUpVarMap_id.
  rewrite hfFormulaAt_id_rename.
  reflexivity.
Qed.

Lemma hfFormulaAt_closeN_id : forall k phi,
  hfFormulaAt (fun n : nat => n) (Fol.closeN k phi) =
  PA.Formula.closeN k (hfFormulaAt (fun n : nat => n) phi).
Proof.
  induction k as [|k IH]; intro phi.
  - reflexivity.
  - simpl.
    rewrite IH.
    change (PA.Formula.closeN k
      (pAll (hfFormulaAt (hfUpVarMap (fun n : nat => n)) phi)) =
      PA.Formula.closeN k
      (pAll (hfFormulaAt (fun n : nat => n) phi))).
    rewrite hfUpVarMap_id.
    reflexivity.
Qed.

Lemma translateHFFormula_sealed_induction : forall phi,
  translateHFFormula (Fol.seal (HF_induction_form phi)) =
  PA.Formula.closeN (Fol.bound (HF_induction_form phi))
    (translatedHFInductionBody
      (hfFormulaAt (fun n : nat => n) phi)).
Proof.
  intro phi.
  unfold translateHFFormula, Fol.seal.
  rewrite hfFormulaAt_closeN_id.
  rewrite hfFormulaAt_HF_induction_form.
  reflexivity.
Qed.

(** Full closed translated HF induction, conditional only on the uniform
    Ackermann membership-order theorem. *)
Lemma BProv_Ax_s_translated_HF_induction_of_all_hfMembersBelowAt :
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)) ->
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_induction_form phi))).
Proof.
  intros hmembersBelow phi.
  set (psi := hfFormulaAt (fun n : nat => n) phi).
  assert (hbody : BProv Ax_s [] (translatedHFInductionBody psi)).
  {
    exact (BProv_Ax_s_translatedHFInductionBody_of_all_hfMembersBelowAt
      hmembersBelow psi).
  }
  assert (hclosed : BProv Ax_s []
      (PA.Formula.closeN (Fol.bound (HF_induction_form phi))
        (translatedHFInductionBody psi))).
  {
    exact (BProv_closeN_nil_of_sentences Ax_s sentence_ax_s
      (Fol.bound (HF_induction_form phi))
      (translatedHFInductionBody psi) hbody).
  }
  rewrite translateHFFormula_sealed_induction.
  unfold psi in hclosed.
  exact hclosed.
Qed.
