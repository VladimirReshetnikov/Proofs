(* ===================================================================== *)
(*  PAHFMembershipTail.v                                                 *)
(*                                                                       *)
(*  Term-parametric beta-trace adapters used to prove that successor     *)
(*  membership descends through a binary head step.                      *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import
  PAHF PAHFTranslatedHFFin PAHFMembershipBound PAHFMembershipBoundSucc.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Eliminate code and step witnesses after an arbitrary substitution has
    already been applied to term-parametric membership. *)
Lemma BProv_Ax_s_subst_hfMemTermAt_elim_opened_code_step :
  forall G target elem setCode sigma,
  BProv Ax_s G (subst sigma (hfMemTermAt elem setCode)) ->
  (let bitBody :=
      pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (S (S (S elem)))) in
   let tail :=
      pAnd (betaDiv2StepsThroughAt 1 0 (S (S elem))) (pEx bitBody) in
   let body :=
      pAnd
        (betaTermAtConstIdx
          (Term.rename S (Term.rename S setCode)) 1 0 0)
        tail in
   let stepEx := subst (Term.upSubst sigma) (pEx body) in
   let openedBody := subst (Term.upSubst (Term.upSubst sigma)) body in
   BProv Ax_s
     (openedBody :: map (rename S) (stepEx :: map (rename S) G))
     (rename S (rename S target))) ->
  BProv Ax_s G target.
Proof.
  intros G target elem setCode sigma hmem hopened.
  set (bitBody :=
    pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (S (S (S elem))))).
  set (tail :=
    pAnd (betaDiv2StepsThroughAt 1 0 (S (S elem))) (pEx bitBody)).
  set (body :=
    pAnd
      (betaTermAtConstIdx
        (Term.rename S (Term.rename S setCode)) 1 0 0)
      tail).
  set (stepEx := subst (Term.upSubst sigma) (pEx body)).
  set (openedBody := subst (Term.upSubst (Term.upSubst sigma)) body).
  assert (hmem' : BProv Ax_s G (pEx stepEx)).
  {
    unfold hfMemTermAt in hmem.
    unfold stepEx, openedBody, body, tail, bitBody.
    exact hmem.
  }
  assert (houter : BProv Ax_s
      (stepEx :: map (rename S) G) (rename S target)).
  {
    set (D1 := stepEx :: map (rename S) G).
    assert (hex : BProv Ax_s D1 stepEx).
    { apply BProv_ass. unfold D1. simpl. left. reflexivity. }
    unfold stepEx in hex.
    apply (BProv_exE_of_sentences Ax_s D1 openedBody
      (rename S target) sentence_ax_s hex).
    unfold D1.
    exact hopened.
  }
  exact (BProv_exE_of_sentences Ax_s G stepEx target
    sentence_ax_s hmem' houter).
Qed.

(** Recover a fully term-parametric beta entry from its term-indexed wrapper. *)
Lemma BProv_Ax_s_betaTermTermAt_of_betaTermAtTermIdx :
  forall G out idxTerm code step,
  BProv Ax_s G (betaTermAtTermIdx out code step idxTerm) ->
  BProv Ax_s G
    (betaTermTermAt out (tVar code) (tVar step) idxTerm).
Proof.
  intros G out idxTerm code step hbeta.
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm))
    (betaTermAt (Term.rename S out) (S code) (S step) 0)).
  assert (hbody : BProv Ax_s (body :: map (rename S) G)
      (rename S
        (betaTermTermAt out (tVar code) (tVar step) idxTerm))).
  {
    set (C := body :: map (rename S) G).
    assert (hidxSlot : BProv Ax_s C
        (pEq (tVar 0) (Term.rename S idxTerm))).
    {
      unfold C, body.
      exact (BProv_Ax_s_betaTermAtTermIdx_opened_body_idx
        G out idxTerm code step).
    }
    assert (hraw : BProv Ax_s C
        (betaTermAt (Term.rename S out) (S code) (S step) 0)).
    {
      unfold C, body.
      exact (BProv_Ax_s_betaTermAtTermIdx_opened_body_beta
        G out idxTerm code step).
    }
    assert (hrawTerm : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (tVar (S code)) (tVar (S step)) (tVar 0))).
    { rewrite <- betaTermAt_eq_betaTermTermAt_var. exact hraw. }
    assert (htarget : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (tVar (S code)) (tVar (S step))
          (Term.rename S idxTerm))).
    {
      exact (BProv_Ax_s_betaTermTermAt_of_eq_index C
        (Term.rename S out) (tVar (S code)) (tVar (S step))
        (tVar 0) (Term.rename S idxTerm) hidxSlot hrawTerm).
    }
    unfold body, betaTermTermAt, remTermTermAt, ltTermAt,
      betaModTermTerm in *.
    simpl in *.
    repeat rewrite Term.rename_comp in *.
    exact htarget.
  }
  unfold betaTermAtTermIdx in hbeta.
  unfold body in hbody.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaTermAt (Term.rename S out) (S code) (S step) 0))
    (betaTermTermAt out (tVar code) (tVar step) idxTerm)
    sentence_ax_s hbeta hbody).
Qed.

(** Eliminate a term-bounded beta-halving trace at an arbitrary index term. *)
Lemma BProv_Ax_s_betaDiv2StepsThroughTermAt_step_termIdx_of_leTerm :
  forall G code step idxTerm lastTerm,
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt code step lastTerm) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step idxTerm).
Proof.
  intros G code step idxTerm lastTerm hsteps hle.
  set (rawWitness := betaDiv2StepWitnessAt (S code) (S step) 0).
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm)) rawWitness).
  pose proof (BProv_allE Ax_s G
    (pImp (leTermAt (tVar 0) (Term.rename S lastTerm)) rawWitness)
    idxTerm hsteps) as himpRaw.
  assert (himp : BProv Ax_s G
      (pImp (leTermAt idxTerm lastTerm)
        (subst (instTerm idxTerm) rawWitness))).
  {
    unfold rawWitness, leTermAt in *.
    simpl in *.
    repeat rewrite Term.rename_comp in *.
    repeat rewrite term_subst_instTerm_rename_succ in *.
    repeat rewrite term_subst_instTerm_rename_two_succ in *.
    repeat rewrite term_subst_upSubst_instTerm_rename_two_succ in *.
    repeat rewrite term_subst_upSubst_instTerm_rename_three_succ in *.
    repeat rewrite term_subst_up_up_instTerm_rename_four_succ in *.
    exact himpRaw.
  }
  assert (hwitSubst : BProv Ax_s G
      (subst (instTerm idxTerm) rawWitness)).
  {
    exact (BProv_mp Ax_s G (leTermAt idxTerm lastTerm)
      (subst (instTerm idxTerm) rawWitness) himp hle).
  }
  assert (hidxInst : BProv Ax_s G
      (subst (instTerm idxTerm)
        (pEq (tVar 0) (Term.rename S idxTerm)))).
  {
    simpl.
    rewrite term_subst_instTerm_rename_succ.
    apply BProv_eqRefl.
  }
  assert (hbody : BProv Ax_s G (subst (instTerm idxTerm) body)).
  {
    unfold body.
    exact (BProv_andI Ax_s G _ _ hidxInst hwitSubst).
  }
  unfold betaDiv2StepWitnessAtTermIdx, body, rawWitness.
  exact (BProv_exI Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaDiv2StepWitnessAt (S code) (S step) 0))
    idxTerm hbody).
Qed.

Lemma BProv_Ax_s_betaDiv2StepsThroughTermAt_step_succ_termIdx_of_leTerm :
  forall G code step idxTerm lastTerm,
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt code step (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step (tSucc idxTerm)).
Proof.
  intros G code step idxTerm lastTerm hsteps hle.
  apply (BProv_Ax_s_betaDiv2StepsThroughTermAt_step_termIdx_of_leTerm
    G code step (tSucc idxTerm) (tSucc lastTerm) hsteps).
  exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle).
Qed.

(** Package explicit term-parametric beta entries and a halving equation. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components :
  forall G code step idx cur next bit,
  BProv Ax_s G (betaTermTermAt cur code step idx) ->
  BProv Ax_s G (betaTermTermAt next code step (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2StepWitnessTermAt code step idx).
Proof.
  intros G code step idx cur next bit hcur hnext hdiv.
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename (fun n => n + 3) code)
      (Term.rename (fun n => n + 3) step)
      (Term.rename (fun n => n + 3) idx))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 3) code)
        (Term.rename (fun n => n + 3) step)
        (tSucc (Term.rename (fun n => n + 3) idx)))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hcurBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 2)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (Term.rename (fun n => n + 3) idx)))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 2)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (Term.rename (fun n => n + 3) idx)))))
      with (betaTermTermAt cur code step idx).
    - exact hcur.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_two_var_zero.
      repeat rewrite term_subst_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_five_succ.
      repeat rewrite Term.rename_comp.
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three step cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three code cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three idx cur next bit).
      reflexivity.
  }
  assert (hnextBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 1)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (tSucc (Term.rename (fun n => n + 3) idx))))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 1)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (tSucc (Term.rename (fun n => n + 3) idx))))))
      with (betaTermTermAt next code step (tSucc idx)).
    - exact hnext.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_two_var_zero.
      repeat rewrite term_subst_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_five_succ.
      repeat rewrite Term.rename_comp.
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three step cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three code cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three idx cur next bit).
      reflexivity.
  }
  assert (hdivBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))))
      with (div2StepTermAt cur next bit).
    - exact hdiv.
    - unfold div2StepTermAt, boolTermAt.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_rename_up_succ_rename_succ.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_two_var_zero.
      repeat rewrite term_subst_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_four_succ.
      repeat rewrite term_subst_up_up_up_instTerm_rename_five_succ.
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (htailBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (pAnd
              (betaTermTermAt (tVar 1)
                (Term.rename (fun n => n + 3) code)
                (Term.rename (fun n => n + 3) step)
                (tSucc (Term.rename (fun n => n + 3) idx)))
              (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))))))).
  { simpl. exact (BProv_andI Ax_s G _ _ hnextBody hdivBody). }
  assert (hbody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur))) body)))).
  { unfold body. simpl. exact (BProv_andI Ax_s G _ _ hcurBody htailBody). }
  assert (hbitEx : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur)) (pEx body)))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm next))
        (subst (Term.upSubst (Term.upSubst (instTerm cur))) body))
      bit hbody).
  }
  assert (hnextEx : BProv Ax_s G
      (subst (instTerm cur) (pEx (pEx body)))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm cur)) (pEx body))
      next hbitEx).
  }
  unfold betaDiv2StepWitnessTermAt, body.
  exact (BProv_exI Ax_s G (pEx (pEx
    (pAnd
      (betaTermTermAt (tVar 2)
        (Term.rename (fun n => n + 3) code)
        (Term.rename (fun n => n + 3) step)
        (Term.rename (fun n => n + 3) idx))
      (pAnd
        (betaTermTermAt (tVar 1)
          (Term.rename (fun n => n + 3) code)
          (Term.rename (fun n => n + 3) step)
          (tSucc (Term.rename (fun n => n + 3) idx)))
        (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))))))
    cur hnextEx).
Qed.

(** Copy one opened old binary step into the shifted beta trace. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_components :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm cur next bit,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaTermTermAt cur (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaTermTermAt next (tVar oldCode) (tVar oldStep)
      (tSucc (tSucc idxTerm))) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    cur next bit htail hle hcurOld hnextOld hdiv.
  assert (hleCurrent : BProv Ax_s G
      (leTermAt idxTerm (tSucc lastTerm))).
  {
    exact (BProv_Ax_s_leTermAt_trans G idxTerm lastTerm
      (tSucc lastTerm) hle
      (BProv_Ax_s_leTermAt_self_succ G lastTerm)).
  }
  assert (hcurNew : BProv Ax_s G
      (betaTermTermAt cur newCode newStep idxTerm)).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      idxTerm cur htail hleCurrent hcurOld).
  }
  assert (hleNext : BProv Ax_s G
      (leTermAt (tSucc idxTerm) (tSucc lastTerm))).
  { exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle). }
  assert (hnextNew : BProv Ax_s G
      (betaTermTermAt next newCode newStep (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      (tSucc idxTerm) next htail hleNext hnextOld).
  }
  exact (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
    G newCode newStep idxTerm cur next bit hcurNew hnextNew hdiv).
Qed.

(** Package explicit term-parametric entries as a beta bit read. *)
Lemma BProv_Ax_s_betaDiv2BitTermAt_of_components :
  forall G bit code step idx cur next,
  BProv Ax_s G (betaTermTermAt cur code step idx) ->
  BProv Ax_s G (betaTermTermAt next code step (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2BitTermAt bit code step idx).
Proof.
  intros G bit code step idx cur next hcur hnext hdiv.
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename (fun n => n + 2) code)
      (Term.rename (fun n => n + 2) step)
      (Term.rename (fun n => n + 2) idx))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename (fun n => n + 2) code)
        (Term.rename (fun n => n + 2) step)
        (tSucc (Term.rename (fun n => n + 2) idx)))
      (div2StepTermAt (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) bit)))).
  assert (hcurBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 1)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (Term.rename (fun n => n + 2) idx))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 1)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (Term.rename (fun n => n + 2) idx))))
      with (betaTermTermAt cur code step idx).
    - exact hcur.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite Term.rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two code cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two step cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two idx cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (hnextBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (tSucc (Term.rename (fun n => n + 2) idx)))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (tSucc (Term.rename (fun n => n + 2) idx)))))
      with (betaTermTermAt next code step (tSucc idx)).
    - exact hnext.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite Term.rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two code cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two step cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two idx cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (hdivBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (div2StepTermAt (tVar 1) (tVar 0)
            (Term.rename (fun n => n + 2) bit))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (div2StepTermAt (tVar 1) (tVar 0)
            (Term.rename (fun n => n + 2) bit))))
      with (div2StepTermAt cur next bit).
    - exact hdiv.
    - unfold div2StepTermAt, boolTermAt.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_rename_up_succ_rename_succ.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
      repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
      repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
      repeat rewrite Term.rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two bit cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (htailBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (pAnd
            (betaTermTermAt (tVar 0)
              (Term.rename (fun n => n + 2) code)
              (Term.rename (fun n => n + 2) step)
              (tSucc (Term.rename (fun n => n + 2) idx)))
            (div2StepTermAt (tVar 1) (tVar 0)
              (Term.rename (fun n => n + 2) bit)))))).
  { simpl. exact (BProv_andI Ax_s G _ _ hnextBody hdivBody). }
  assert (hbody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur)) body))).
  { unfold body. simpl. exact (BProv_andI Ax_s G _ _ hcurBody htailBody). }
  assert (hnextEx : BProv Ax_s G
      (subst (instTerm cur) (pEx body))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm cur)) body) next hbody).
  }
  unfold betaDiv2BitTermAt, body.
  exact (BProv_exI Ax_s G (pEx
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) code)
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) idx))
      (pAnd
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) code)
          (Term.rename (fun n => n + 2) step)
          (tSucc (Term.rename (fun n => n + 2) idx)))
        (div2StepTermAt (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) bit))))) cur hnextEx).
Qed.

Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_components :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm
    bit cur next,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaTermTermAt cur (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaTermTermAt next (tVar oldCode) (tVar oldStep)
      (tSucc (tSucc idxTerm))) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2BitTermAt bit newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    bit cur next htail hle hcurOld hnextOld hdiv.
  assert (hleCurrent : BProv Ax_s G
      (leTermAt idxTerm (tSucc lastTerm))).
  {
    exact (BProv_Ax_s_leTermAt_trans G idxTerm lastTerm
      (tSucc lastTerm) hle
      (BProv_Ax_s_leTermAt_self_succ G lastTerm)).
  }
  assert (hcurNew : BProv Ax_s G
      (betaTermTermAt cur newCode newStep idxTerm)).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      idxTerm cur htail hleCurrent hcurOld).
  }
  assert (hleNext : BProv Ax_s G
      (leTermAt (tSucc idxTerm) (tSucc lastTerm))).
  { exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle). }
  assert (hnextNew : BProv Ax_s G
      (betaTermTermAt next newCode newStep (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      (tSucc idxTerm) next htail hleNext hnextOld).
  }
  exact (BProv_Ax_s_betaDiv2BitTermAt_of_components
    G bit newCode newStep idxTerm cur next hcurNew hnextNew hdiv).
Qed.

Lemma rename_S_betaShiftTailThroughTermAt :
  forall oldCode oldStep newCode newStep lastTerm,
  rename S
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep lastTerm) =
  betaShiftTailThroughTermAt (S oldCode) (S oldStep)
    (Term.rename S newCode) (Term.rename S newStep)
    (Term.rename S lastTerm).
Proof.
  intros oldCode oldStep newCode newStep lastTerm.
  unfold betaShiftTailThroughTermAt, betaTermTermAt,
    remTermTermAt, ltTermAt, betaModTermTerm, leTermAt.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hup2Add2 : forall n,
      Fol.up (Fol.up S) (n + 2) = S (n + 2)).
  {
    intro n.
    replace (n + 2) with (S (S n)) by lia.
    reflexivity.
  }
  repeat rewrite hup2Add2.
  assert (hlast :
      Term.rename (fun n => Fol.up (Fol.up S) (S (S n))) lastTerm =
      Term.rename (fun n => S (S (S n))) lastTerm).
  {
    apply Term.rename_ext. intro n. reflexivity.
  }
  rewrite hlast.
  assert (hstep :
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up S)) (S (n + 2))) newStep =
      Term.rename (fun n => S (S n + 2)) newStep).
  {
    apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  rewrite hstep.
  assert (hcode :
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (S (n + 2)))) newCode =
      Term.rename (fun n => S (S (S n + 2))) newCode).
  {
    apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  rewrite hcode.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2StepWitnessTermAt :
  forall code step idx,
  rename S (betaDiv2StepWitnessTermAt code step idx) =
  betaDiv2StepWitnessTermAt
    (Term.rename S code) (Term.rename S step) (Term.rename S idx).
Proof.
  intros code step idx.
  unfold betaDiv2StepWitnessTermAt, betaTermTermAt,
    remTermTermAt, div2StepTermAt, boolTermAt, ltTermAt,
    betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (n + 3))) t =
      Term.rename (fun n => S (S n + 3)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 3) with (S (S (S n))) by lia.
    replace (S n + 3) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up (Fol.up S))))
          (S (S (n + 3)))) t =
      Term.rename (fun n => S (S (S n + 3))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 3) with (S (S (S n))) by lia.
    replace (S n + 3) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2BitTermAt :
  forall bit code step idx,
  rename S (betaDiv2BitTermAt bit code step idx) =
  betaDiv2BitTermAt (Term.rename S bit) (Term.rename S code)
    (Term.rename S step) (Term.rename S idx).
Proof.
  intros bit code step idx.
  unfold betaDiv2BitTermAt, betaTermTermAt, remTermTermAt,
    div2StepTermAt, boolTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up S)) (S (n + 2))) t =
      Term.rename (fun n => S (S n + 2)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (S (n + 2)))) t =
      Term.rename (fun n => S (S (S n + 2))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  assert (hbit : forall t,
      Term.rename (fun n => Fol.up (Fol.up S) (n + 2)) t =
      Term.rename (fun n => S n + 2) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hbit.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2BitOneTermExAt :
  forall code step idx,
  rename S (betaDiv2BitOneTermExAt code step idx) =
  betaDiv2BitOneTermExAt
    (Term.rename S code) (Term.rename S step) (Term.rename S idx).
Proof.
  intros code step idx.
  unfold betaDiv2BitOneTermExAt, oneAt, zeroAt, eqConstAt,
    betaDiv2BitTermAt, betaTermTermAt, remTermTermAt,
    div2StepTermAt, boolTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (S n + 2))) t =
      Term.rename (fun n => S (S (S n) + 2)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (S n + 2) with (S (S (S n))) by lia.
    replace (S (S n) + 2) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up (Fol.up S))))
          (S (S (S n + 2)))) t =
      Term.rename (fun n => S (S (S (S n) + 2))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (S n + 2) with (S (S (S n))) by lia.
    replace (S (S n) + 2) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  reflexivity.
Qed.

Lemma rename_S_betaTermTermAt :
  forall out code step idx,
  rename S (betaTermTermAt out code step idx) =
  betaTermTermAt (Term.rename S out) (Term.rename S code)
    (Term.rename S step) (Term.rename S idx).
Proof.
  intros out code step idx.
  unfold betaTermTermAt, remTermTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2StepsThroughTermAt :
  forall code step lastTerm,
  rename S (betaDiv2StepsThroughTermAt code step lastTerm) =
  betaDiv2StepsThroughTermAt (S code) (S step)
    (Term.rename S lastTerm).
Proof.
  intros code step lastTerm.
  unfold betaDiv2StepsThroughTermAt, leTermAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAt, remAt, ltAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_of_betaAt_eq_index :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaAt out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaTermTermAt (tVar out) (tVar code) (tVar step) idxTerm).
Proof.
  intros G out code step idx idxTerm hbeta hidx.
  assert (hraw : BProv Ax_s G
      (betaTermTermAt (tVar out) (tVar code) (tVar step)
        (tVar idx))).
  {
    rewrite <- betaTermAt_eq_betaTermTermAt_var.
    rewrite betaTermAt_var.
    exact hbeta.
  }
  exact (BProv_Ax_s_betaTermTermAt_of_eq_index G
    (tVar out) (tVar code) (tVar step) (tVar idx) idxTerm
    (BProv_eqSym Ax_s G idxTerm (tVar idx) hidx) hraw).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_succ_of_betaTermTermAtSuccIdx_eq_term :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaTermTermAtSuccIdx out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G (betaTermTermAt out code step (tSucc idxTerm)).
Proof.
  intros G out code step idx idxTerm hwrap hidx.
  set (target := betaTermTermAt out code step (tSucc idxTerm)).
  set (body := pAnd
    (pEq (tVar 0) (tSucc (tVar (S idx))))
    (betaTermTermAt (Term.rename S out)
      (Term.rename S code) (Term.rename S step) (tVar 0))).
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hslot : BProv Ax_s C
        (pEq (tVar 0) (tSucc (tVar (S idx))))).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (hraw : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (Term.rename S code) (Term.rename S step) (tVar 0))).
    { exact (BProv_andE2 Ax_s C _ _ hbody). }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
      _ hidx S) as hidxRen.
    simpl in hidxRen.
    assert (hidxC : BProv Ax_s C
        (pEq (Term.rename S idxTerm) (tVar (S idx)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G) body _ hidxRen).
    }
    assert (hsuccIdx : BProv Ax_s C
        (pEq (tSucc (Term.rename S idxTerm))
          (tSucc (tVar (S idx))))).
    { exact (BProv_eq_congr_succ Ax_s C _ _ hidxC). }
    assert (hidxForRaw : BProv Ax_s C
        (pEq (tVar 0) (tSucc (Term.rename S idxTerm)))).
    {
      exact (BProv_eqTrans Ax_s C _ _ _ hslot
        (BProv_eqSym Ax_s C _ _ hsuccIdx)).
    }
    assert (htarget : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (Term.rename S code) (Term.rename S step)
          (tSucc (Term.rename S idxTerm)))).
    {
      exact (BProv_Ax_s_betaTermTermAt_of_eq_index C
        (Term.rename S out) (Term.rename S code) (Term.rename S step)
        (tVar 0) (tSucc (Term.rename S idxTerm)) hidxForRaw hraw).
    }
    unfold target.
    rewrite rename_S_betaTermTermAt.
    simpl.
    exact htarget.
  }
  unfold betaTermTermAtSuccIdx in hwrap.
  unfold body in hopened.
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (tSucc (tVar (S idx))))
      (betaTermTermAt (Term.rename S out)
        (Term.rename S code) (Term.rename S step) (tVar 0)))
    (betaTermTermAt out code step (tSucc idxTerm))
    sentence_ax_s hwrap hopened).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_succ_of_betaAtSuccIdx_eq_index :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaAtSuccIdx out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaTermTermAt (tVar out) (tVar code) (tVar step)
      (tSucc idxTerm)).
Proof.
  intros G out code step idx idxTerm hbeta hidx.
  assert (hwrap : BProv Ax_s G
      (betaTermTermAtSuccIdx
        (tVar out) (tVar code) (tVar step) idx)).
  {
    replace (betaTermTermAtSuccIdx
        (tVar out) (tVar code) (tVar step) idx)
      with (betaAtSuccIdx out code step idx) by reflexivity.
    exact hbeta.
  }
  exact
    (BProv_Ax_s_betaTermTermAt_succ_of_betaTermTermAtSuccIdx_eq_term
      G (tVar out) (tVar code) (tVar step) idx idxTerm hwrap hidx).
Qed.

(** Convert a legacy slot-indexed three-witness step to the fully
    term-parametric form, transporting its index through a PA equality. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessAt_to_termAt_of_idxEq :
  forall G code step idx idxTerm,
  BProv Ax_s G (betaDiv2StepWitnessAt code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar code) (tVar step) idxTerm).
Proof.
  intros G code step idx idxTerm hwitness hidx.
  set (target := betaDiv2StepWitnessTermAt
    (tVar code) (tVar step) idxTerm).
  set (body := pAnd
    (betaAt 2 (S (S (S code))) (S (S (S step)))
      (S (S (S idx))))
    (pAnd
      (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
        (S (S (S idx))))
      (div2StepAt 2 1 0))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  { unfold betaDiv2StepWitnessAt in hwitness. unfold body. exact hwitness. }
  assert (houter : BProv Ax_s
      (pEx (pEx body) :: map (rename S) G)
      (rename S target)).
  {
    set (G1 := pEx (pEx body) :: map (rename S) G).
    assert (hex2 : BProv Ax_s G1 (pEx (pEx body))).
    { apply BProv_ass. unfold G1. simpl. left. reflexivity. }
    assert (hmid : BProv Ax_s
        (pEx body :: map (rename S) G1)
        (rename S (rename S target))).
    {
      set (G2 := pEx body :: map (rename S) G1).
      assert (hex3 : BProv Ax_s G2 (pEx body)).
      { apply BProv_ass. unfold G2. simpl. left. reflexivity. }
      assert (hinner : BProv Ax_s
          (body :: map (rename S) G2)
          (rename S (rename S (rename S target)))).
      {
        set (C := body :: map (rename S) G2).
        set (idx3 := Term.rename S (Term.rename S (Term.rename S idxTerm))).
        assert (hbody : BProv Ax_s C body).
        { apply BProv_ass. unfold C. simpl. left. reflexivity. }
        assert (hcurRaw : BProv Ax_s C
            (betaAt 2 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))))).
        { exact (BProv_andE1 Ax_s C _ _ hbody). }
        assert (htailBody : BProv Ax_s C
            (pAnd
              (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
                (S (S (S idx))))
              (div2StepAt 2 1 0))).
        { exact (BProv_andE2 Ax_s C _ _ hbody). }
        assert (hnextRaw : BProv Ax_s C
            (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))))).
        { exact (BProv_andE1 Ax_s C _ _ htailBody). }
        assert (hdivRaw : BProv Ax_s C (div2StepAt 2 1 0)).
        { exact (BProv_andE2 Ax_s C _ _ htailBody). }
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
          _ hidx S) as hidxRen1.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) G) _ hidxRen1 S) as hidxRen2.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) (map (rename S) G)) _ hidxRen2 S)
          as hidxRen3.
        simpl in hidxRen3.
        pose proof (BProv_context_cons Ax_s
          (map (rename S) (map (rename S) (map (rename S) G)))
          (rename S (rename S (pEx (pEx body)))) _ hidxRen3) as hi4.
        pose proof (BProv_context_cons Ax_s _
          (rename S (pEx body)) _ hi4) as hi5.
        pose proof (BProv_context_cons Ax_s _ body _ hi5) as hi6.
        assert (hidxC : BProv Ax_s C
            (pEq idx3 (tVar (S (S (S idx)))))).
        {
          unfold C, G2, G1, idx3.
          exact hi6.
        }
        assert (hcurTerm : BProv Ax_s C
            (betaTermTermAt (tVar 2)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              idx3)).
        {
          exact (BProv_Ax_s_betaTermTermAt_of_betaAt_eq_index C
            2 (S (S (S code))) (S (S (S step)))
            (S (S (S idx))) idx3 hcurRaw hidxC).
        }
        assert (hnextTerm : BProv Ax_s C
            (betaTermTermAt (tVar 1)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              (tSucc idx3))).
        {
          exact
            (BProv_Ax_s_betaTermTermAt_succ_of_betaAtSuccIdx_eq_index C
              1 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))) idx3 hnextRaw hidxC).
        }
        assert (hdivTerm : BProv Ax_s C
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
        {
          replace (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))
            with (div2StepAt 2 1 0) by reflexivity.
          exact hdivRaw.
        }
        pose proof (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
          C (tVar (S (S (S code)))) (tVar (S (S (S step))))
          idx3 (tVar 2) (tVar 1) (tVar 0)
          hcurTerm hnextTerm hdivTerm) as hpacked.
        unfold target.
        repeat rewrite rename_S_betaDiv2StepWitnessTermAt.
        unfold C, G2, G1, idx3.
        simpl.
        exact hpacked.
      }
      exact (BProv_exE_of_sentences Ax_s G2 body
        (rename S (rename S target)) sentence_ax_s hex3 hinner).
    }
    exact (BProv_exE_of_sentences Ax_s G1 (pEx body)
      (rename S target) sentence_ax_s hex2 hmid).
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G (pEx (pEx body))
    (betaDiv2StepWitnessTermAt (tVar code) (tVar step) idxTerm)
    sentence_ax_s hwit houter).
Qed.

(** Remove the outer term-index wrapper around a legacy step witness. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_to_termAt :
  forall G code step idxTerm,
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step idxTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar code) (tVar step) idxTerm).
Proof.
  intros G code step idxTerm hwitness.
  set (target := betaDiv2StepWitnessTermAt
    (tVar code) (tVar step) idxTerm).
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm))
    (betaDiv2StepWitnessAt (S code) (S step) 0)).
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hidx : BProv Ax_s C
        (pEq (tVar 0) (Term.rename S idxTerm))).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (hwitRaw : BProv Ax_s C
        (betaDiv2StepWitnessAt (S code) (S step) 0)).
    { exact (BProv_andE2 Ax_s C _ _ hbody). }
    assert (hterm : BProv Ax_s C
        (betaDiv2StepWitnessTermAt
          (tVar (S code)) (tVar (S step))
          (Term.rename S idxTerm))).
    {
      exact (BProv_Ax_s_betaDiv2StepWitnessAt_to_termAt_of_idxEq C
        (S code) (S step) 0 (Term.rename S idxTerm)
        hwitRaw (BProv_eqSym Ax_s C _ _ hidx)).
    }
    unfold target.
    rewrite rename_S_betaDiv2StepWitnessTermAt.
    simpl.
    exact hterm.
  }
  unfold betaDiv2StepWitnessAtTermIdx in hwitness.
  unfold body in hopened.
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaDiv2StepWitnessAt (S code) (S step) 0))
    (betaDiv2StepWitnessTermAt (tVar code) (tVar step) idxTerm)
    sentence_ax_s hwitness hopened).
Qed.

(** Open an old three-witness beta step and copy it one position down the
    shifted trace. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldWitness :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar oldCode) (tVar oldStep) (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hle hwitness.
  set (target :=
    betaDiv2StepWitnessTermAt newCode newStep idxTerm).
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename S (Term.rename S (Term.rename S (tVar oldCode))))
      (Term.rename S (Term.rename S (Term.rename S (tVar oldStep))))
      (Term.rename S (Term.rename S (Term.rename S (tSucc idxTerm)))))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename S (Term.rename S (Term.rename S (tVar oldCode))))
        (Term.rename S (Term.rename S (Term.rename S (tVar oldStep))))
        (tSucc
          (Term.rename S (Term.rename S (Term.rename S (tSucc idxTerm))))))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  {
    unfold betaDiv2StepWitnessTermAt in hwitness.
    unfold body.
    assert (hrename3 : forall t,
        Term.rename (fun n => n + 3) t =
        Term.rename S (Term.rename S (Term.rename S t))).
    {
      intro t.
      repeat rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    repeat rewrite hrename3 in hwitness.
    exact hwitness.
  }
  assert (houter : BProv Ax_s
      (pEx (pEx body) :: map (rename S) G)
      (rename S target)).
  {
    set (G1 := pEx (pEx body) :: map (rename S) G).
    assert (hex2 : BProv Ax_s G1 (pEx (pEx body))).
    { apply BProv_ass. unfold G1. simpl. left. reflexivity. }
    assert (hmid : BProv Ax_s
        (pEx body :: map (rename S) G1)
        (rename S (rename S target))).
    {
      set (G2 := pEx body :: map (rename S) G1).
      assert (hex3 : BProv Ax_s G2 (pEx body)).
      { apply BProv_ass. unfold G2. simpl. left. reflexivity. }
      assert (hinner : BProv Ax_s
          (body :: map (rename S) G2)
          (rename S (rename S (rename S target)))).
      {
        set (C := body :: map (rename S) G2).
        set (idx3 := Term.rename S (Term.rename S (Term.rename S idxTerm))).
        set (last3 := Term.rename S (Term.rename S (Term.rename S lastTerm))).
        set (newCode3 := Term.rename S (Term.rename S (Term.rename S newCode))).
        set (newStep3 := Term.rename S (Term.rename S (Term.rename S newStep))).
        assert (hbody : BProv Ax_s C body).
        { apply BProv_ass. unfold C. simpl. left. reflexivity. }
        assert (hcurOld : BProv Ax_s C
            (betaTermTermAt (tVar 2)
              (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
              (tSucc idx3))).
        {
          pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcur.
          unfold body, idx3 in *.
          simpl in *.
          exact hcur.
        }
        assert (htailBody : BProv Ax_s C
            (pAnd
              (betaTermTermAt (tVar 1)
                (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
                (tSucc (tSucc idx3)))
              (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
        {
          pose proof (BProv_andE2 Ax_s C _ _ hbody) as hrest.
          unfold body, idx3 in *.
          simpl in *.
          exact hrest.
        }
        assert (hnextOld : BProv Ax_s C
            (betaTermTermAt (tVar 1)
              (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
              (tSucc (tSucc idx3)))).
        { exact (BProv_andE1 Ax_s C _ _ htailBody). }
        assert (hdiv : BProv Ax_s C
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
        { exact (BProv_andE2 Ax_s C _ _ htailBody). }
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
          _ htail S) as htailRen1.
        rewrite rename_S_betaShiftTailThroughTermAt in htailRen1.
        simpl in htailRen1.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) G) _ htailRen1 S) as htailRen2.
        rewrite rename_S_betaShiftTailThroughTermAt in htailRen2.
        simpl in htailRen2.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) (map (rename S) G)) _ htailRen2 S)
          as htailRen3.
        rewrite rename_S_betaShiftTailThroughTermAt in htailRen3.
        simpl in htailRen3.
        pose proof (BProv_context_cons Ax_s
          (map (rename S) (map (rename S) (map (rename S) G)))
          (rename S (rename S (pEx (pEx body)))) _ htailRen3) as ht4.
        pose proof (BProv_context_cons Ax_s _
          (rename S (pEx body)) _ ht4) as ht5.
        pose proof (BProv_context_cons Ax_s _ body _ ht5) as ht6.
        assert (htailC : BProv Ax_s C
            (betaShiftTailThroughTermAt (S (S (S oldCode)))
              (S (S (S oldStep)))
              newCode3 newStep3 (tSucc last3))).
        {
          unfold C, G2, G1, newCode3, newStep3, last3.
          exact ht6.
        }
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
          _ hle S) as hleRen1.
        rewrite rename_S_leTermAt in hleRen1.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) G) _ hleRen1 S) as hleRen2.
        rewrite rename_S_leTermAt in hleRen2.
        pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
          (map (rename S) (map (rename S) G)) _ hleRen2 S)
          as hleRen3.
        rewrite rename_S_leTermAt in hleRen3.
        pose proof (BProv_context_cons Ax_s
          (map (rename S) (map (rename S) (map (rename S) G)))
          (rename S (rename S (pEx (pEx body)))) _ hleRen3) as hl4.
        pose proof (BProv_context_cons Ax_s _
          (rename S (pEx body)) _ hl4) as hl5.
        pose proof (BProv_context_cons Ax_s _ body _ hl5) as hl6.
        assert (hleC : BProv Ax_s C (leTermAt idx3 last3)).
        {
          unfold C, G2, G1, idx3, last3.
          exact hl6.
        }
        pose proof
          (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_components
            C (S (S (S oldCode))) (S (S (S oldStep)))
            newCode3 newStep3
            last3 idx3 (tVar 2) (tVar 1) (tVar 0)
            htailC hleC hcurOld hnextOld hdiv) as hshifted.
        unfold target.
        repeat rewrite rename_S_betaDiv2StepWitnessTermAt.
        unfold C, G2, G1, idx3, newCode3, newStep3.
        exact hshifted.
      }
      exact (BProv_exE_of_sentences Ax_s G2 body
        (rename S (rename S target)) sentence_ax_s hex3 hinner).
    }
    exact (BProv_exE_of_sentences Ax_s G1 (pEx body)
      (rename S target) sentence_ax_s hex2 hmid).
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G (pEx (pEx body))
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm)
    sentence_ax_s hwit houter).
Qed.

Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldSteps :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt oldCode oldStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hsteps hle.
  assert (holdSlot : BProv Ax_s G
      (betaDiv2StepWitnessAtTermIdx oldCode oldStep
        (tSucc idxTerm))).
  {
    exact
      (BProv_Ax_s_betaDiv2StepsThroughTermAt_step_succ_termIdx_of_leTerm
        G oldCode oldStep idxTerm lastTerm hsteps hle).
  }
  assert (holdTerm : BProv Ax_s G
      (betaDiv2StepWitnessTermAt
        (tVar oldCode) (tVar oldStep) (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_to_termAt
      G oldCode oldStep (tSucc idxTerm) holdSlot).
  }
  exact
    (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldWitness
      G oldCode oldStep newCode newStep lastTerm idxTerm
      htail hle holdTerm).
Qed.

(** Package all pointwise shifted steps under the new term-parametric trace
    bound. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepsThrough_of_oldSteps :
  forall G oldCode oldStep newCode newStep lastTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt oldCode oldStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt newCode newStep lastTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm htail hsteps.
  set (body := pImp
    (leTermAt (tVar 0) (Term.rename S lastTerm))
    (betaDiv2StepWitnessTermAt
      (Term.rename S newCode) (Term.rename S newStep) (tVar 0))).
  assert (hbody : BProv Ax_s (map (rename S) G) body).
  {
    set (leHyp := leTermAt (tVar 0) (Term.rename S lastTerm)).
    set (C := leHyp :: map (rename S) G).
    assert (hle : BProv Ax_s C
        (leTermAt (tVar 0) (Term.rename S lastTerm))).
    { apply BProv_ass. unfold C, leHyp. simpl. left. reflexivity. }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
      _ htail S) as htailRen.
    rewrite rename_S_betaShiftTailThroughTermAt in htailRen.
    simpl in htailRen.
    assert (htailC : BProv Ax_s C
        (betaShiftTailThroughTermAt (S oldCode) (S oldStep)
          (Term.rename S newCode) (Term.rename S newStep)
          (tSucc (Term.rename S lastTerm)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G) leHyp _ htailRen).
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
      _ hsteps S) as hstepsRen.
    rewrite rename_S_betaDiv2StepsThroughTermAt in hstepsRen.
    simpl in hstepsRen.
    assert (hstepsC : BProv Ax_s C
        (betaDiv2StepsThroughTermAt (S oldCode) (S oldStep)
          (tSucc (Term.rename S lastTerm)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G) leHyp _ hstepsRen).
    }
    assert (hpoint : BProv Ax_s C
        (betaDiv2StepWitnessTermAt
          (Term.rename S newCode) (Term.rename S newStep) (tVar 0))).
    {
      exact
        (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldSteps
          C (S oldCode) (S oldStep)
          (Term.rename S newCode) (Term.rename S newStep)
          (Term.rename S lastTerm) (tVar 0)
          htailC hstepsC hle).
    }
    unfold body, leHyp, C.
    exact (BProv_impI Ax_s (map (rename S) G)
      (leTermAt (tVar 0) (Term.rename S lastTerm))
      (betaDiv2StepWitnessTermAt
        (Term.rename S newCode) (Term.rename S newStep) (tVar 0))
      hpoint).
  }
  unfold betaDiv2StepsThroughTermTermAt, body.
  exact (BProv_allI_of_sentences Ax_s G
    (pImp
      (leTermAt (tVar 0) (Term.rename S lastTerm))
      (betaDiv2StepWitnessTermAt
        (Term.rename S newCode) (Term.rename S newStep) (tVar 0)))
    sentence_ax_s hbody).
Qed.

(** Open an old term-parametric bit read and copy it down the shifted tail. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_oldBit :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm bit,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2BitTermAt bit (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G (betaDiv2BitTermAt bit newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm bit
    htail hle hbit.
  set (target := betaDiv2BitTermAt bit newCode newStep idxTerm).
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename S (Term.rename S (tVar oldCode)))
      (Term.rename S (Term.rename S (tVar oldStep)))
      (Term.rename S (Term.rename S (tSucc idxTerm))))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename S (Term.rename S (tVar oldCode)))
        (Term.rename S (Term.rename S (tVar oldStep)))
        (tSucc (Term.rename S (Term.rename S (tSucc idxTerm)))))
      (div2StepTermAt (tVar 1) (tVar 0)
        (Term.rename S (Term.rename S bit))))).
  assert (hbit' : BProv Ax_s G (pEx (pEx body))).
  {
    unfold betaDiv2BitTermAt in hbit.
    unfold body.
    assert (hrename2 : forall t,
        Term.rename (fun n => n + 2) t =
        Term.rename S (Term.rename S t)).
    {
      intro t. rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    repeat rewrite hrename2 in hbit.
    exact hbit.
  }
  assert (houter : BProv Ax_s
      (pEx body :: map (rename S) G)
      (rename S target)).
  {
    set (G1 := pEx body :: map (rename S) G).
    assert (hex2 : BProv Ax_s G1 (pEx body)).
    { apply BProv_ass. unfold G1. simpl. left. reflexivity. }
    assert (hinner : BProv Ax_s
        (body :: map (rename S) G1)
        (rename S (rename S target))).
    {
      set (C := body :: map (rename S) G1).
      set (idx2 := Term.rename S (Term.rename S idxTerm)).
      set (last2 := Term.rename S (Term.rename S lastTerm)).
      set (bit2 := Term.rename S (Term.rename S bit)).
      set (newCode2 := Term.rename S (Term.rename S newCode)).
      set (newStep2 := Term.rename S (Term.rename S newStep)).
      assert (hbody : BProv Ax_s C body).
      { apply BProv_ass. unfold C. simpl. left. reflexivity. }
      assert (hcurOld : BProv Ax_s C
          (betaTermTermAt (tVar 1)
            (tVar (S (S oldCode))) (tVar (S (S oldStep)))
            (tSucc idx2))).
      {
        pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcur.
        unfold body, idx2 in *.
        simpl in *.
        exact hcur.
      }
      assert (htailBody : BProv Ax_s C
          (pAnd
            (betaTermTermAt (tVar 0)
              (tVar (S (S oldCode))) (tVar (S (S oldStep)))
              (tSucc (tSucc idx2)))
            (div2StepTermAt (tVar 1) (tVar 0) bit2))).
      {
        pose proof (BProv_andE2 Ax_s C _ _ hbody) as hrest.
        unfold body, idx2, bit2 in *.
        simpl in *.
        exact hrest.
      }
      assert (hnextOld : BProv Ax_s C
          (betaTermTermAt (tVar 0)
            (tVar (S (S oldCode))) (tVar (S (S oldStep)))
            (tSucc (tSucc idx2)))).
      { exact (BProv_andE1 Ax_s C _ _ htailBody). }
      assert (hdiv : BProv Ax_s C
          (div2StepTermAt (tVar 1) (tVar 0) bit2)).
      { exact (BProv_andE2 Ax_s C _ _ htailBody). }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
        _ htail S) as htailRen1.
      rewrite rename_S_betaShiftTailThroughTermAt in htailRen1.
      simpl in htailRen1.
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        (map (rename S) G) _ htailRen1 S) as htailRen2.
      rewrite rename_S_betaShiftTailThroughTermAt in htailRen2.
      simpl in htailRen2.
      pose proof (BProv_context_cons Ax_s
        (map (rename S) (map (rename S) G))
        (rename S (pEx body)) _ htailRen2) as ht3.
      pose proof (BProv_context_cons Ax_s _ body _ ht3) as ht4.
      assert (htailC : BProv Ax_s C
          (betaShiftTailThroughTermAt (S (S oldCode)) (S (S oldStep))
            newCode2 newStep2 (tSucc last2))).
      {
        unfold C, G1, newCode2, newStep2, last2.
        exact ht4.
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
        _ hle S) as hleRen1.
      rewrite rename_S_leTermAt in hleRen1.
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        (map (rename S) G) _ hleRen1 S) as hleRen2.
      rewrite rename_S_leTermAt in hleRen2.
      pose proof (BProv_context_cons Ax_s
        (map (rename S) (map (rename S) G))
        (rename S (pEx body)) _ hleRen2) as hl3.
      pose proof (BProv_context_cons Ax_s _ body _ hl3) as hl4.
      assert (hleC : BProv Ax_s C (leTermAt idx2 last2)).
      {
        unfold C, G1, idx2, last2.
        exact hl4.
      }
      pose proof
        (BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_components
          C (S (S oldCode)) (S (S oldStep)) newCode2 newStep2
          last2 idx2 bit2 (tVar 1) (tVar 0)
          htailC hleC hcurOld hnextOld hdiv) as hshifted.
      unfold target.
      repeat rewrite rename_S_betaDiv2BitTermAt.
      unfold C, G1, idx2, bit2, newCode2, newStep2.
      exact hshifted.
    }
    exact (BProv_exE_of_sentences Ax_s G1 body
      (rename S target) sentence_ax_s hex2 hinner).
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G (pEx body)
    (betaDiv2BitTermAt bit newCode newStep idxTerm)
    sentence_ax_s hbit' houter).
Qed.

(** Preserve the final bit-1 existential while shifting a beta tail. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitOneEx_of_oldBitOneEx :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt
      (tVar oldCode) (tVar oldStep) (tSucc idxTerm)) ->
  BProv Ax_s G (betaDiv2BitOneTermExAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hle hbitEx.
  set (target := betaDiv2BitOneTermExAt newCode newStep idxTerm).
  set (body := pAnd
    (oneAt 0)
    (betaDiv2BitTermAt (tVar 0)
      (Term.rename S (tVar oldCode))
      (Term.rename S (tVar oldStep))
      (Term.rename S (tSucc idxTerm)))).
  assert (hbitEx' : BProv Ax_s G (pEx body)).
  { unfold betaDiv2BitOneTermExAt in hbitEx. unfold body. exact hbitEx. }
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    set (idx1 := Term.rename S idxTerm).
    set (last1 := Term.rename S lastTerm).
    set (newCode1 := Term.rename S newCode).
    set (newStep1 := Term.rename S newStep).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hone : BProv Ax_s C (oneAt 0)).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (holdBit : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0)
          (tVar (S oldCode)) (tVar (S oldStep))
          (tSucc idx1))).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hbody) as hb.
      unfold body, idx1 in *.
      simpl in *.
      exact hb.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
      _ htail S) as htailRen.
    rewrite rename_S_betaShiftTailThroughTermAt in htailRen.
    simpl in htailRen.
    assert (htailC : BProv Ax_s C
        (betaShiftTailThroughTermAt (S oldCode) (S oldStep)
          newCode1 newStep1 (tSucc last1))).
    {
      unfold C, newCode1, newStep1, last1.
      exact (BProv_context_cons Ax_s (map (rename S) G) body _ htailRen).
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G
      _ hle S) as hleRen.
    rewrite rename_S_leTermAt in hleRen.
    assert (hleC : BProv Ax_s C (leTermAt idx1 last1)).
    {
      unfold C, idx1, last1.
      exact (BProv_context_cons Ax_s (map (rename S) G) body _ hleRen).
    }
    assert (hnewBit : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1)).
    {
      exact (BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_oldBit
        C (S oldCode) (S oldStep) newCode1 newStep1
        last1 idx1 (tVar 0) htailC hleC holdBit).
    }
    assert (hnewBody : BProv Ax_s C
        (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1))).
    { exact (BProv_andI Ax_s C _ _ hone hnewBit). }
    set (newBody := pAnd
      (oneAt 0)
      (betaDiv2BitTermAt (tVar 0)
        (Term.rename S newCode1)
        (Term.rename S newStep1)
        (Term.rename S idx1))).
    assert (hnewBodySubst : BProv Ax_s C
        (subst (instTerm (tVar 0)) newBody)).
    {
      replace (subst (instTerm (tVar 0)) newBody)
        with (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1)).
      - exact hnewBody.
      - unfold newBody, betaDiv2BitTermAt, betaTermTermAt,
          remTermTermAt, div2StepTermAt, boolTermAt, ltTermAt,
          betaModTermTerm, oneAt, zeroAt, eqConstAt.
        simpl.
        assert (hrename3 : forall t,
            Term.rename (fun n => S n + 2) t =
            Term.rename (fun n => S (S (S n))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite Term.rename_comp.
        repeat rewrite hrename3.
        assert (hrename4 : forall t,
            Term.rename (fun n => S (S n + 2)) t =
            Term.rename (fun n => S (S (S (S n)))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite hrename4.
        assert (hrename5 : forall t,
            Term.rename (fun n => S (S (S n + 2))) t =
            Term.rename (fun n => S (S (S (S (S n))))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite hrename5.
        repeat rewrite Term.subst_rename_succ_up.
        repeat rewrite term_subst_instTerm_rename_succ.
        repeat rewrite term_subst_instTerm_rename_two_succ.
        repeat rewrite term_subst_upSubst_instTerm_rename_two_succ.
        repeat rewrite term_subst_upSubst_instTerm_rename_three_succ.
        repeat rewrite term_subst_up_up_instTerm_rename_three_succ.
        repeat rewrite term_subst_up_up_instTerm_rename_two_var_zero.
        repeat rewrite term_subst_up_up_instTerm_rename_four_succ.
        repeat rewrite term_subst_up_up_up_instTerm_rename_four_succ.
        repeat rewrite term_subst_up_up_up_instTerm_rename_five_succ.
        repeat rewrite term_subst_up_up_up_up_instTerm_rename_five_succ.
        repeat rewrite term_subst_up_up_up_up_up_instTerm_rename_six_succ.
        repeat rewrite term_subst_up_up_up_up_up_instTerm_rename_six_succ.
        repeat rewrite term_subst_up_up_up_up_up_up_instTerm_rename_seven_succ.
        repeat rewrite Term.rename_comp.
        reflexivity.
    }
    assert (hnewEx : BProv Ax_s C (pEx newBody)).
    { exact (BProv_exI Ax_s C newBody (tVar 0) hnewBodySubst). }
    unfold target.
    rewrite rename_S_betaDiv2BitOneTermExAt.
    unfold betaDiv2BitOneTermExAt, newBody,
      newCode1, newStep1, idx1 in *.
    exact hnewEx.
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G body
    (betaDiv2BitOneTermExAt newCode newStep idxTerm)
    sentence_ax_s hbitEx' hopened).
Qed.
