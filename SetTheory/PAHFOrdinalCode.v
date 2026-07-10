(* ===================================================================== *)
(*  PAHFOrdinalCode.v                                                     *)
(*                                                                       *)
(*  The PA-internal graph of Ackermann's finite-ordinal code function.    *)
(*  This is the first, self-contained part of the PA/HFFin round trip:    *)
(*  syntax, standard-model semantics, and the structural substitution     *)
(*  laws used by the later deductive proof.                               *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia PeanoNat.
From SetTheory Require Import Fol PAHF.

Import PA PA.Term PA.Formula.

(* A term-parametric version of the translated Ackermann membership
   predicate.  PAHF already contains the slot-parametric exactness theorem;
   this small wrapper is the form needed by the code graph. *)
Lemma hfMemTermAt_exact : forall (e : nat -> nat) elem setCode,
  Sat natModel e (hfMemTermAt elem setCode) <->
    hf_mem (e elem) (Term.eval natModel e setCode).
Proof.
  intros e elem setCode.
  rewrite <- (subst_instTerm_hfMemAt_succ_zero elem setCode).
  rewrite Sat_subst.
  assert (henv : forall n,
    Term.eval natModel e (instTerm setCode n) =
      scons nat (Term.eval natModel e setCode) e n).
  { intros [|n]; reflexivity. }
  eapply iff_trans.
  - exact (Sat_ext natModel (hfMemAt (S elem) 0)
      (fun n => Term.eval natModel e (instTerm setCode n))
      (scons nat (Term.eval natModel e setCode) e) henv).
  - change
      (Sat natModel (scons nat (Term.eval natModel e setCode) e)
          (hfMemAt (S elem) 0) <->
        hf_mem (e elem) (Term.eval natModel e setCode)).
    apply hfMemAt_exact.
Qed.

(* [newCode] is obtained by adjoining the element [elemCode] to the set
   [oldCode].  Coq's concrete [hf_adjoin] takes the element first and the old
   set second. *)
Definition hfAdjoinGraphTermAt
    (newCode oldCode elemCode : term) : formula :=
  pAll
    (iffForm
      (hfMemTermAt 0 (Term.rename S newCode))
      (pOr
        (hfMemTermAt 0 (Term.rename S oldCode))
        (pEq (tVar 0) (Term.rename S elemCode)))).

Lemma hfAdjoinGraphTermAt_exact :
  forall (e : nat -> nat) newCode oldCode elemCode,
  Sat natModel e (hfAdjoinGraphTermAt newCode oldCode elemCode) <->
    Term.eval natModel e newCode =
      hf_adjoin (Term.eval natModel e elemCode)
        (Term.eval natModel e oldCode).
Proof.
  intros e newCode oldCode elemCode.
  split.
  - intro hgraph.
    apply hf_ext.
    intro x.
    specialize (hgraph x).
    change
      ((Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S newCode)) ->
        Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S oldCode)) \/
        x = Term.eval natModel (scons nat x e)
          (Term.rename S elemCode)) /\
       ((Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S oldCode)) \/
        x = Term.eval natModel (scons nat x e)
          (Term.rename S elemCode)) ->
        Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S newCode)))) in hgraph.
    rewrite !hfMemTermAt_exact in hgraph.
    repeat rewrite Term.eval_rename in hgraph.
    simpl in hgraph.
    rewrite hf_mem_adjoin.
    exact hgraph.
  - intro hnew.
    intro x.
    change
      ((Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S newCode)) ->
        Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S oldCode)) \/
        x = Term.eval natModel (scons nat x e)
          (Term.rename S elemCode)) /\
       ((Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S oldCode)) \/
        x = Term.eval natModel (scons nat x e)
          (Term.rename S elemCode)) ->
        Sat natModel (scons nat x e)
          (hfMemTermAt 0 (Term.rename S newCode)))).
    rewrite !hfMemTermAt_exact.
    repeat rewrite Term.eval_rename.
    change
      ((hf_mem x (Term.eval natModel e newCode) ->
          hf_mem x (Term.eval natModel e oldCode) \/
          x = Term.eval natModel e elemCode) /\
       ((hf_mem x (Term.eval natModel e oldCode) \/
          x = Term.eval natModel e elemCode) ->
          hf_mem x (Term.eval natModel e newCode))).
    rewrite hnew.
    apply hf_mem_adjoin.
Qed.

(* A beta-coded trace of the recurrence n |-> ordinal_code n. *)
Definition OrdinalCodeBetaTrace
    (raw coded sequenceCode sequenceStep : nat) : Prop :=
  BetaEntry sequenceCode sequenceStep 0 0 /\
  BetaEntry sequenceCode sequenceStep raw coded /\
  forall i, i < raw ->
    exists current next,
      BetaEntry sequenceCode sequenceStep i current /\
      BetaEntry sequenceCode sequenceStep (S i) next /\
      next = hf_adjoin current current.

Lemma OrdinalCodeBetaTrace_value :
  forall raw coded sequenceCode sequenceStep,
  OrdinalCodeBetaTrace raw coded sequenceCode sequenceStep ->
  coded = ordinal_code raw.
Proof.
  induction raw as [|raw IH]; intros coded sequenceCode sequenceStep htrace.
  - destruct htrace as [hzero [hend _]].
    exact (BetaEntry_functional sequenceCode sequenceStep 0 coded 0
      hend hzero).
  - destruct htrace as [hzero [hend hsteps]].
    destruct (hsteps raw (Nat.lt_succ_diag_r raw)) as
      [current [next [hcurrent [hnext hadjoin]]]].
    assert (hprefix :
      OrdinalCodeBetaTrace raw current sequenceCode sequenceStep).
    {
      split; [exact hzero |].
      split; [exact hcurrent |].
      intros i hi.
      apply hsteps.
      lia.
    }
    pose proof (IH current sequenceCode sequenceStep hprefix) as hcurrentCode.
    pose proof (BetaEntry_functional sequenceCode sequenceStep (S raw)
      coded next hend hnext) as hcoded.
    rewrite hcoded, hadjoin, hcurrentCode.
    symmetry.
    apply ordinal_code_succ.
Qed.

Lemma OrdinalCodeBetaTrace_exists : forall raw,
  exists sequenceCode sequenceStep,
    OrdinalCodeBetaTrace raw (ordinal_code raw)
      sequenceCode sequenceStep.
Proof.
  intro raw.
  set (scale := S (ordinal_code raw)).
  assert (hvalue_le : forall i, i <= raw ->
    ordinal_code i <= ordinal_code raw).
  {
    intros i hi.
    destruct (Nat.eq_dec i raw) as [-> | hne].
    - lia.
    - apply Nat.lt_le_incl.
      apply ordinal_code_lt_of_lt.
      lia.
  }
  assert (hsmall : forall i, i <= raw ->
    ordinal_code i < BetaModulus (betaFact raw * scale) i).
  {
    intros i hi.
    assert (hscale : ordinal_code i < scale).
    { pose proof (hvalue_le i hi). unfold scale. lia. }
    assert (hfact : 1 <= betaFact raw).
    { pose proof (betaFact_pos raw). lia. }
    unfold BetaModulus.
    nia.
  }
  destruct (beta_entries_exist_through_mul_betaFact
    raw scale ordinal_code hsmall) as [sequenceCode hentries].
  exists sequenceCode, (betaFact raw * scale).
  split.
  - replace 0 with (ordinal_code 0) by reflexivity.
    apply hentries.
    lia.
  - split.
    + apply hentries. lia.
    + intros i hi.
      exists (ordinal_code i), (ordinal_code (S i)).
      split.
      * apply hentries. lia.
      * split.
        (* The successor index remains within the requested prefix. *)
        { apply hentries. lia. }
        { apply ordinal_code_succ. }
Qed.

(* Fully term-parametric one-step and bounded-trace formulas. *)
Definition ordinalCodeStepWitnessTermAt
    (sequenceCode sequenceStep index : term) : formula :=
  pEx (pEx
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) sequenceCode)
        (Term.rename (fun n => n + 2) sequenceStep)
        (Term.rename (fun n => n + 2) index))
      (pAnd
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) sequenceCode)
          (Term.rename (fun n => n + 2) sequenceStep)
          (tSucc (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))))).

Definition ordinalCodeStepsTermAt
    (sequenceCode sequenceStep raw : term) : formula :=
  pAll
    (pImp
      (ltTermAt (tVar 0) (Term.rename S raw))
      (ordinalCodeStepWitnessTermAt
        (Term.rename S sequenceCode)
        (Term.rename S sequenceStep)
        (tVar 0))).

Definition ordinalCodeGraphTermAt (raw coded : term) : formula :=
  pEx (pEx
    (pAnd
      (betaTermTermAt tZero (tVar 1) (tVar 0) tZero)
      (pAnd
        (betaTermTermAt
          (Term.rename (fun n => n + 2) coded)
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw))
        (ordinalCodeStepsTermAt
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw))))).

Definition ordinalCodeGraphAt (raw coded : nat) : formula :=
  ordinalCodeGraphTermAt (tVar raw) (tVar coded).

(* Small evaluation normalizers keep the semantic proofs below independent
   of the concrete shape of terms. *)
Lemma eval_rename_succ_scons : forall t x (e : nat -> nat),
  Term.eval natModel (scons nat x e) (Term.rename S t) =
    Term.eval natModel e t.
Proof.
  intros t x e.
  rewrite Term.eval_rename.
  apply Term.eval_ext.
  intro n.
  reflexivity.
Qed.

Lemma eval_rename_add2_scons : forall t x y (e : nat -> nat),
  Term.eval natModel (scons nat y (scons nat x e))
      (Term.rename (fun n => n + 2) t) =
    Term.eval natModel e t.
Proof.
  intros t x y e.
  rewrite Term.eval_rename.
  apply Term.eval_ext.
  intro n.
  replace (n + 2) with (S (S n)) by lia.
  reflexivity.
Qed.

Lemma ordinalCodeStepWitnessTermAt_exact :
  forall (e : nat -> nat) sequenceCode sequenceStep index,
  Sat natModel e
      (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index) <->
    exists current next,
      BetaEntry
        (Term.eval natModel e sequenceCode)
        (Term.eval natModel e sequenceStep)
        (Term.eval natModel e index) current /\
      BetaEntry
        (Term.eval natModel e sequenceCode)
        (Term.eval natModel e sequenceStep)
        (S (Term.eval natModel e index)) next /\
      next = hf_adjoin current current.
Proof.
  intros e sequenceCode sequenceStep index.
  change
    ((exists current, exists next,
      Sat natModel (scons nat next (scons nat current e))
        (betaTermTermAt (tVar 1)
          (Term.rename (fun n => n + 2) sequenceCode)
          (Term.rename (fun n => n + 2) sequenceStep)
          (Term.rename (fun n => n + 2) index)) /\
      Sat natModel (scons nat next (scons nat current e))
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) sequenceCode)
          (Term.rename (fun n => n + 2) sequenceStep)
          (tSucc (Term.rename (fun n => n + 2) index))) /\
      Sat natModel (scons nat next (scons nat current e))
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))) <->
      exists current next,
        BetaEntry
          (Term.eval natModel e sequenceCode)
          (Term.eval natModel e sequenceStep)
          (Term.eval natModel e index) current /\
        BetaEntry
          (Term.eval natModel e sequenceCode)
          (Term.eval natModel e sequenceStep)
          (S (Term.eval natModel e index)) next /\
        next = hf_adjoin current current).
  split.
  - intros [current [next [hcurrent [hnext hadjoin]]]].
    exists current, next.
    split.
    + apply (proj1 (betaTermTermAt_nat_entry _ _ _ _ _)) in hcurrent.
      rewrite !eval_rename_add2_scons in hcurrent.
      simpl in hcurrent.
      exact hcurrent.
    + split.
      * apply (proj1 (betaTermTermAt_nat_entry _ _ _ _ _)) in hnext.
        simpl in hnext.
        rewrite !eval_rename_add2_scons in hnext.
        exact hnext.
      * apply (proj1 (hfAdjoinGraphTermAt_exact _ _ _ _)) in hadjoin.
        simpl in hadjoin.
        exact hadjoin.
  - intros [current [next [hcurrent [hnext hadjoin]]]].
    exists current, next.
    split.
    + apply (proj2 (betaTermTermAt_nat_entry _ _ _ _ _)).
      rewrite !eval_rename_add2_scons.
      simpl.
      exact hcurrent.
    + split.
      * apply (proj2 (betaTermTermAt_nat_entry _ _ _ _ _)).
        simpl.
        rewrite !eval_rename_add2_scons.
        exact hnext.
      * apply (proj2 (hfAdjoinGraphTermAt_exact _ _ _ _)).
        simpl.
        exact hadjoin.
Qed.

Lemma ordinalCodeStepsTermAt_exact :
  forall (e : nat -> nat) sequenceCode sequenceStep raw,
  Sat natModel e
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) <->
    forall i, i < Term.eval natModel e raw ->
      exists current next,
        BetaEntry
          (Term.eval natModel e sequenceCode)
          (Term.eval natModel e sequenceStep) i current /\
        BetaEntry
          (Term.eval natModel e sequenceCode)
          (Term.eval natModel e sequenceStep) (S i) next /\
        next = hf_adjoin current current.
Proof.
  intros e sequenceCode sequenceStep raw.
  change
    ((forall i,
      Sat natModel (scons nat i e)
        (ltTermAt (tVar 0) (Term.rename S raw)) ->
      Sat natModel (scons nat i e)
        (ordinalCodeStepWitnessTermAt
          (Term.rename S sequenceCode)
          (Term.rename S sequenceStep) (tVar 0))) <->
      forall i, i < Term.eval natModel e raw ->
        exists current next,
          BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep) i current /\
          BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep) (S i) next /\
          next = hf_adjoin current current).
  split.
  - intros h i hi.
    assert (hlt : Sat natModel (scons nat i e)
      (ltTermAt (tVar 0) (Term.rename S raw))).
    {
      apply (proj2 (ltTermAt_nat _ _ _)).
      simpl.
      rewrite eval_rename_succ_scons.
      exact hi.
    }
    specialize (h i hlt).
    apply (proj1 (ordinalCodeStepWitnessTermAt_exact _ _ _ _)) in h.
    rewrite !eval_rename_succ_scons in h.
    simpl in h.
    exact h.
  - intros h i hlt.
    apply (proj1 (ltTermAt_nat _ _ _)) in hlt.
    simpl in hlt.
    rewrite eval_rename_succ_scons in hlt.
    apply (proj2 (ordinalCodeStepWitnessTermAt_exact _ _ _ _)).
    rewrite !eval_rename_succ_scons.
    simpl.
    apply h.
    exact hlt.
Qed.

Lemma ordinalCodeGraphTermAt_trace_exact :
  forall (e : nat -> nat) raw coded,
  Sat natModel e (ordinalCodeGraphTermAt raw coded) <->
    exists sequenceCode sequenceStep,
      OrdinalCodeBetaTrace
        (Term.eval natModel e raw)
        (Term.eval natModel e coded)
        sequenceCode sequenceStep.
Proof.
  intros e raw coded.
  change
    ((exists sequenceCode, exists sequenceStep,
      Sat natModel (scons nat sequenceStep (scons nat sequenceCode e))
        (betaTermTermAt tZero (tVar 1) (tVar 0) tZero) /\
      Sat natModel (scons nat sequenceStep (scons nat sequenceCode e))
        (betaTermTermAt
          (Term.rename (fun n => n + 2) coded)
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw)) /\
      Sat natModel (scons nat sequenceStep (scons nat sequenceCode e))
        (ordinalCodeStepsTermAt
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw))) <->
      exists sequenceCode sequenceStep,
        OrdinalCodeBetaTrace
          (Term.eval natModel e raw)
          (Term.eval natModel e coded)
          sequenceCode sequenceStep).
  split.
  - intros [sequenceCode [sequenceStep [hzero [hend hsteps]]]].
    exists sequenceCode, sequenceStep.
    split.
    + apply (proj1 (betaTermTermAt_nat_entry _ _ _ _ _)) in hzero.
      simpl in hzero.
      exact hzero.
    + split.
      * apply (proj1 (betaTermTermAt_nat_entry _ _ _ _ _)) in hend.
        rewrite !eval_rename_add2_scons in hend.
        simpl in hend.
        exact hend.
      * pose proof (proj1 (ordinalCodeStepsTermAt_exact
          (scons nat sequenceStep (scons nat sequenceCode e))
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw)) hsteps) as hsteps'.
        rewrite eval_rename_add2_scons in hsteps'.
        simpl in hsteps'.
        exact hsteps'.
  - intros [sequenceCode [sequenceStep [hzero [hend hsteps]]]].
    exists sequenceCode, sequenceStep.
    split.
    + apply (proj2 (betaTermTermAt_nat_entry _ _ _ _ _)).
      simpl.
      exact hzero.
    + split.
      * apply (proj2 (betaTermTermAt_nat_entry _ _ _ _ _)).
        rewrite !eval_rename_add2_scons.
        simpl.
        exact hend.
      * apply (proj2 (ordinalCodeStepsTermAt_exact
          (scons nat sequenceStep (scons nat sequenceCode e))
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) raw))).
        rewrite eval_rename_add2_scons.
        simpl.
        exact hsteps.
Qed.

Lemma ordinalCodeGraphTermAt_exact :
  forall (e : nat -> nat) raw coded,
  Sat natModel e (ordinalCodeGraphTermAt raw coded) <->
    Term.eval natModel e coded =
      ordinal_code (Term.eval natModel e raw).
Proof.
  intros e raw coded.
  split.
  - intro h.
    apply (proj1 (ordinalCodeGraphTermAt_trace_exact e raw coded)) in h.
    destruct h as [sequenceCode [sequenceStep htrace]].
    exact (OrdinalCodeBetaTrace_value _ _ _ _ htrace).
  - intro hcode.
    destruct (OrdinalCodeBetaTrace_exists
      (Term.eval natModel e raw)) as [sequenceCode [sequenceStep htrace]].
    apply (proj2 (ordinalCodeGraphTermAt_trace_exact e raw coded)).
    exists sequenceCode, sequenceStep.
    unfold OrdinalCodeBetaTrace in *.
    rewrite hcode.
    exact htrace.
Qed.

Lemma ordinalCodeGraphAt_exact : forall (e : nat -> nat) raw coded,
  Sat natModel e (ordinalCodeGraphAt raw coded) <->
    e coded = ordinal_code (e raw).
Proof.
  intros e raw coded.
  unfold ordinalCodeGraphAt.
  apply ordinalCodeGraphTermAt_exact.
Qed.

Definition codedOrdinalDomain : formula :=
  translateHFFormula domainForm.

Lemma codedOrdinalDomain_exact : forall e : nat -> nat,
  Sat natModel e codedOrdinalDomain <->
    exists raw, ordinal_code raw = e 0.
Proof.
  intro e.
  unfold codedOrdinalDomain.
  eapply iff_trans.
  - apply translateHFFormula_exact.
  - apply domain_exact.
Qed.

(* ===================================================================== *)
(*  Structural normalization                                               *)
(* ===================================================================== *)

Lemma term_subst_iterUpSubst_rename_add :
  forall k (sigma : nat -> term) t,
  Term.subst (iterUpSubst k sigma)
      (Term.rename (fun n => n + k) t) =
    Term.rename (fun n => n + k) (Term.subst sigma t).
Proof.
  induction k as [|k IH]; intros sigma t.
  - simpl.
    replace (Term.rename (fun n => n + 0) t) with t.
    2: {
      transitivity (Term.rename (fun n => n) t).
      - symmetry. apply Term.rename_id.
      - apply Term.rename_ext. intro n. lia.
    }
    replace (Term.rename (fun n => n + 0) (Term.subst sigma t))
      with (Term.subst sigma t).
    + reflexivity.
    + transitivity (Term.rename (fun n => n) (Term.subst sigma t)).
      * symmetry. apply Term.rename_id.
      * apply Term.rename_ext. intro n. lia.
  - simpl.
    replace (Term.rename (fun n => n + S k) t)
      with (Term.rename S (Term.rename (fun n => n + k) t)).
    2: {
      rewrite Term.rename_comp.
      apply Term.rename_ext.
      intro n.
      lia.
    }
    rewrite Term.subst_rename_succ_up.
    rewrite IH.
    rewrite Term.rename_comp.
    apply Term.rename_ext.
    intro n.
    lia.
Qed.

Lemma subst_betaTermTermAt : forall sigma out code step index,
  subst sigma (betaTermTermAt out code step index) =
    betaTermTermAt
      (Term.subst sigma out)
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma index).
Proof.
  intros sigma out code step index.
  unfold betaTermTermAt, betaModTermTerm, remTermTermAt, ltTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_betaTermTermAt : forall r out code step index,
  rename r (betaTermTermAt out code step index) =
    betaTermTermAt
      (Term.rename r out)
      (Term.rename r code)
      (Term.rename r step)
      (Term.rename r index).
Proof.
  intros r out code step index.
  rewrite <- subst_var_rename.
  rewrite subst_betaTermTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma subst_ltTermAt : forall sigma a b,
  subst sigma (ltTermAt a b) =
    ltTermAt (Term.subst sigma a) (Term.subst sigma b).
Proof.
  intros sigma a b.
  unfold ltTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ltTermAt : forall r a b,
  rename r (ltTermAt a b) =
    ltTermAt (Term.rename r a) (Term.rename r b).
Proof.
  intros r a b.
  rewrite <- subst_var_rename.
  rewrite subst_ltTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

(* Substitution under the protected membership query.  This is the sole
   low-level fact needed to make the adjunction graph functorial in its three
   term parameters. *)
Lemma subst_up_hfMemTermAt_zero_rename_succ :
  forall sigma setCode,
  subst (Term.upSubst sigma)
      (hfMemTermAt 0 (Term.rename S setCode)) =
    hfMemTermAt 0
      (Term.rename S (Term.subst sigma setCode)).
Proof.
  intros sigma setCode.
  unfold hfMemTermAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaAt, remAt, ltAt, leAt,
    betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaDiv2BitAt, betaAtSuccIdx, div2StepAt, boolAt,
    zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma subst_hfAdjoinGraphTermAt :
  forall sigma newCode oldCode elemCode,
  subst sigma (hfAdjoinGraphTermAt newCode oldCode elemCode) =
    hfAdjoinGraphTermAt
      (Term.subst sigma newCode)
      (Term.subst sigma oldCode)
      (Term.subst sigma elemCode).
Proof.
  intros sigma newCode oldCode elemCode.
  unfold hfAdjoinGraphTermAt.
  change
    (pAll
      (iffForm
        (subst (Term.upSubst sigma)
          (hfMemTermAt 0 (Term.rename S newCode)))
        (pOr
          (subst (Term.upSubst sigma)
            (hfMemTermAt 0 (Term.rename S oldCode)))
          (pEq (tVar 0)
            (Term.subst (Term.upSubst sigma)
              (Term.rename S elemCode))))) =
     pAll
      (iffForm
        (hfMemTermAt 0
          (Term.rename S (Term.subst sigma newCode)))
        (pOr
          (hfMemTermAt 0
            (Term.rename S (Term.subst sigma oldCode)))
          (pEq (tVar 0)
            (Term.rename S (Term.subst sigma elemCode)))))).
  rewrite !subst_up_hfMemTermAt_zero_rename_succ.
  rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_hfAdjoinGraphTermAt :
  forall r newCode oldCode elemCode,
  rename r (hfAdjoinGraphTermAt newCode oldCode elemCode) =
    hfAdjoinGraphTermAt
      (Term.rename r newCode)
      (Term.rename r oldCode)
      (Term.rename r elemCode).
Proof.
  intros r newCode oldCode elemCode.
  rewrite <- subst_var_rename.
  rewrite subst_hfAdjoinGraphTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma subst_ordinalCodeStepWitnessTermAt :
  forall sigma sequenceCode sequenceStep index,
  subst sigma
      (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index) =
    ordinalCodeStepWitnessTermAt
      (Term.subst sigma sequenceCode)
      (Term.subst sigma sequenceStep)
      (Term.subst sigma index).
Proof.
  intros sigma sequenceCode sequenceStep index.
  assert (hshift2 : forall t,
    Term.subst (Term.upSubst (Term.upSubst sigma))
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.subst sigma t)).
  {
    intro t.
    change
      (Term.subst (iterUpSubst 2 sigma)
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2) (Term.subst sigma t)).
    apply term_subst_iterUpSubst_rename_add.
  }
  unfold ordinalCodeStepWitnessTermAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite subst_hfAdjoinGraphTermAt.
  rewrite !hshift2.
  simpl.
  rewrite !hshift2.
  reflexivity.
Qed.

Lemma subst_ordinalCodeStepsTermAt :
  forall sigma sequenceCode sequenceStep raw,
  subst sigma
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) =
    ordinalCodeStepsTermAt
      (Term.subst sigma sequenceCode)
      (Term.subst sigma sequenceStep)
      (Term.subst sigma raw).
Proof.
  intros sigma sequenceCode sequenceStep raw.
  unfold ordinalCodeStepsTermAt.
  cbn [subst].
  rewrite subst_ltTermAt.
  rewrite subst_ordinalCodeStepWitnessTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma subst_ordinalCodeGraphTermAt : forall sigma raw coded,
  subst sigma (ordinalCodeGraphTermAt raw coded) =
    ordinalCodeGraphTermAt
      (Term.subst sigma raw) (Term.subst sigma coded).
Proof.
  intros sigma raw coded.
  assert (hshift2 : forall t,
    Term.subst (Term.upSubst (Term.upSubst sigma))
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.subst sigma t)).
  {
    intro t.
    change
      (Term.subst (iterUpSubst 2 sigma)
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2) (Term.subst sigma t)).
    apply term_subst_iterUpSubst_rename_add.
  }
  unfold ordinalCodeGraphTermAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite subst_ordinalCodeStepsTermAt.
  rewrite !hshift2.
  reflexivity.
Qed.

Lemma rename_ordinalCodeStepWitnessTermAt :
  forall r sequenceCode sequenceStep index,
  rename r
      (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index) =
    ordinalCodeStepWitnessTermAt
      (Term.rename r sequenceCode)
      (Term.rename r sequenceStep)
      (Term.rename r index).
Proof.
  intros r sequenceCode sequenceStep index.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeStepWitnessTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma rename_ordinalCodeStepsTermAt :
  forall r sequenceCode sequenceStep raw,
  rename r (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) =
    ordinalCodeStepsTermAt
      (Term.rename r sequenceCode)
      (Term.rename r sequenceStep)
      (Term.rename r raw).
Proof.
  intros r sequenceCode sequenceStep raw.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeStepsTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma rename_ordinalCodeGraphTermAt : forall r raw coded,
  rename r (ordinalCodeGraphTermAt raw coded) =
    ordinalCodeGraphTermAt
      (Term.rename r raw) (Term.rename r coded).
Proof.
  intros r raw coded.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeGraphTermAt.
  repeat rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma codedOrdinalDomain_free : forall i,
  Free i codedOrdinalDomain -> i = 0.
Proof.
  intros i hfree.
  unfold codedOrdinalDomain, translateHFFormula in hfree.
  destruct (hfFormulaAt_free domainForm (fun n => n) i hfree)
    as [n [hn hi]].
  pose proof (domainForm_free n hn) as hn0.
  lia.
Qed.
