(* ===================================================================== *)
(*  PAHFRoundTripEquality.v                                             *)
(*                                                                       *)
(*  Equality-atom reduction for the PA -> HF -> PA round trip.          *)
(*                                                                       *)
(*  This module isolates the exact graph interface needed by equality:   *)
(*  totality of ordinal coding, injectivity in the raw input, and        *)
(*  compatibility of translated PA term graphs with ordinal coding.     *)
(*  It deliberately does not depend on the pending model-semantic graph  *)
(*  modules.                                                             *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFProofCalculus PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Select the PA slots occupied by the output and inputs of a translated
    HF term graph. *)
Definition codedTermSlotMap
    (codedOut : nat) (codedMap : nat -> nat) : nat -> nat :=
  fun n =>
    match n with
    | 0 => codedOut
    | S k => codedMap k
    end.

(** Reverse-translate a finite-ordinal graph of a PA term. *)
Definition compositeTermGraphAt
    (codedOut : nat) (codedMap : nat -> nat) (t : term) : formula :=
  hfFormulaAt (codedTermSlotMap codedOut codedMap)
    (termGraphAt (fun n => S n) 0 t).

(** The two proof-theoretic graph laws not supplied by bare graph
    totality.  They are stated separately so downstream arithmetic can
    discharge them independently. *)
Definition PAOrdinalCodeGraphInjectiveProof : Prop :=
  forall (G : list formula) (raw1 raw2 coded : term),
    BProv Ax_s G (ordinalCodeGraphTermAt raw1 coded) ->
    BProv Ax_s G (ordinalCodeGraphTermAt raw2 coded) ->
    BProv Ax_s G (pEq raw1 raw2).

Definition PACompositeTermGraphProof : Prop :=
  forall (G : list formula) (t : term)
      (rawMap codedMap : nat -> nat) (codedOut : nat),
    (forall n, Term.Free n t ->
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap t)
        (ordinalCodeGraphTermAt
          (Term.rename rawMap t) (tVar codedOut))).

Record PACompositeEqualityGraphProofs : Prop := {
  pa_eq_graph_total : PAOrdinalCodeGraphTotalProof;
  pa_eq_graph_injective : PAOrdinalCodeGraphInjectiveProof;
  pa_eq_term_graph : PACompositeTermGraphProof
}.

(** Equality comparison through two existentially selected ordinal codes. *)
Definition codeEqualityBodyTermAt
    (leftCode rightCode leftRaw rightRaw : term) : formula :=
  pAnd
    (ordinalCodeGraphTermAt leftRaw leftCode)
    (pAnd
      (ordinalCodeGraphTermAt rightRaw rightCode)
      (pEq leftCode rightCode)).

Definition codeEqualityTermAt (leftRaw rightRaw : term) : formula :=
  pEx (pEx
    (codeEqualityBodyTermAt
      (tVar 1) (tVar 0)
      (Term.rename (fun n => n + 2) leftRaw)
      (Term.rename (fun n => n + 2) rightRaw))).

Lemma subst_codeEqualityBodyTermAt : forall sigma
    leftCode rightCode leftRaw rightRaw,
  subst sigma
      (codeEqualityBodyTermAt leftCode rightCode leftRaw rightRaw) =
    codeEqualityBodyTermAt
      (Term.subst sigma leftCode)
      (Term.subst sigma rightCode)
      (Term.subst sigma leftRaw)
      (Term.subst sigma rightRaw).
Proof.
  intros sigma leftCode rightCode leftRaw rightRaw.
  unfold codeEqualityBodyTermAt.
  cbn [subst].
  rewrite !subst_ordinalCodeGraphTermAt.
  reflexivity.
Qed.

Lemma subst_codeEqualityTermAt : forall sigma leftRaw rightRaw,
  subst sigma (codeEqualityTermAt leftRaw rightRaw) =
    codeEqualityTermAt
      (Term.subst sigma leftRaw) (Term.subst sigma rightRaw).
Proof.
  intros sigma leftRaw rightRaw.
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
  unfold codeEqualityTermAt.
  cbn [subst].
  rewrite subst_codeEqualityBodyTermAt.
  cbn [Term.subst Term.upSubst Term.rename].
  rewrite !hshift2.
  reflexivity.
Qed.

Lemma rename_codeEqualityTermAt : forall r leftRaw rightRaw,
  rename r (codeEqualityTermAt leftRaw rightRaw) =
    codeEqualityTermAt
      (Term.rename r leftRaw) (Term.rename r rightRaw).
Proof.
  intros r leftRaw rightRaw.
  rewrite <- subst_var_rename.
  rewrite subst_codeEqualityTermAt.
  rewrite !term_subst_var_rename.
  reflexivity.
Qed.

Lemma subst_instTerm_codeEqualityBody_inner : forall
    leftCode rightCode leftRaw rightRaw,
  subst (instTerm rightCode)
      (codeEqualityBodyTermAt
        (Term.rename S leftCode) (tVar 0)
        (Term.rename S leftRaw) (Term.rename S rightRaw)) =
    codeEqualityBodyTermAt leftCode rightCode leftRaw rightRaw.
Proof.
  intros leftCode rightCode leftRaw rightRaw.
  rewrite subst_codeEqualityBodyTermAt.
  cbn [instTerm Term.subst].
  rewrite !term_subst_instTerm_rename_succ.
  reflexivity.
Qed.

Lemma subst_instTerm_codeEqualityBody_outer : forall
    leftCode leftRaw rightRaw,
  subst (instTerm leftCode)
      (pEx (codeEqualityBodyTermAt
        (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) leftRaw)
        (Term.rename (fun n => n + 2) rightRaw))) =
    pEx (codeEqualityBodyTermAt
      (Term.rename S leftCode) (tVar 0)
      (Term.rename S leftRaw) (Term.rename S rightRaw)).
Proof.
  intros leftCode leftRaw rightRaw.
  cbn [subst].
  rewrite subst_codeEqualityBodyTermAt.
  cbn [instTerm Term.subst Term.upSubst].
  rewrite !term_subst_upSubst_instTerm_rename_add_two.
  reflexivity.
Qed.

Lemma BProv_codeEqualityTermAt_of_components : forall
    (B : formula -> Prop) G leftCode rightCode leftRaw rightRaw,
  BProv B G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv B G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv B G (pEq leftCode rightCode) ->
  BProv B G (codeEqualityTermAt leftRaw rightRaw).
Proof.
  intros B G leftCode rightCode leftRaw rightRaw hleft hright heq.
  assert (hbody : BProv B G
      (codeEqualityBodyTermAt leftCode rightCode leftRaw rightRaw)).
  {
    unfold codeEqualityBodyTermAt.
    exact (BProv_andI B G _ _ hleft
      (BProv_andI B G _ _ hright heq)).
  }
  assert (hinnerInst : BProv B G
      (subst (instTerm rightCode)
        (codeEqualityBodyTermAt
          (Term.rename S leftCode) (tVar 0)
          (Term.rename S leftRaw) (Term.rename S rightRaw)))).
  {
    rewrite subst_instTerm_codeEqualityBody_inner.
    exact hbody.
  }
  assert (hinner : BProv B G
      (pEx (codeEqualityBodyTermAt
        (Term.rename S leftCode) (tVar 0)
        (Term.rename S leftRaw) (Term.rename S rightRaw)))).
  {
    exact (BProv_exI B G _ rightCode hinnerInst).
  }
  assert (houterInst : BProv B G
      (subst (instTerm leftCode)
        (pEx (codeEqualityBodyTermAt
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) leftRaw)
          (Term.rename (fun n => n + 2) rightRaw))))).
  {
    rewrite subst_instTerm_codeEqualityBody_outer.
    exact hinner.
  }
  unfold codeEqualityTermAt.
  exact (BProv_exI B G _ leftCode houterInst).
Qed.

(** Small equivalence-calculus kit needed to lift graph equivalences through
    the two existential witnesses of an equality atom. *)
Lemma BProv_PA_iffForm_symm : forall
    (B : formula -> Prop) G a b,
  BProv B G (iffForm a b) ->
  BProv B G (iffForm b a).
Proof.
  intros B G a b h.
  assert (hab : BProv B G (pImp a b)).
  { unfold iffForm in h. exact (BProv_andE1 B G _ _ h). }
  assert (hba : BProv B G (pImp b a)).
  { unfold iffForm in h. exact (BProv_andE2 B G _ _ h). }
  unfold iffForm.
  exact (BProv_andI B G _ _ hba hab).
Qed.

Lemma BProv_PA_iffForm_trans : forall
    (B : formula -> Prop) G a b c,
  BProv B G (iffForm a b) ->
  BProv B G (iffForm b c) ->
  BProv B G (iffForm a c).
Proof.
  intros B G a b c hab hbc.
  assert (habF : BProv B G (pImp a b)).
  { unfold iffForm in hab. exact (BProv_andE1 B G _ _ hab). }
  assert (habR : BProv B G (pImp b a)).
  { unfold iffForm in hab. exact (BProv_andE2 B G _ _ hab). }
  assert (hbcF : BProv B G (pImp b c)).
  { unfold iffForm in hbc. exact (BProv_andE1 B G _ _ hbc). }
  assert (hbcR : BProv B G (pImp c b)).
  { unfold iffForm in hbc. exact (BProv_andE2 B G _ _ hbc). }
  assert (hac : BProv B G (pImp a c)).
  {
    apply BProv_impI.
    assert (ha : BProv B (a :: G) a).
    { apply BProv_ass. simpl. now left. }
    assert (hb : BProv B (a :: G) b).
    {
      exact (BProv_mp B (a :: G) a b
        (BProv_context_cons B G a (pImp a b) habF) ha).
    }
    exact (BProv_mp B (a :: G) b c
      (BProv_context_cons B G a (pImp b c) hbcF) hb).
  }
  assert (hca : BProv B G (pImp c a)).
  {
    apply BProv_impI.
    assert (hc : BProv B (c :: G) c).
    { apply BProv_ass. simpl. now left. }
    assert (hb : BProv B (c :: G) b).
    {
      exact (BProv_mp B (c :: G) c b
        (BProv_context_cons B G c (pImp c b) hbcR) hc).
    }
    exact (BProv_mp B (c :: G) b a
      (BProv_context_cons B G c (pImp b a) habR) hb).
  }
  unfold iffForm.
  exact (BProv_andI B G _ _ hac hca).
Qed.

Lemma BProv_PA_iffForm_ex_congr_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G a b,
    BProv B (map (rename S) G) (iffForm a b) ->
    BProv B G (iffForm (pEx a) (pEx b)).
Proof.
  intros B hB G a b h.
  assert (hab : BProv B (map (rename S) G) (pImp a b)).
  { unfold iffForm in h. exact (BProv_andE1 B _ _ _ h). }
  assert (hba : BProv B (map (rename S) G) (pImp b a)).
  { unfold iffForm in h. exact (BProv_andE2 B _ _ _ h). }
  assert (hforward : BProv B G (pImp (pEx a) (pEx b))).
  {
    apply BProv_impI.
    set (C := pEx a :: G).
    assert (hexa : BProv B C (pEx a)).
    { apply BProv_ass. unfold C. simpl. now left. }
    apply (BProv_exE_of_sentences B C a (pEx b) hB hexa).
    set (D := a :: map (rename S) C).
    assert (ha : BProv B D a).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (habD : BProv B D (pImp a b)).
    {
      pose proof (BProv_context_cons B (map (rename S) G)
        (rename S (pEx a)) (pImp a b) hab) as hctx.
      pose proof (BProv_context_cons B
        (rename S (pEx a) :: map (rename S) G)
        a (pImp a b) hctx) as hctx'.
      unfold D, C.
      simpl.
      exact hctx'.
    }
    assert (hb : BProv B D b).
    { exact (BProv_mp B D a b habD ha). }
    assert (hinst : BProv B D
        (subst (instTerm (tVar 0)) (rename (up S) b))).
    {
      rewrite subst_instTerm_var_zero_rename_up_succ.
      exact hb.
    }
    pose proof (BProv_exI B D (rename (up S) b) (tVar 0) hinst)
      as hex.
    change (BProv B D (rename S (pEx b))).
    simpl.
    exact hex.
  }
  assert (hreverse : BProv B G (pImp (pEx b) (pEx a))).
  {
    apply BProv_impI.
    set (C := pEx b :: G).
    assert (hexb : BProv B C (pEx b)).
    { apply BProv_ass. unfold C. simpl. now left. }
    apply (BProv_exE_of_sentences B C b (pEx a) hB hexb).
    set (D := b :: map (rename S) C).
    assert (hb : BProv B D b).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hbaD : BProv B D (pImp b a)).
    {
      pose proof (BProv_context_cons B (map (rename S) G)
        (rename S (pEx b)) (pImp b a) hba) as hctx.
      pose proof (BProv_context_cons B
        (rename S (pEx b) :: map (rename S) G)
        b (pImp b a) hctx) as hctx'.
      unfold D, C.
      simpl.
      exact hctx'.
    }
    assert (ha : BProv B D a).
    { exact (BProv_mp B D b a hbaD hb). }
    assert (hinst : BProv B D
        (subst (instTerm (tVar 0)) (rename (up S) a))).
    {
      rewrite subst_instTerm_var_zero_rename_up_succ.
      exact ha.
    }
    pose proof (BProv_exI B D (rename (up S) a) (tVar 0) hinst)
      as hex.
    change (BProv B D (rename S (pEx a))).
    simpl.
    exact hex.
  }
  unfold iffForm.
  exact (BProv_andI B G _ _ hforward hreverse).
Qed.

(** Graph totality turns raw equality into equality through selected codes. *)
Lemma BProv_codeEqualityTermAt_of_eq : forall
    (P : PACompositeEqualityGraphProofs) G leftRaw rightRaw,
  BProv Ax_s G (pEq leftRaw rightRaw) ->
  BProv Ax_s G (codeEqualityTermAt leftRaw rightRaw).
Proof.
  intros P G leftRaw rightRaw heq.
  set (graphBody := ordinalCodeGraphTermAt
    (Term.rename S leftRaw) (tVar 0)).
  assert (htotal : BProv Ax_s G (pEx graphBody)).
  {
    unfold graphBody.
    exact (pa_eq_graph_total P G leftRaw).
  }
  assert (hbody : BProv Ax_s
      (graphBody :: map (rename S) G)
      (rename S (codeEqualityTermAt leftRaw rightRaw))).
  {
    set (C := graphBody :: map (rename S) G).
    assert (hleft : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename S leftRaw) (tVar 0))).
    {
      apply BProv_ass.
      unfold C, graphBody.
      simpl. now left.
    }
    assert (heqShift : BProv Ax_s C
        (pEq (Term.rename S leftRaw) (Term.rename S rightRaw))).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G graphBody (pEq leftRaw rightRaw) heq) as h.
      unfold C.
      exact h.
    }
    assert (hright : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename S rightRaw) (tVar 0))).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C _ _ _ heqShift hleft).
    }
    assert (hcodes : BProv Ax_s C
        (codeEqualityTermAt
          (Term.rename S leftRaw) (Term.rename S rightRaw))).
    {
      exact (BProv_codeEqualityTermAt_of_components Ax_s C
        (tVar 0) (tVar 0)
        (Term.rename S leftRaw) (Term.rename S rightRaw)
        hleft hright (BProv_eqRefl Ax_s C (tVar 0))).
    }
    rewrite rename_codeEqualityTermAt.
    exact hcodes.
  }
  exact (BProv_exE_of_sentences Ax_s G graphBody
    (codeEqualityTermAt leftRaw rightRaw)
    sentence_ax_s htotal hbody).
Qed.

(** Raw-input injectivity recovers equality from equal code witnesses. *)
Lemma BProv_eq_of_codeEqualityTermAt : forall
    (P : PACompositeEqualityGraphProofs) G leftRaw rightRaw,
  BProv Ax_s G (codeEqualityTermAt leftRaw rightRaw) ->
  BProv Ax_s G (pEq leftRaw rightRaw).
Proof.
  intros P G leftRaw rightRaw hcodes.
  set (body := codeEqualityBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) leftRaw)
    (Term.rename (fun n => n + 2) rightRaw)).
  set (inner := pEx body).
  assert (houter : BProv Ax_s G (pEx inner)).
  {
    unfold codeEqualityTermAt in hcodes.
    unfold inner, body.
    exact hcodes.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body (pEq leftRaw rightRaw) houter).
  set (C := body ::
    map (rename S) (pEx body :: map (rename S) G)).
  assert (hpacked : BProv Ax_s C body).
  { apply BProv_ass. unfold C. simpl. now left. }
  assert (hleft : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) leftRaw) (tVar 1))).
  {
    unfold body, codeEqualityBodyTermAt in hpacked.
    exact (BProv_andE1 Ax_s C _ _ hpacked).
  }
  assert (hrightAndEq : BProv Ax_s C
      (pAnd
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2) rightRaw) (tVar 0))
        (pEq (tVar 1) (tVar 0)))).
  {
    unfold body, codeEqualityBodyTermAt in hpacked.
    exact (BProv_andE2 Ax_s C _ _ hpacked).
  }
  assert (hright : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rightRaw) (tVar 0))).
  { exact (BProv_andE1 Ax_s C _ _ hrightAndEq). }
  assert (heqCode : BProv Ax_s C (pEq (tVar 1) (tVar 0))).
  { exact (BProv_andE2 Ax_s C _ _ hrightAndEq). }
  assert (hleftAtRightCode : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) leftRaw) (tVar 0))).
  {
    exact (BProv_ordinalCodeGraphTermAt_congr_coded
      Ax_s C _ _ _ heqCode hleft).
  }
  assert (hraw : BProv Ax_s C
      (pEq
        (Term.rename (fun n => n + 2) leftRaw)
        (Term.rename (fun n => n + 2) rightRaw))).
  {
    exact (pa_eq_graph_injective P C _ _ _
      hleftAtRightCode hright).
  }
  cbn [rename].
  rewrite !Term.rename_comp.
  replace (Term.rename (fun n => S (S n)) leftRaw)
    with (Term.rename (fun n => n + 2) leftRaw)
    by (apply Term.rename_ext; intro n; lia).
  replace (Term.rename (fun n => S (S n)) rightRaw)
    with (Term.rename (fun n => n + 2) rightRaw)
    by (apply Term.rename_ext; intro n; lia).
  exact hraw.
Qed.

Lemma BProv_eq_iff_codeEqualityTermAt : forall
    (P : PACompositeEqualityGraphProofs) G leftRaw rightRaw,
  BProv Ax_s G
    (iffForm
      (pEq leftRaw rightRaw)
      (codeEqualityTermAt leftRaw rightRaw)).
Proof.
  intros P G leftRaw rightRaw.
  assert (hforward : BProv Ax_s G
      (pImp (pEq leftRaw rightRaw)
        (codeEqualityTermAt leftRaw rightRaw))).
  {
    apply BProv_impI.
    apply (BProv_codeEqualityTermAt_of_eq P
      (pEq leftRaw rightRaw :: G) leftRaw rightRaw).
    apply BProv_ass. simpl. now left.
  }
  assert (hreverse : BProv Ax_s G
      (pImp (codeEqualityTermAt leftRaw rightRaw)
        (pEq leftRaw rightRaw))).
  {
    apply BProv_impI.
    apply (BProv_eq_of_codeEqualityTermAt P
      (codeEqualityTermAt leftRaw rightRaw :: G) leftRaw rightRaw).
    apply BProv_ass. simpl. now left.
  }
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(** Normal form of a reverse-translated equality after opening its two
    term-value witnesses. *)
Definition paCompositeEqBodyAt
    (codedMap : nat -> nat) (left right : term) : formula :=
  pAnd
    (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
    (pAnd
      (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
      (pEq (tVar 1) (tVar 0))).

Lemma hfFormulaAt_termGraph_left_eq_composite : forall codedMap t,
  hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
      (termGraphAt (fun n => n + 2) 1 t) =
    compositeTermGraphAt 1 (fun n => codedMap n + 2) t.
Proof.
  intros codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename S graph =
      termGraphAt (fun n => n + 2) 1 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n. lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n]; cbn [hfUpVarMap codedTermSlotMap]; lia.
Qed.

Lemma hfFormulaAt_termGraph_right_eq_composite : forall codedMap t,
  hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
      (termGraphAt (fun n => n + 2) 0 t) =
    compositeTermGraphAt 0 (fun n => codedMap n + 2) t.
Proof.
  intros codedMap t.
  set (graph := termGraphAt S 0 t).
  assert (hgraph : Fol.rename (Fol.up S) graph =
      termGraphAt (fun n => n + 2) 0 t).
  {
    unfold graph.
    rewrite termGraphAt_rename.
    apply termGraphAt_map_ext.
    intro n.
    unfold Fol.up.
    cbn.
    lia.
  }
  unfold compositeTermGraphAt.
  rewrite <- hgraph.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intros [|n]; cbn [hfUpVarMap codedTermSlotMap Fol.up]; lia.
Qed.

Lemma paCompositeAt_eq_normalForm : forall codedMap left right,
  paCompositeAt codedMap (pEq left right) =
    pEx (pEx (paCompositeEqBodyAt codedMap left right)).
Proof.
  intros codedMap left right.
  unfold paCompositeAt, paCompositeEqBodyAt.
  cbn [formulaAt hfFormulaAt].
  rewrite hfFormulaAt_termGraph_left_eq_composite.
  rewrite hfFormulaAt_termGraph_right_eq_composite.
  reflexivity.
Qed.

Lemma BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs :
  forall G left right rawLeft rawRight codedMap,
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rawLeft) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rawRight) (tVar 0))) ->
  BProv Ax_s G
    (iffForm
      (paCompositeAt codedMap (pEq left right))
      (codeEqualityTermAt rawLeft rawRight)).
Proof.
  intros G left right rawLeft rawRight codedMap hleft hright.
  set (G2 := map (rename S) (map (rename S) G)).
  assert (heq : BProv Ax_s G2
      (iffForm (pEq (tVar 1) (tVar 0))
        (pEq (tVar 1) (tVar 0)))).
  { apply BProv_PA_iffForm_refl. }
  assert (hbody : BProv Ax_s G2
      (iffForm
        (paCompositeEqBodyAt codedMap left right)
        (codeEqualityBodyTermAt
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) rawLeft)
          (Term.rename (fun n => n + 2) rawRight)))).
  {
    assert (hp : BProv Ax_s G2
        (iffForm
          (pAnd
            (compositeTermGraphAt 0
              (fun n => codedMap n + 2) right)
            (pEq (tVar 1) (tVar 0)))
          (pAnd
            (ordinalCodeGraphTermAt
              (Term.rename (fun n => n + 2) rawRight) (tVar 0))
            (pEq (tVar 1) (tVar 0))))).
    {
      apply BProv_PA_iffForm_and_congr.
      - unfold G2. exact hright.
      - exact heq.
    }
    unfold paCompositeEqBodyAt, codeEqualityBodyTermAt.
    apply BProv_PA_iffForm_and_congr.
    - unfold G2. exact hleft.
    - exact hp.
  }
  assert (hinner : BProv Ax_s (map (rename S) G)
      (iffForm
        (pEx (paCompositeEqBodyAt codedMap left right))
        (pEx (codeEqualityBodyTermAt
          (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) rawLeft)
          (Term.rename (fun n => n + 2) rawRight))))).
  {
    apply (BProv_PA_iffForm_ex_congr_of_sentences
      Ax_s sentence_ax_s (map (rename S) G)).
    unfold G2 in hbody.
    exact hbody.
  }
  pose proof (BProv_PA_iffForm_ex_congr_of_sentences
    Ax_s sentence_ax_s G _ _ hinner) as houter.
  rewrite paCompositeAt_eq_normalForm.
  unfold codeEqualityTermAt.
  exact houter.
Qed.

(** The equality-atom field of [PACompositeConstructorProofs]. *)
Definition PACompositeEqualityProof : Prop :=
  forall left right, PACompositeFormulaExact (pEq left right).

Theorem pa_composite_eq_exact_of_equalityGraphProofs :
  PACompositeEqualityGraphProofs -> PACompositeEqualityProof.
Proof.
  intros P left right G rawMap codedMap hcode.
  set (G2 := map (rename S) (map (rename S) G)).
  set (rawMap2 := fun n => rawMap n + 2).
  set (codedMap2 := fun n => codedMap n + 2).
  assert (hcode2 : forall n, Free n (pEq left right) ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  {
    intros n hn.
    pose proof (hcode n hn) as h0.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      G (ordinalCodeGraphAt (rawMap n) (codedMap n)) h0 S) as h1.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      (map (rename S) G)
      (rename S (ordinalCodeGraphAt (rawMap n) (codedMap n)))
      h1 S) as h2.
    unfold G2, rawMap2, codedMap2.
    unfold ordinalCodeGraphAt in h2 |- *.
    rewrite !rename_ordinalCodeGraphTermAt in h2.
    cbn [Term.rename] in h2.
    replace (rawMap n + 2) with (S (S (rawMap n))) by lia.
    replace (codedMap n + 2) with (S (S (codedMap n))) by lia.
    exact h2.
  }
  assert (hleftRaw : forall n, Term.Free n left ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  { intros n hn. apply hcode2. now left. }
  assert (hrightRaw : forall n, Term.Free n right ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  { intros n hn. apply hcode2. now right. }
  pose proof (pa_eq_term_graph P G2 left
    rawMap2 codedMap2 1 hleftRaw) as hleft0.
  pose proof (pa_eq_term_graph P G2 right
    rawMap2 codedMap2 0 hrightRaw) as hright0.
  assert (hleft : BProv Ax_s G2
      (iffForm
        (compositeTermGraphAt 1
          (fun n => codedMap n + 2) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2)
            (Term.rename rawMap left))
          (tVar 1)))).
  {
    unfold rawMap2, codedMap2 in hleft0.
    replace (Term.rename (fun n => rawMap n + 2) left)
      with (Term.rename (fun n => n + 2)
        (Term.rename rawMap left)) in hleft0.
    - exact hleft0.
    - rewrite Term.rename_comp.
      apply Term.rename_ext.
      intro n. reflexivity.
  }
  assert (hright : BProv Ax_s G2
      (iffForm
        (compositeTermGraphAt 0
          (fun n => codedMap n + 2) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2)
            (Term.rename rawMap right))
          (tVar 0)))).
  {
    unfold rawMap2, codedMap2 in hright0.
    replace (Term.rename (fun n => rawMap n + 2) right)
      with (Term.rename (fun n => n + 2)
        (Term.rename rawMap right)) in hright0.
    - exact hright0.
    - rewrite Term.rename_comp.
      apply Term.rename_ext.
      intro n. reflexivity.
  }
  assert (hcomposite : BProv Ax_s G
      (iffForm
        (paCompositeAt codedMap (pEq left right))
        (codeEqualityTermAt
          (Term.rename rawMap left)
          (Term.rename rawMap right)))).
  {
    apply (BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs
      G left right (Term.rename rawMap left)
      (Term.rename rawMap right) codedMap).
    - unfold G2 in hleft. exact hleft.
    - unfold G2 in hright. exact hright.
  }
  pose proof (BProv_eq_iff_codeEqualityTermAt P G
    (Term.rename rawMap left) (Term.rename rawMap right)) as hraw.
  pose proof (BProv_PA_iffForm_symm Ax_s G _ _ hcomposite)
    as hcompositeSymm.
  pose proof (BProv_PA_iffForm_trans Ax_s G _ _ _
    hraw hcompositeSymm) as hresult.
  cbn [PA.Formula.rename].
  exact hresult.
Qed.

(** Existing ordinal-code totality leaves precisely injectivity and term
    compatibility as the equality-specific arithmetic residuals. *)
Definition PACompositeEqualityGraphProofs_of_adjoinExistence
    (hadjoin : PAHFAdjoinExistence)
    (hinjective : PAOrdinalCodeGraphInjectiveProof)
    (hterm : PACompositeTermGraphProof) :
  PACompositeEqualityGraphProofs :=
  {| pa_eq_graph_total :=
       PAOrdinalCodeGraphTotalProof_of_adjoinExistence hadjoin;
     pa_eq_graph_injective := hinjective;
     pa_eq_term_graph := hterm |}.

Theorem pa_composite_eq_exact_of_adjoin_injective_termGraph :
  PAHFAdjoinExistence ->
  PAOrdinalCodeGraphInjectiveProof ->
  PACompositeTermGraphProof ->
  PACompositeEqualityProof.
Proof.
  intros hadjoin hinjective hterm.
  apply pa_composite_eq_exact_of_equalityGraphProofs.
  exact (PACompositeEqualityGraphProofs_of_adjoinExistence
    hadjoin hinjective hterm).
Qed.
