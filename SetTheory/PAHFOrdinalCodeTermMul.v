(* ===================================================================== *)
(*  PAHFOrdinalCodeTermMul.v                                            *)
(*                                                                       *)
(*  Structural lifting of multiplication core compatibility to all PA    *)
(*  terms.  The open and existentially bound output cores are supplied   *)
(*  by the arithmetic layer; this file handles only witness plumbing.    *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFProofCalculus
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeTermOperations PAHFOrdinalCodeTermAdd.

Import ListNotations.
Import PA PA.Term PA.Formula.

Lemma BProv_Ax_s_term_graph_mul_forward_of_shifted_operands : forall
    (hcore : PAOrdinalCodeMulOpenCoreCompatibility)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 3) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 2 (fun n => codedMap n + 3) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) rightRaw) (tVar 2))) ->
  BProv Ax_s G
    (pImp
      (compositeTermGraphAt codedOut codedMap (tMul left right))
      (ordinalCodeGraphTermAt
        (tMul leftRaw rightRaw) (tVar codedOut))).
Proof.
  intros hcore G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  set (composite := compositeTermGraphAt codedOut codedMap
    (tMul left right)).
  set (target := ordinalCodeGraphTermAt
    (tMul leftRaw rightRaw) (tVar codedOut)).
  set (leftComposite := compositeTermGraphAt 1
    (fun n => codedMap n + 3) left).
  set (rightComposite := compositeTermGraphAt 2
    (fun n => codedMap n + 3) right).
  set (core := compositeMulCoreAt codedOut).
  set (body := pAnd leftComposite (pAnd rightComposite core)).
  apply BProv_impI.
  set (C := composite :: G).
  assert (hcomposite : BProv Ax_s C composite).
  { apply BProv_ass. unfold C. simpl. now left. }
  assert (hex : BProv Ax_s C (pEx (pEx (pEx body)))).
  {
    unfold composite in hcomposite.
    rewrite compositeTermGraphAt_mul_normalForm in hcomposite.
    unfold body, leftComposite, rightComposite, core.
    exact hcomposite.
  }
  set (inner1 := pEx body).
  set (inner2 := pEx (pEx body)).
  set (D := body :: map (rename S)
    (inner1 :: map (rename S)
      (inner2 :: map (rename S) C))).
  assert (hopened : BProv Ax_s D
      (rename S (rename S (rename S target)))).
  {
    assert (hbody : BProv Ax_s D body).
    { apply BProv_ass. unfold D. simpl. now left. }
    pose proof (BProv_andE1 Ax_s D _ _ hbody) as hleftComposite.
    pose proof (BProv_andE2 Ax_s D _ _ hbody) as htail.
    pose proof (BProv_andE1 Ax_s D _ _ htail) as hrightComposite.
    pose proof (BProv_andE2 Ax_s D _ _ htail) as hcoreD.
    (* Three opened witnesses shift the operand hypotheses three times.  The
       remaining difference between their context and [D] is only this local
       four-formula prefix. *)
    assert (liftShifted : forall phi,
        BProv Ax_s
          (map (rename S) (map (rename S) (map (rename S) G))) phi ->
        BProv Ax_s D phi).
    {
      intros phi hphi.
      pose proof (BProv_context_prefix Ax_s
        [body; rename S inner1; rename S (rename S inner2);
          rename S (rename S (rename S composite))]
        (map (rename S) (map (rename S) (map (rename S) G)))
        phi hphi) as h.
      unfold D, C.
      simpl.
      exact h.
    }
    pose proof (liftShifted _ hleft) as hleftD.
    assert (hleftForward : BProv Ax_s D
        (pImp leftComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 3) leftRaw) (tVar 1)))).
    {
      unfold iffForm in hleftD.
      exact (BProv_andE1 Ax_s D _ _ hleftD).
    }
    assert (hleftGraph : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3) leftRaw) (tVar 1))).
    { exact (BProv_mp Ax_s D _ _ hleftForward hleftComposite). }
    pose proof (liftShifted _ hright) as hrightD.
    assert (hrightForward : BProv Ax_s D
        (pImp rightComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 3) rightRaw) (tVar 2)))).
    {
      unfold iffForm in hrightD.
      exact (BProv_andE1 Ax_s D _ _ hrightD).
    }
    assert (hrightGraph : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3) rightRaw) (tVar 2))).
    { exact (BProv_mp Ax_s D _ _ hrightForward hrightComposite). }
    pose proof (hcore D
      (Term.rename (fun n => n + 3) leftRaw)
      (Term.rename (fun n => n + 3) rightRaw)
      codedOut hleftGraph hrightGraph) as hcoreIff.
    assert (hcoreForward : BProv Ax_s D
        (pImp core
          (ordinalCodeGraphTermAt
            (tMul
              (Term.rename (fun n => n + 3) leftRaw)
              (Term.rename (fun n => n + 3) rightRaw))
            (tVar (codedOut + 3))))).
    {
      unfold iffForm in hcoreIff.
      exact (BProv_andE1 Ax_s D _ _ hcoreIff).
    }
    pose proof (BProv_mp Ax_s D _ _ hcoreForward hcoreD) as htarget.
    unfold target.
    repeat rewrite rename_ordinalCodeGraphTermAt.
    cbn [Term.rename].
    replace (Term.rename S (Term.rename S (Term.rename S leftRaw)))
      with (Term.rename (fun n => n + 3) leftRaw).
    2: {
      repeat rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (Term.rename S (Term.rename S (Term.rename S rightRaw)))
      with (Term.rename (fun n => n + 3) rightRaw).
    2: {
      repeat rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (S (S (S codedOut))) with (codedOut + 3) by lia.
    exact htarget.
  }
  unfold C.
  apply (BProv_three_exE_of_sentences Ax_s sentence_ax_s
    (composite :: G) body target hex).
  unfold D, inner1, inner2.
  exact hopened.
Qed.

Lemma BProv_Ax_s_term_graph_mul_reverse_of_shifted_operands : forall
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hcore : PAOrdinalCodeMulBoundCoreCompatibility)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 3) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 2 (fun n => codedMap n + 3) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) rightRaw) (tVar 2))) ->
  BProv Ax_s G
    (pImp
      (ordinalCodeGraphTermAt
        (tMul leftRaw rightRaw) (tVar codedOut))
      (compositeTermGraphAt codedOut codedMap (tMul left right))).
Proof.
  intros htotal hcore G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  set (composite := compositeTermGraphAt codedOut codedMap
    (tMul left right)).
  set (target := ordinalCodeGraphTermAt
    (tMul leftRaw rightRaw) (tVar codedOut)).
  set (leftComposite := compositeTermGraphAt 1
    (fun n => codedMap n + 3) left).
  set (rightComposite := compositeTermGraphAt 2
    (fun n => codedMap n + 3) right).
  set (core := compositeMulCoreAt codedOut).
  set (body := pAnd leftComposite (pAnd rightComposite core)).
  apply BProv_impI.
  set (C := target :: G).
  assert (htarget : BProv Ax_s C target).
  { apply BProv_ass. unfold C. simpl. now left. }
  set (rightGraphBody := ordinalCodeGraphTermAt
    (Term.rename S rightRaw) (tVar 0)).
  assert (hrightTotal : BProv Ax_s C (pEx rightGraphBody)).
  { unfold rightGraphBody. exact (htotal C rightRaw). }
  set (R := rightGraphBody :: map (rename S) C).
  set (leftGraphBody := ordinalCodeGraphTermAt
    (Term.rename (fun n => n + 2) leftRaw) (tVar 0)).
  assert (hleftTotal : BProv Ax_s R (pEx leftGraphBody)).
  {
    pose proof (htotal R (Term.rename S leftRaw)) as hraw.
    unfold leftGraphBody.
    replace (Term.rename S (Term.rename S leftRaw))
      with (Term.rename (fun n => n + 2) leftRaw) in hraw.
    - exact hraw.
    - rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
  }
  set (L := leftGraphBody :: map (rename S) R).
  assert (hleftGraph : BProv Ax_s L leftGraphBody).
  { apply BProv_ass. unfold L. simpl. now left. }
  assert (hrightGraphR : BProv Ax_s R rightGraphBody).
  { apply BProv_ass. unfold R. simpl. now left. }
  assert (hrightGraph : BProv Ax_s L
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rightRaw) (tVar 1))).
  {
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      R rightGraphBody hrightGraphR S) as hren.
    pose proof (BProv_context_cons Ax_s (map (rename S) R)
      leftGraphBody _ hren) as hctx.
    unfold L, rightGraphBody in hctx.
    rewrite rename_ordinalCodeGraphTermAt in hctx.
    cbn [Term.rename] in hctx.
    replace (Term.rename S (Term.rename S rightRaw))
      with (Term.rename (fun n => n + 2) rightRaw) in hctx.
    - exact hctx.
    - rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
  }
  set (targetL := ordinalCodeGraphTermAt
    (tMul
      (Term.rename (fun n => n + 2) leftRaw)
      (Term.rename (fun n => n + 2) rightRaw))
    (tVar (codedOut + 2))).
  assert (htargetL : BProv Ax_s L targetL).
  {
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      C target htarget S) as h1.
    pose proof (BProv_context_cons Ax_s (map (rename S) C)
      rightGraphBody _ h1) as h1c.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      R _ h1c S) as h2.
    pose proof (BProv_context_cons Ax_s (map (rename S) R)
      leftGraphBody _ h2) as h2c.
    unfold L, R, C, target, targetL in h2c.
    repeat rewrite rename_ordinalCodeGraphTermAt in h2c.
    cbn [Term.rename] in h2c.
    replace (Term.rename S (Term.rename S leftRaw))
      with (Term.rename (fun n => n + 2) leftRaw) in h2c.
    2: {
      rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (Term.rename S (Term.rename S rightRaw))
      with (Term.rename (fun n => n + 2) rightRaw) in h2c.
    2: {
      rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (S (S codedOut)) with (codedOut + 2) in h2c by lia.
    exact h2c.
  }
  pose proof (hcore L
    (Term.rename (fun n => n + 2) leftRaw)
    (Term.rename (fun n => n + 2) rightRaw)
    codedOut hleftGraph hrightGraph) as hcoreIff.
  assert (hcoreReverse : BProv Ax_s L (pImp targetL (pEx core))).
  {
    unfold iffForm in hcoreIff.
    exact (BProv_andE2 Ax_s L _ _ hcoreIff).
  }
  assert (hcoreEx : BProv Ax_s L (pEx core)).
  { exact (BProv_mp Ax_s L _ _ hcoreReverse htargetL). }
  set (D := core :: map (rename S) L).
  assert (hrenamedComposite : BProv Ax_s D
      (rename S (rename S (rename S composite)))).
  {
    assert (hcoreD : BProv Ax_s D core).
    { apply BProv_ass. unfold D. simpl. now left. }
    (* Reconstruct the existential graph by weakening under its four opened
       assumptions; no additional renaming is performed at this stage. *)
    assert (liftShifted : forall phi,
        BProv Ax_s
          (map (rename S) (map (rename S) (map (rename S) G))) phi ->
        BProv Ax_s D phi).
    {
      intros phi hphi.
      pose proof (BProv_context_prefix Ax_s
        [core; rename S leftGraphBody;
          rename S (rename S rightGraphBody);
          rename S (rename S (rename S target))]
        (map (rename S) (map (rename S) (map (rename S) G)))
        phi hphi) as h.
      unfold D, L, R, C.
      simpl.
      exact h.
    }
    pose proof (liftShifted _ hleft) as hleftD.
    assert (hleftReverse : BProv Ax_s D
        (pImp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 3) leftRaw) (tVar 1))
          leftComposite)).
    {
      unfold iffForm in hleftD.
      exact (BProv_andE2 Ax_s D _ _ hleftD).
    }
    assert (hleftGraphD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3) leftRaw) (tVar 1))).
    {
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        L leftGraphBody hleftGraph S) as hren.
      pose proof (BProv_context_cons Ax_s (map (rename S) L)
        core _ hren) as hctx.
      unfold D, leftGraphBody in hctx.
      rewrite rename_ordinalCodeGraphTermAt in hctx.
      cbn [Term.rename] in hctx.
      replace (Term.rename S
          (Term.rename (fun n => n + 2) leftRaw))
        with (Term.rename (fun n => n + 3) leftRaw) in hctx.
      - exact hctx.
      - rewrite Term.rename_comp.
        apply Term.rename_ext. intro n. lia.
    }
    assert (hleftComposite : BProv Ax_s D leftComposite).
    { exact (BProv_mp Ax_s D _ _ hleftReverse hleftGraphD). }
    pose proof (liftShifted _ hright) as hrightD.
    assert (hrightReverse : BProv Ax_s D
        (pImp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 3) rightRaw) (tVar 2))
          rightComposite)).
    {
      unfold iffForm in hrightD.
      exact (BProv_andE2 Ax_s D _ _ hrightD).
    }
    assert (hrightGraphD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3) rightRaw) (tVar 2))).
    {
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        L _ hrightGraph S) as hren.
      pose proof (BProv_context_cons Ax_s (map (rename S) L)
        core _ hren) as hctx.
      unfold D in hctx.
      rewrite rename_ordinalCodeGraphTermAt in hctx.
      cbn [Term.rename] in hctx.
      replace (Term.rename S
          (Term.rename (fun n => n + 2) rightRaw))
        with (Term.rename (fun n => n + 3) rightRaw) in hctx.
      - exact hctx.
      - rewrite Term.rename_comp.
        apply Term.rename_ext. intro n. lia.
    }
    assert (hrightComposite : BProv Ax_s D rightComposite).
    { exact (BProv_mp Ax_s D _ _ hrightReverse hrightGraphD). }
    assert (hbody : BProv Ax_s D body).
    {
      exact (BProv_andI Ax_s D _ _ hleftComposite
        (BProv_andI Ax_s D _ _ hrightComposite hcoreD)).
    }
    change (BProv Ax_s D
      (rename S (rename S (rename S
        (compositeTermGraphAt codedOut codedMap (tMul left right)))))).
    rewrite compositeTermGraphAt_mul_normalForm.
    apply (BProv_exI Ax_s D _ (tVar 2)).
    apply (BProv_exI Ax_s D _ (tVar 1)).
    apply (BProv_exI Ax_s D _ (tVar 0)).
    change (BProv Ax_s D
      (subst (instTerm (tVar 0))
        (subst (Term.upSubst (instTerm (tVar 1)))
          (subst
            (Term.upSubst (Term.upSubst (instTerm (tVar 2))))
            (rename (Fol.up (Fol.up (Fol.up S)))
              (rename (Fol.up (Fol.up (Fol.up S)))
                (rename (Fol.up (Fol.up (Fol.up S))) body))))))).
    rewrite subst_three_witnesses_rename_three_succ.
    exact hbody.
  }
  assert (hcompositeL : BProv Ax_s L
      (rename S (rename S composite))).
  {
    apply (BProv_exE_of_sentences Ax_s L core
      (rename S (rename S composite)) sentence_ax_s hcoreEx).
    unfold D in hrenamedComposite.
    exact hrenamedComposite.
  }
  assert (hcompositeR : BProv Ax_s R (rename S composite)).
  {
    apply (BProv_exE_of_sentences Ax_s R leftGraphBody
      (rename S composite) sentence_ax_s hleftTotal).
    unfold L in hcompositeL.
    exact hcompositeL.
  }
  assert (hcompositeC : BProv Ax_s C composite).
  {
    apply (BProv_exE_of_sentences Ax_s C rightGraphBody
      composite sentence_ax_s hrightTotal).
    unfold R in hcompositeR.
    exact hcompositeR.
  }
  exact hcompositeC.
Qed.

Lemma BProv_Ax_s_term_graph_mul_of_shifted_operands : forall
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hcores : PAOrdinalCodeMulCoreProofs)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 3) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) (map (rename S) G)))
    (iffForm
      (compositeTermGraphAt 2 (fun n => codedMap n + 3) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 3) rightRaw) (tVar 2))) ->
  BProv Ax_s G
    (iffForm
      (compositeTermGraphAt codedOut codedMap (tMul left right))
      (ordinalCodeGraphTermAt
        (tMul leftRaw rightRaw) (tVar codedOut))).
Proof.
  intros htotal hcores G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  assert (hforward :=
    BProv_Ax_s_term_graph_mul_forward_of_shifted_operands
      (pa_mul_open_core hcores)
      G left right leftRaw rightRaw codedMap codedOut hleft hright).
  assert (hreverse :=
    BProv_Ax_s_term_graph_mul_reverse_of_shifted_operands
      htotal (pa_mul_bound_core hcores)
      G left right leftRaw rightRaw codedMap codedOut hleft hright).
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Theorem PAOrdinalCodeTermMulCompatibility_of_total_cores :
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeMulCoreProofs ->
  PAOrdinalCodeTermMulCompatibility.
Proof.
  intros htotal hcores left right ihleft ihrigh.
  intros G rawMap codedMap codedOut hcode.
  set (G3 := map (rename S) (map (rename S) (map (rename S) G))).
  set (rawMap3 := fun n => rawMap n + 3).
  set (codedMap3 := fun n => codedMap n + 3).
  assert (hcode3 : forall n, Term.Free n (tMul left right) ->
      BProv Ax_s G3
        (ordinalCodeGraphAt (rawMap3 n) (codedMap3 n))).
  {
    intros n hn.
    pose proof (hcode n hn) as h0.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      G _ h0 S) as h1.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      (map (rename S) G) _ h1 S) as h2.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
      (map (rename S) (map (rename S) G)) _ h2 S) as h3.
    unfold G3, rawMap3, codedMap3, ordinalCodeGraphAt.
    unfold ordinalCodeGraphAt in h3.
    repeat rewrite rename_ordinalCodeGraphTermAt in h3.
    cbn [Term.rename] in h3.
    replace (S (S (S (rawMap n)))) with (rawMap n + 3) in h3 by lia.
    replace (S (S (S (codedMap n)))) with (codedMap n + 3) in h3 by lia.
    exact h3.
  }
  assert (hleftCode : forall n, Term.Free n left ->
      BProv Ax_s G3
        (ordinalCodeGraphAt (rawMap3 n) (codedMap3 n))).
  { intros n hn. apply hcode3. now left. }
  assert (hrightCode : forall n, Term.Free n right ->
      BProv Ax_s G3
        (ordinalCodeGraphAt (rawMap3 n) (codedMap3 n))).
  { intros n hn. apply hcode3. now right. }
  pose proof (ihleft G3 rawMap3 codedMap3 1 hleftCode) as hleft0.
  assert (hleft : BProv Ax_s G3
      (iffForm
        (compositeTermGraphAt 1 (fun n => codedMap n + 3) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3)
            (Term.rename rawMap left))
          (tVar 1)))).
  {
    unfold rawMap3, codedMap3 in hleft0.
    replace (Term.rename (fun n => rawMap n + 3) left)
      with (Term.rename (fun n => n + 3)
        (Term.rename rawMap left)) in hleft0.
    - exact hleft0.
    - rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. reflexivity.
  }
  pose proof (ihrigh G3 rawMap3 codedMap3 2 hrightCode) as hright0.
  assert (hright : BProv Ax_s G3
      (iffForm
        (compositeTermGraphAt 2 (fun n => codedMap n + 3) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 3)
            (Term.rename rawMap right))
          (tVar 2)))).
  {
    unfold rawMap3, codedMap3 in hright0.
    replace (Term.rename (fun n => rawMap n + 3) right)
      with (Term.rename (fun n => n + 3)
        (Term.rename rawMap right)) in hright0.
    - exact hright0.
    - rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. reflexivity.
  }
  pose proof (BProv_Ax_s_term_graph_mul_of_shifted_operands
    htotal hcores G left right
    (Term.rename rawMap left) (Term.rename rawMap right)
    codedMap codedOut hleft hright) as hmul.
  cbn [Term.rename].
  exact hmul.
Qed.
