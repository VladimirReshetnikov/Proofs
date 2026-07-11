(* ===================================================================== *)
(*  PAHFOrdinalCodeTermMulCorrected.v                                   *)
(*                                                                       *)
(*  Sound structural lifting of multiplication compatibility.           *)
(*                                                                       *)
(*  The historical open multiplication core asks for an invalid reverse *)
(*  implication.  The forward term-graph construction only consumes the *)
(*  sound forward half; the reverse construction already uses the exact  *)
(*  existentially bound core.  This module reconnects those two halves.  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFProofCalculus
  PAHFDeductiveAssembly PAHFCompositeArithmetic
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFRoundTripQuantifiers
  PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeTermOperations
  PAHFOrdinalCodeTermMul PAHFOrdinalCodeMulCore
  PAHFRoundTripArithmeticAssembly.

Import ListNotations.
Import PA PA.Term PA.Formula.

Lemma BProv_Ax_s_term_graph_mul_forward_of_shifted_operands_corrected :
  forall
    (hcore : PAOrdinalCodeMulOpenCoreForwardCompatibility)
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
      codedOut hleftGraph hrightGraph) as hcoreForward.
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

Lemma BProv_Ax_s_term_graph_mul_of_shifted_operands_corrected : forall
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hcores : PAOrdinalCodeMulCoreProofsCorrected)
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
    BProv_Ax_s_term_graph_mul_forward_of_shifted_operands_corrected
      (pa_mul_open_core_forward hcores)
      G left right leftRaw rightRaw codedMap codedOut hleft hright).
  assert (hreverse :=
    BProv_Ax_s_term_graph_mul_reverse_of_shifted_operands
      htotal (pa_mul_bound_core_exact hcores)
      G left right leftRaw rightRaw codedMap codedOut hleft hright).
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Theorem PAOrdinalCodeTermMulCompatibility_of_total_corrected_cores :
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeMulCoreProofsCorrected ->
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
  pose proof (BProv_Ax_s_term_graph_mul_of_shifted_operands_corrected
    htotal hcores G left right
    (Term.rename rawMap left) (Term.rename rawMap right)
    codedMap codedOut hleft hright) as hmul.
  cbn [Term.rename].
  exact hmul.
Qed.

(* --------------------------------------------------------------------- *)
(* Corrected arithmetic round-trip assembly.                             *)

Definition PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs_corrected
    (hadjoin : PAHFAdjoinExistence)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PAOrdinalCodeTermMulCompatibility :=
  PAOrdinalCodeTermMulCompatibility_of_total_corrected_cores
    (PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs hadjoin)
    hmul.

Definition PACompositeTermGraphProof_of_arithmetic_inputs_corrected
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeTermGraphProof :=
  PACompositeTermGraphProof_of_base_add_mul
    (PAOrdinalCodeTermBaseCompatibilityProofs_of_arithmetic_inputs
      hext hadjoin)
    (PAOrdinalCodeTermAddCompatibility_of_arithmetic_inputs
      hadjoin hadd)
    (PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs_corrected
      hadjoin hmul).

Definition PACompositeEqualityProof_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeEqualityProof :=
  pa_composite_eq_exact_of_adjoin_injective_termGraph
    hadjoin
    (PAOrdinalCodeGraphInjectiveProof_of_arithmetic_inputs P)
    (PACompositeTermGraphProof_of_arithmetic_inputs_corrected
      hext hadjoin hadd hmul).

Definition PACompositeConstructorProofs_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeConstructorProofs :=
  PACompositeConstructorProofs_of_eq_and_quantifiers
    (PACompositeEqualityProof_of_arithmetic_inputs_corrected
      P hext hadjoin hadd hmul)
    (PAOrdinalCodeQuantifierProofs_of_arithmetic_inputs
      P hext hadjoin).

Definition PARoundTripProof_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PARoundTripProof :=
  PARoundTripProof_of_constructorProofs
    (PACompositeConstructorProofs_of_arithmetic_inputs_corrected
      P hext hadjoin hadd hmul).
