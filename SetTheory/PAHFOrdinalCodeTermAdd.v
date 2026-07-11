(* ===================================================================== *)
(*  PAHFOrdinalCodeTermAdd.v                                            *)
(*                                                                       *)
(*  Structural lifting of the ordinal-code addition core to arbitrary    *)
(*  PA terms.  The arithmetic core itself is an explicit argument; this  *)
(*  file contains only proof-calculus and binder bookkeeping.            *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFProofCalculus
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeTermOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Forward direction after both recursive operand theorems have been
    instantiated below the two fresh output-code binders. *)
Lemma BProv_Ax_s_term_graph_add_forward_of_shifted_operands : forall
    (hcore : PAOrdinalCodeAddCoreCompatibility)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rightRaw) (tVar 0))) ->
  BProv Ax_s G
    (pImp
      (compositeTermGraphAt codedOut codedMap (tAdd left right))
      (ordinalCodeGraphTermAt
        (tAdd leftRaw rightRaw) (tVar codedOut))).
Proof.
  intros hcore G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  set (composite := compositeTermGraphAt codedOut codedMap
    (tAdd left right)).
  set (target := ordinalCodeGraphTermAt
    (tAdd leftRaw rightRaw) (tVar codedOut)).
  set (leftComposite := compositeTermGraphAt 1
    (fun n => codedMap n + 2) left).
  set (rightComposite := compositeTermGraphAt 0
    (fun n => codedMap n + 2) right).
  set (core := compositeAddCoreAt codedOut).
  set (body := pAnd leftComposite (pAnd rightComposite core)).
  apply BProv_impI.
  set (C := composite :: G).
  assert (hcomposite : BProv Ax_s C composite).
  { apply BProv_ass. unfold C. simpl. now left. }
  assert (hex : BProv Ax_s C (pEx (pEx body))).
  {
    unfold composite in hcomposite.
    rewrite compositeTermGraphAt_add_normalForm in hcomposite.
    unfold body, leftComposite, rightComposite, core.
    exact hcomposite.
  }
  set (inner := pEx body).
  set (D := body :: map (rename S) (inner :: map (rename S) C)).
  assert (hopened : BProv Ax_s D (rename S (rename S target))).
  {
    assert (hbody : BProv Ax_s D body).
    { apply BProv_ass. unfold D. simpl. now left. }
    pose proof (BProv_andE1 Ax_s D _ _ hbody) as hleftComposite.
    pose proof (BProv_andE2 Ax_s D _ _ hbody) as htail.
    pose proof (BProv_andE1 Ax_s D _ _ htail) as hrightComposite.
    pose proof (BProv_andE2 Ax_s D _ _ htail) as hcoreD.
    (* The operand induction hypotheses are already shifted twice.  Opening
       the two output witnesses only prepends the three formulas listed
       below, so generic prefix weakening is sufficient. *)
    assert (liftShifted : forall phi,
        BProv Ax_s (map (rename S) (map (rename S) G)) phi ->
        BProv Ax_s D phi).
    {
      intros phi hphi.
      pose proof (BProv_context_prefix Ax_s
        [body; rename S inner; rename S (rename S composite)]
        (map (rename S) (map (rename S) G)) phi hphi) as h.
      unfold D, C.
      simpl.
      exact h.
    }
    pose proof (liftShifted _ hleft) as hleftD.
    assert (hleftForward : BProv Ax_s D
        (pImp leftComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 2) leftRaw) (tVar 1)))).
    {
      unfold iffForm in hleftD.
      exact (BProv_andE1 Ax_s D _ _ hleftD).
    }
    assert (hleftGraph : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2) leftRaw) (tVar 1))).
    { exact (BProv_mp Ax_s D _ _ hleftForward hleftComposite). }
    pose proof (liftShifted _ hright) as hrightD.
    assert (hrightForward : BProv Ax_s D
        (pImp rightComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 2) rightRaw) (tVar 0)))).
    {
      unfold iffForm in hrightD.
      exact (BProv_andE1 Ax_s D _ _ hrightD).
    }
    assert (hrightGraph : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2) rightRaw) (tVar 0))).
    { exact (BProv_mp Ax_s D _ _ hrightForward hrightComposite). }
    pose proof (hcore D
      (Term.rename (fun n => n + 2) leftRaw)
      (Term.rename (fun n => n + 2) rightRaw)
      codedOut hleftGraph hrightGraph) as hcoreIff.
    assert (hcoreForward : BProv Ax_s D
        (pImp core
          (ordinalCodeGraphTermAt
            (tAdd
              (Term.rename (fun n => n + 2) leftRaw)
              (Term.rename (fun n => n + 2) rightRaw))
            (tVar (codedOut + 2))))).
    {
      unfold iffForm in hcoreIff.
      exact (BProv_andE1 Ax_s D _ _ hcoreIff).
    }
    pose proof (BProv_mp Ax_s D _ _ hcoreForward hcoreD) as htarget.
    unfold target.
    repeat rewrite rename_ordinalCodeGraphTermAt.
    cbn [Term.rename].
    replace (Term.rename S (Term.rename S leftRaw))
      with (Term.rename (fun n => n + 2) leftRaw).
    2: {
      rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (Term.rename S (Term.rename S rightRaw))
      with (Term.rename (fun n => n + 2) rightRaw).
    2: {
      rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
    }
    replace (S (S codedOut)) with (codedOut + 2) by lia.
    exact htarget.
  }
  unfold C.
  apply (BProv_two_exE_of_sentences Ax_s sentence_ax_s
    (composite :: G) body target hex).
  unfold D, inner.
  exact hopened.
Qed.

(** Reverse direction chooses codes for the two raw operands by graph
    totality, then reconstructs the translated existential witnesses. *)
Lemma BProv_Ax_s_term_graph_add_reverse_of_shifted_operands : forall
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hcore : PAOrdinalCodeAddCoreCompatibility)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rightRaw) (tVar 0))) ->
  BProv Ax_s G
    (pImp
      (ordinalCodeGraphTermAt
        (tAdd leftRaw rightRaw) (tVar codedOut))
      (compositeTermGraphAt codedOut codedMap (tAdd left right))).
Proof.
  intros htotal hcore G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  set (composite := compositeTermGraphAt codedOut codedMap
    (tAdd left right)).
  set (target := ordinalCodeGraphTermAt
    (tAdd leftRaw rightRaw) (tVar codedOut)).
  set (leftComposite := compositeTermGraphAt 1
    (fun n => codedMap n + 2) left).
  set (rightComposite := compositeTermGraphAt 0
    (fun n => codedMap n + 2) right).
  set (core := compositeAddCoreAt codedOut).
  set (body := pAnd leftComposite (pAnd rightComposite core)).
  apply BProv_impI.
  set (C := target :: G).
  assert (htarget : BProv Ax_s C target).
  { apply BProv_ass. unfold C. simpl. now left. }
  set (leftGraphBody := ordinalCodeGraphTermAt
    (Term.rename S leftRaw) (tVar 0)).
  assert (hleftTotal : BProv Ax_s C (pEx leftGraphBody)).
  {
    unfold leftGraphBody.
    exact (htotal C leftRaw).
  }
  set (L := leftGraphBody :: map (rename S) C).
  set (rightGraphBody := ordinalCodeGraphTermAt
    (Term.rename (fun n => n + 2) rightRaw) (tVar 0)).
  assert (hrightTotal : BProv Ax_s L (pEx rightGraphBody)).
  {
    pose proof (htotal L (Term.rename S rightRaw)) as hraw.
    unfold rightGraphBody.
    replace (Term.rename S (Term.rename S rightRaw))
      with (Term.rename (fun n => n + 2) rightRaw) in hraw.
    - exact hraw.
    - rewrite Term.rename_comp.
      apply Term.rename_ext. intro n. lia.
  }
  set (R := rightGraphBody :: map (rename S) L).
  assert (hrenamedComposite : BProv Ax_s R
      (rename S (rename S composite))).
  {
    assert (hrightGraph : BProv Ax_s R rightGraphBody).
    { apply BProv_ass. unfold R. simpl. now left. }
    assert (hleftGraphL : BProv Ax_s L leftGraphBody).
    { apply BProv_ass. unfold L. simpl. now left. }
    assert (hleftGraph : BProv Ax_s R
        (ordinalCodeGraphTermAt
          (Term.rename (fun n => n + 2) leftRaw) (tVar 1))).
    {
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        L leftGraphBody hleftGraphL S) as hren.
      pose proof (BProv_context_cons Ax_s (map (rename S) L)
        rightGraphBody _ hren) as hctx.
      unfold R, leftGraphBody in hctx.
      rewrite rename_ordinalCodeGraphTermAt in hctx.
      cbn [Term.rename] in hctx.
      replace (Term.rename S (Term.rename S leftRaw))
        with (Term.rename (fun n => n + 2) leftRaw) in hctx.
      - exact hctx.
      - rewrite Term.rename_comp.
        apply Term.rename_ext. intro n. lia.
    }
    assert (htargetR : BProv Ax_s R
        (ordinalCodeGraphTermAt
          (tAdd
            (Term.rename (fun n => n + 2) leftRaw)
            (Term.rename (fun n => n + 2) rightRaw))
          (tVar (codedOut + 2)))).
    {
      pose proof (BProv_lift_two_contexts_of_sentences
        Ax_s sentence_ax_s C leftGraphBody rightGraphBody target htarget)
        as h2c.
      unfold R, L, C, target in h2c.
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
    (* The reverse branch has the same shifted tail but a different local
       prefix: right witness, left witness, then the translated target. *)
    assert (liftShifted : forall phi,
        BProv Ax_s (map (rename S) (map (rename S) G)) phi ->
        BProv Ax_s R phi).
    {
      intros phi hphi.
      pose proof (BProv_context_prefix Ax_s
        [rightGraphBody; rename S leftGraphBody;
          rename S (rename S target)]
        (map (rename S) (map (rename S) G)) phi hphi) as h.
      unfold R, L, C.
      simpl.
      exact h.
    }
    pose proof (liftShifted _ hleft) as hleftR.
    assert (hleftReverse : BProv Ax_s R
        (pImp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 2) leftRaw) (tVar 1))
          leftComposite)).
    {
      unfold iffForm in hleftR.
      exact (BProv_andE2 Ax_s R _ _ hleftR).
    }
    assert (hleftComposite : BProv Ax_s R leftComposite).
    { exact (BProv_mp Ax_s R _ _ hleftReverse hleftGraph). }
    pose proof (liftShifted _ hright) as hrightR.
    assert (hrightReverse : BProv Ax_s R
        (pImp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n => n + 2) rightRaw) (tVar 0))
          rightComposite)).
    {
      unfold iffForm in hrightR.
      exact (BProv_andE2 Ax_s R _ _ hrightR).
    }
    assert (hrightComposite : BProv Ax_s R rightComposite).
    { exact (BProv_mp Ax_s R _ _ hrightReverse hrightGraph). }
    pose proof (hcore R
      (Term.rename (fun n => n + 2) leftRaw)
      (Term.rename (fun n => n + 2) rightRaw)
      codedOut hleftGraph hrightGraph) as hcoreIff.
    assert (hcoreReverse : BProv Ax_s R
        (pImp
          (ordinalCodeGraphTermAt
            (tAdd
              (Term.rename (fun n => n + 2) leftRaw)
              (Term.rename (fun n => n + 2) rightRaw))
            (tVar (codedOut + 2)))
          core)).
    {
      unfold iffForm in hcoreIff.
      exact (BProv_andE2 Ax_s R _ _ hcoreIff).
    }
    assert (hcoreR : BProv Ax_s R core).
    { exact (BProv_mp Ax_s R _ _ hcoreReverse htargetR). }
    assert (hbody : BProv Ax_s R body).
    {
      exact (BProv_andI Ax_s R _ _ hleftComposite
        (BProv_andI Ax_s R _ _ hrightComposite hcoreR)).
    }
    change (BProv Ax_s R
      (rename S (rename S
        (compositeTermGraphAt codedOut codedMap (tAdd left right))))).
    rewrite compositeTermGraphAt_add_normalForm.
    apply (BProv_exI Ax_s R _ (tVar 1)).
    apply (BProv_exI Ax_s R _ (tVar 0)).
    change (BProv Ax_s R
      (subst (instTerm (tVar 0))
        (subst (Term.upSubst (instTerm (tVar 1)))
          (rename (Fol.up (Fol.up S))
            (rename (Fol.up (Fol.up S)) body))))).
    rewrite subst_instTerm_var_zero_up_var_one_rename_up_up_succ_twice.
    exact hbody.
  }
  assert (hcompositeL : BProv Ax_s L (rename S composite)).
  {
    apply (BProv_exE_of_sentences Ax_s L rightGraphBody
      (rename S composite) sentence_ax_s hrightTotal).
    unfold R in hrenamedComposite.
    exact hrenamedComposite.
  }
  assert (hcompositeC : BProv Ax_s C composite).
  {
    apply (BProv_exE_of_sentences Ax_s C leftGraphBody
      composite sentence_ax_s hleftTotal).
    unfold L in hcompositeL.
    exact hcompositeL.
  }
  exact hcompositeC.
Qed.

Lemma BProv_Ax_s_term_graph_add_of_shifted_operands : forall
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hcore : PAOrdinalCodeAddCoreCompatibility)
    G left right leftRaw rightRaw codedMap codedOut,
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) leftRaw) (tVar 1))) ->
  BProv Ax_s
    (map (rename S) (map (rename S) G))
    (iffForm
      (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) rightRaw) (tVar 0))) ->
  BProv Ax_s G
    (iffForm
      (compositeTermGraphAt codedOut codedMap (tAdd left right))
      (ordinalCodeGraphTermAt
        (tAdd leftRaw rightRaw) (tVar codedOut))).
Proof.
  intros htotal hcore G left right leftRaw rightRaw codedMap codedOut
    hleft hright.
  assert (hforward :=
    BProv_Ax_s_term_graph_add_forward_of_shifted_operands
      hcore G left right leftRaw rightRaw codedMap codedOut
      hleft hright).
  assert (hreverse :=
    BProv_Ax_s_term_graph_add_reverse_of_shifted_operands
      htotal hcore G left right leftRaw rightRaw codedMap codedOut
      hleft hright).
  unfold iffForm.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

(** Addition preserves the complete term-graph property once graph
    totality and the operation core are available. *)
Theorem PAOrdinalCodeTermAddCompatibility_of_total_core :
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeAddCoreCompatibility ->
  PAOrdinalCodeTermAddCompatibility.
Proof.
  intros htotal hcore left right ihleft ihrigh.
  intros G rawMap codedMap codedOut hcode.
  set (G2 := map (rename S) (map (rename S) G)).
  set (rawMap2 := fun n => rawMap n + 2).
  set (codedMap2 := fun n => codedMap n + 2).
  assert (hcode2 : forall n, Term.Free n (tAdd left right) ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  {
    intros n hn.
    pose proof (hcode n hn) as h0.
    pose proof (BProv_iterRenameSucc_of_sentences
      Ax_s sentence_ax_s 2 G _ h0) as h2.
    cbn [iterRenameContextSucc iterRenameSucc] in h2.
    unfold G2, rawMap2, codedMap2, ordinalCodeGraphAt.
    unfold ordinalCodeGraphAt in h2.
    repeat rewrite rename_ordinalCodeGraphTermAt in h2.
    cbn [Term.rename] in h2.
    replace (S (S (rawMap n))) with (rawMap n + 2) in h2 by lia.
    replace (S (S (codedMap n))) with (codedMap n + 2) in h2 by lia.
    exact h2.
  }
  assert (hleftCode : forall n, Term.Free n left ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  { intros n hn. apply hcode2. now left. }
  assert (hrightCode : forall n, Term.Free n right ->
      BProv Ax_s G2
        (ordinalCodeGraphAt (rawMap2 n) (codedMap2 n))).
  { intros n hn. apply hcode2. now right. }
  pose proof (ihleft G2 rawMap2 codedMap2 1 hleftCode) as hleft0.
  assert (hleft : BProv Ax_s G2
      (iffForm
        (compositeTermGraphAt 1 (fun n => codedMap n + 2) left)
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
      apply Term.rename_ext. intro n. reflexivity.
  }
  pose proof (ihrigh G2 rawMap2 codedMap2 0 hrightCode) as hright0.
  assert (hright : BProv Ax_s G2
      (iffForm
        (compositeTermGraphAt 0 (fun n => codedMap n + 2) right)
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
      apply Term.rename_ext. intro n. reflexivity.
  }
  pose proof (BProv_Ax_s_term_graph_add_of_shifted_operands
    htotal hcore G left right
    (Term.rename rawMap left) (Term.rename rawMap right)
    codedMap codedOut hleft hright) as hadd.
  cbn [Term.rename].
  exact hadd.
Qed.
