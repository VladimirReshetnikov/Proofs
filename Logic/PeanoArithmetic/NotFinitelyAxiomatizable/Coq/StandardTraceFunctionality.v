(**
  Cross-table functionality of the fixed program-trace evaluator.

  The two satisfying evaluator assignments may choose completely unrelated
  beta codes and beta steps.  Standard-row inversion exposes their recursive
  lookups, and strong induction on the external row code identifies the two
  tables entry by entry.
*)

From Stdlib Require Import List Arith Lia Classical
  Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding ProgramTrace TotalProgramRows
  EvaluatorCutContract StandardTraceRows.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PASkolemProgramCode.
Import PAFiniteBetaCoding.
Import PAProgramTrace.
Import PATotalProgramRows.
Import PAEvaluatorCutContract.
Import PAStandardTraceRows.

Module PAStandardTraceFunctionality.

(** Every displayed entry occurs in its standard fixed-width code list. *)
Lemma standardCodeList_in : forall start count codes i,
  start <= i < start + count ->
  In (codes i) (standardCodeList start count codes).
Proof.
  intros start count codes i hi.
  unfold standardCodeList.
  apply in_map. apply in_seq. lia.
Qed.

(** Equality of fixed-width code lists is pointwise equality on the displayed
    interval. *)
Lemma standardCodeList_eq_pointwise : forall start count left right,
  standardCodeList start count left =
    standardCodeList start count right ->
  forall i, start <= i < start + count -> left i = right i.
Proof.
  intros start count. revert start.
  induction count as [|count IH]; intros start left right hlists i hi.
  - lia.
  - rewrite !standardCodeList_succ in hlists.
    injection hlists as hhead htail.
    destruct (Nat.eq_dec i start) as [-> | hne].
    + exact hhead.
    + apply (IH (S start) left right htail i). lia.
Qed.

Lemma standardCodeList_length : forall start count codes,
  length (standardCodeList start count codes) = count.
Proof.
  intros start count codes. unfold standardCodeList.
  now rewrite length_map, length_seq.
Qed.

(** Only the first [rank] entries of a chooser environment are observable. *)
Lemma boundedEnv_ext : forall (M : RawPAModel) rank left right,
  (forall i, i < rank -> left i = right i) ->
  boundedEnv M rank left = boundedEnv M rank right.
Proof.
  intros M rank left right heq.
  apply functional_extensionality. intro i.
  unfold boundedEnv.
  destruct (i <? rank) eqn:hi; [|reflexivity].
  apply Nat.ltb_lt in hi. apply heq. exact hi.
Qed.

Lemma raw_term_eval_liftTerm_scons : forall (M : RawPAModel) x e t,
  raw_term_eval M (scons M x e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M x e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Ltac reject_distinct_row_tags hleft hright :=
  let hnode := fresh "hnode" in
  let htag := fresh "htag" in
  pose proof (eq_trans (eq_sym hleft) hright) as hnode;
  apply polynomialNode_injective in hnode;
  destruct hnode as [htag _];
  unfold tagSeed, tagZero, tagSucc, tagAdd, tagMul, tagChoose in htag;
  lia.

(** Two recognized rows at the same standard parent code have equal outputs
    once the two beta tables agree at every strictly earlier child code. *)
Theorem standardRowWitness_output_eq_of_child_entries : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall target
    (betaCode1 betaStep1 betaCode2 betaStep2
      seed value1 value2 :
      skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)),
  (forall child, child < target ->
    forall x y :
      skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M),
    RawBetaEntry
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
      x betaCode1 betaStep1
      (rawNumeralValue
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
        child) ->
    RawBetaEntry
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
      y betaCode2 betaStep2
      (rawNumeralValue
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
        child) ->
    x = y) ->
  StandardRowWitness
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    rank target betaCode1 betaStep1 seed value1 ->
  StandardRowWitness
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    rank target betaCode2 betaStep2 seed value2 ->
  value1 = value2.
Proof.
  intros M ambientSeed rank hPA hLtRank target
    betaCode1 betaStep1 betaCode2 betaStep2 seed value1 value2
    hchildren hleft hright.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  destruct hleft as
    [ht1 hv1
    | ht1 hv1
    | c1 x1 ht1 hx1 hv1
    | l1 r1 x1 y1 ht1 hx1 hy1 hv1
    | l1 r1 x1 y1 ht1 hx1 hy1 hv1
    | i1 codes1 values1 hi1 ht1 hlook1 hgraph1];
  destruct hright as
    [ht2 hv2
    | ht2 hv2
    | c2 x2 ht2 hx2 hv2
    | l2 r2 x2 y2 ht2 hx2 hy2 hv2
    | l2 r2 x2 y2 ht2 hx2 hy2 hv2
    | i2 codes2 values2 hi2 ht2 hlook2 hgraph2].
  all: try solve [reject_distinct_row_tags ht1 ht2].
  all: try solve [congruence].
  - assert (hc : c1 = c2).
    {
      assert (hnode : polynomialNode tagSucc c1 =
        polynomialNode tagSucc c2) by congruence.
      exact (proj2 (polynomialNode_injective
        tagSucc c1 tagSucc c2 hnode)).
    }
    subst c2. rewrite hv1, hv2. f_equal.
    eapply hchildren.
    + rewrite ht1. apply polynomialNode_payload_lt.
    + exact hx1.
    + exact hx2.
  - assert (hp : polynomialPair l1 r1 = polynomialPair l2 r2).
    {
      assert (hnode :
        polynomialNode tagAdd (polynomialPair l1 r1) =
        polynomialNode tagAdd (polynomialPair l2 r2)) by congruence.
      exact (proj2 (polynomialNode_injective
        tagAdd (polynomialPair l1 r1)
        tagAdd (polynomialPair l2 r2) hnode)).
    }
    destruct (polynomialPair_injective l1 r1 l2 r2 hp) as [hl hr].
    subst l2. subst r2. rewrite hv1, hv2. f_equal.
    + eapply hchildren.
      * rewrite ht1. eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * exact hx1.
      * exact hx2.
    + eapply hchildren.
      * rewrite ht1. eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * exact hy1.
      * exact hy2.
  - assert (hp : polynomialPair l1 r1 = polynomialPair l2 r2).
    {
      assert (hnode :
        polynomialNode tagMul (polynomialPair l1 r1) =
        polynomialNode tagMul (polynomialPair l2 r2)) by congruence.
      exact (proj2 (polynomialNode_injective
        tagMul (polynomialPair l1 r1)
        tagMul (polynomialPair l2 r2) hnode)).
    }
    destruct (polynomialPair_injective l1 r1 l2 r2 hp) as [hl hr].
    subst l2. subst r2. rewrite hv1, hv2. f_equal.
    + eapply hchildren.
      * rewrite ht1. eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * exact hx1.
      * exact hx2.
    + eapply hchildren.
      * rewrite ht1. eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * exact hy1.
      * exact hy2.
  - assert (hp :
      polynomialPair i1
        (argsCodeOfCodes (standardCodeList 0 rank codes1)) =
      polynomialPair i2
        (argsCodeOfCodes (standardCodeList 0 rank codes2))).
    {
      assert (hnode :
        polynomialNode tagChoose
          (polynomialPair i1
            (argsCodeOfCodes (standardCodeList 0 rank codes1))) =
        polynomialNode tagChoose
          (polynomialPair i2
            (argsCodeOfCodes (standardCodeList 0 rank codes2)))) by
        congruence.
      exact (proj2 (polynomialNode_injective
        tagChoose
          (polynomialPair i1
            (argsCodeOfCodes (standardCodeList 0 rank codes1)))
        tagChoose
          (polynomialPair i2
            (argsCodeOfCodes (standardCodeList 0 rank codes2))) hnode)).
    }
    destruct (polynomialPair_injective i1
      (argsCodeOfCodes (standardCodeList 0 rank codes1)) i2
      (argsCodeOfCodes (standardCodeList 0 rank codes2)) hp)
      as [hindex hargs].
    subst i2.
    assert (hlists :
      standardCodeList 0 rank codes1 =
      standardCodeList 0 rank codes2).
    {
      pose proof (decodeFixedArgs_codes
        (standardCodeList 0 rank codes1)) as hdecode1.
      pose proof (decodeFixedArgs_codes
        (standardCodeList 0 rank codes2)) as hdecode2.
      rewrite !standardCodeList_length in hdecode1, hdecode2.
      rewrite hargs in hdecode1. congruence.
    }
    assert (hcodes : forall j, j < rank -> codes1 j = codes2 j).
    {
      intros j hj.
      eapply (standardCodeList_eq_pointwise 0 rank codes1 codes2);
        [exact hlists | lia].
    }
    assert (hvalues : forall j, j < rank -> values1 j = values2 j).
    {
      intros j hj. eapply hchildren.
      - rewrite ht1. eapply Nat.lt_trans.
        + apply argsCodeOfCodes_entry_lt.
          apply (standardCodeList_in 0 rank codes1 j). lia.
        + eapply Nat.le_lt_trans.
          * apply polynomialPair_right_le.
          * apply polynomialNode_payload_lt.
      - exact (hlook1 j hj).
      - pose proof (hlook2 j hj) as hlookup.
        rewrite <- (hcodes j hj) in hlookup. exact hlookup.
    }
    assert (henv : boundedEnv K rank values1 =
      boundedEnv K rank values2).
    {
      apply boundedEnv_ext. exact hvalues.
    }
    rewrite <- henv in hgraph2.
    eapply (skolemHull_canonicalSelectorFormula_functional
      M ambientSeed rank (rawCanonicalSelector M)).
    + apply rawCanonicalSelector_witnesses.
      exact (raw_definable_least_number_of_pa M hPA).
    + exact hLtRank.
    + exact (raw_order_trichotomy M hPA).
    + exact hgraph1.
    + exact hgraph2.
Qed.

(** Rebase a recognized row onto another beta table.  Earlier-entry
    existence in the target table plus cross-table uniqueness lets us retain
    the source row's child values and therefore its output verbatim. *)
Theorem standardRowWitness_transfer : forall
    (K : RawPAModel) rank target
    (sourceCode sourceStep targetCode targetStep seed value : K),
  (forall child, child < target -> exists y : K,
    RawBetaEntry K y targetCode targetStep
      (rawNumeralValue K child)) ->
  (forall child, child < target -> forall x y : K,
    RawBetaEntry K x sourceCode sourceStep
      (rawNumeralValue K child) ->
    RawBetaEntry K y targetCode targetStep
      (rawNumeralValue K child) -> x = y) ->
  StandardRowWitness K rank target
    sourceCode sourceStep seed value ->
  StandardRowWitness K rank target
    targetCode targetStep seed value.
Proof.
  intros K rank target sourceCode sourceStep targetCode targetStep seed value
    htarget hchildren hrow.
  destruct hrow as
    [ht hv
    | ht hv
    | child childValue ht hlookup hv
    | left right leftValue rightValue ht hleft hright hv
    | left right leftValue rightValue ht hleft hright hv
    | index codes values hi ht hlook hgraph].
  - now apply standardRowSeed.
  - now apply standardRowZero.
  - apply standardRowSucc with (childCode := child)
      (childValue := childValue); try assumption.
    destruct (htarget child) as [other hother].
    + rewrite ht. apply polynomialNode_payload_lt.
    + assert (childValue = other) by
        (eapply hchildren; [rewrite ht; apply polynomialNode_payload_lt
          | exact hlookup | exact hother]).
      now subst other.
  - apply standardRowAdd with (leftCode := left) (rightCode := right)
      (leftValue := leftValue) (rightValue := rightValue); try assumption.
    + destruct (htarget left) as [other hother].
      * rewrite ht. eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * assert (leftValue = other) by
          (eapply hchildren;
            [rewrite ht; eapply Nat.le_lt_trans;
              [apply polynomialPair_left_le | apply polynomialNode_payload_lt]
            | exact hleft | exact hother]).
        now subst other.
    + destruct (htarget right) as [other hother].
      * rewrite ht. eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * assert (rightValue = other) by
          (eapply hchildren;
            [rewrite ht; eapply Nat.le_lt_trans;
              [apply polynomialPair_right_le | apply polynomialNode_payload_lt]
            | exact hright | exact hother]).
        now subst other.
  - apply standardRowMul with (leftCode := left) (rightCode := right)
      (leftValue := leftValue) (rightValue := rightValue); try assumption.
    + destruct (htarget left) as [other hother].
      * rewrite ht. eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * assert (leftValue = other) by
          (eapply hchildren;
            [rewrite ht; eapply Nat.le_lt_trans;
              [apply polynomialPair_left_le | apply polynomialNode_payload_lt]
            | exact hleft | exact hother]).
        now subst other.
    + destruct (htarget right) as [other hother].
      * rewrite ht. eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * assert (rightValue = other) by
          (eapply hchildren;
            [rewrite ht; eapply Nat.le_lt_trans;
              [apply polynomialPair_right_le | apply polynomialNode_payload_lt]
            | exact hright | exact hother]).
        now subst other.
  - apply standardRowChoose with (formulaIndex := index)
      (codes := codes) (values := values); try assumption.
    intros i hit.
    destruct (htarget (codes i)) as [other hother].
    + rewrite ht. eapply Nat.lt_trans.
      * apply argsCodeOfCodes_entry_lt.
        apply (standardCodeList_in 0 rank codes i). lia.
      * eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
    + assert (values i = other) by
        (eapply hchildren;
          [rewrite ht; eapply Nat.lt_trans;
            [apply argsCodeOfCodes_entry_lt;
              apply (standardCodeList_in 0 rank codes i); lia
            | eapply Nat.le_lt_trans;
              [apply polynomialPair_right_le | apply polynomialNode_payload_lt]]
          | exact (hlook i hit) | exact hother]).
      now subst other.
Qed.

(** The concrete free-variable convention used by the cut contract is
    output, code, seed. *)
Definition traceEvaluator (rank : nat) : PA.formula :=
  evaluator rank (PA.tVar 1) (PA.tVar 0) (PA.tVar 2).

(** Standard hull numerals preserve external non-strict order. *)
Lemma skolemHull_rawLe_numeralValue_of_le : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall left right, left <= right ->
  rawLe (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) left)
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) right).
Proof.
  intros M ambientSeed rank hPA hLtRank left right hle.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)).
  destruct (Nat.eq_dec left right) as [-> | hne].
  - exists (raw_zero K).
    apply (skolemHullVal_injective M ambientSeed rank
      (rawCanonicalSelector M)).
    rewrite skolemHullVal_add, skolemHullVal_zero,
      !skolemHull_rawNumeralValue_val.
    change (raw_add M (rawNumeralValue M right)
      (rawNumeralValue M 0) = rawNumeralValue M right).
    rewrite (raw_add_numeral_values M hPA right 0).
    now rewrite Nat.add_0_r.
  - apply raw_lt_to_le.
    apply (skolemHull_rawLt_of_ambient M ambientSeed rank
      (rawCanonicalSelector M)).
    + apply rawCanonicalSelector_witnesses.
      exact (raw_definable_least_number_of_pa M hPA).
    + exact hLtRank.
    + rewrite !skolemHull_rawNumeralValue_val.
      apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
Qed.

(** A beta table carrying genuine/default row witnesses through a standard
    target.  The tail and seed term are retained so the default guard can be
    challenged in exactly the environment in which it was asserted. *)
Record StandardProgramTable (M : RawPAModel) (rank : nat)
    (seed : M) (target : nat) : Type := {
  spt_betaCode : M;
  spt_betaStep : M;
  spt_tail : nat -> M;
  spt_seedTerm : PA.term;
  spt_seed_eq : raw_term_eval M spt_tail spt_seedTerm = seed;
  spt_row : forall code, code <= target -> exists value : M,
    RawBetaEntry M value spt_betaCode spt_betaStep
      (rawNumeralValue M code) /\
    raw_formula_sat M
      (evaluatorRowEnv M value (rawNumeralValue M code)
        spt_betaStep spt_betaCode spt_tail)
      (programStep rank (PA.tVar 1) (PA.tVar 0)
        (PA.tVar 3) (PA.tVar 2) (liftTerm 4 spt_seedTerm))
}.

Arguments spt_betaCode {M rank seed target} _.
Arguments spt_betaStep {M rank seed target} _.
Arguments spt_tail {M rank seed target} _.
Arguments spt_seedTerm {M rank seed target} _.
Arguments spt_seed_eq {M rank seed target} _.
Arguments spt_row {M rank seed target} _ code _.

(** A normalized genuine row rebased onto a table contradicts that table's
    output-independent default guard.  The extra [scons] is exactly the
    existential output slot introduced by [noProgramCase]. *)
Lemma noProgramCase_refutes_standardRowWitness : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall seed target
    (table : StandardProgramTable
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
      rank seed target)
    code oldValue proposed,
  raw_formula_sat
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    (evaluatorRowEnv _ oldValue
      (rawNumeralValue
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) code)
      table.(spt_betaStep) table.(spt_betaCode) table.(spt_tail))
    (noProgramCase rank (PA.tVar 1) (PA.tVar 3) (PA.tVar 2)
      (liftTerm 4 table.(spt_seedTerm))) ->
  StandardRowWitness
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    rank code table.(spt_betaCode) table.(spt_betaStep) seed proposed ->
  False.
Proof.
  intros M ambientSeed rank hPA hLtRank seed target table code
    oldValue proposed hno hwitness.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  set (rowEnv := evaluatorRowEnv K oldValue (rawNumeralValue K code)
    table.(spt_betaStep) table.(spt_betaCode) table.(spt_tail)) in *.
  apply (proj1 (raw_sat_noProgramCase_iff K rank
    (PA.tVar 1) (PA.tVar 3) (PA.tVar 2)
    (liftTerm 4 table.(spt_seedTerm)) rowEnv)) in hno.
  apply hno. exists proposed.
  eapply (sat_programCases_of_standardRowWitness
    M ambientSeed rank hPA hLtRank code
    (liftTerm 1 (PA.tVar 1)) (PA.tVar 0)
    (liftTerm 1 (PA.tVar 3)) (liftTerm 1 (PA.tVar 2))
    (liftTerm 1 (liftTerm 4 table.(spt_seedTerm)))
    (scons K proposed rowEnv)).
  - reflexivity.
  - rewrite !raw_term_eval_liftTerm_scons.
    change (StandardRowWitness K rank code
      table.(spt_betaCode) table.(spt_betaStep)
      (raw_term_eval K rowEnv (liftTerm 4 table.(spt_seedTerm))) proposed).
    unfold rowEnv, evaluatorRowEnv.
    rewrite raw_term_eval_liftTerm_four_scons.
    rewrite table.(spt_seed_eq). exact hwitness.
Qed.

Lemma standardRowWitness_of_table_programCases : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  forall seed target
    (table : StandardProgramTable
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
      rank seed target)
    code value,
  raw_formula_sat
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    (evaluatorRowEnv _ value
      (rawNumeralValue
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) code)
      table.(spt_betaStep) table.(spt_betaCode) table.(spt_tail))
    (programCases rank (PA.tVar 1) (PA.tVar 0)
      (PA.tVar 3) (PA.tVar 2) (liftTerm 4 table.(spt_seedTerm))) ->
  StandardRowWitness
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    rank code table.(spt_betaCode) table.(spt_betaStep) seed value.
Proof.
  intros M ambientSeed rank hPA seed target table code value hcases.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  pose proof (standardRowWitness_of_sat_programCases
    M ambientSeed rank hPA code
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
    (liftTerm 4 table.(spt_seedTerm))
    (evaluatorRowEnv K value (rawNumeralValue K code)
      table.(spt_betaStep) table.(spt_betaCode) table.(spt_tail))
    eq_refl hcases) as hrow.
  unfold evaluatorRowEnv in hrow.
  rewrite raw_term_eval_liftTerm_four_scons in hrow.
  rewrite table.(spt_seed_eq) in hrow. exact hrow.
Qed.

(** Strong induction compares arbitrary beta tables entry by entry. *)
Theorem StandardProgramTable_entries_eq : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall seed target
    (left right : StandardProgramTable
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
      rank seed target)
    code, code <= target ->
  forall x y :
    skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M),
  RawBetaEntry
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    x left.(spt_betaCode) left.(spt_betaStep)
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) code) ->
  RawBetaEntry
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    y right.(spt_betaCode) right.(spt_betaStep)
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) code) ->
  x = y.
Proof.
  intros M ambientSeed rank hPA hLtRank hBetaRank seed target
    left right code.
  induction code as [code IH] using (well_founded_induction lt_wf).
  intros hcode x y hx hy.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  destruct (left.(spt_row) code hcode) as
    [leftValue [hleftEntry hleftStep]].
  destruct (right.(spt_row) code hcode) as
    [rightValue [hrightEntry hrightStep]].
  assert (hxrow : x = leftValue).
  {
    eapply (skolemHull_rawBetaEntry_functional
      M ambientSeed rank (rawCanonicalSelector M)).
    - apply rawCanonicalSelector_witnesses.
      exact (raw_definable_least_number_of_pa M hPA).
    - exact hBetaRank.
    - exact hPA.
    - exact hx.
    - exact hleftEntry.
  }
  assert (hyrow : y = rightValue).
  {
    eapply (skolemHull_rawBetaEntry_functional
      M ambientSeed rank (rawCanonicalSelector M)).
    - apply rawCanonicalSelector_witnesses.
      exact (raw_definable_least_number_of_pa M hPA).
    - exact hBetaRank.
    - exact hPA.
    - exact hy.
    - exact hrightEntry.
  }
  subst x. subst y.
  assert (hchildren : forall child, child < code -> forall a b : K,
    RawBetaEntry K a left.(spt_betaCode) left.(spt_betaStep)
      (rawNumeralValue K child) ->
    RawBetaEntry K b right.(spt_betaCode) right.(spt_betaStep)
      (rawNumeralValue K child) -> a = b).
  {
    intros child hchild a b ha hb.
    eapply IH; [exact hchild | lia | exact ha | exact hb].
  }
  assert (hleftTotal : forall child, child < code -> exists a : K,
    RawBetaEntry K a left.(spt_betaCode) left.(spt_betaStep)
      (rawNumeralValue K child)).
  {
    intros child hchild.
    destruct (left.(spt_row) child (ltac:(lia))) as [a [ha _]].
    now exists a.
  }
  assert (hrightTotal : forall child, child < code -> exists b : K,
    RawBetaEntry K b right.(spt_betaCode) right.(spt_betaStep)
      (rawNumeralValue K child)).
  {
    intros child hchild.
    destruct (right.(spt_row) child (ltac:(lia))) as [b [hb _]].
    now exists b.
  }
  apply (proj1 (raw_sat_programStep_iff K rank
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
    (liftTerm 4 left.(spt_seedTerm))
    (evaluatorRowEnv K leftValue (rawNumeralValue K code)
      left.(spt_betaStep) left.(spt_betaCode) left.(spt_tail))))
    in hleftStep.
  apply (proj1 (raw_sat_programStep_iff K rank
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
    (liftTerm 4 right.(spt_seedTerm))
    (evaluatorRowEnv K rightValue (rawNumeralValue K code)
      right.(spt_betaStep) right.(spt_betaCode) right.(spt_tail))))
    in hrightStep.
  destruct hleftStep as [hleftCases | [hleftNo hleftZero]];
  destruct hrightStep as [hrightCases | [hrightNo hrightZero]].
  - apply (standardRowWitness_output_eq_of_child_entries
      M ambientSeed rank hPA hLtRank code
      left.(spt_betaCode) left.(spt_betaStep)
      right.(spt_betaCode) right.(spt_betaStep)
      seed leftValue rightValue hchildren).
    + apply (standardRowWitness_of_table_programCases
        M ambientSeed rank hPA seed target left code leftValue).
      exact hleftCases.
    + apply (standardRowWitness_of_table_programCases
        M ambientSeed rank hPA seed target right code rightValue).
      exact hrightCases.
  - exfalso.
    eapply (noProgramCase_refutes_standardRowWitness
      M ambientSeed rank hPA hLtRank seed target right
      code rightValue leftValue).
    + exact hrightNo.
    + eapply (standardRowWitness_transfer K rank code
        left.(spt_betaCode) left.(spt_betaStep)
        right.(spt_betaCode) right.(spt_betaStep) seed leftValue).
      * exact hrightTotal.
      * exact hchildren.
      * apply (standardRowWitness_of_table_programCases
          M ambientSeed rank hPA seed target left code leftValue).
        exact hleftCases.
  - exfalso.
    eapply (noProgramCase_refutes_standardRowWitness
      M ambientSeed rank hPA hLtRank seed target left
      code leftValue rightValue).
    + exact hleftNo.
    + eapply (standardRowWitness_transfer K rank code
        right.(spt_betaCode) right.(spt_betaStep)
        left.(spt_betaCode) left.(spt_betaStep) seed rightValue).
      * exact hleftTotal.
      * intros child hchild a b ha hb.
        symmetry. eapply hchildren; eassumption.
      * apply (standardRowWitness_of_table_programCases
          M ambientSeed rank hPA seed target right code rightValue).
        exact hrightCases.
  - cbn [raw_term_eval evaluatorRowEnv scons] in hleftZero, hrightZero.
    congruence.
Qed.

(** The fixed trace evaluator is functional at every standard numeral code,
    even when its two satisfying assignments choose unrelated beta tables. *)
Theorem traceEvaluator_standardCode_functional : forall
    (M : RawPAModel) (ambientSeed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall target
    (x y : skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)),
  Evaluates
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    (traceEvaluator rank)
    (skolemHullSeed M ambientSeed rank (rawCanonicalSelector M))
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) target)
    x ->
  Evaluates
    (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
    (traceEvaluator rank)
    (skolemHullSeed M ambientSeed rank (rawCanonicalSelector M))
    (rawNumeralValue
      (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M)) target)
    y ->
  x = y.
Proof.
  intros M ambientSeed rank hPA hLtRank hBetaRank target x y hx hy.
  set (K := skolemHullRawModel M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  set (seedK := skolemHullSeed M ambientSeed rank
    (rawCanonicalSelector M)) in *.
  set (targetK := rawNumeralValue K target) in *.
  set (leftEnv := evalEnv K seedK targetK x) in *.
  set (rightEnv := evalEnv K seedK targetK y) in *.
  change (raw_formula_sat K leftEnv
    (evaluator rank (PA.tVar 1) (PA.tVar 0) (PA.tVar 2))) in hx.
  change (raw_formula_sat K rightEnv
    (evaluator rank (PA.tVar 1) (PA.tVar 0) (PA.tVar 2))) in hy.
  destruct (proj1 (raw_sat_evaluator_iff K rank
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 2) leftEnv) hx)
    as [leftCode [leftStep [hxTarget hxRows]]].
  destruct (proj1 (raw_sat_evaluator_iff K rank
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 2) rightEnv) hy)
    as [rightCode [rightStep [hyTarget hyRows]]].
  cbn [raw_term_eval evalEnv] in hxTarget, hyTarget, hxRows, hyRows.
  change (RawBetaEntry K x leftCode leftStep targetK) in hxTarget.
  change (RawBetaEntry K y rightCode rightStep targetK) in hyTarget.
  pose (leftTable :=
    ({| spt_betaCode := leftCode;
       spt_betaStep := leftStep;
       spt_tail := leftEnv;
       spt_seedTerm := PA.tVar 2;
       spt_seed_eq := eq_refl;
       spt_row := fun code hcode =>
         let hle := skolemHull_rawLe_numeralValue_of_le
           M ambientSeed rank hPA hLtRank code target hcode in
         hxRows (rawNumeralValue K code) hle |} :
      StandardProgramTable K rank seedK target)).
  pose (rightTable :=
    ({| spt_betaCode := rightCode;
       spt_betaStep := rightStep;
       spt_tail := rightEnv;
       spt_seedTerm := PA.tVar 2;
       spt_seed_eq := eq_refl;
       spt_row := fun code hcode =>
         let hle := skolemHull_rawLe_numeralValue_of_le
           M ambientSeed rank hPA hLtRank code target hcode in
         hyRows (rawNumeralValue K code) hle |} :
      StandardProgramTable K rank seedK target)).
  eapply (StandardProgramTable_entries_eq
    M ambientSeed rank hPA hLtRank hBetaRank seedK target
    leftTable rightTable target (Nat.le_refl target) x y).
  - exact hxTarget.
  - exact hyTarget.
Qed.

End PAStandardTraceFunctionality.
