(** Totality of the fixed trace evaluator at every standard program code. *)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding ProgramTrace TotalProgramRows
  EvaluatorCutContract StandardTraceRows StandardTraceFunctionality
  CanonicalTotalRows.

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
Import PAStandardTraceFunctionality.
Import PACanonicalTotalRows.

Module PATotalTraceEvaluator.

(** Transport the externally finite table into the hull.  Its two beta
    parameters are themselves hull values represented by finite programs. *)
Theorem finite_total_row_beta_hull : forall
    (M : RawPAModel) seed rank target,
  RawPASatisfies M ->
  formula_rank betaCodeExtensionSelectorBody <= rank ->
  formula_rank hullBetaFormula <= rank ->
  exists codeProgram stepProgram,
    forall k, k <= target ->
    RawBetaEntry
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank k))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        codeProgram)
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        stepProgram)
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) k).
Proof.
  intros M seed rank target hPA hExtensionRank hBetaRank.
  destruct (finite_total_row_beta_programs
    M seed rank rank target hPA hExtensionRank)
    as [codeProgram [stepProgram htable]].
  exists codeProgram, stepProgram. intros k hk.
  assert (hselector : SelectorWitnesses M (rawCanonicalSelector M)).
  {
    apply rawCanonicalSelector_witnesses.
    exact (raw_definable_least_number_of_pa M hPA).
  }
  apply (proj2 (skolemHull_rawBetaEntry_iff_ambient
    M seed rank (rawCanonicalSelector M) hselector hBetaRank
    _ _ _ _)).
  rewrite !skolemHullProgramValue_val,
    skolemHull_rawNumeralValue_val.
  exact (htable k hk).
Qed.

Lemma skolemHull_rawLe_to_ambient : forall
    (M : RawPAModel) seed rank selector
    (x y : skolemHullRawModel M seed rank selector),
  rawLe (skolemHullRawModel M seed rank selector) x y ->
  rawLe M
    (skolemHullVal M seed rank selector x)
    (skolemHullVal M seed rank selector y).
Proof.
  intros M seed rank selector x y [gap hgap].
  exists (skolemHullVal M seed rank selector gap).
  apply (f_equal (skolemHullVal M seed rank selector)) in hgap.
  now rewrite skolemHullVal_add in hgap.
Qed.

(** Every hull element below a standard non-strict bound is a standard
    numeral.  This is proved in the ambient PA model; the finite hull itself
    is not assumed to satisfy induction. *)
Lemma skolemHull_rawLe_numeralValue_cases : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  forall x target,
  rawLe (skolemHullRawModel M seed rank (rawCanonicalSelector M)) x
    (rawNumeralValue
      (skolemHullRawModel M seed rank (rawCanonicalSelector M)) target) ->
  exists k, k <= target /\
    x = rawNumeralValue
      (skolemHullRawModel M seed rank (rawCanonicalSelector M)) k.
Proof.
  intros M seed rank hPA x target hle.
  set (K := skolemHullRawModel M seed rank (rawCanonicalSelector M)).
  pose proof (skolemHull_rawLe_to_ambient M seed rank
    (rawCanonicalSelector M) x (rawNumeralValue K target) hle)
    as hambient.
  rewrite skolemHull_rawNumeralValue_val in hambient.
  destruct (raw_order_trichotomy M hPA
    (skolemHullVal M seed rank (rawCanonicalSelector M) x)
    (rawNumeralValue M target)) as [heq | [hlt | hgt]].
  - exists target. split; [lia |].
    apply (skolemHullVal_injective M seed rank (rawCanonicalSelector M)).
    now rewrite skolemHull_rawNumeralValue_val.
  - destruct (raw_lt_numeralValue_cases M hPA _ target hlt)
      as [k [hk heq]].
    exists k. split; [lia |].
    apply (skolemHullVal_injective M seed rank (rawCanonicalSelector M)).
    now rewrite skolemHull_rawNumeralValue_val.
  - exfalso.
    pose proof (raw_le_antisymm M hPA _ _ hambient
      (raw_lt_to_le M _ _ hgt)) as heq.
    rewrite heq in hgt.
    exact (raw_not_lt_self M hPA (rawNumeralValue M target) hgt).
Qed.

(** Any genuine row over the canonical finite table computes the value of
    the total row program.  This also handles the one apparent ambiguity in
    the decoder: [spZero] is both the genuine zero row and the value assigned
    to malformed/default row codes. *)
Theorem standardRowWitness_matches_totalRow : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall betaCode betaStep target proposed,
  (forall child, child < target ->
    RawBetaEntry
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank child))
      betaCode betaStep
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) child)) ->
  StandardRowWitness
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    rank target betaCode betaStep
    (skolemHullSeed M seed rank (rawCanonicalSelector M)) proposed ->
  proposed = skolemHullProgramValue M seed rank (rawCanonicalSelector M)
    (totalRowProgram rank target).
Proof.
  intros M seed rank hPA hLtRank hBetaRank
    betaCode betaStep target proposed htable hrow.
  set (K := skolemHullRawModel M seed rank (rawCanonicalSelector M)) in *.
  destruct (canonicalStandardRowWitness_or_zero
    M seed rank hPA hLtRank betaCode betaStep target htable)
    as [hcanonical | hzero].
  - eapply (standardRowWitness_output_eq_of_child_entries
      M seed rank hPA hLtRank target
      betaCode betaStep betaCode betaStep
      (skolemHullSeed M seed rank (rawCanonicalSelector M))
      proposed
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank target))).
    + intros child hchild x y hx hy.
      eapply (skolemHull_rawBetaEntry_functional
        M seed rank (rawCanonicalSelector M)).
      * apply rawCanonicalSelector_witnesses.
        exact (raw_definable_least_number_of_pa M hPA).
      * exact hBetaRank.
      * exact hPA.
      * exact hx.
      * exact hy.
    + exact hrow.
    + exact hcanonical.
  - rewrite hzero, skolemHullProgramValue_zero.
    destruct hrow as
      [ht hv
      | ht hv
      | child childValue ht hchild hv
      | lhs rhs leftValue rightValue ht hleft hright hv
      | lhs rhs leftValue rightValue ht hleft hright hv
      | formulaIndex codes values hindex ht hlook hgraph].
    + exfalso.
      assert (hschedule : scheduleSkolemCode target = siSeed).
      {
        rewrite ht. change (scheduleSkolemCode (skolemProgramCode spSeed) =
          siSeed). rewrite scheduleSkolemCode_program. reflexivity.
      }
      pose proof (totalRowProgram_of_seed rank target hschedule) as hp.
      rewrite hzero in hp. discriminate.
    + exact hv.
    + exfalso.
      assert (hschedule : scheduleSkolemCode target = siSucc child).
      {
        rewrite ht. unfold scheduleSkolemCode.
        rewrite polynomialUnnode_node. reflexivity.
      }
      assert (hsmaller : child < target).
      { rewrite ht. apply polynomialNode_payload_lt. }
      pose proof (totalRowProgram_of_succ rank target child
        hschedule hsmaller) as hp.
      rewrite hzero in hp. discriminate.
    + exfalso.
      assert (hschedule : scheduleSkolemCode target = siAdd lhs rhs).
      {
        rewrite ht. unfold scheduleSkolemCode.
        rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
      }
      assert (hl : lhs < target).
      {
        rewrite ht. eapply Nat.le_lt_trans.
        - apply polynomialPair_left_le.
        - apply polynomialNode_payload_lt.
      }
      assert (hr : rhs < target).
      {
        rewrite ht. eapply Nat.le_lt_trans.
        - apply polynomialPair_right_le.
        - apply polynomialNode_payload_lt.
      }
      pose proof (totalRowProgram_of_add rank target lhs rhs
        hschedule hl hr) as hp.
      rewrite hzero in hp. discriminate.
    + exfalso.
      assert (hschedule : scheduleSkolemCode target = siMul lhs rhs).
      {
        rewrite ht. unfold scheduleSkolemCode.
        rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
      }
      assert (hl : lhs < target).
      {
        rewrite ht. eapply Nat.le_lt_trans.
        - apply polynomialPair_left_le.
        - apply polynomialNode_payload_lt.
      }
      assert (hr : rhs < target).
      {
        rewrite ht. eapply Nat.le_lt_trans.
        - apply polynomialPair_right_le.
        - apply polynomialNode_payload_lt.
      }
      pose proof (totalRowProgram_of_mul rank target lhs rhs
        hschedule hl hr) as hp.
      rewrite hzero in hp. discriminate.
    + exfalso.
      set (childCodes := standardCodeList 0 rank codes).
      assert (hschedule : scheduleSkolemCode target =
        siChoose formulaIndex (argsCodeOfCodes childCodes)).
      {
        unfold childCodes. rewrite ht. unfold scheduleSkolemCode.
        rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
      }
      assert (hdecode : decodeFixedArgs rank
        (argsCodeOfCodes childCodes) = Some childCodes).
      {
        replace rank with (length childCodes).
        - apply decodeFixedArgs_codes.
        - unfold childCodes. apply standardCodeList_length.
      }
      assert (hchildren : forall child,
        In child childCodes -> child < target).
      {
        intros child hin. rewrite ht.
        eapply Nat.lt_trans.
        - apply argsCodeOfCodes_entry_lt. exact hin.
        - eapply Nat.le_lt_trans.
          + apply polynomialPair_right_le.
          + apply polynomialNode_payload_lt.
      }
      pose proof (totalRowProgram_of_choose rank target formulaIndex
        (argsCodeOfCodes childCodes) childCodes hschedule hindex
        hdecode hchildren) as hp.
      rewrite hzero in hp. discriminate.
Qed.

(** The canonical finite-table entry satisfies the genuine row formula when
    a constructor is recognized, and otherwise satisfies the
    output-independent default guard with value zero. *)
Theorem canonical_total_row_programStep : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall betaCode betaStep target,
  (forall child, child < target ->
    RawBetaEntry
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank child))
      betaCode betaStep
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) child)) ->
  forall tail seedTerm,
  raw_term_eval
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    tail seedTerm =
    skolemHullSeed M seed rank (rawCanonicalSelector M) ->
  raw_formula_sat
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    (evaluatorRowEnv
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (totalRowProgram rank target))
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) target)
      betaStep betaCode tail)
    (programStep rank (PA.tVar 1) (PA.tVar 0)
      (PA.tVar 3) (PA.tVar 2) (liftTerm 4 seedTerm)).
Proof.
  intros M seed rank hPA hLtRank hBetaRank
    betaCode betaStep target htable tail seedTerm hseed.
  set (K := skolemHullRawModel M seed rank (rawCanonicalSelector M)) in *.
  set (rowValue := skolemHullProgramValue M seed rank
    (rawCanonicalSelector M) (totalRowProgram rank target)) in *.
  set (rowEnv := evaluatorRowEnv K rowValue
    (rawNumeralValue K target) betaStep betaCode tail) in *.
  destruct (classic (StandardRowWitness K rank target betaCode betaStep
    (skolemHullSeed M seed rank (rawCanonicalSelector M)) rowValue))
    as [hrow | hnoRow].
  - apply (proj2 (raw_sat_programStep_iff K rank
      (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
      (liftTerm 4 seedTerm) rowEnv)).
    left.
    eapply (sat_programCases_of_standardRowWitness
      M seed rank hPA hLtRank target
      (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
      (liftTerm 4 seedTerm) rowEnv).
    + reflexivity.
    + unfold rowEnv, evaluatorRowEnv.
      cbn [raw_term_eval scons].
      rewrite raw_term_eval_liftTerm_four_scons, hseed.
      exact hrow.
  - apply (proj2 (raw_sat_programStep_iff K rank
      (PA.tVar 1) (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
      (liftTerm 4 seedTerm) rowEnv)).
    right. split.
    + apply (proj2 (raw_sat_noProgramCase_iff K rank
        (PA.tVar 1) (PA.tVar 3) (PA.tVar 2)
        (liftTerm 4 seedTerm) rowEnv)).
      intros [proposed hcases].
      pose proof (standardRowWitness_of_sat_programCases
        M seed rank hPA target
        (liftTerm 1 (PA.tVar 1)) (PA.tVar 0)
        (liftTerm 1 (PA.tVar 3)) (liftTerm 1 (PA.tVar 2))
        (liftTerm 1 (liftTerm 4 seedTerm))
        (scons K proposed rowEnv) eq_refl hcases) as hproposed.
      unfold rowEnv, evaluatorRowEnv in hproposed.
      rewrite !raw_term_eval_liftTerm_scons in hproposed.
      cbn [raw_term_eval scons] in hproposed.
      rewrite raw_term_eval_liftTerm_four_scons, hseed in hproposed.
      assert (heq : proposed = rowValue).
      {
        eapply (standardRowWitness_matches_totalRow
          M seed rank hPA hLtRank hBetaRank
          betaCode betaStep target proposed htable).
        exact hproposed.
      }
      apply hnoRow. now rewrite <- heq.
    + unfold rowEnv, evaluatorRowEnv.
      cbn [raw_term_eval scons].
      destruct (canonicalStandardRowWitness_or_zero
        M seed rank hPA hLtRank betaCode betaStep target htable)
        as [hrow | hzero].
      * contradiction.
      * unfold rowValue. rewrite hzero.
        apply skolemHullProgramValue_zero.
Qed.

(** The canonical total-row value is accepted by the trace evaluator at
    every external standard code. *)
Theorem traceEvaluator_total_at_totalRow : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank betaCodeExtensionSelectorBody <= rank ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall target,
  Evaluates
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    (traceEvaluator rank)
    (skolemHullSeed M seed rank (rawCanonicalSelector M))
    (rawNumeralValue
      (skolemHullRawModel M seed rank (rawCanonicalSelector M)) target)
    (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
      (totalRowProgram rank target)).
Proof.
  intros M seed rank hPA hExtensionRank hLtRank hBetaRank target.
  set (K := skolemHullRawModel M seed rank (rawCanonicalSelector M)).
  set (seedK := skolemHullSeed M seed rank (rawCanonicalSelector M)).
  set (rowValue := fun k => skolemHullProgramValue M seed rank
    (rawCanonicalSelector M) (totalRowProgram rank k)).
  set (targetK := rawNumeralValue K target).
  set (tail := evalEnv K seedK targetK (rowValue target)).
  destruct (finite_total_row_beta_hull M seed rank target hPA
    hExtensionRank hBetaRank) as [codeProgram [stepProgram htable]].
  set (betaCode := skolemHullProgramValue M seed rank
    (rawCanonicalSelector M) codeProgram).
  set (betaStep := skolemHullProgramValue M seed rank
    (rawCanonicalSelector M) stepProgram).
  unfold Evaluates, traceEvaluator.
  eapply (raw_sat_evaluator_of_standard_table K rank target
    (PA.tVar 1) (PA.tVar 0) (PA.tVar 2) tail
    betaCode betaStep rowValue).
  - reflexivity.
  - reflexivity.
  - intros rowCode hle.
    exact (skolemHull_rawLe_numeralValue_cases
      M seed rank hPA rowCode target hle).
  - intros k hk. unfold rowValue, betaCode, betaStep.
    exact (htable k hk).
  - intros k hk.
    eapply (canonical_total_row_programStep
      M seed rank hPA hLtRank hBetaRank betaCode betaStep k).
    + intros child hchild. unfold rowValue, betaCode, betaStep in *.
      apply htable. lia.
    + reflexivity.
Qed.

(** Every element of the hull is denoted by a trace-normalized program.
    Its external program code is therefore a standard input at which the
    evaluator returns that element. *)
Theorem traceEvaluator_standardCode_total : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank betaCodeExtensionSelectorBody <= rank ->
  formula_rank hullLtFormula <= rank ->
  formula_rank hullBetaFormula <= rank ->
  forall output :
    skolemHullRawModel M seed rank (rawCanonicalSelector M),
  exists code : nat,
    Evaluates
      (skolemHullRawModel M seed rank (rawCanonicalSelector M))
      (traceEvaluator rank)
      (skolemHullSeed M seed rank (rawCanonicalSelector M))
      (rawNumeralValue
        (skolemHullRawModel M seed rank (rawCanonicalSelector M)) code)
      output.
Proof.
  intros M seed rank hPA hExtensionRank hLtRank hBetaRank output.
  set (source := skolemHullProgram M seed rank
    (rawCanonicalSelector M) output).
  set (normalized := normalizeTraceProgram rank source).
  set (code := skolemProgramCode normalized).
  exists code.
  pose proof (traceEvaluator_total_at_totalRow
    M seed rank hPA hExtensionRank hLtRank hBetaRank code) as htotal.
  assert (htrace : TraceProgram rank normalized).
  { unfold normalized. apply normalizeTraceProgram_trace. }
  assert (hrow : totalRowProgram rank code = normalized).
  {
    unfold code. apply totalRowProgram_trace. exact htrace.
  }
  assert (hvalue : skolemHullProgramValue M seed rank
    (rawCanonicalSelector M) normalized = output).
  {
    apply (skolemHullVal_injective M seed rank (rawCanonicalSelector M)).
    rewrite skolemHullProgramValue_val.
    unfold normalized, source.
    rewrite (normalizeTraceProgram_eval M hPA seed rank).
    apply skolemHullProgram_spec.
  }
  rewrite hrow, hvalue in htotal. exact htotal.
Qed.

End PATotalTraceEvaluator.
