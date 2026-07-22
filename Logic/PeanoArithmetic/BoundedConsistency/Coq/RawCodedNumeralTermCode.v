(**
  Transparent numeral-term syntax codes at nonstandard levels.

  In every raw PA model, an explicit beta trace starts with the code of
  [tZero] and repeatedly applies the transparent [tSucc] code constructor.
  A genuine PA induction instance proves that such a trace reaches every
  carrier element, including nonstandard ones.  This is a reusable first
  component of a uniform proof package; it does not by itself construct a
  bounded-consistency proof certificate.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedFormulaRankTotality RawCodedFixedLevelTruthTotality.

Import ListNotations.

Module PABoundedRawCodedNumeralTermCode.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.

Definition numeralCodeLiftTerm (n : nat) (t : term) : term :=
  Term.rename (fun index => index + n) t.

(** ------------------------------------------------------------------
    A transparent trace for codes of numeral terms.

    The trace is a beta-coded function whose zeroth value is the code of
    [tZero] and whose successor value is obtained with the transparent
    [tSucc] syntax-code constructor.  It is kept as a relation rather than a
    carrier-level recursive function, since a raw nonstandard model cannot
    be eliminated into a Rocq recursion over [nat]. *)

Definition RawNumeralTermCodeRows (M : RawPAModel)
    (bound code step : M) : Prop :=
  forall index current next : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M code step index current ->
    RawCodedAssignmentLookup M code step (raw_succ M index) next ->
    next = rawTermSuccCode M current.

Arguments RawNumeralTermCodeRows M bound code step : clear implicits.

Definition RawNumeralTermCodeTrace (M : RawPAModel)
    (bound code step : M) : Prop :=
  RawCodedAssignmentDefinedThrough M code step (raw_succ M bound) /\
  RawCodedAssignmentLookup M code step (raw_zero M) (rawTermZeroCode M) /\
  RawNumeralTermCodeRows M bound code step.

Arguments RawNumeralTermCodeTrace M bound code step : clear implicits.

Definition RawNumeralTermCodeAt (M : RawPAModel)
    (bound output : M) : Prop :=
  exists code step : M,
    RawNumeralTermCodeTrace M bound code step /\
    RawCodedAssignmentLookup M code step bound output.

Arguments RawNumeralTermCodeAt M bound output : clear implicits.

(** Formula-facing row relation.  Under the three universal binders the
    variables 2, 1, and 0 are [index], [current], and [next]. *)
Definition numeralTermCodeRowsTermAt
    (bound code step : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (numeralCodeLiftTerm 3 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (numeralCodeLiftTerm 3 code) (numeralCodeLiftTerm 3 step)
          (tVar 2) (tVar 1))
        (pImp
          (codedAssignmentLookupTermAt
            (numeralCodeLiftTerm 3 code) (numeralCodeLiftTerm 3 step)
            (tSucc (tVar 2)) (tVar 0))
          (termSuccCodeTermAt (tVar 0) (tVar 1))))))).

Lemma raw_numeralCode_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (numeralCodeLiftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold numeralCodeLiftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia. reflexivity.
Qed.

Lemma raw_sat_numeralTermCodeRowsTermAt_iff : forall
    (M : RawPAModel) e bound code step,
  raw_formula_sat M e
    (numeralTermCodeRowsTermAt bound code step) <->
  RawNumeralTermCodeRows M
    (raw_term_eval M e bound)
    (raw_term_eval M e code) (raw_term_eval M e step).
Proof.
  intros M e bound code step.
  unfold numeralTermCodeRowsTermAt, RawNumeralTermCodeRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_termSuccCodeTermAt_iff.
  repeat setoid_rewrite raw_numeralCode_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition numeralTermCodeTraceTermAt
    (bound code step : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt
      code step (tSucc bound))
    (pAnd
      (codedAssignmentLookupTermAt
        code step tZero (codeList1Term (Term.numeral 1)))
      (numeralTermCodeRowsTermAt bound code step)).

Lemma raw_sat_numeralTermCodeTraceTermAt_iff : forall
    (M : RawPAModel) e bound code step,
  raw_formula_sat M e
    (numeralTermCodeTraceTermAt bound code step) <->
  RawNumeralTermCodeTrace M
    (raw_term_eval M e bound)
    (raw_term_eval M e code) (raw_term_eval M e step).
Proof.
  intros M e bound code step.
  unfold numeralTermCodeTraceTermAt, RawNumeralTermCodeTrace.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_numeralTermCodeRowsTermAt_iff.
  rewrite raw_eval_codeList1Term, raw_term_eval_numeral.
  cbn [raw_term_eval].
  unfold rawTermZeroCode. reflexivity.
Qed.

Definition numeralTermCodeAtTermAt
    (bound output : term) : formula :=
  pEx (pEx
    (pAnd
      (numeralTermCodeTraceTermAt
        (numeralCodeLiftTerm 2 bound) (tVar 1) (tVar 0))
      (codedAssignmentLookupTermAt
        (tVar 1) (tVar 0)
        (numeralCodeLiftTerm 2 bound) (numeralCodeLiftTerm 2 output)))).

Lemma raw_numeralCode_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (numeralCodeLiftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold numeralCodeLiftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_sat_numeralTermCodeAtTermAt_iff : forall
    (M : RawPAModel) e bound output,
  raw_formula_sat M e (numeralTermCodeAtTermAt bound output) <->
  RawNumeralTermCodeAt M
    (raw_term_eval M e bound) (raw_term_eval M e output).
Proof.
  intros M e bound output.
  unfold numeralTermCodeAtTermAt, RawNumeralTermCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeTraceTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_numeralCode_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawNumeralTermCodeExists (M : RawPAModel) (bound : M) : Prop :=
  exists output : M, RawNumeralTermCodeAt M bound output.

Arguments RawNumeralTermCodeExists M bound : clear implicits.

Definition numeralTermCodeExistsTermAt (bound : term) : formula :=
  pEx (numeralTermCodeAtTermAt (numeralCodeLiftTerm 1 bound) (tVar 0)).

Lemma raw_numeralCode_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (numeralCodeLiftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold numeralCodeLiftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_sat_numeralTermCodeExistsTermAt_iff : forall
    (M : RawPAModel) e bound,
  raw_formula_sat M e (numeralTermCodeExistsTermAt bound) <->
  RawNumeralTermCodeExists M (raw_term_eval M e bound).
Proof.
  intros M e bound.
  unfold numeralTermCodeExistsTermAt, RawNumeralTermCodeExists.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_numeralCode_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The base trace has one entry, namely the code of [tZero]. *)
Lemma raw_numeralTermCodeExists_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawNumeralTermCodeExists M (raw_zero M).
Proof.
  intros M hPA.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    (raw_zero M) (raw_zero M) (raw_zero M)
    (rawTermZeroCode M)
    (raw_codedAssignment_empty_defined M hPA))
    as (code & step & hdefined & _ & hlookup).
  exists (rawTermZeroCode M), code, step. split.
  - repeat split.
    + exact hdefined.
    + exact hlookup.
    + intros index current next hlt _ _.
      exfalso. exact (raw_not_lt_zero M hPA index hlt).
  - exact hlookup.
Qed.

(** Appending the transparent successor constructor extends a trace by one
    row.  Functionality of the beta table identifies the old last entry. *)
Lemma raw_numeralTermCodeExists_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound,
  RawNumeralTermCodeExists M bound ->
  RawNumeralTermCodeExists M (raw_succ M bound).
Proof.
  intros M hPA bound
    (output & code & step & [hdefined [hzero hrows]] & houtput).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    code step (raw_succ M bound) (rawTermSuccCode M output) hdefined)
    as (newCode & newStep & hnewDefined & hpreserved & hnewLookup).
  exists (rawTermSuccCode M output), newCode, newStep. split.
  - repeat split.
    + exact hnewDefined.
    + apply hpreserved.
      * apply raw_lt_succ_of_le; [exact hPA |].
        apply raw_rank_zero_le. exact hPA.
      * exact hzero.
    + intros index current next hindex hcurrent hnext.
      destruct (raw_lt_succ_cases M hPA index bound hindex) as
          [hlt | heq].
      * assert (hindexOldBound : rawLt M index (raw_succ M bound)).
        {
          exact (raw_assignment_lt_trans M hPA
            index bound (raw_succ M bound) hlt
            (raw_assignment_lt_self_succ M hPA bound)).
        }
        assert (hnextOldBound :
            rawLt M (raw_succ M index) (raw_succ M bound)).
        {
          apply raw_lt_succ_of_le; [exact hPA |].
          exact (raw_succ_le_of_lt_pair M hPA index bound hlt).
        }
        destruct (hdefined index hindexOldBound) as
          [oldCurrent holdCurrent].
        destruct (hdefined (raw_succ M index) hnextOldBound) as
          [oldNext holdNext].
        assert (hnewOldCurrent :
            RawCodedAssignmentLookup M
              newCode newStep index oldCurrent).
        {
          exact (hpreserved index oldCurrent
            hindexOldBound holdCurrent).
        }
        assert (hnewOldNext :
            RawCodedAssignmentLookup M
              newCode newStep (raw_succ M index) oldNext).
        {
          exact (hpreserved (raw_succ M index) oldNext
            hnextOldBound holdNext).
        }
        assert (hcurrentEq : current = oldCurrent).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep index current oldCurrent
            hcurrent hnewOldCurrent).
        }
        assert (hnextEq : next = oldNext).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newCode newStep (raw_succ M index) next oldNext
            hnext hnewOldNext).
        }
        rewrite hcurrentEq, hnextEq.
        exact (hrows index oldCurrent oldNext hlt
          holdCurrent holdNext).
      * subst index.
        assert (hcurrentEq : current = output).
        {
          eapply raw_codedAssignmentLookup_functional;
            [exact hPA | exact hcurrent |].
          apply hpreserved.
          - exact (raw_assignment_lt_self_succ M hPA bound).
          - exact houtput.
        }
        assert (hnextEq : next = rawTermSuccCode M output).
        {
          eapply raw_codedAssignmentLookup_functional;
            [exact hPA | exact hnext |].
          exact hnewLookup.
        }
        now subst current next.
  - exact hnewLookup.
Qed.

(** Definable induction is the crucial nonstandard step: [bound] ranges over
    the carrier of an arbitrary raw PA model, not over external naturals. *)
Theorem raw_numeralTermCodeExists_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound,
  RawNumeralTermCodeExists M bound.
Proof.
  intros M hPA.
  set (phi := numeralTermCodeExistsTermAt (tVar 0)).
  set (parameterEnv := fun _ : nat => raw_zero M).
  assert (hall : forall bound,
      raw_formula_sat M (scons M bound parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_numeralTermCodeExistsTermAt_iff M
        (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_numeralTermCodeExists_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_numeralTermCodeExistsTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_numeralTermCodeExistsTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_numeralTermCodeExists_succ M hPA current hcurrent).
  }
  intro bound. unfold phi in hall.
  pose proof (proj1
    (raw_sat_numeralTermCodeExistsTermAt_iff M
      (scons M bound parameterEnv) (tVar 0))
    (hall bound)) as hbound.
  cbn [raw_term_eval scons] in hbound. exact hbound.
Qed.

(** Closed object-language totality statement.  Sealing keeps closure robust
    if the trace representation later acquires additional auxiliaries. *)
Definition numeralTermCodeTotalityBodyFormula : formula :=
  pAll (numeralTermCodeExistsTermAt (tVar 0)).

Lemma raw_sat_numeralTermCodeTotalityBodyFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e numeralTermCodeTotalityBodyFormula <->
  forall bound : M, RawNumeralTermCodeExists M bound.
Proof.
  intros M e. unfold numeralTermCodeTotalityBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeExistsTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition numeralTermCodeTotalityFormula : formula :=
  Formula.sealPA numeralTermCodeTotalityBodyFormula.

Theorem numeralTermCodeTotalityFormula_sentence :
  Formula.Sentence numeralTermCodeTotalityFormula.
Proof.
  unfold numeralTermCodeTotalityFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem numeralTermCodeTotalityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e numeralTermCodeTotalityFormula.
Proof.
  intros M hPA e.
  unfold numeralTermCodeTotalityFormula.
  apply raw_formula_sat_sealPA_of_valid.
  intro tail.
  apply (proj2
    (raw_sat_numeralTermCodeTotalityBodyFormula_iff M tail)).
  exact (raw_numeralTermCodeExists_all M hPA).
Qed.

Theorem PA_proves_numeralTermCodeTotalityFormula :
  Formula.BProv Formula.Ax_s [] numeralTermCodeTotalityFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact numeralTermCodeTotalityFormula_sentence.
  - exact numeralTermCodeTotalityFormula_raw_valid.
Qed.

End PABoundedRawCodedNumeralTermCode.
