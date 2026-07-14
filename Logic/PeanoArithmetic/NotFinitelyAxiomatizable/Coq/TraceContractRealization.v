(**
  Unconditional realization of the evaluator-cut contract.

  The construction deliberately uses one rank for all three roles: the
  finite Skolem hull, its canonical selector enumeration, and the program
  trace evaluator.  In particular, selector indices occurring in trace
  programs are never reinterpreted at a second rank.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFRawSemantics.
From PAFiniteBasisReduction Require Import FiniteBasisReduction
  HierarchyReduction NonstandardHFFin FiniteSkolemHull CanonicalSelector
  CanonicalSelectorPA FiniteBetaCoding EvaluatorCutContract ProgramTrace
  TotalProgramRows StandardTraceRows StandardTraceFunctionality
  CanonicalTotalRows TotalTraceEvaluator.

Import PAFiniteBasisReduction.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PAEvaluatorCutContract.
Import PAProgramTrace.
Import PATotalProgramRows.
Import PAStandardTraceRows.
Import PAStandardTraceFunctionality.
Import PATotalTraceEvaluator.

Module PATraceContractRealization.

(** The fixed support needed independently of the requested PA fragment.
    The beta-extension selector builds hull-resident finite tables; the two
    fixed formulas transport strict order and beta entries between the hull
    and its ambient PA model. *)
Definition traceSupportRank : nat :=
  Nat.max (formula_rank betaCodeExtensionSelectorBody)
    (Nat.max (formula_rank hullLtFormula)
      (formula_rank hullBetaFormula)).

(** A single support rank for the fragment, hull selectors, and trace. *)
Definition traceConstructionRank (n : nat) : nat :=
  Nat.max (rankFragmentSyntaxRank n) traceSupportRank.

Lemma betaCodeExtensionSelectorBody_rank_le_traceSupportRank :
  formula_rank betaCodeExtensionSelectorBody <= traceSupportRank.
Proof.
  unfold traceSupportRank. apply Nat.le_max_l.
Qed.

Lemma hullLtFormula_rank_le_traceSupportRank :
  formula_rank hullLtFormula <= traceSupportRank.
Proof.
  unfold traceSupportRank.
  eapply Nat.le_trans; [apply Nat.le_max_l | apply Nat.le_max_r].
Qed.

Lemma hullBetaFormula_rank_le_traceSupportRank :
  formula_rank hullBetaFormula <= traceSupportRank.
Proof.
  unfold traceSupportRank.
  eapply Nat.le_trans; [apply Nat.le_max_r | apply Nat.le_max_r].
Qed.

Lemma rankFragmentSyntaxRank_le_traceConstructionRank : forall n,
  rankFragmentSyntaxRank n <= traceConstructionRank n.
Proof.
  intro n. unfold traceConstructionRank. apply Nat.le_max_l.
Qed.

Lemma traceSupportRank_le_traceConstructionRank : forall n,
  traceSupportRank <= traceConstructionRank n.
Proof.
  intro n. unfold traceConstructionRank. apply Nat.le_max_r.
Qed.

Lemma betaCodeExtensionSelectorBody_rank_le_traceConstructionRank :
  forall n,
  formula_rank betaCodeExtensionSelectorBody <= traceConstructionRank n.
Proof.
  intro n. eapply Nat.le_trans.
  - apply betaCodeExtensionSelectorBody_rank_le_traceSupportRank.
  - apply traceSupportRank_le_traceConstructionRank.
Qed.

Lemma hullLtFormula_rank_le_traceConstructionRank : forall n,
  formula_rank hullLtFormula <= traceConstructionRank n.
Proof.
  intro n. eapply Nat.le_trans.
  - apply hullLtFormula_rank_le_traceSupportRank.
  - apply traceSupportRank_le_traceConstructionRank.
Qed.

Lemma hullBetaFormula_rank_le_traceConstructionRank : forall n,
  formula_rank hullBetaFormula <= traceConstructionRank n.
Proof.
  intro n. eapply Nat.le_trans.
  - apply hullBetaFormula_rank_le_traceSupportRank.
  - apply traceSupportRank_le_traceConstructionRank.
Qed.

(** The distinguished compactness-model ordinal is above every standard
    arithmetic numeral in the extracted raw PA model. *)
Lemma fofamStar_above_all_numerals : forall
    (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (star : FOFAMOrdinal M),
  (forall n,
    fofamPAFormulaSat M (fun _ => star)
      (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))) ->
  AboveAllNumerals (fofamRawPAModel M) star.
Proof.
  intros V M star hstar n.
  pose proof (proj2 (raw_formula_sat_fofam V M (fun _ => star)
    (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0)))
    (hstar n)) as hsat.
  apply (proj1 (raw_sat_ltTermAt_iff (fofamRawPAModel M)
    (PA.Term.numeral n) (PA.tVar 0) (fun _ => star))) in hsat.
  rewrite raw_term_eval_numeral in hsat.
  cbn [raw_term_eval] in hsat.
  exact hsat.
Qed.

(** Interfaces matching the two independently proved semantic trace
    theorems.  Stating the assembly through these records keeps compactness
    and rank plumbing independent of the internals of row construction. *)
Definition TraceEvaluatorStandardCodeTotal : Prop :=
  forall (M : RawPAModel) (ambientSeed : M) rank,
    RawPASatisfies M ->
    formula_rank betaCodeExtensionSelectorBody <= rank ->
    formula_rank hullLtFormula <= rank ->
    formula_rank hullBetaFormula <= rank ->
    forall output :
      skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M),
      exists code : nat,
        Evaluates
          (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
          (traceEvaluator rank)
          (skolemHullSeed M ambientSeed rank (rawCanonicalSelector M))
          (rawNumeralValue
            (skolemHullRawModel M ambientSeed rank
              (rawCanonicalSelector M)) code)
          output.

Definition TraceEvaluatorStandardCodeFunctional : Prop :=
  forall (M : RawPAModel) (ambientSeed : M) rank,
    RawPASatisfies M ->
    formula_rank hullLtFormula <= rank ->
    formula_rank hullBetaFormula <= rank ->
    forall target
      (x y : skolemHullRawModel M ambientSeed rank
        (rawCanonicalSelector M)),
      Evaluates
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
        (traceEvaluator rank)
        (skolemHullSeed M ambientSeed rank (rawCanonicalSelector M))
        (rawNumeralValue
          (skolemHullRawModel M ambientSeed rank
            (rawCanonicalSelector M)) target)
        x ->
      Evaluates
        (skolemHullRawModel M ambientSeed rank (rawCanonicalSelector M))
        (traceEvaluator rank)
        (skolemHullSeed M ambientSeed rank (rawCanonicalSelector M))
        (rawNumeralValue
          (skolemHullRawModel M ambientSeed rank
            (rawCanonicalSelector M)) target)
        y ->
      x = y.

Lemma traceEvaluator_standardCode_functionality :
  TraceEvaluatorStandardCodeFunctional.
Proof.
  intros M ambientSeed rank hPA hLtRank hBetaRank target x y hx hy.
  exact (traceEvaluator_standardCode_functional
    M ambientSeed rank hPA hLtRank hBetaRank target x y hx hy).
Qed.

(** Compactness, the one bounded Skolem hull, and the evaluator contract
    assemble uniformly once totality and cross-table functionality are
    supplied. *)
Theorem trace_contractCountermodels_of_trace :
  TraceEvaluatorStandardCodeTotal ->
  TraceEvaluatorStandardCodeFunctional ->
  ContractCountermodels.
Proof.
  intros hTotal hFunctional n.
  destruct nonstandardHFFin_fofam_exists as
    [V [ambient [star [_ hstar]]]].
  set (M := fofamRawPAModel ambient).
  set (rank := traceConstructionRank n).
  set (K := skolemHullRawModel M star rank (rawCanonicalSelector M)).
  set (seedK := skolemHullSeed M star rank (rawCanonicalSelector M)).
  assert (hPA : RawPASatisfies M).
  { unfold M. apply fofam_raw_pa_satisfies. }
  assert (hselector : SelectorWitnesses M (rawCanonicalSelector M)).
  {
    apply rawCanonicalSelector_witnesses.
    apply raw_definable_least_number_of_pa. exact hPA.
  }
  assert (hseedAbove : AboveAllNumerals M star).
  {
    unfold M. apply fofamStar_above_all_numerals. exact hstar.
  }
  assert (hFragmentRank : rankFragmentSyntaxRank n <= rank).
  { unfold rank. apply rankFragmentSyntaxRank_le_traceConstructionRank. }
  assert (hBetaSupport :
      formula_rank betaCodeExtensionSelectorBody <= rank).
  {
    unfold rank.
    apply betaCodeExtensionSelectorBody_rank_le_traceConstructionRank.
  }
  assert (hLtRank : formula_rank hullLtFormula <= rank).
  { unfold rank. apply hullLtFormula_rank_le_traceConstructionRank. }
  assert (hBetaRank : formula_rank hullBetaFormula <= rank).
  { unfold rank. apply hullBetaFormula_rank_le_traceConstructionRank. }
  exists K, (traceEvaluator rank), seedK. split.
  - unfold K, seedK.
    apply (skolemHull_evaluator_contract_of_ambient_pa
      M star rank (rawCanonicalSelector M)
      hselector hPA hLtRank hseedAbove (traceEvaluator rank)).
    + exact (hTotal M star rank hPA hBetaSupport hLtRank hBetaRank).
    + exact (hFunctional M star rank hPA hLtRank hBetaRank).
  - unfold K.
    apply (skolemHull_satisfies_rank_fragment_at_rank
      M star n rank (rawCanonicalSelector M)); assumption.
Qed.

(** The fixed total trace discharges the totality interface. *)
Lemma traceEvaluator_standardCode_totality :
  TraceEvaluatorStandardCodeTotal.
Proof.
  intros M ambientSeed rank hPA hExtensionRank hLtRank hBetaRank output.
  exact (traceEvaluator_standardCode_total
    M ambientSeed rank hPA hExtensionRank hLtRank hBetaRank output).
Qed.

(** At every finite syntax rank there is a bounded Skolem-hull
    countermodel whose trace evaluator realizes the proper-cut contract. *)
Theorem trace_contractCountermodels : ContractCountermodels.
Proof.
  exact (trace_contractCountermodels_of_trace
    traceEvaluator_standardCode_totality
    traceEvaluator_standardCode_functionality).
Qed.

(** First-order Peano Arithmetic in its original language has no finite
    deductive sentence axiomatization. *)
Theorem peano_arithmetic_not_finitely_axiomatizable :
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  apply peano_arithmetic_not_finitely_axiomatizable_of_contracts.
  exact trace_contractCountermodels.
Qed.

End PATraceContractRealization.
