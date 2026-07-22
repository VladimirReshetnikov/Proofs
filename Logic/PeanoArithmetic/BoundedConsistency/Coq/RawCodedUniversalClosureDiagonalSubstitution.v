(**
  Propagate diagonal substitution through a nonstandard universal closure.

  The shared-table certificate from [RawCodedFormulaDiagonalOperation] is
  represented here by an ordinary PA formula.  We then apply PA's definable
  induction to the model-coded closure count.  At a successor, closure
  inversion exposes the previous prefix and the exact diagonal [all]
  constructor lowers its child certificate from depth [S d] to depth [d].

  Consequently one all-depth diagonal substitution certificate for the
  unclosed body yields the entire bounded prefix self-instantiation family
  required by the proof-producing unsealing orbit.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedFormulaRankTraversal RawCodedFormulaOperations
  RawCodedFormulaDiagonalOperation
  RawCodedPAUniversalClosureProofReduction.

Module PABoundedRawCodedUniversalClosureDiagonalSubstitution.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedPAUniversalClosureProofReduction.

(** Represent the shared formula/depth table bundle. *)
Definition diagonalFormulaOperationBundleTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter formulaCode formulaStep depthCode depthStep bound : term)
    : formula :=
  operationAnd3
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt depthCode depthStep bound)
    (diagonalFormulaOperationRowsTermAt atom parameter
      formulaCode formulaStep depthCode depthStep bound).

Lemma raw_sat_diagonalFormulaOperationBundleTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter formulaCode formulaStep depthCode depthStep bound,
  raw_formula_sat M e
    (diagonalFormulaOperationBundleTermAt atom parameter
      formulaCode formulaStep depthCode depthStep bound) <->
  RawDiagonalFormulaOperationBundle M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold diagonalFormulaOperationBundleTermAt,
    RawDiagonalFormulaOperationBundle, operationAnd3.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite (raw_sat_diagonalFormulaOperationRowsTermAt_iff
    M e atom rawAtom hatom).
  reflexivity.
Qed.

Definition diagonalFormulaOperationTraceTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input : term) : formula :=
  operationAnd3
    (diagonalFormulaOperationBundleTermAt atom parameter
      formulaCode formulaStep depthCode depthStep bound)
    (Formula.ltTermAt rootIndex bound)
    (diagonalFormulaOperationLookupTermAt
      formulaCode formulaStep depthCode depthStep
      rootIndex input rootDepth).

Lemma raw_sat_diagonalFormulaOperationTraceTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input,
  raw_formula_sat M e
    (diagonalFormulaOperationTraceTermAt atom parameter rootDepth
      formulaCode formulaStep depthCode depthStep bound rootIndex input) <->
  RawDiagonalFormulaOperationTrace M rawAtom
    (raw_term_eval M e parameter) (raw_term_eval M e rootDepth)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e input).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold diagonalFormulaOperationTraceTermAt,
    RawDiagonalFormulaOperationTrace, operationAnd3.
  cbn [raw_formula_sat].
  rewrite (raw_sat_diagonalFormulaOperationBundleTermAt_iff
    M e atom rawAtom hatom).
  rewrite raw_sat_ltTermAt_iff,
    raw_sat_diagonalFormulaOperationLookupTermAt_iff.
  reflexivity.
Qed.

Definition codedFormulaDiagonalOperationTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter rootDepth input : term) : formula :=
  operationEx6
    (diagonalFormulaOperationTraceTermAt atom
      (liftTerm 6 parameter) (liftTerm 6 rootDepth)
      (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 6 input)).

Lemma raw_sat_codedFormulaDiagonalOperationTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter rootDepth input,
  raw_formula_sat M e
    (codedFormulaDiagonalOperationTermAt atom
      parameter rootDepth input) <->
  RawCodedFormulaDiagonalOperation M rawAtom
    (raw_term_eval M e parameter) (raw_term_eval M e rootDepth)
    (raw_term_eval M e input).
Proof.
  intros M e atom rawAtom hatom parameter rootDepth input.
  unfold codedFormulaDiagonalOperationTermAt, operationEx6,
    RawCodedFormulaDiagonalOperation.
  cbn [raw_formula_sat].
  setoid_rewrite (raw_sat_diagonalFormulaOperationTraceTermAt_iff
    M _ atom rawAtom hatom).
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaDiagonalSubstitutionTermAt
    (replacement depth input : term) : formula :=
  codedFormulaDiagonalOperationTermAt
    codedFormulaSubstitutionAtomTermAt replacement depth input.

Lemma raw_sat_codedFormulaDiagonalSubstitutionTermAt_iff : forall
    (M : RawPAModel) e replacement depth input,
  raw_formula_sat M e
    (codedFormulaDiagonalSubstitutionTermAt replacement depth input) <->
  RawCodedFormulaDiagonalSubstitution M
    (raw_term_eval M e replacement) (raw_term_eval M e depth)
    (raw_term_eval M e input).
Proof.
  intros. unfold codedFormulaDiagonalSubstitutionTermAt,
    RawCodedFormulaDiagonalSubstitution.
  apply (raw_sat_codedFormulaDiagonalOperationTermAt_iff M e
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)).
  exact (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M).
Qed.

(** A closed-body certificate strong enough to survive any number of added
    universal binders. *)
Definition RawCodedFormulaDiagonalSubstitutionAtAllDepths
    (M : RawPAModel) (replacement input : M) : Prop :=
  forall depth : M,
    RawCodedFormulaDiagonalSubstitution M replacement depth input.

Arguments RawCodedFormulaDiagonalSubstitutionAtAllDepths
  M replacement input : clear implicits.

Definition codedFormulaDiagonalSubstitutionAtAllDepthsTermAt
    (replacement input : term) : formula :=
  pAll
    (codedFormulaDiagonalSubstitutionTermAt
      (liftTerm 1 replacement) (tVar 0) (liftTerm 1 input)).

Lemma raw_sat_codedFormulaDiagonalSubstitutionAtAllDepthsTermAt_iff : forall
    (M : RawPAModel) e replacement input,
  raw_formula_sat M e
    (codedFormulaDiagonalSubstitutionAtAllDepthsTermAt
      replacement input) <->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M
    (raw_term_eval M e replacement) (raw_term_eval M e input).
Proof.
  intros M e replacement input.
  unfold codedFormulaDiagonalSubstitutionAtAllDepthsTermAt,
    RawCodedFormulaDiagonalSubstitutionAtAllDepths.
  cbn [raw_formula_sat]. split.
  - intros h depth.
    pose proof (proj1
      (raw_sat_codedFormulaDiagonalSubstitutionTermAt_iff M
        (scons M depth e) (liftTerm 1 replacement)
        (tVar 0) (liftTerm 1 input)) (h depth)) as hdepth.
    rewrite (raw_operation_eval_liftTerm_one M depth e replacement)
      in hdepth.
    rewrite (raw_operation_eval_liftTerm_one M depth e input)
      in hdepth.
    cbn [raw_term_eval scons] in hdepth. exact hdepth.
  - intros h depth.
    apply (proj2
      (raw_sat_codedFormulaDiagonalSubstitutionTermAt_iff M
        (scons M depth e) (liftTerm 1 replacement)
        (tVar 0) (liftTerm 1 input))).
    rewrite (raw_operation_eval_liftTerm_one M depth e replacement).
    rewrite (raw_operation_eval_liftTerm_one M depth e input).
    cbn [raw_term_eval scons]. exact (h depth).
Qed.

Definition RawCodedUniversalClosureDiagonalSubstitutionAt
    (M : RawPAModel) (replacement body count : M) : Prop :=
  forall prefix : M,
    RawCodedUniversalClosure M count body prefix ->
    RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement prefix.

Arguments RawCodedUniversalClosureDiagonalSubstitutionAt
  M replacement body count : clear implicits.

Definition codedUniversalClosureDiagonalSubstitutionAtTermAt
    (replacement body count : term) : formula :=
  pAll
    (pImp
      (codedUniversalClosureTermAt
        (liftTerm 1 count) (liftTerm 1 body) (tVar 0))
      (codedFormulaDiagonalSubstitutionAtAllDepthsTermAt
        (liftTerm 1 replacement) (tVar 0))).

Lemma raw_sat_codedUniversalClosureDiagonalSubstitutionAtTermAt_iff : forall
    (M : RawPAModel) e replacement body count,
  raw_formula_sat M e
    (codedUniversalClosureDiagonalSubstitutionAtTermAt
      replacement body count) <->
  RawCodedUniversalClosureDiagonalSubstitutionAt M
    (raw_term_eval M e replacement) (raw_term_eval M e body)
    (raw_term_eval M e count).
Proof.
  intros M e replacement body count.
  unfold codedUniversalClosureDiagonalSubstitutionAtTermAt,
    RawCodedUniversalClosureDiagonalSubstitutionAt.
  cbn [raw_formula_sat]. split.
  - intros h prefix hclosure.
    specialize (h prefix).
    pose proof (proj2 (raw_sat_codedUniversalClosureTermAt_iff M
      (scons M prefix e) (liftTerm 1 count) (liftTerm 1 body)
      (tVar 0))) as hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e count)
      in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e body)
      in hclosureSat.
    cbn [raw_term_eval scons] in hclosureSat.
    pose proof (h (hclosureSat hclosure)) as hstableSat.
    apply (proj1
      (raw_sat_codedFormulaDiagonalSubstitutionAtAllDepthsTermAt_iff M
        (scons M prefix e) (liftTerm 1 replacement) (tVar 0)))
      in hstableSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e replacement)
      in hstableSat.
    cbn [raw_term_eval scons] in hstableSat. exact hstableSat.
  - intros h prefix hclosureSat.
    apply (proj2
      (raw_sat_codedFormulaDiagonalSubstitutionAtAllDepthsTermAt_iff M
        (scons M prefix e) (liftTerm 1 replacement) (tVar 0))).
    rewrite (raw_operation_eval_liftTerm_one M prefix e replacement).
    cbn [raw_term_eval scons]. apply h.
    apply (proj1 (raw_sat_codedUniversalClosureTermAt_iff M
      (scons M prefix e) (liftTerm 1 count) (liftTerm 1 body)
      (tVar 0))) in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e count)
      in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e body)
      in hclosureSat.
    cbn [raw_term_eval scons] in hclosureSat. exact hclosureSat.
Qed.

(** PA-definable induction over the possibly nonstandard closure count. *)
Theorem raw_codedUniversalClosureDiagonalSubstitutionAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement body ->
  forall count,
    RawCodedUniversalClosureDiagonalSubstitutionAt
      M replacement body count.
Proof.
  intros M hPA replacement body hbody.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => replacement
    | _ => body
    end).
  set (phi := codedUniversalClosureDiagonalSubstitutionAtTermAt
    (tVar 1) (tVar 2) (tVar 0)).
  assert (hall : forall count,
      raw_formula_sat M (scons M count parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedUniversalClosureDiagonalSubstitutionAtTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros prefix hprefix.
      pose proof (raw_codedUniversalClosure_zero M hPA
        body prefix hprefix) as hprefixEq.
      subst prefix. exact hbody.
    - intros count hcountSat.
      unfold phi in hcountSat |- *.
      pose proof (proj1
        (raw_sat_codedUniversalClosureDiagonalSubstitutionAtTermAt_iff M
          (scons M count parameterEnv)
          (tVar 1) (tVar 2) (tVar 0)) hcountSat) as hcount.
      apply (proj2
        (raw_sat_codedUniversalClosureDiagonalSubstitutionAtTermAt_iff M
          (scons M (raw_succ M count) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv in hcount |- *.
      cbn [raw_term_eval scons] in hcount |- *.
      intros prefix hprefix.
      destruct (raw_codedUniversalClosure_succ_inversion M hPA
        count body prefix hprefix) as
        [previous [hprevious hprefixEq]].
      subst prefix. intro depth.
      exact (raw_codedFormulaDiagonalSubstitution_all M hPA
        replacement depth previous
        (hcount previous hprevious (raw_succ M depth))).
  }
  intro count. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedUniversalClosureDiagonalSubstitutionAtTermAt_iff M
      (scons M count parameterEnv)
      (tVar 1) (tVar 2) (tVar 0)) (hall count)) as hresult.
  unfold parameterEnv in hresult.
  cbn [raw_term_eval scons] in hresult. exact hresult.
Qed.

(** Discharge the exact prefix identity family consumed by proof reduction. *)
Corollary
    raw_codedUniversalClosureSelfInstantiationThrough_of_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body limit,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement body ->
  RawCodedUniversalClosureSelfInstantiationThrough M
    replacement body limit.
Proof.
  intros M hPA replacement body limit hbody count prefix _ hprefix.
  pose proof (raw_codedUniversalClosureDiagonalSubstitutionAt_all
    M hPA replacement body hbody count prefix hprefix) as hdiagonal.
  exact (raw_codedFormulaSingleSubstitution_of_diagonal M hPA
    replacement prefix (hdiagonal (raw_zero M))).
Qed.

End PABoundedRawCodedUniversalClosureDiagonalSubstitution.
