(**
  Atomic syntax adequacy for arbitrary coded formula shifts.

  A formula-operation trace already contains a structural row for every
  target occurrence.  At equality rows, its two atomic premises are coded
  term-shift traces.  The target-syntax theorem for such term traces was
  proved by PA-definable induction, so this argument applies unchanged to
  nonstandard formula and term codes in an arbitrary model of PA.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedProofDescent
  RawCodedTermEvaluationStepFunctionality
  RawCodedFormulaOperations RawCodedFormulaOperationQuotedRankSound
  RawCodedFixedLevelTruthTotality RawCodedTermShiftSyntaxRealization
  RawCodedPAAxiomTruth
  RawCodedPAAxiomInductionTruthConcrete.

Import ListNotations.

Module PABoundedRawCodedFormulaShiftAtomicAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationQuotedRankSound.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedPAAxiomInductionTruthConcrete.

(** Equality fields lie below their enclosing list code.  These bounds are
    what lets an assignment known through the equality code serve every
    variable occurring in either shifted term. *)
Lemma raw_formulaShift_eq_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M left (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_formulaShift_eq_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M right (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

(** A binary formula constructor with a nonzero tag cannot be an equality.
    Keeping this small inversion lemma local avoids importing any truth
    evaluator merely for constructor separation. *)
Lemma raw_formulaShift_nonzero_binary_neq_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right eqLeft eqRight,
  tag <> 0 ->
  rawCodeList3 M (rawNumeralValue M tag) left right <>
  rawFormulaEqCode M eqLeft eqRight.
Proof.
  intros M hPA tag left right eqLeft eqRight htag heq.
  unfold rawFormulaEqCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [htags _].
  apply (rawNumeralValue_injective M hPA tag 0) in htags.
  exact (htag htags).
Qed.

(** If the target code is known to be an equality, constructor separation
    rules out every non-atomic traversal branch. *)
Lemma raw_formulaShift_eq_row_of_target : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth left right,
  RawCodedFormulaOperationTraversalRow M (RawCodedFormulaShiftAtom M)
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  output = rawFormulaEqCode M left right ->
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    parameter depth input output.
Proof.
  intros M hPA parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth left right hrow houtputEq.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [exact heq | ..].
  - destruct hbot as [_ houtput]. exfalso.
    unfold rawFormulaBotCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct himp as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 2 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaImpCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hand as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 3 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaAndCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hor as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 4 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaOrCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hall as
      (_ & _ & outputChild & _ & _ & _ & _ & _ & houtput).
    exfalso. unfold rawFormulaAllCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) outputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hex as
      (_ & _ & outputChild & _ & _ & _ & _ & _ & houtput).
    exfalso. unfold rawFormulaExCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) outputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
Qed.

(** Formula shift produces an atomically adequate target without requiring
    atomic adequacy of the source as an extra premise. *)
Theorem raw_codedFormulaShift_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount input output,
  RawCodedFormulaShift M cutoff amount input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA cutoff amount input output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof (raw_formulaOperationTrace_target_syntax M
    (RawCodedFormulaShiftAtom M) amount cutoff
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output htrace) as htargetSyntax.
  exists targetCode, targetStep, bound, rootIndex.
  split; [exact htargetSyntax |].
  intros index code left right assignmentCode assignmentStep
    hindex htargetLookup hcodeEq hassignment.
  destruct htrace as
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  destruct (hsourceDefined index hindex) as [source hsourceLookup].
  destruct (hdepthDefined index hindex) as [depth hdepthLookup].
  pose proof (hrows index source code depth hindex
    (conj hsourceLookup (conj htargetLookup hdepthLookup))) as hrow.
  pose proof (raw_formulaShift_eq_row_of_target M hPA
    amount sourceCode sourceStep targetCode targetStep depthCode depthStep
    index source code depth left right hrow hcodeEq) as heqRow.
  destruct heqRow as
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsourceEq & htargetEq & hleftShift & hrightShift).
  assert (htargetFields : targetLeft = left /\ targetRight = right).
  {
    unfold rawFormulaEqCode in htargetEq, hcodeEq.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ (eq_trans (eq_sym htargetEq) hcodeEq))
      as [_ [hleft hright]]. exact (conj hleft hright).
  }
  destruct htargetFields as [-> ->]. split.
  - apply (raw_codedTermShift_target_syntax_realizable M hPA
      depth amount sourceLeft left assignmentCode assignmentStep code).
    + exact hleftShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_left_lt M hPA left right).
    + exact hassignment.
  - apply (raw_codedTermShift_target_syntax_realizable M hPA
      depth amount sourceRight right assignmentCode assignmentStep code).
    + exact hrightShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_right_lt M hPA left right).
    + exact hassignment.
Qed.

(** This is the callback used by the PA-induction truth construction. *)
Theorem raw_inductionShiftAtomicAdequacy_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawInductionShiftAtomicAdequacy M.
Proof.
  intros M hPA cutoff amount input output hshift _.
  exact (raw_codedFormulaShift_target_atomically_adequate
    M hPA cutoff amount input output hshift).
Qed.

(** Hence the formerly parameterized induction-axiom soundness theorem is
    unconditional for every external fixed truth level. *)
Theorem raw_fixedLevelPAAxiomInductionSigmaSound_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelPAAxiomInductionSigmaSound M level.
Proof.
  intros M hPA level.
  apply (raw_fixedLevelPAAxiomInductionSigmaSound_of_shift_atomic
    M hPA level).
  exact (raw_inductionShiftAtomicAdequacy_all M hPA).
Qed.

End PABoundedRawCodedFormulaShiftAtomicAdequacy.
