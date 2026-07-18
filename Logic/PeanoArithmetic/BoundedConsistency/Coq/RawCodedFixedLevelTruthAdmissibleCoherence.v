(**
  Admissibility-guarded coherence at every externally fixed truth level.

  Lowering a positive fixed-level certificate cannot reuse its source table:
  the table may contain unrelated rows whose ranks are too large for the
  lower level.  The proof below instead performs PA-definable induction over
  source prefixes.  Whenever a source row has the honest syntax, assignment,
  and polarity domain needed at the target level, its reachable children
  have already been rebuilt as independent target certificates.  Their
  tables can then be concatenated and the current row appended.

  This file deliberately keeps the auxiliary construction explicit.  In
  particular, no metatheoretic decoding of a possibly nonstandard formula
  code, and no finite-vector choice outside the model, is used.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofDescent RawCodedFormulaRankTotality
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFormulaRankTraversal RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelDomainLaws RawCodedFixedLevelTruthCoherence
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthConcatenation RawCodedFixedLevelTruthConstruction.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthConcatenation.
Import PABoundedRawCodedFixedLevelTruthConstruction.

(** A syntax-row view indexed by the common formula-shape datatype.  The
    equality and bottom cases carry no recursive occurrences; every other
    case records exactly the earlier lookup(s) from the syntax traversal. *)
Definition RawCodedFormulaShapeSyntaxRow (M : RawPAModel)
    (formulaCode formulaStep index : M)
    (shape : RawCodedFormulaShape M) : Prop :=
  match shape with
  | rawShapeEq _ _ => True
  | rawShapeBot => True
  | rawShapeImp leftChild rightChild =>
      exists leftIndex rightIndex : M,
        rawLt M leftIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep leftIndex leftChild /\
        rawLt M rightIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep rightIndex rightChild
  | rawShapeAnd leftChild rightChild =>
      exists leftIndex rightIndex : M,
        rawLt M leftIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep leftIndex leftChild /\
        rawLt M rightIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep rightIndex rightChild
  | rawShapeOr leftChild rightChild =>
      exists leftIndex rightIndex : M,
        rawLt M leftIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep leftIndex leftChild /\
        rawLt M rightIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep rightIndex rightChild
  | rawShapeAll child =>
      exists childIndex : M,
        rawLt M childIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep childIndex child
  | rawShapeEx child =>
      exists childIndex : M,
        rawLt M childIndex index /\
        RawCodedAssignmentLookup M
          formulaCode formulaStep childIndex child
  end.

Arguments RawCodedFormulaShapeSyntaxRow
  M formulaCode formulaStep index shape : clear implicits.

Lemma raw_codedFormulaSyntaxTraversalRow_shape : forall
    (M : RawPAModel) formulaCode formulaStep index code,
  RawCodedFormulaSyntaxTraversalRow M
    formulaCode formulaStep index code ->
  exists shape : RawCodedFormulaShape M,
    code = rawCodedFormulaShapeCode M shape /\
    RawCodedFormulaShapeSyntaxRow M
      formulaCode formulaStep index shape.
Proof.
  intros M formulaCode formulaStep index code hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as (left & right & hcode).
    exists (rawShapeEq left right). split; [exact hcode | exact I].
  - exists rawShapeBot. split; [exact hbot | exact I].
  - destruct himp as
      (leftIndex & left & rightIndex & right &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
    exists (rawShapeImp left right). split; [exact hcode |].
    exists leftIndex, rightIndex. repeat split; assumption.
  - destruct hand as
      (leftIndex & left & rightIndex & right &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
    exists (rawShapeAnd left right). split; [exact hcode |].
    exists leftIndex, rightIndex. repeat split; assumption.
  - destruct hor as
      (leftIndex & left & rightIndex & right &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
    exists (rawShapeOr left right). split; [exact hcode |].
    exists leftIndex, rightIndex. repeat split; assumption.
  - destruct hall as (childIndex & child & hchildIndex & hchildLookup & hcode).
    exists (rawShapeAll child). split; [exact hcode |].
    exists childIndex. split; assumption.
  - destruct hex as (childIndex & child & hchildIndex & hchildLookup & hcode).
    exists (rawShapeEx child). split; [exact hcode |].
    exists childIndex. split; assumption.
Qed.

(** Constructor injectivity identifies the root row of an independently
    chosen atomic-adequacy traversal with the displayed public constructor. *)
Lemma raw_codedFormulaAtomicallyAdequate_shape_at : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (wanted : RawCodedFormulaShape M),
  RawCodedFormulaAtomicallyAdequate M
    (rawCodedFormulaShapeCode M wanted) ->
  exists formulaCode formulaStep bound rootIndex,
    RawCodedFormulaSyntaxTraversal M
      formulaCode formulaStep bound rootIndex
      (rawCodedFormulaShapeCode M wanted) /\
    RawCodedFormulaAtomicTermAdequate M
      formulaCode formulaStep bound /\
    RawCodedFormulaShapeSyntaxRow M
      formulaCode formulaStep rootIndex wanted.
Proof.
  intros M hPA wanted
    (formulaCode & formulaStep & bound & rootIndex & hsyntax & hadequate).
  destruct hsyntax as [hdefined [hrootBelow [hrootLookup hrows]]].
  pose proof (hrows rootIndex (rawCodedFormulaShapeCode M wanted)
    hrootBelow hrootLookup) as hrootRow.
  destruct (raw_codedFormulaSyntaxTraversalRow_shape M
    formulaCode formulaStep rootIndex
    (rawCodedFormulaShapeCode M wanted) hrootRow)
    as (actual & hcode & hshape).
  assert (hactual : actual = wanted).
  {
    apply (rawCodedFormulaShapeCode_injective
      polynomialPairInjectivityProof M hPA).
    symmetry. exact hcode.
  }
  subst actual.
  exists formulaCode, formulaStep, bound, rootIndex.
  split.
  - repeat split; assumption.
  - split; assumption.
Qed.

(** Every payload of a two-field constructor code is below the enclosing
    list code.  The analogous three-field facts are imported from the base
    lowering module. *)
Lemma raw_formulaCodeList2_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag child,
  rawLt M child (rawCodeList2 M tag child).
Proof.
  intros M hPA tag child. unfold rawCodeList2.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** The next five lemmas package the syntax and assignment halves inherited
    by displayed children.  Their polarity domain is intentionally left to
    the caller, because implication and quantifiers change polarity. *)
Lemma raw_fixedLevelTruthAdmissible_imp_children_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level left right assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  (RawCodedFormulaAtomicallyAdequate M left /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep left) /\
  (RawCodedFormulaAtomicallyAdequate M right /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep right).
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  destruct hadmissible as [hatomic [hassignment hdomain]].
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeImp left right) hatomic) as
    (formulaCode & formulaStep & bound & rootIndex &
     hsyntax & hadequate & leftIndex & rightIndex &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup).
  assert (hleftBound : rawLt M leftIndex bound).
  { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
      hleftIndex (proj1 (proj2 hsyntax))). }
  assert (hrightBound : rawLt M rightIndex bound).
  { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
      hrightIndex (proj1 (proj2 hsyntax))). }
  assert (hfull : RawFixedLevelTruthAdmissible M level
      (rawFormulaImpCode M left right) assignmentCode assignmentStep).
  { repeat split; assumption. }
  split.
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaImpCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex leftIndex left
      hsyntax hadequate hleftBound hleftLookup
      (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 2) left right)).
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaImpCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex rightIndex right
      hsyntax hadequate hrightBound hrightLookup
      (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 2) left right)).
Qed.

Lemma raw_fixedLevelTruthAdmissible_and_children_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level left right assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  (RawCodedFormulaAtomicallyAdequate M left /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep left) /\
  (RawCodedFormulaAtomicallyAdequate M right /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep right).
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  destruct hadmissible as [hatomic [hassignment hdomain]].
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeAnd left right) hatomic) as
    (formulaCode & formulaStep & bound & rootIndex &
     hsyntax & hadequate & leftIndex & rightIndex &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup).
  assert (hleftBound : rawLt M leftIndex bound).
  { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
      hleftIndex (proj1 (proj2 hsyntax))). }
  assert (hrightBound : rawLt M rightIndex bound).
  { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
      hrightIndex (proj1 (proj2 hsyntax))). }
  assert (hfull : RawFixedLevelTruthAdmissible M level
      (rawFormulaAndCode M left right) assignmentCode assignmentStep).
  { repeat split; assumption. }
  split.
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaAndCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex leftIndex left
      hsyntax hadequate hleftBound hleftLookup
      (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 3) left right)).
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaAndCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex rightIndex right
      hsyntax hadequate hrightBound hrightLookup
      (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 3) left right)).
Qed.

Lemma raw_fixedLevelTruthAdmissible_or_children_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level left right assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  (RawCodedFormulaAtomicallyAdequate M left /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep left) /\
  (RawCodedFormulaAtomicallyAdequate M right /\
   RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep right).
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  destruct hadmissible as [hatomic [hassignment hdomain]].
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeOr left right) hatomic) as
    (formulaCode & formulaStep & bound & rootIndex &
     hsyntax & hadequate & leftIndex & rightIndex &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup).
  assert (hleftBound : rawLt M leftIndex bound).
  { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
      hleftIndex (proj1 (proj2 hsyntax))). }
  assert (hrightBound : rawLt M rightIndex bound).
  { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
      hrightIndex (proj1 (proj2 hsyntax))). }
  assert (hfull : RawFixedLevelTruthAdmissible M level
      (rawFormulaOrCode M left right) assignmentCode assignmentStep).
  { repeat split; assumption. }
  split.
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaOrCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex leftIndex left
      hsyntax hadequate hleftBound hleftLookup
      (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 4) left right)).
  - exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
      (rawFormulaOrCode M left right) assignmentCode assignmentStep hfull
      formulaCode formulaStep bound rootIndex rightIndex right
      hsyntax hadequate hrightBound hrightLookup
      (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 4) left right)).
Qed.

Lemma raw_fixedLevelTruthAdmissible_all_child_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level child assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep child.
Proof.
  intros M hPA level child assignmentCode assignmentStep hadmissible.
  destruct hadmissible as [hatomic [hassignment hdomain]].
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeAll child) hatomic) as
    (formulaCode & formulaStep & bound & rootIndex &
     hsyntax & hadequate & childIndex & hchildIndex & hchildLookup).
  assert (hchildBound : rawLt M childIndex bound).
  { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
      hchildIndex (proj1 (proj2 hsyntax))). }
  assert (hfull : RawFixedLevelTruthAdmissible M level
      (rawFormulaAllCode M child) assignmentCode assignmentStep).
  { repeat split; assumption. }
  exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
    (rawFormulaAllCode M child) assignmentCode assignmentStep hfull
    formulaCode formulaStep bound rootIndex childIndex child
    hsyntax hadequate hchildBound hchildLookup
    (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 5) child)).
Qed.

Lemma raw_fixedLevelTruthAdmissible_ex_child_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level child assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep child.
Proof.
  intros M hPA level child assignmentCode assignmentStep hadmissible.
  destruct hadmissible as [hatomic [hassignment hdomain]].
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeEx child) hatomic) as
    (formulaCode & formulaStep & bound & rootIndex &
     hsyntax & hadequate & childIndex & hchildIndex & hchildLookup).
  assert (hchildBound : rawLt M childIndex bound).
  { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
      hchildIndex (proj1 (proj2 hsyntax))). }
  assert (hfull : RawFixedLevelTruthAdmissible M level
      (rawFormulaExCode M child) assignmentCode assignmentStep).
  { repeat split; assumption. }
  exact (raw_fixedLevelTruthAdmissible_child_core M hPA level
    (rawFormulaExCode M child) assignmentCode assignmentStep hfull
    formulaCode formulaStep bound rootIndex childIndex child
    hsyntax hadequate hchildBound hchildLookup
    (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 6) child)).
Qed.

(** Empty positive bundles and the one-row constructor are convenient for
    rank-zero leaves and opposite-quantifier rows, neither of which consults
    an earlier same-level state. *)
Lemma raw_fixedLevelPositiveTraversalBundle_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelPositiveTraversalBundle M lower
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M).
Proof.
  intros M hPA lower.
  repeat split; try exact (raw_codedAssignment_empty_defined M hPA).
  intros index mode code assignmentCode assignmentStep hindex _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Appending a closed row to any bundle and choosing the new final row as
    root yields a complete successor traversal. *)
Lemma raw_fixedLevelPositiveTraversalBundle_append_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep,
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      (raw_succ M bound) bound mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep hbundle hclosed.
  destruct (raw_fixedLevelPositiveTraversalBundle_append M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep hbundle hclosed) as
    (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
     newAssignmentCodeCode & newAssignmentCodeStep &
     newAssignmentStepCode & newAssignmentStepStep &
     hnewBundle & hprefix & hrootLookup).
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  destruct hnewBundle as
    [hmode [hformula [hassignmentCode [hassignmentStep hrows]]]].
  exact (conj hmode
    (conj hformula
      (conj hassignmentCode
        (conj hassignmentStep
          (conj (raw_assignment_lt_self_succ M hPA bound)
            (conj hrootLookup hrows)))))).
Qed.

Corollary raw_fixedLevelClosedSuccessorRow_singleton_traversal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower mode code assignmentCode assignmentStep,
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) mode code assignmentCode assignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex : M,
    RawFixedLevelSuccessorTruthTraversal M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower mode code assignmentCode assignmentStep hclosed.
  destruct (raw_fixedLevelPositiveTraversalBundle_append_root M hPA lower
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) mode code assignmentCode assignmentStep
    (raw_fixedLevelPositiveTraversalBundle_empty M hPA lower) hclosed) as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & htraversal).
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  exact htraversal.
Qed.

(** ------------------------------------------------------------------
    The definable reachable-row invariant.

    A source state is rebuilt only when it is honestly admissible at the
    target level and has the polarity domain requested by its stored mode.
    The explicit [index < sourceBound] premise makes the invariant meaningful
    for every induction value, including values beyond the source table. *)

Definition RawFixedLevelAdmissibleLoweringBelow (M : RawPAModel)
    (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current : M) : Prop :=
  forall index mode code assignmentCode assignmentStep : M,
    rawLt M index current ->
    rawLt M index sourceBound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawFixedLevelTruthAdmissible M (S lower)
      code assignmentCode assignmentStep ->
    (mode = rawFixedLevelSigmaMode M ->
      RawFixedLevelSigmaDomain M (S lower) code ->
      RawFixedLevelSigmaTruthCertificate M (S lower)
        code assignmentCode assignmentStep) /\
    (mode = rawFixedLevelPiMode M ->
      RawFixedLevelPiDomain M (S lower) code ->
      RawFixedLevelPiFalsityCertificate M (S lower)
        code assignmentCode assignmentStep).

Arguments RawFixedLevelAdmissibleLoweringBelow
  M lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
  : clear implicits.

Definition fixedLevelAdmissibleLoweringConclusionTermAt (lower : nat)
    (mode code assignmentCode assignmentStep : term) : formula :=
  pAnd
    (pImp
      (pEq mode tZero)
      (pImp
        (fixedLevelSigmaDomainTermAt (S lower) code)
        (fixedLevelSigmaTruthCertificateTermAt (S lower)
          code assignmentCode assignmentStep)))
    (pImp
      (pEq mode (Term.numeral 1))
      (pImp
        (fixedLevelPiDomainTermAt (S lower) code)
        (fixedLevelPiFalsityCertificateTermAt (S lower)
          code assignmentCode assignmentStep))).

Definition fixedLevelAdmissibleLoweringBelowTermAt (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current : term)
    : formula :=
  fixedTruthTraversalAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (Formula.ltTermAt (tVar 4) (liftTerm 5 sourceBound))
        (pImp
          (fixedLevelStateLookupTermAt
            (liftTerm 5 modeCode) (liftTerm 5 modeStep)
            (liftTerm 5 formulaCode) (liftTerm 5 formulaStep)
            (liftTerm 5 assignmentCodeCode)
            (liftTerm 5 assignmentCodeStep)
            (liftTerm 5 assignmentStepCode)
            (liftTerm 5 assignmentStepStep)
            (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
          (pImp
            (fixedLevelTruthAdmissibleTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelAdmissibleLoweringConclusionTermAt lower
              (tVar 3) (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_fixedLevelAdmissibleLoweringBelowTermAt_iff : forall
    (M : RawPAModel) e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current,
  raw_formula_sat M e
    (fixedLevelAdmissibleLoweringBelowTermAt lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current) <->
  RawFixedLevelAdmissibleLoweringBelow M lower
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e current).
Proof.
  intros. unfold fixedLevelAdmissibleLoweringBelowTermAt,
    fixedLevelAdmissibleLoweringConclusionTermAt,
    fixedTruthTraversalAll5, RawFixedLevelAdmissibleLoweringBelow,
    rawFixedLevelSigmaMode, rawFixedLevelPiMode.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_five.
  cbn [raw_term_eval scons].
  repeat rewrite raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_fixedLevelAdmissibleLoweringBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound (raw_zero M).
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    index mode code assignmentCode assignmentStep hindex.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Earlier source references can be fed directly to the prefix invariant
    once constructor inversion supplies the child's honest guard. *)
Lemma raw_fixedLevelAdmissibleLoweringBelow_sigma_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedAssignmentDefinedThrough M
    childAssignmentCode childAssignmentStep child ->
  RawFixedLevelSigmaDomain M (S lower) child ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep
    hbelow hcurrentBound [hchildIndex hchildLookup]
    hatomic hassignment hdomain.
  destruct (hbelow childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep hchildIndex
    (raw_assignment_lt_trans M hPA childIndex current sourceBound
      hchildIndex hcurrentBound)
    hchildLookup
    (conj hatomic (conj hassignment (or_introl hdomain))))
    as [hsigma _].
  exact (hsigma eq_refl hdomain).
Qed.

Lemma raw_fixedLevelAdmissibleLoweringBelow_pi_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedAssignmentDefinedThrough M
    childAssignmentCode childAssignmentStep child ->
  RawFixedLevelPiDomain M (S lower) child ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep
    hbelow hcurrentBound [hchildIndex hchildLookup]
    hatomic hassignment hdomain.
  destruct (hbelow childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep hchildIndex
    (raw_assignment_lt_trans M hPA childIndex current sourceBound
      hchildIndex hcurrentBound)
    hchildLookup
    (conj hatomic (conj hassignment (or_intror hdomain))))
    as [_ hpi].
  exact (hpi eq_refl hdomain).
Qed.

(** Meta-level assembly combinators.  They hide only table plumbing: every
    table is still obtained from the PA-internal append/concatenation proofs.
    The row-building continuation receives the child root(s) as genuine
    earlier states at the fresh parent index. *)
Lemma raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    childMode child childAssignmentCode childAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound childIndex,
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound childIndex childMode child
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelSigmaMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & childIndex &
     htraversal) hrow.
  pose proof htraversal as hparts.
  destruct hparts as [_ [_ [_ [_ [hchildBelow [hchildLookup _]]]]]].
  exact (raw_fixedLevelSuccessorTruthTraversal_append_sigma M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound childIndex childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal
    (hrow modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound childIndex
      (conj hchildBelow hchildLookup))).
Qed.

Lemma raw_fixedLevelSuccessorCertificateTraversal_build_pi_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    childMode child childAssignmentCode childAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound childIndex,
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound childIndex childMode child
      childAssignmentCode childAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelPiMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & childIndex &
     htraversal) hrow.
  pose proof htraversal as hparts.
  destruct hparts as [_ [_ [_ [_ [hchildBelow [hchildLookup _]]]]]].
  exact (raw_fixedLevelSuccessorTruthTraversal_append_pi M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound childIndex childMode child childAssignmentCode childAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal
    (hrow modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound childIndex
      (conj hchildBelow hchildLookup))).
Qed.

Lemma raw_fixedLevelSuccessorCertificateTraversal_build_sigma_two : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    secondMode secondChild secondAssignmentCode secondAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex firstIndex,
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondChild
      secondAssignmentCode secondAssignmentStep ->
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound firstIndex firstMode firstChild
      firstAssignmentCode firstAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelSigmaMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    hfirst hsecond hrow.
  destruct (raw_fixedLevelSuccessorCertificateTraversals_join M hPA lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    hfirst hsecond) as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & secondIndex &
     htraversal & hsecondEarlier & firstIndex & hfirstEarlier).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_sigma M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound secondIndex secondMode secondChild
    secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal
    (hrow modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex firstIndex
      hsecondEarlier hfirstEarlier)).
Qed.

Lemma raw_fixedLevelSuccessorCertificateTraversal_build_pi_two : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelSuccessorCertificateTraversal M lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep ->
  RawFixedLevelSuccessorCertificateTraversal M lower
    secondMode secondChild secondAssignmentCode secondAssignmentStep ->
  (forall modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex firstIndex,
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound secondIndex secondMode secondChild
      secondAssignmentCode secondAssignmentStep ->
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound firstIndex firstMode firstChild
      firstAssignmentCode firstAssignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      (RawFixedLevelSigmaTruthCertificate M lower)
      (RawFixedLevelPiFalsityCertificate M lower)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound (rawFixedLevelPiMode M) parent
      parentAssignmentCode parentAssignmentStep) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep
    hfirst hsecond hrow.
  destruct (raw_fixedLevelSuccessorCertificateTraversals_join M hPA lower
    firstMode firstChild firstAssignmentCode firstAssignmentStep
    secondMode secondChild secondAssignmentCode secondAssignmentStep
    hfirst hsecond) as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & secondIndex &
     htraversal & hsecondEarlier & firstIndex & hfirstEarlier).
  exact (raw_fixedLevelSuccessorTruthTraversal_append_pi M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound secondIndex secondMode secondChild
    secondAssignmentCode secondAssignmentStep
    parent parentAssignmentCode parentAssignmentStep htraversal
    (hrow modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound secondIndex firstIndex
      hsecondEarlier hfirstEarlier)).
Qed.

Corollary raw_fixedLevelClosedEmptyRow_build_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFixedLevelSigmaMode M) parent
    parentAssignmentCode parentAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower parent parentAssignmentCode parentAssignmentStep hrow.
  cbn [RawFixedLevelSigmaTruthCertificate].
  exact (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA lower
    (rawFixedLevelSigmaMode M) parent
    parentAssignmentCode parentAssignmentStep hrow).
Qed.

Corollary raw_fixedLevelClosedEmptyRow_build_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    lower parent parentAssignmentCode parentAssignmentStep,
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFixedLevelPiMode M) parent
    parentAssignmentCode parentAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    parent parentAssignmentCode parentAssignmentStep.
Proof.
  intros M hPA lower parent parentAssignmentCode parentAssignmentStep hrow.
  cbn [RawFixedLevelPiFalsityCertificate].
  exact (raw_fixedLevelClosedSuccessorRow_singleton_traversal M hPA lower
    (rawFixedLevelPiMode M) parent
    parentAssignmentCode parentAssignmentStep hrow).
Qed.

(** Lower one Sigma source row.  The source witness is at traversal parameter
    [S lower], hence certifies level [S (S lower)]; the result is a freshly
    assembled certificate at level [S lower]. *)
Lemma raw_fixedLevelSigmaSuccessorWitnessRow_admissible_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M (S lower) code ->
  RawFixedLevelSigmaSuccessorWitnessRow M (S lower)
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M (S lower)
        leftCode binderAssignmentCode binderAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare
    hbelow hcurrentBound hadmissible htargetDomain
    [_ hcases].
  destruct hcases as
    [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
  - exact (raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero
      M hPA lower code assignmentCode assignmentStep htargetDomain hzero).
  - destruct himpLeft as [hcode [hsourceEarlier _]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment] _].
    destruct (raw_fixedLevelSigmaDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain _].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceEarlier
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA lower (rawFixedLevelPiMode M) leftCode
      assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M lower leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetLeftIndex htargetEarlier.
      left. split; [reflexivity |].
      exists targetLeftIndex, leftCode,
        (raw_zero M), rightCode, (raw_zero M),
        assignmentCode, assignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. left. split; [reflexivity |].
      split; [exact htargetEarlier | reflexivity].
  - destruct himpRight as [hcode [hsourceEarlier _]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [_ [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelSigmaDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [_ hrightDomain].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceEarlier
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA lower (rawFixedLevelSigmaMode M) rightCode
      assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M lower rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetRightIndex htargetEarlier.
      left. split; [reflexivity |].
      exists (raw_zero M), leftCode,
        targetRightIndex, rightCode, (raw_zero M),
        assignmentCode, assignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. right. left. split; [reflexivity |].
      split; [exact htargetEarlier | reflexivity].
  - destruct hand as [hcode [hsourceLeft hsourceRight]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelSigmaDomain_and M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_two
      M hPA lower
      (rawFixedLevelSigmaMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelSigmaMode M) rightCode assignmentCode assignmentStep
      (rawFormulaAndCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M lower leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M lower rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex
        htargetRight htargetLeft.
      left. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hor as [hcode [hsourceLeft | hsourceRight]]; subst code.
    + destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [[hleftAtomic hleftAssignment] _].
      destruct (raw_fixedLevelSigmaDomain_or M hPA (S lower)
        leftCode rightCode htargetDomain) as [hleftDomain _].
      pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        leftIndex leftCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceLeft
        hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
        M hPA lower (rawFixedLevelSigmaMode M) leftCode
        assignmentCode assignmentStep
        (rawFormulaOrCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
          M lower leftCode assignmentCode assignmentStep)).
        exact hleftCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetLeftIndex htargetEarlier.
        left. split; [reflexivity |].
        exists targetLeftIndex, leftCode,
          (raw_zero M), rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact htargetDomain |].
        right. right. right. right. left.
        split; [reflexivity |]. left. exact htargetEarlier.
    + destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [_ [hrightAtomic hrightAssignment]].
      destruct (raw_fixedLevelSigmaDomain_or M hPA (S lower)
        leftCode rightCode htargetDomain) as [_ hrightDomain].
      pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        rightIndex rightCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceRight
        hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
        M hPA lower (rawFixedLevelSigmaMode M) rightCode
        assignmentCode assignmentStep
        (rawFormulaOrCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
          M lower rightCode assignmentCode assignmentStep)).
        exact hrightCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetRightIndex htargetEarlier.
        left. split; [reflexivity |].
        exists (raw_zero M), leftCode,
          targetRightIndex, rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact htargetDomain |].
        right. right. right. right. left.
        split; [reflexivity |]. right. exact htargetEarlier.
  - destruct hex as [hcode [hprepend hsourceEarlier]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    assert (hchildCode : rawLt M leftCode
        (rawFormulaExCode M leftCode)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 6) leftCode). }
    pose proof (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaExCode M leftCode)
      newAssignmentCode newAssignmentStep leftCode
      hparentAssignment hprepend hchildCode) as hchildAssignment.
    pose proof (raw_fixedLevelSigmaDomain_ex M hPA (S lower)
      leftCode htargetDomain) as hchildDomain.
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode newAssignmentCode newAssignmentStep
      hbelow hcurrentBound hsourceEarlier
      hchildAtomic hchildAssignment hchildDomain) as hchildCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA lower (rawFixedLevelSigmaMode M) leftCode
      newAssignmentCode newAssignmentStep
      (rawFormulaExCode M leftCode) assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M lower leftCode newAssignmentCode newAssignmentStep)).
      exact hchildCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetChildIndex htargetEarlier.
      left. split; [reflexivity |].
      exists targetChildIndex, leftCode,
        (raw_zero M), (raw_zero M), witness,
        newAssignmentCode, newAssignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. right. right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hall as [hcode hsourceNone]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    pose proof (raw_fixedLevelSigmaDomain_all_successor M hPA lower
      leftCode htargetDomain) as hchildDomain.
    assert (htargetNone : RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            leftCode binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep (rawFormulaAllCode M leftCode)).
    {
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hlowerCertificate).
      apply hsourceNone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          binderAssignmentCode binderAssignmentStep leftCode).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep binderWitness
          (rawFormulaAllCode M leftCode)
          binderAssignmentCode binderAssignmentStep leftCode
          hparentAssignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) leftCode).
      }
      destruct (hcoherence leftCode binderAssignmentCode binderAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_intror hchildDomain)))) as [_ hpi].
      exact (proj1 (hpi hchildDomain) hlowerCertificate).
    }
    apply (raw_fixedLevelClosedEmptyRow_build_sigma M hPA lower
      (rawFormulaAllCode M leftCode) assignmentCode assignmentStep).
    left. split; [reflexivity |].
    exists (raw_zero M), leftCode, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact htargetDomain |].
    right. right. right. right. right. right.
    split; [reflexivity | exact htargetNone].
Qed.

(** The dual Pi row construction.  Existential counterexamples are the only
    place where the lower-level Sigma half of coherence is used. *)
Lemma raw_fixedLevelPiSuccessorWitnessRow_admissible_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelPiDomain M (S lower) code ->
  RawFixedLevelPiSuccessorWitnessRow M (S lower)
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M (S lower)
        leftCode binderAssignmentCode binderAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare
    hbelow hcurrentBound hadmissible htargetDomain
    [_ hcases].
  destruct hcases as
    [hzero | [himp | [hand | [hor | [hall | hex]]]]].
  - exact (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero
      M hPA lower code assignmentCode assignmentStep htargetDomain hzero).
  - destruct himp as
      [hcode [hsourceLeft [hsourceRight _]]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelPiDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_two
      M hPA lower
      (rawFixedLevelSigmaMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelPiMode M) rightCode assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M lower leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M lower rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex
        htargetRight htargetLeft.
      right. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. left. split; [reflexivity |].
      split; [exact htargetLeft |].
      split; [exact htargetRight | reflexivity].
  - destruct hand as [hcode [hsourceLeft | hsourceRight]]; subst code.
    + destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [[hleftAtomic hleftAssignment] _].
      destruct (raw_fixedLevelPiDomain_and M hPA (S lower)
        leftCode rightCode htargetDomain) as [hleftDomain _].
      pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        leftIndex leftCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceLeft
        hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
        M hPA lower (rawFixedLevelPiMode M) leftCode
        assignmentCode assignmentStep
        (rawFormulaAndCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
          M lower leftCode assignmentCode assignmentStep)).
        exact hleftCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetLeftIndex htargetEarlier.
        right. split; [reflexivity |].
        exists targetLeftIndex, leftCode,
          (raw_zero M), rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact htargetDomain |].
        right. right. left.
        split; [reflexivity |]. left. exact htargetEarlier.
    + destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [_ [hrightAtomic hrightAssignment]].
      destruct (raw_fixedLevelPiDomain_and M hPA (S lower)
        leftCode rightCode htargetDomain) as [_ hrightDomain].
      pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        rightIndex rightCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceRight
        hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
        M hPA lower (rawFixedLevelPiMode M) rightCode
        assignmentCode assignmentStep
        (rawFormulaAndCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
          M lower rightCode assignmentCode assignmentStep)).
        exact hrightCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetRightIndex htargetEarlier.
        right. split; [reflexivity |].
        exists (raw_zero M), leftCode,
          targetRightIndex, rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact htargetDomain |].
        right. right. left.
        split; [reflexivity |]. right. exact htargetEarlier.
  - destruct hor as [hcode [hsourceLeft hsourceRight]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelPiDomain_or M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_two
      M hPA lower
      (rawFixedLevelPiMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelPiMode M) rightCode assignmentCode assignmentStep
      (rawFormulaOrCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M lower leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M lower rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex
        htargetRight htargetLeft.
      right. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hall as [hcode [hprepend hsourceEarlier]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    assert (hchildCode : rawLt M leftCode
        (rawFormulaAllCode M leftCode)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 5) leftCode). }
    pose proof (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaAllCode M leftCode)
      newAssignmentCode newAssignmentStep leftCode
      hparentAssignment hprepend hchildCode) as hchildAssignment.
    pose proof (raw_fixedLevelPiDomain_all M hPA (S lower)
      leftCode htargetDomain) as hchildDomain.
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode newAssignmentCode newAssignmentStep
      hbelow hcurrentBound hsourceEarlier
      hchildAtomic hchildAssignment hchildDomain) as hchildCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
      M hPA lower (rawFixedLevelPiMode M) leftCode
      newAssignmentCode newAssignmentStep
      (rawFormulaAllCode M leftCode) assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M lower leftCode newAssignmentCode newAssignmentStep)).
      exact hchildCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetChildIndex htargetEarlier.
      right. split; [reflexivity |].
      exists targetChildIndex, leftCode,
        (raw_zero M), (raw_zero M), witness,
        newAssignmentCode, newAssignmentStep, (raw_zero M).
      split; [exact htargetDomain |].
      right. right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hex as [hcode hsourceNone]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    pose proof (raw_fixedLevelPiDomain_ex_successor M hPA lower
      leftCode htargetDomain) as hchildDomain.
    assert (htargetNone : RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            leftCode binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep (rawFormulaExCode M leftCode)).
    {
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hlowerCertificate).
      apply hsourceNone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          binderAssignmentCode binderAssignmentStep leftCode).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep binderWitness
          (rawFormulaExCode M leftCode)
          binderAssignmentCode binderAssignmentStep leftCode
          hparentAssignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) leftCode).
      }
      destruct (hcoherence leftCode binderAssignmentCode binderAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_introl hchildDomain)))) as [hsigma _].
      exact (proj1 (hsigma hchildDomain) hlowerCertificate).
    }
    apply (raw_fixedLevelClosedEmptyRow_build_pi M hPA lower
      (rawFormulaExCode M leftCode) assignmentCode assignmentStep).
    right. split; [reflexivity |].
    exists (raw_zero M), leftCode, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact htargetDomain |].
    right. right. right. right. right.
    split; [reflexivity | exact htargetNone].
Qed.

Lemma raw_fixedLevelClosedSuccessorRow_admissible_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    mode code assignmentCode assignmentStep,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M (S lower)
    (RawFixedLevelSigmaTruthCertificate M (S lower))
    (RawFixedLevelPiFalsityCertificate M (S lower))
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current mode code assignmentCode assignmentStep ->
  (mode = rawFixedLevelSigmaMode M ->
    RawFixedLevelSigmaDomain M (S lower) code ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      code assignmentCode assignmentStep) /\
  (mode = rawFixedLevelPiMode M ->
    RawFixedLevelPiDomain M (S lower) code ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      code assignmentCode assignmentStep).
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    mode code assignmentCode assignmentStep
    hbelow hcurrentBound hadmissible hclosed.
  destruct hclosed as
    [[hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hsigma)] |
     [hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hpi)]].
  - split.
    + intros _ hdomain.
      exact (raw_fixedLevelSigmaSuccessorWitnessRow_admissible_lower
        M hPA lower hcoherence
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare
        hbelow hcurrentBound hadmissible hdomain hsigma).
    + intros hpiMode _.
      exfalso. apply (raw_zero_neq_truthOne M hPA).
      unfold rawFixedLevelSigmaMode, rawFixedLevelPiMode in hmode, hpiMode.
      rewrite <- hmode. exact hpiMode.
  - split.
    + intros hsigmaMode _.
      exfalso. apply (raw_zero_neq_truthOne M hPA).
      unfold rawFixedLevelSigmaMode, rawFixedLevelPiMode in hmode, hsigmaMode.
      rewrite <- hsigmaMode. exact hmode.
    + intros _ hdomain.
      exact (raw_fixedLevelPiSuccessorWitnessRow_admissible_lower
        M hPA lower hcoherence
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare
        hbelow hcurrentBound hadmissible hdomain hpi).
Qed.

Lemma raw_fixedLevelAdmissibleLoweringBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M (S lower)
    (RawFixedLevelSigmaTruthCertificate M (S lower))
    (RawFixedLevelPiFalsityCertificate M (S lower))
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    sourceBound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  forall current,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound (raw_succ M current).
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal current hbelow
    index mode code assignmentCode assignmentStep
    hindexSucc hindexBound hlookup hadmissible.
  destruct (raw_lt_succ_cases M hPA index current hindexSucc)
    as [hindexCurrent | ->].
  - exact (hbelow index mode code assignmentCode assignmentStep
      hindexCurrent hindexBound hlookup hadmissible).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [_ [_ hrows]]]]]].
    exact (raw_fixedLevelClosedSuccessorRow_admissible_lower
      M hPA lower hcoherence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      mode code assignmentCode assignmentStep
      hbelow hindexBound hadmissible
      (hrows current mode code assignmentCode assignmentStep
        hindexBound hlookup)).
Qed.

(** PA's own induction, rather than Rocq recursion, crosses the possibly
    nonstandard source-table bound. *)
Theorem raw_fixedLevelAdmissibleLoweringBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M (S lower)
    (RawFixedLevelSigmaTruthCertificate M (S lower))
    (RawFixedLevelPiFalsityCertificate M (S lower))
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    sourceBound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  forall current,
  RawFixedLevelAdmissibleLoweringBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => modeCode
    | 1 => modeStep
    | 2 => formulaCode
    | 3 => formulaStep
    | 4 => assignmentCodeCode
    | 5 => assignmentCodeStep
    | 6 => assignmentStepCode
    | 7 => assignmentStepStep
    | _ => sourceBound
    end).
  set (phi := fixedLevelAdmissibleLoweringBelowTermAt lower
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 8)
    (tVar 9) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_fixedLevelAdmissibleLoweringBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_fixedLevelAdmissibleLoweringBelow_zero M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelAdmissibleLoweringBelowTermAt_iff M
          (scons M current parameterEnv) lower
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8)
          (tVar 9) (tVar 0)) hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_fixedLevelAdmissibleLoweringBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelAdmissibleLoweringBelow_succ M hPA lower
        hcoherence modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound
        rootIndex rootMode root rootAssignmentCode rootAssignmentStep
        htraversal current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelAdmissibleLoweringBelowTermAt_iff M
      (scons M current parameterEnv) lower
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 8)
      (tVar 9) (tVar 0)) (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_fixedLevelTruthCertificate_admissible_successor_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  (forall root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaDomain M (S lower) root ->
    RawFixedLevelSigmaTruthCertificate M (S (S lower))
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      root assignmentCode assignmentStep) /\
  (forall root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelPiDomain M (S lower) root ->
    RawFixedLevelPiFalsityCertificate M (S (S lower))
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      root assignmentCode assignmentStep).
Proof.
  intros M hPA lower hcoherence. split;
    intros root assignmentCode assignmentStep hadmissible hdomain hcertificate;
    cbn [RawFixedLevelSigmaTruthCertificate
      RawFixedLevelPiFalsityCertificate] in hcertificate;
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       htraversal).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_all M hPA lower
      hcoherence modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound
      rootIndex (rawFixedLevelSigmaMode M) root
      assignmentCode assignmentStep htraversal bound) as hall.
    exact (proj1 (hall rootIndex (rawFixedLevelSigmaMode M) root
      assignmentCode assignmentStep hrootBelow hrootBelow
      hrootLookup hadmissible) eq_refl hdomain).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    pose proof (raw_fixedLevelAdmissibleLoweringBelow_all M hPA lower
      hcoherence modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound
      rootIndex (rawFixedLevelPiMode M) root
      assignmentCode assignmentStep htraversal bound) as hall.
    exact (proj2 (hall rootIndex (rawFixedLevelPiMode M) root
      assignmentCode assignmentStep hrootBelow hrootBelow
      hrootLookup hadmissible) eq_refl hdomain).
Qed.

(** ------------------------------------------------------------------
    Guarded raising uses the same reachable-row discipline.

    The earlier unguarded raising lemma can replay an entire source table
    only when lowering is available for every hidden row.  Our corrected
    coherence boundary is admissibility-guarded, so unrelated source rows
    must again be ignored and reachable rows rebuilt. *)

Definition RawFixedLevelAdmissibleRaisingBelow (M : RawPAModel)
    (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current : M) : Prop :=
  forall index mode code assignmentCode assignmentStep : M,
    rawLt M index current ->
    rawLt M index sourceBound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawFixedLevelTruthAdmissible M (S lower)
      code assignmentCode assignmentStep ->
    (mode = rawFixedLevelSigmaMode M ->
      RawFixedLevelSigmaDomain M (S lower) code ->
      RawFixedLevelSigmaTruthCertificate M (S (S lower))
        code assignmentCode assignmentStep) /\
    (mode = rawFixedLevelPiMode M ->
      RawFixedLevelPiDomain M (S lower) code ->
      RawFixedLevelPiFalsityCertificate M (S (S lower))
        code assignmentCode assignmentStep).

Arguments RawFixedLevelAdmissibleRaisingBelow
  M lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
  : clear implicits.

Definition fixedLevelAdmissibleRaisingConclusionTermAt (lower : nat)
    (mode code assignmentCode assignmentStep : term) : formula :=
  pAnd
    (pImp
      (pEq mode tZero)
      (pImp
        (fixedLevelSigmaDomainTermAt (S lower) code)
        (fixedLevelSigmaTruthCertificateTermAt (S (S lower))
          code assignmentCode assignmentStep)))
    (pImp
      (pEq mode (Term.numeral 1))
      (pImp
        (fixedLevelPiDomainTermAt (S lower) code)
        (fixedLevelPiFalsityCertificateTermAt (S (S lower))
          code assignmentCode assignmentStep))).

Definition fixedLevelAdmissibleRaisingBelowTermAt (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current : term)
    : formula :=
  fixedTruthTraversalAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (Formula.ltTermAt (tVar 4) (liftTerm 5 sourceBound))
        (pImp
          (fixedLevelStateLookupTermAt
            (liftTerm 5 modeCode) (liftTerm 5 modeStep)
            (liftTerm 5 formulaCode) (liftTerm 5 formulaStep)
            (liftTerm 5 assignmentCodeCode)
            (liftTerm 5 assignmentCodeStep)
            (liftTerm 5 assignmentStepCode)
            (liftTerm 5 assignmentStepStep)
            (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
          (pImp
            (fixedLevelTruthAdmissibleTermAt (S lower)
              (tVar 2) (tVar 1) (tVar 0))
            (fixedLevelAdmissibleRaisingConclusionTermAt lower
              (tVar 3) (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_fixedLevelAdmissibleRaisingBelowTermAt_iff : forall
    (M : RawPAModel) e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current,
  raw_formula_sat M e
    (fixedLevelAdmissibleRaisingBelowTermAt lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current) <->
  RawFixedLevelAdmissibleRaisingBelow M lower
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e current).
Proof.
  intros. unfold fixedLevelAdmissibleRaisingBelowTermAt,
    fixedLevelAdmissibleRaisingConclusionTermAt,
    fixedTruthTraversalAll5, RawFixedLevelAdmissibleRaisingBelow,
    rawFixedLevelSigmaMode, rawFixedLevelPiMode.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_five.
  cbn [raw_term_eval scons].
  repeat rewrite raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_fixedLevelAdmissibleRaisingBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound (raw_zero M).
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    index mode code assignmentCode assignmentStep hindex.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_fixedLevelAdmissibleRaisingBelow_sigma_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedAssignmentDefinedThrough M
    childAssignmentCode childAssignmentStep child ->
  RawFixedLevelSigmaDomain M (S lower) child ->
  RawFixedLevelSigmaTruthCertificate M (S (S lower))
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep
    hbelow hcurrentBound [hchildIndex hchildLookup]
    hatomic hassignment hdomain.
  destruct (hbelow childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep hchildIndex
    (raw_assignment_lt_trans M hPA childIndex current sourceBound
      hchildIndex hcurrentBound)
    hchildLookup
    (conj hatomic (conj hassignment (or_introl hdomain))))
    as [hsigma _].
  exact (hsigma eq_refl hdomain).
Qed.

Lemma raw_fixedLevelAdmissibleRaisingBelow_pi_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedAssignmentDefinedThrough M
    childAssignmentCode childAssignmentStep child ->
  RawFixedLevelPiDomain M (S lower) child ->
  RawFixedLevelPiFalsityCertificate M (S (S lower))
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    childIndex child childAssignmentCode childAssignmentStep
    hbelow hcurrentBound [hchildIndex hchildLookup]
    hatomic hassignment hdomain.
  destruct (hbelow childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep hchildIndex
    (raw_assignment_lt_trans M hPA childIndex current sourceBound
      hchildIndex hcurrentBound)
    hchildLookup
    (conj hatomic (conj hassignment (or_intror hdomain))))
    as [_ hpi].
  exact (hpi eq_refl hdomain).
Qed.

Lemma raw_fixedLevelSigmaSuccessorWitnessRow_admissible_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M (S lower) code ->
  RawFixedLevelSigmaSuccessorWitnessRow M lower
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        leftCode binderAssignmentCode binderAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare ->
  RawFixedLevelSigmaTruthCertificate M (S (S lower))
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare
    hbelow hcurrentBound hadmissible htargetDomain
    [_ hcases].
  pose proof (raw_fixedLevelSigmaDomain_mono M hPA (S lower)
    code htargetDomain) as hupperDomain.
  destruct hcases as
    [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
  - exact (raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero
      M hPA (S lower) code assignmentCode assignmentStep hupperDomain hzero).
  - destruct himpLeft as [hcode [hsourceEarlier _]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment] _].
    destruct (raw_fixedLevelSigmaDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain _].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceEarlier
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA (S lower) (rawFixedLevelPiMode M) leftCode
      assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M (S lower) leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetLeftIndex htargetEarlier.
      left. split; [reflexivity |].
      exists targetLeftIndex, leftCode,
        (raw_zero M), rightCode, (raw_zero M),
        assignmentCode, assignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. left. split; [reflexivity |].
      split; [exact htargetEarlier | reflexivity].
  - destruct himpRight as [hcode [hsourceEarlier _]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [_ [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelSigmaDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [_ hrightDomain].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceEarlier
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA (S lower) (rawFixedLevelSigmaMode M) rightCode
      assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M (S lower) rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetRightIndex htargetEarlier.
      left. split; [reflexivity |].
      exists (raw_zero M), leftCode,
        targetRightIndex, rightCode, (raw_zero M),
        assignmentCode, assignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. right. left. split; [reflexivity |].
      split; [exact htargetEarlier | reflexivity].
  - destruct hand as [hcode [hsourceLeft hsourceRight]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelSigmaDomain_and M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_two
      M hPA (S lower)
      (rawFixedLevelSigmaMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelSigmaMode M) rightCode assignmentCode assignmentStep
      (rawFormulaAndCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M (S lower) leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M (S lower) rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex htargetRight htargetLeft.
      left. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hor as [hcode [hsourceLeft | hsourceRight]]; subst code.
    + destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [[hleftAtomic hleftAssignment] _].
      destruct (raw_fixedLevelSigmaDomain_or M hPA (S lower)
        leftCode rightCode htargetDomain) as [hleftDomain _].
      pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        leftIndex leftCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceLeft
        hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
        M hPA (S lower) (rawFixedLevelSigmaMode M) leftCode
        assignmentCode assignmentStep
        (rawFormulaOrCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
          M (S lower) leftCode assignmentCode assignmentStep)).
        exact hleftCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetLeftIndex htargetEarlier.
        left. split; [reflexivity |].
        exists targetLeftIndex, leftCode,
          (raw_zero M), rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact hupperDomain |].
        right. right. right. right. left.
        split; [reflexivity |]. left. exact htargetEarlier.
    + destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [_ [hrightAtomic hrightAssignment]].
      destruct (raw_fixedLevelSigmaDomain_or M hPA (S lower)
        leftCode rightCode htargetDomain) as [_ hrightDomain].
      pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        rightIndex rightCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceRight
        hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
        M hPA (S lower) (rawFixedLevelSigmaMode M) rightCode
        assignmentCode assignmentStep
        (rawFormulaOrCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
          M (S lower) rightCode assignmentCode assignmentStep)).
        exact hrightCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetRightIndex htargetEarlier.
        left. split; [reflexivity |].
        exists (raw_zero M), leftCode,
          targetRightIndex, rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact hupperDomain |].
        right. right. right. right. left.
        split; [reflexivity |]. right. exact htargetEarlier.
  - destruct hex as [hcode [hprepend hsourceEarlier]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    assert (hchildCode : rawLt M leftCode
        (rawFormulaExCode M leftCode)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 6) leftCode). }
    pose proof (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaExCode M leftCode)
      newAssignmentCode newAssignmentStep leftCode
      hparentAssignment hprepend hchildCode) as hchildAssignment.
    pose proof (raw_fixedLevelSigmaDomain_ex M hPA (S lower)
      leftCode htargetDomain) as hchildDomain.
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode newAssignmentCode newAssignmentStep
      hbelow hcurrentBound hsourceEarlier
      hchildAtomic hchildAssignment hchildDomain) as hchildCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_sigma_one
      M hPA (S lower) (rawFixedLevelSigmaMode M) leftCode
      newAssignmentCode newAssignmentStep
      (rawFormulaExCode M leftCode) assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M (S lower) leftCode newAssignmentCode newAssignmentStep)).
      exact hchildCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetChildIndex htargetEarlier.
      left. split; [reflexivity |].
      exists targetChildIndex, leftCode,
        (raw_zero M), (raw_zero M), witness,
        newAssignmentCode, newAssignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. right. right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hall as [hcode hsourceNone]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    pose proof (raw_fixedLevelSigmaDomain_all_successor M hPA lower
      leftCode htargetDomain) as hchildDomain.
    assert (htargetNone : RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M (S lower)
            leftCode binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep (rawFormulaAllCode M leftCode)).
    {
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hupperCertificate).
      apply hsourceNone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          binderAssignmentCode binderAssignmentStep leftCode).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep binderWitness
          (rawFormulaAllCode M leftCode)
          binderAssignmentCode binderAssignmentStep leftCode
          hparentAssignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) leftCode).
      }
      destruct (hcoherence leftCode binderAssignmentCode binderAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_intror hchildDomain)))) as [_ hpi].
      exact (proj2 (hpi hchildDomain) hupperCertificate).
    }
    apply (raw_fixedLevelClosedEmptyRow_build_sigma M hPA (S lower)
      (rawFormulaAllCode M leftCode) assignmentCode assignmentStep).
    left. split; [reflexivity |].
    exists (raw_zero M), leftCode, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hupperDomain |].
    right. right. right. right. right. right.
    split; [reflexivity | exact htargetNone].
Qed.

Lemma raw_fixedLevelPiSuccessorWitnessRow_admissible_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelPiDomain M (S lower) code ->
  RawFixedLevelPiSuccessorWitnessRow M lower
    (fun _ binderAssignmentCode binderAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        leftCode binderAssignmentCode binderAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare ->
  RawFixedLevelPiFalsityCertificate M (S (S lower))
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare
    hbelow hcurrentBound hadmissible htargetDomain
    [_ hcases].
  pose proof (raw_fixedLevelPiDomain_mono M hPA (S lower)
    code htargetDomain) as hupperDomain.
  destruct hcases as
    [hzero | [himp | [hand | [hor | [hall | hex]]]]].
  - exact (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero
      M hPA (S lower) code assignmentCode assignmentStep hupperDomain hzero).
  - destruct himp as
      [hcode [hsourceLeft [hsourceRight _]]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelPiDomain_imp M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_sigma_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_two
      M hPA (S lower)
      (rawFixedLevelSigmaMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelPiMode M) rightCode assignmentCode assignmentStep
      (rawFormulaImpCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
        M (S lower) leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M (S lower) rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex htargetRight htargetLeft.
      right. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. left. split; [reflexivity |].
      split; [exact htargetLeft |].
      split; [exact htargetRight | reflexivity].
  - destruct hand as [hcode [hsourceLeft | hsourceRight]]; subst code.
    + destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [[hleftAtomic hleftAssignment] _].
      destruct (raw_fixedLevelPiDomain_and M hPA (S lower)
        leftCode rightCode htargetDomain) as [hleftDomain _].
      pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        leftIndex leftCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceLeft
        hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
        M hPA (S lower) (rawFixedLevelPiMode M) leftCode
        assignmentCode assignmentStep
        (rawFormulaAndCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
          M (S lower) leftCode assignmentCode assignmentStep)).
        exact hleftCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetLeftIndex htargetEarlier.
        right. split; [reflexivity |].
        exists targetLeftIndex, leftCode,
          (raw_zero M), rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact hupperDomain |].
        right. right. left.
        split; [reflexivity |]. left. exact htargetEarlier.
    + destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
        (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
        as [_ [hrightAtomic hrightAssignment]].
      destruct (raw_fixedLevelPiDomain_and M hPA (S lower)
        leftCode rightCode htargetDomain) as [_ hrightDomain].
      pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        rightIndex rightCode assignmentCode assignmentStep
        hbelow hcurrentBound hsourceRight
        hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
      apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
        M hPA (S lower) (rawFixedLevelPiMode M) rightCode
        assignmentCode assignmentStep
        (rawFormulaAndCode M leftCode rightCode)
        assignmentCode assignmentStep).
      * apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
          M (S lower) rightCode assignmentCode assignmentStep)).
        exact hrightCertificate.
      * intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
          targetAssignmentCodeCode targetAssignmentCodeStep
          targetAssignmentStepCode targetAssignmentStepStep
          targetBound targetRightIndex htargetEarlier.
        right. split; [reflexivity |].
        exists (raw_zero M), leftCode,
          targetRightIndex, rightCode, (raw_zero M),
          assignmentCode, assignmentStep, (raw_zero M).
        split; [exact hupperDomain |].
        right. right. left.
        split; [reflexivity |]. right. exact htargetEarlier.
  - destruct hor as [hcode [hsourceLeft hsourceRight]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
      (S lower) leftCode rightCode assignmentCode assignmentStep hadmissible)
      as [[hleftAtomic hleftAssignment]
          [hrightAtomic hrightAssignment]].
    destruct (raw_fixedLevelPiDomain_or M hPA (S lower)
      leftCode rightCode htargetDomain) as [hleftDomain hrightDomain].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceLeft
      hleftAtomic hleftAssignment hleftDomain) as hleftCertificate.
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      rightIndex rightCode assignmentCode assignmentStep
      hbelow hcurrentBound hsourceRight
      hrightAtomic hrightAssignment hrightDomain) as hrightCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_two
      M hPA (S lower)
      (rawFixedLevelPiMode M) leftCode assignmentCode assignmentStep
      (rawFixedLevelPiMode M) rightCode assignmentCode assignmentStep
      (rawFormulaOrCode M leftCode rightCode)
      assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M (S lower) leftCode assignmentCode assignmentStep)).
      exact hleftCertificate.
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M (S lower) rightCode assignmentCode assignmentStep)).
      exact hrightCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep targetBound
        targetRightIndex targetLeftIndex htargetRight htargetLeft.
      right. split; [reflexivity |].
      exists targetLeftIndex, leftCode, targetRightIndex, rightCode,
        (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hall as [hcode [hprepend hsourceEarlier]]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    assert (hchildCode : rawLt M leftCode
        (rawFormulaAllCode M leftCode)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 5) leftCode). }
    pose proof (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaAllCode M leftCode)
      newAssignmentCode newAssignmentStep leftCode
      hparentAssignment hprepend hchildCode) as hchildAssignment.
    pose proof (raw_fixedLevelPiDomain_all M hPA (S lower)
      leftCode htargetDomain) as hchildDomain.
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_pi_child M hPA lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      leftIndex leftCode newAssignmentCode newAssignmentStep
      hbelow hcurrentBound hsourceEarlier
      hchildAtomic hchildAssignment hchildDomain) as hchildCertificate.
    apply (raw_fixedLevelSuccessorCertificateTraversal_build_pi_one
      M hPA (S lower) (rawFixedLevelPiMode M) leftCode
      newAssignmentCode newAssignmentStep
      (rawFormulaAllCode M leftCode) assignmentCode assignmentStep).
    + apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
        M (S lower) leftCode newAssignmentCode newAssignmentStep)).
      exact hchildCertificate.
    + intros targetModeCode targetModeStep targetFormulaCode targetFormulaStep
        targetAssignmentCodeCode targetAssignmentCodeStep
        targetAssignmentStepCode targetAssignmentStepStep
        targetBound targetChildIndex htargetEarlier.
      right. split; [reflexivity |].
      exists targetChildIndex, leftCode,
        (raw_zero M), (raw_zero M), witness,
        newAssignmentCode, newAssignmentStep, (raw_zero M).
      split; [exact hupperDomain |].
      right. right. right. right. left.
      split; [reflexivity |]. split; assumption.
  - destruct hex as [hcode hsourceNone]. subst code.
    destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
      (S lower) leftCode assignmentCode assignmentStep hadmissible)
      as [hchildAtomic _].
    pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
    pose proof (raw_fixedLevelPiDomain_ex_successor M hPA lower
      leftCode htargetDomain) as hchildDomain.
    assert (htargetNone : RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M (S lower)
            leftCode binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep (rawFormulaExCode M leftCode)).
    {
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hupperCertificate).
      apply hsourceNone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          binderAssignmentCode binderAssignmentStep leftCode).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep binderWitness
          (rawFormulaExCode M leftCode)
          binderAssignmentCode binderAssignmentStep leftCode
          hparentAssignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) leftCode).
      }
      destruct (hcoherence leftCode binderAssignmentCode binderAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_introl hchildDomain)))) as [hsigma _].
      exact (proj2 (hsigma hchildDomain) hupperCertificate).
    }
    apply (raw_fixedLevelClosedEmptyRow_build_pi M hPA (S lower)
      (rawFormulaExCode M leftCode) assignmentCode assignmentStep).
    right. split; [reflexivity |].
    exists (raw_zero M), leftCode, (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hupperDomain |].
    right. right. right. right. right.
    split; [reflexivity | exact htargetNone].
Qed.

Lemma raw_fixedLevelClosedSuccessorRow_admissible_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    mode code assignmentCode assignmentStep,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  rawLt M current sourceBound ->
  RawFixedLevelTruthAdmissible M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current mode code assignmentCode assignmentStep ->
  (mode = rawFixedLevelSigmaMode M ->
    RawFixedLevelSigmaDomain M (S lower) code ->
    RawFixedLevelSigmaTruthCertificate M (S (S lower))
      code assignmentCode assignmentStep) /\
  (mode = rawFixedLevelPiMode M ->
    RawFixedLevelPiDomain M (S lower) code ->
    RawFixedLevelPiFalsityCertificate M (S (S lower))
      code assignmentCode assignmentStep).
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current
    mode code assignmentCode assignmentStep
    hbelow hcurrentBound hadmissible hclosed.
  destruct hclosed as
    [[hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hsigma)] |
     [hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hpi)]].
  - split.
    + intros _ hdomain.
      exact (raw_fixedLevelSigmaSuccessorWitnessRow_admissible_raise
        M hPA lower hcoherence
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare
        hbelow hcurrentBound hadmissible hdomain hsigma).
    + intros hpiMode _.
      exfalso. apply (raw_zero_neq_truthOne M hPA).
      unfold rawFixedLevelSigmaMode, rawFixedLevelPiMode in hmode, hpiMode.
      rewrite <- hmode. exact hpiMode.
  - split.
    + intros hsigmaMode _.
      exfalso. apply (raw_zero_neq_truthOne M hPA).
      unfold rawFixedLevelSigmaMode, rawFixedLevelPiMode in hmode, hsigmaMode.
      rewrite <- hsigmaMode. exact hmode.
    + intros _ hdomain.
      exact (raw_fixedLevelPiSuccessorWitnessRow_admissible_raise
        M hPA lower hcoherence
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound current
        code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare
        hbelow hcurrentBound hadmissible hdomain hpi).
Qed.

Lemma raw_fixedLevelAdmissibleRaisingBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    sourceBound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  forall current,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current ->
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound (raw_succ M current).
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal current hbelow
    index mode code assignmentCode assignmentStep
    hindexSucc hindexBound hlookup hadmissible.
  destruct (raw_lt_succ_cases M hPA index current hindexSucc)
    as [hindexCurrent | ->].
  - exact (hbelow index mode code assignmentCode assignmentStep
      hindexCurrent hindexBound hlookup hadmissible).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [_ [_ hrows]]]]]].
    exact (raw_fixedLevelClosedSuccessorRow_admissible_raise
      M hPA lower hcoherence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep sourceBound current
      mode code assignmentCode assignmentStep
      hbelow hindexBound hadmissible
      (hrows current mode code assignmentCode assignmentStep
        hindexBound hlookup)).
Qed.

Theorem raw_fixedLevelAdmissibleRaisingBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    sourceBound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep ->
  forall current,
  RawFixedLevelAdmissibleRaisingBelow M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound current.
Proof.
  intros M hPA lower hcoherence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep sourceBound
    rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => modeCode
    | 1 => modeStep
    | 2 => formulaCode
    | 3 => formulaStep
    | 4 => assignmentCodeCode
    | 5 => assignmentCodeStep
    | 6 => assignmentStepCode
    | 7 => assignmentStepStep
    | _ => sourceBound
    end).
  set (phi := fixedLevelAdmissibleRaisingBelowTermAt lower
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 8)
    (tVar 9) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_fixedLevelAdmissibleRaisingBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_fixedLevelAdmissibleRaisingBelow_zero M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelAdmissibleRaisingBelowTermAt_iff M
          (scons M current parameterEnv) lower
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8)
          (tVar 9) (tVar 0)) hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_fixedLevelAdmissibleRaisingBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) lower
        (tVar 1) (tVar 2) (tVar 3) (tVar 4)
        (tVar 5) (tVar 6) (tVar 7) (tVar 8)
        (tVar 9) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelAdmissibleRaisingBelow_succ M hPA lower
        hcoherence modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep sourceBound
        rootIndex rootMode root rootAssignmentCode rootAssignmentStep
        htraversal current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelAdmissibleRaisingBelowTermAt_iff M
      (scons M current parameterEnv) lower
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 8)
      (tVar 9) (tVar 0)) (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_fixedLevelTruthCertificate_admissible_successor_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower ->
  (forall root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaDomain M (S lower) root ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S (S lower))
      root assignmentCode assignmentStep) /\
  (forall root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelPiDomain M (S lower) root ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M (S (S lower))
      root assignmentCode assignmentStep).
Proof.
  intros M hPA lower hcoherence. split;
    intros root assignmentCode assignmentStep hadmissible hdomain hcertificate;
    cbn [RawFixedLevelSigmaTruthCertificate
      RawFixedLevelPiFalsityCertificate] in hcertificate;
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       htraversal).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_all M hPA lower
      hcoherence modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound
      rootIndex (rawFixedLevelSigmaMode M) root
      assignmentCode assignmentStep htraversal bound) as hall.
    exact (proj1 (hall rootIndex (rawFixedLevelSigmaMode M) root
      assignmentCode assignmentStep hrootBelow hrootBelow
      hrootLookup hadmissible) eq_refl hdomain).
  - pose proof htraversal as hparts.
    destruct hparts as [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    pose proof (raw_fixedLevelAdmissibleRaisingBelow_all M hPA lower
      hcoherence modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound
      rootIndex (rawFixedLevelPiMode M) root
      assignmentCode assignmentStep htraversal bound) as hall.
    exact (proj2 (hall rootIndex (rawFixedLevelPiMode M) root
      assignmentCode assignmentStep hrootBelow hrootBelow
      hrootLookup hadmissible) eq_refl hdomain).
Qed.

(** ------------------------------------------------------------------
    External level induction and the exact PA theorem. *)

Theorem raw_fixedLevelAdmissibleTruthCertificateCoherence_all :
  forall lower (M : RawPAModel), RawPASatisfies M ->
    RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower.
Proof.
  induction lower as [|lower hIH].
  - intros M hPA.
    exact (raw_fixedLevelAdmissibleTruthCertificateCoherence_zero M hPA).
  - intros M hPA.
    specialize (hIH M hPA).
    destruct (raw_fixedLevelTruthCertificate_admissible_successor_lower
      M hPA lower hIH) as [hsigmaLower hpiLower].
    destruct (raw_fixedLevelTruthCertificate_admissible_successor_raise
      M hPA lower hIH) as [hsigmaRaise hpiRaise].
    intros root assignmentCode assignmentStep hadmissible.
    split.
    + intros hdomain. split.
      * exact (hsigmaRaise root assignmentCode assignmentStep
          hadmissible hdomain).
      * exact (hsigmaLower root assignmentCode assignmentStep
          hadmissible hdomain).
    + intros hdomain. split.
      * exact (hpiRaise root assignmentCode assignmentStep
          hadmissible hdomain).
      * exact (hpiLower root assignmentCode assignmentStep
          hadmissible hdomain).
Qed.

Theorem fixedLevelAdmissibleTruthCertificateCoherenceFormula_raw_valid :
  forall lower (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula lower).
Proof.
  intros lower M hPA e.
  apply (proj2
    (raw_sat_fixedLevelAdmissibleTruthCertificateCoherenceFormula_iff
      M e lower)).
  exact (raw_fixedLevelAdmissibleTruthCertificateCoherence_all lower M hPA).
Qed.

Definition fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed
    (lower : nat) : formula :=
  Formula.sealPA
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula lower).

Theorem fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed_sentence :
  forall lower,
  Formula.Sentence
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed lower).
Proof.
  intros lower.
  unfold fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed_raw_valid :
  forall lower (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed lower).
Proof.
  intros lower M hPA e.
  unfold fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed.
  apply (raw_formula_sat_sealPA_of_valid M).
  intros e'.
  exact (fixedLevelAdmissibleTruthCertificateCoherenceFormula_raw_valid
    lower M hPA e').
Qed.

Theorem PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed :
  forall lower,
  Formula.BProv Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed lower).
Proof.
  intros lower.
  apply PA_BProv_of_raw_valid.
  - exact
      (fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed_sentence
        lower).
  - exact
      (fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed_raw_valid
        lower).
Qed.

(** Universal elimination of [sealPA] recovers the exact displayed formula,
    so the final statement is an object-language PA proof rather than merely
    a semantic metatheorem. *)
Theorem PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula :
  forall lower,
  Formula.BProv Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula lower).
Proof.
  intros lower.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula lower)
    (fun n => n)
    (PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula_closed
      lower)) as hclosed.
  now rewrite Formula.rename_id in hclosed.
Qed.

End PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
