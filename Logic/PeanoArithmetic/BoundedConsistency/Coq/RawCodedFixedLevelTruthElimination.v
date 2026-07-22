(**
  Root views for globally closed positive fixed-level truth certificates.

  The public Sigma/Pi predicates hide a synchronized beta traversal.  A
  local Tarski row may refer to an earlier state of that traversal, but proof
  soundness needs an ordinary globally closed certificate for the referred
  child.  The restriction lemmas below reroot the same traversal at that
  earlier state.  Consequently the two public views expose only the logical
  constructor cases and globally usable child certificates; no table index
  escapes their interface.
*)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal.

Module PABoundedRawCodedFixedLevelTruthElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.

(** A positive Sigma root is either discharged by the rank-zero evaluator,
    or has exactly one of the six recursive Tarski witnesses.  Notice that
    the universal case deliberately retains its lower-level negative
    condition: this is the polarity switch built into the hierarchy. *)
Definition RawFixedLevelSigmaSuccessorRootView (M : RawPAModel)
    (lower : nat) (code assignmentCode assignmentStep : M) : Prop :=
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
      assignmentCode assignmentStep \/
  (exists left right : M,
    code = rawFormulaImpCode M left right /\
    RawFixedLevelPiFalsityCertificate M (S lower)
      left assignmentCode assignmentStep) \/
  (exists left right : M,
    code = rawFormulaImpCode M left right /\
    RawFixedLevelSigmaTruthCertificate M (S lower)
      right assignmentCode assignmentStep) \/
  (exists left right : M,
    code = rawFormulaAndCode M left right /\
    RawFixedLevelSigmaTruthCertificate M (S lower)
      left assignmentCode assignmentStep /\
    RawFixedLevelSigmaTruthCertificate M (S lower)
      right assignmentCode assignmentStep) \/
  (exists left right : M,
    code = rawFormulaOrCode M left right /\
    (RawFixedLevelSigmaTruthCertificate M (S lower)
       left assignmentCode assignmentStep \/
     RawFixedLevelSigmaTruthCertificate M (S lower)
       right assignmentCode assignmentStep)) \/
  (exists child witness newAssignmentCode newAssignmentStep : M,
    code = rawFormulaExCode M child /\
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
      newAssignmentCode newAssignmentStep /\
    RawFixedLevelSigmaTruthCertificate M (S lower)
      child newAssignmentCode newAssignmentStep) \/
  (exists child : M,
    code = rawFormulaAllCode M child /\
    RawFixedLevelNoBinderCounterexample M
      (fun _ binderAssignmentCode binderAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower child
          binderAssignmentCode binderAssignmentStep)
      assignmentCode assignmentStep code).

Arguments RawFixedLevelSigmaSuccessorRootView
  M lower code assignmentCode assignmentStep : clear implicits.

(** The dual root view. *)
Definition RawFixedLevelPiSuccessorRootView (M : RawPAModel)
    (lower : nat) (code assignmentCode assignmentStep : M) : Prop :=
  RawRankZeroTruthCertificate M code (raw_zero M)
      assignmentCode assignmentStep \/
  (exists left right : M,
    code = rawFormulaImpCode M left right /\
    RawFixedLevelSigmaTruthCertificate M (S lower)
      left assignmentCode assignmentStep /\
    RawFixedLevelPiFalsityCertificate M (S lower)
      right assignmentCode assignmentStep) \/
  (exists left right : M,
    code = rawFormulaAndCode M left right /\
    (RawFixedLevelPiFalsityCertificate M (S lower)
       left assignmentCode assignmentStep \/
     RawFixedLevelPiFalsityCertificate M (S lower)
       right assignmentCode assignmentStep)) \/
  (exists left right : M,
    code = rawFormulaOrCode M left right /\
    RawFixedLevelPiFalsityCertificate M (S lower)
      left assignmentCode assignmentStep /\
    RawFixedLevelPiFalsityCertificate M (S lower)
      right assignmentCode assignmentStep) \/
  (exists child witness newAssignmentCode newAssignmentStep : M,
    code = rawFormulaAllCode M child /\
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
      newAssignmentCode newAssignmentStep /\
    RawFixedLevelPiFalsityCertificate M (S lower)
      child newAssignmentCode newAssignmentStep) \/
  (exists child : M,
    code = rawFormulaExCode M child /\
    RawFixedLevelNoBinderCounterexample M
      (fun _ binderAssignmentCode binderAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower child
          binderAssignmentCode binderAssignmentStep)
      assignmentCode assignmentStep code).

Arguments RawFixedLevelPiSuccessorRootView
  M lower code assignmentCode assignmentStep : clear implicits.

(** Restrict a globally closed successor traversal to an earlier Sigma row.
    The new bound is [S childIndex], so every row needed by that child is
    retained while unrelated later rows disappear. *)
Lemma raw_fixedLevelSuccessorTruthTraversal_earlier_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    currentIndex childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep ->
  rawLt M currentIndex bound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    currentIndex childIndex child childAssignmentCode childAssignmentStep
    htraversal hcurrent [hchild hlookup].
  assert (hchildBound : rawLt M childIndex bound).
  {
    exact (raw_assignment_lt_trans M hPA
      childIndex currentIndex bound hchild hcurrent).
  }
  cbn [RawFixedLevelSigmaTruthCertificate].
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep,
    (raw_succ M childIndex), childIndex.
  exact (raw_fixedLevelSuccessorTruthTraversal_restrict_to_row M hPA lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal childIndex (rawFixedLevelSigmaMode M) child
    childAssignmentCode childAssignmentStep hchildBound hlookup).
Qed.

Lemma raw_fixedLevelSuccessorTruthTraversal_earlier_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    currentIndex childIndex child childAssignmentCode childAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep ->
  rawLt M currentIndex bound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    child childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    currentIndex childIndex child childAssignmentCode childAssignmentStep
    htraversal hcurrent [hchild hlookup].
  assert (hchildBound : rawLt M childIndex bound).
  {
    exact (raw_assignment_lt_trans M hPA
      childIndex currentIndex bound hchild hcurrent).
  }
  cbn [RawFixedLevelPiFalsityCertificate].
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep,
    (raw_succ M childIndex), childIndex.
  exact (raw_fixedLevelSuccessorTruthTraversal_restrict_to_row M hPA lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep
    htraversal childIndex (rawFixedLevelPiMode M) child
    childAssignmentCode childAssignmentStep hchildBound hlookup).
Qed.

(** Open the hidden root row and reroot each referenced same-level state.
    The mode-separation contradiction rules out the impossible Pi root row. *)
Theorem raw_fixedLevelSigmaTruthCertificate_successor_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
      code assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelSigmaSuccessorRootView M lower
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower code assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal).
  pose proof htraversal as hparts.
  destruct hparts as [_ [_ [_ [_ [hrootBelow _]]]]].
  pose proof (raw_fixedLevelSuccessorTruthTraversal_root_row M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex (rawFixedLevelSigmaMode M)
    code assignmentCode assignmentStep htraversal) as hrow.
  destruct hrow as [[_ hsigma] | [hmodes _]].
  - destruct hsigma as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare &
       [_ hcases]).
    destruct hcases as
      [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
    + now left.
    + right. left.
      exists leftCode, rightCode. split; [exact (proj1 himpLeft) |].
      exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound rootIndex (rawFixedLevelSigmaMode M) code
        assignmentCode assignmentStep rootIndex leftIndex leftCode
        assignmentCode assignmentStep htraversal hrootBelow
        (proj1 (proj2 himpLeft))).
    + right. right. left.
      exists leftCode, rightCode. split; [exact (proj1 himpRight) |].
      exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound rootIndex (rawFixedLevelSigmaMode M) code
        assignmentCode assignmentStep rootIndex rightIndex rightCode
        assignmentCode assignmentStep htraversal hrootBelow
        (proj1 (proj2 himpRight))).
    + right. right. right. left.
      exists leftCode, rightCode. split; [exact (proj1 hand) |]. split.
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M) code
          assignmentCode assignmentStep rootIndex leftIndex leftCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj1 (proj2 hand))).
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M) code
          assignmentCode assignmentStep rootIndex rightIndex rightCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj2 (proj2 hand))).
    + right. right. right. right. left.
      exists leftCode, rightCode. split; [exact (proj1 hor) |].
      destruct (proj2 hor) as [hleft | hright].
      * left. exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma
          M hPA lower modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M) code
          assignmentCode assignmentStep rootIndex leftIndex leftCode
          assignmentCode assignmentStep htraversal hrootBelow hleft).
      * right. exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma
          M hPA lower modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M) code
          assignmentCode assignmentStep rootIndex rightIndex rightCode
          assignmentCode assignmentStep htraversal hrootBelow hright).
    + right. right. right. right. right. left.
      exists leftCode, witness, newAssignmentCode, newAssignmentStep.
      split; [exact (proj1 hex) |]. split; [exact (proj1 (proj2 hex)) |].
      exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound rootIndex (rawFixedLevelSigmaMode M) code
        assignmentCode assignmentStep rootIndex leftIndex leftCode
        newAssignmentCode newAssignmentStep htraversal hrootBelow
        (proj2 (proj2 hex))).
    + right. right. right. right. right. right.
      exists leftCode. exact hall.
  - exfalso. apply (raw_zero_neq_truthOne M hPA). exact hmodes.
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_successor_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
      code assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M (S lower)
    code assignmentCode assignmentStep ->
  RawFixedLevelPiSuccessorRootView M lower
    code assignmentCode assignmentStep.
Proof.
  intros M hPA lower code assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal).
  pose proof htraversal as hparts.
  destruct hparts as [_ [_ [_ [_ [hrootBelow _]]]]].
  pose proof (raw_fixedLevelSuccessorTruthTraversal_root_row M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex (rawFixedLevelPiMode M)
    code assignmentCode assignmentStep htraversal) as hrow.
  destruct hrow as [[hmodes _] | [_ hpi]].
  - exfalso. apply (raw_zero_neq_truthOne M hPA). symmetry. exact hmodes.
  - destruct hpi as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare &
       [_ hcases]).
    destruct hcases as
      [hzero | [himp | [hand | [hor | [hall | hex]]]]].
    + now left.
    + right. left.
      exists leftCode, rightCode. split; [exact (proj1 himp) |]. split.
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_sigma M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex leftIndex leftCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj1 (proj2 himp))).
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex rightIndex rightCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj1 (proj2 (proj2 himp)))).
    + right. right. left.
      exists leftCode, rightCode. split; [exact (proj1 hand) |].
      destruct (proj2 hand) as [hleft | hright].
      * left. exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex leftIndex leftCode
          assignmentCode assignmentStep htraversal hrootBelow hleft).
      * right. exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex rightIndex rightCode
          assignmentCode assignmentStep htraversal hrootBelow hright).
    + right. right. right. left.
      exists leftCode, rightCode. split; [exact (proj1 hor) |]. split.
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex leftIndex leftCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj1 (proj2 hor))).
      * exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M) code
          assignmentCode assignmentStep rootIndex rightIndex rightCode
          assignmentCode assignmentStep htraversal hrootBelow
          (proj2 (proj2 hor))).
    + right. right. right. right. left.
      exists leftCode, witness, newAssignmentCode, newAssignmentStep.
      split; [exact (proj1 hall) |]. split; [exact (proj1 (proj2 hall)) |].
      exact (raw_fixedLevelSuccessorTruthTraversal_earlier_pi M hPA lower
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound rootIndex (rawFixedLevelPiMode M) code
        assignmentCode assignmentStep rootIndex leftIndex leftCode
        newAssignmentCode newAssignmentStep htraversal hrootBelow
        (proj2 (proj2 hall))).
    + right. right. right. right. right.
      exists leftCode. exact hex.
Qed.

End PABoundedRawCodedFixedLevelTruthElimination.
