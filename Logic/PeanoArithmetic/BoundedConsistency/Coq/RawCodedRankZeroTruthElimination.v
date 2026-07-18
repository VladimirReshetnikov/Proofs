(**
  Public Boolean views for rank-zero truth certificates.

  A rank-zero root certificate hides its support and truth beta tables.  The
  closed-step constructor views expose the child lookups, while the prefix
  restriction theorem turns those lookups back into independent child
  certificates.  These lemmas combine the two operations so higher-level
  truth elimination never needs to mention hidden tables.
*)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRankZeroTruthStep
  RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruthAdmissibleLowering.

Module PABoundedRawCodedRankZeroTruthElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.

Definition RawRankZeroImpCertificateView (M : RawPAModel)
    (output left right assignmentCode assignmentStep : M) : Prop :=
  exists leftOutput rightOutput : M,
    RawRankZeroTruthCertificate M left leftOutput
      assignmentCode assignmentStep /\
    RawRankZeroTruthCertificate M right rightOutput
      assignmentCode assignmentStep /\
    RawImpTruth M output leftOutput rightOutput.

Definition RawRankZeroAndCertificateView (M : RawPAModel)
    (output left right assignmentCode assignmentStep : M) : Prop :=
  exists leftOutput rightOutput : M,
    RawRankZeroTruthCertificate M left leftOutput
      assignmentCode assignmentStep /\
    RawRankZeroTruthCertificate M right rightOutput
      assignmentCode assignmentStep /\
    RawAndTruth M output leftOutput rightOutput.

Definition RawRankZeroOrCertificateView (M : RawPAModel)
    (output left right assignmentCode assignmentStep : M) : Prop :=
  exists leftOutput rightOutput : M,
    RawRankZeroTruthCertificate M left leftOutput
      assignmentCode assignmentStep /\
    RawRankZeroTruthCertificate M right rightOutput
      assignmentCode assignmentStep /\
    RawOrTruth M output leftOutput rightOutput.

Arguments RawRankZeroImpCertificateView
  M output left right assignmentCode assignmentStep : clear implicits.
Arguments RawRankZeroAndCertificateView
  M output left right assignmentCode assignmentStep : clear implicits.
Arguments RawRankZeroOrCertificateView
  M output left right assignmentCode assignmentStep : clear implicits.

Theorem raw_rankZeroTruthCertificate_imp_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code output assignmentCode assignmentStep left right,
  code = rawFormulaImpCode M left right ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep ->
  RawRankZeroImpCertificateView M output left right
    assignmentCode assignmentStep.
Proof.
  intros M hPA code output assignmentCode assignmentStep left right
    hcode (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof htables as htablesCopy.
  pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep htables) as hclosed.
  destruct (raw_rankZeroTruthClosedStep_imp_view M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right
    hcode hclosed) as
    (leftOutput & rightOutput & hleftLookup & hrightLookup & htruth &
     hleftSupport & hrightSupport & hleftLt & hrightLt).
  exists leftOutput, rightOutput. split.
  - exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
      code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep htablesCopy
      left leftOutput hleftLt hleftSupport hleftLookup (proj1 htruth)).
  - split.
    + exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
        code output assignmentCode assignmentStep
        truthCode truthStep supportCode supportStep htablesCopy
        right rightOutput hrightLt hrightSupport hrightLookup
        (proj1 (proj2 htruth))).
    + exact htruth.
Qed.

Theorem raw_rankZeroTruthCertificate_and_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code output assignmentCode assignmentStep left right,
  code = rawFormulaAndCode M left right ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep ->
  RawRankZeroAndCertificateView M output left right
    assignmentCode assignmentStep.
Proof.
  intros M hPA code output assignmentCode assignmentStep left right
    hcode (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof htables as htablesCopy.
  pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep htables) as hclosed.
  destruct (raw_rankZeroTruthClosedStep_and_view M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right
    hcode hclosed) as
    (leftOutput & rightOutput & hleftLookup & hrightLookup & htruth &
     hleftSupport & hrightSupport & hleftLt & hrightLt).
  exists leftOutput, rightOutput. split.
  - exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
      code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep htablesCopy
      left leftOutput hleftLt hleftSupport hleftLookup (proj1 htruth)).
  - split.
    + exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
        code output assignmentCode assignmentStep
        truthCode truthStep supportCode supportStep htablesCopy
        right rightOutput hrightLt hrightSupport hrightLookup
        (proj1 (proj2 htruth))).
    + exact htruth.
Qed.

Theorem raw_rankZeroTruthCertificate_or_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code output assignmentCode assignmentStep left right,
  code = rawFormulaOrCode M left right ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep ->
  RawRankZeroOrCertificateView M output left right
    assignmentCode assignmentStep.
Proof.
  intros M hPA code output assignmentCode assignmentStep left right
    hcode (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof htables as htablesCopy.
  pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep htables) as hclosed.
  destruct (raw_rankZeroTruthClosedStep_or_view M hPA
    code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right
    hcode hclosed) as
    (leftOutput & rightOutput & hleftLookup & hrightLookup & htruth &
     hleftSupport & hrightSupport & hleftLt & hrightLt).
  exists leftOutput, rightOutput. split.
  - exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
      code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep htablesCopy
      left leftOutput hleftLt hleftSupport hleftLookup (proj1 htruth)).
  - split.
    + exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
        code output assignmentCode assignmentStep
        truthCode truthStep supportCode supportStep htablesCopy
        right rightOutput hrightLt hrightSupport hrightLookup
        (proj1 (proj2 htruth))).
    + exact htruth.
Qed.

End PABoundedRawCodedRankZeroTruthElimination.
