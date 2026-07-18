(**
  The All-I and Ex-E eigenvariable cases, and the resulting unconditional
  six-special-rule soundness theorem.

  All proof-wide normalization and context-shift plumbing lives in the two
  preceding eigen helper modules.  This file contains only the constructor
  arguments themselves and the final assembly with All-E, Ex-I, and the two
  equality rules proved earlier.
*)

From Stdlib Require Import List Arith Lia Classical.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaOperations
  RawCodedContextLists RawCodedContextStructure RawCodedContextShift
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofEndpoints
  RawCodedProofAtomicAdequacy RawCodedProofFormulaCoverage
  RawCodedRestrictedProofTraversal RawCodedRestrictedProofAdmissibility
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthLaws RawCodedFixedLevelContextTruth
  RawCodedFixedLevelTruthAssignmentInvariance
  RawCodedFixedLevelTruthAssignmentInvariancePositive
  RawCodedRestrictedProofCoveredSoundness
  RawCodedRestrictedProofPropositionalSoundness
  RawCodedRestrictedProofSpecialSoundness
  RawCodedRestrictedProofEigenContextTruth
  RawCodedRestrictedProofEigenSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofEigenRuleSoundness.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelTruthAssignmentInvariance.
Import PABoundedRawCodedFixedLevelTruthAssignmentInvariancePositive.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.
Import PABoundedRawCodedRestrictedProofPropositionalSoundness.
Import PABoundedRawCodedRestrictedProofSpecialSoundness.
Import PABoundedRawCodedRestrictedProofEigenContextTruth.
Import PABoundedRawCodedRestrictedProofEigenSoundness.

(** Universal introduction.  The hidden prepend selected by the universal
    truth row is normalized only on the body formula; the recursive proof is
    deliberately run under a separate prepend covering the whole proof. *)
Lemma raw_restrictedProofCovered_allI_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofAllIRuleValidCase M).
Proof.
  intros M hPA level
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as [hcode [hconclusion [hshift hchildEndpoint]]].
  subst conclusion.
  assert (hconstructor : RawProofConstructorCode M root
      context a b c t child1 child2 child3).
  { unfold RawProofConstructorCode. tauto. }
  assert (hentry : In
      ([rawNumeralValue M 11; context; a; child1], [child1])
      (rawProofRecursiveCases M context a b c t
        child1 child2 child3)).
  { solve_raw_special_constructor_membership. }
  pose proof (raw_proofEndpoint_allI_case M root context a b c t
    child1 child2 child3 hcode) as hrootEndpoint.
  destruct (raw_restrictedProofCovered_endpoint_context_data M hPA
    level root coverageBound context (rawFormulaAllCode M a)
    hrestricted hatomic hcoverage hrootEndpoint) as
    [hsourceContextBounded
      [hsourceContextAtomic
        [hsourceContextCoverage hparentBelowCoverage]]].
  destruct
    (raw_restrictedProofCovered_recursive_child_endpoint_context_data
      M hPA level root coverageBound
      hrestricted hatomic hcoverage
      context a b c t child1 child2 child3 hconstructor
      [rawNumeralValue M 11; context; a; child1] [child1]
      hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      b a hchildEndpoint) as
    [htargetContextBounded
      [htargetContextAtomic
        [htargetContextCoverage hbodyBelowCoverage]]].
  apply (raw_fixedLevelAll_sigma_of_no_lower_pi M hPA level
    a assignmentCode assignmentStep).
  - exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
      level (rawFormulaAllCode M a)
      assignmentCode assignmentStep hadmissible)).
  - intros (witness & hiddenCode & hiddenStep &
      hhiddenPrepend & hhiddenLowerPi).
    destruct (raw_codedAssignmentPrepend_defined_exists M hPA
      assignmentCode assignmentStep witness coverageBound hdefined) as
      (coveredCode & coveredStep & hcoveredPrepend & _).
    pose proof (raw_codedAssignmentPrepend_target_definedThrough_bound M hPA
      assignmentCode assignmentStep witness coverageBound
      coveredCode coveredStep hdefined hcoveredPrepend) as hcoveredDefined.
    pose proof (raw_eigenContextShift_sigma_true M hPA level
      context b coverageBound
      assignmentCode assignmentStep coveredCode coveredStep witness
      hshift hsourceContextCoverage htargetContextCoverage
      hsourceContextAtomic hsourceContextBounded
      hdefined hcoveredPrepend hcontext) as hshiftedContext.
    pose proof (hrecursive
      context a b c t child1 child2 child3 hconstructor
      [rawNumeralValue M 11; context; a; child1] [child1]
      hentry hcode child1 ltac:(solve_raw_special_constructor_membership)
      b a hchildEndpoint coveredCode coveredStep
      hcoveredDefined hshiftedContext) as hcoveredBodySigma.
    pose proof
      (raw_restrictedProofCovered_recursive_child_endpoint_admissible
        M hPA level root coverageBound coveredCode coveredStep
        hrestricted hatomic hcoverage hcoveredDefined
        context a b c t child1 child2 child3 hconstructor
        [rawNumeralValue M 11; context; a; child1] [child1]
        hentry hcode child1
        ltac:(solve_raw_special_constructor_membership)
        b a hchildEndpoint) as hcoveredBodyAdmissible.
    destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      level a assignmentCode assignmentStep witness
      hiddenCode hiddenStep hadmissible hhiddenPrepend) as
      [hhiddenBodyAtomic [hhiddenBodyDefined hhiddenBodyDomain]].
    assert (hhiddenBodyAdmissible : RawFixedLevelTruthAdmissible M level
        a hiddenCode hiddenStep).
    { exact (conj hhiddenBodyAtomic
        (conj hhiddenBodyDefined (or_intror hhiddenBodyDomain))). }
    assert (hbodyBelowParent : rawLt M a (rawFormulaAllCode M a)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 5) a). }
    pose proof (raw_codedAssignmentPrepends_agree_common_prefix M hPA
      assignmentCode assignmentStep witness a
      coverageBound (rawFormulaAllCode M a)
      coveredCode coveredStep hiddenCode hiddenStep
      hbodyBelowCoverage hbodyBelowParent
      hdefined (proj1 (proj2 hadmissible))
      hcoveredPrepend hhiddenPrepend) as hagreeBody.
    pose proof (raw_fixedLevelTruthCertificate_assignment_invariance
      M hPA level a coveredCode coveredStep hiddenCode hiddenStep
      hagreeBody hcoveredBodyAdmissible hhiddenBodyAdmissible)
      as hbodyTransport.
    pose proof (proj1 (proj1 hbodyTransport) hcoveredBodySigma)
      as hhiddenBodySigma.
    pose proof
      (raw_fixedLevelAdmissibleTruthCertificateCoherence_all level M hPA)
      as hcoherence.
    destruct (hcoherence a hiddenCode hiddenStep hhiddenBodyAdmissible)
      as [_ hpiCoherence].
    pose proof (proj1 (hpiCoherence hhiddenBodyDomain) hhiddenLowerPi)
      as hhiddenUpperPi.
    exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
      level M hPA a hiddenCode hiddenStep hhiddenBodyAdmissible
      hhiddenBodySigma hhiddenUpperPi).
Qed.

End PABoundedRawCodedRestrictedProofEigenRuleSoundness.
