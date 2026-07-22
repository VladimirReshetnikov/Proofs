(**
  Soundness of existential elimination under a shifted eigenvariable context.

  The existential truth certificate supplies a witness together with a
  beta-coded assignment that is only guaranteed through the existential
  formula.  The recursive proof, however, needs an assignment through the
  proof-wide coverage bound.  We construct a second prepend with the same
  head, use assignment locality on the body formula, shift the ambient
  context under that wide assignment, and finally transport the shifted
  recursive conclusion back to the unshifted goal.
*)

From Stdlib Require Import List Arith Lia Classical.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaOperations
  RawCodedContextLists RawCodedContextStructure RawCodedContextFunctionality
  RawCodedContextShift
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

Module PABoundedRawCodedRestrictedProofExERuleSoundness.

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
Import PABoundedRawCodedContextFunctionality.
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

(** Removing a visible assumption preserves proof-formula coverage whenever
    the tail has an honest model-internal traversal.  Reusing that traversal
    is important here: no decoding of a possibly nonstandard context code is
    involved. *)
Lemma raw_exE_contextAllCodesBelow_cons_tail : forall
    (M : RawPAModel), RawPASatisfies M -> forall head tail coverageBound,
  RawContextListRealizable M tail ->
  RawContextAllCodesBelow M
    (rawListNode M head tail) coverageBound ->
  RawContextAllCodesBelow M tail coverageBound.
Proof.
  intros M hPA head tail coverageBound
    (bound & tailCode & tailStep & headCode & headStep & htraversal)
    hall.
  exists bound, tailCode, tailStep, headCode, headStep.
  split; [exact htraversal |].
  intros index hindex code hlookup.
  apply (raw_contextAllCodesBelow_member M hPA
    (rawListNode M head tail) coverageBound code hall).
  apply (raw_contextList_cons_tail_member M hPA tail head code).
  exists bound, tailCode, tailStep, headCode, headStep.
  split; [exact htraversal |].
  exists index. now split.
Qed.

(** The selected Ex-E constructor is sound at every externally fixed truth
    level and in every (possibly nonstandard) model of PA. *)
Theorem raw_restrictedProofCovered_exE_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExERuleValidCase M).
Proof.
  intros M hPA level
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as
    [hcode [hconclusion [hchild3 [hchild1Endpoint
      [hcontextShift [hgoalShift hchild2Endpoint]]]]]].
  subst conclusion. subst child3.
  assert (hconstructor : RawProofConstructorCode M root
      context a b c t child1 child2 (rawFormulaExCode M a)).
  { unfold RawProofConstructorCode. tauto. }
  assert (hentry : In
      ([rawNumeralValue M 14; context; a; b; child1; child2],
       [child1; child2])
      (rawProofRecursiveCases M context a b c t
        child1 child2 (rawFormulaExCode M a))).
  { solve_raw_special_constructor_membership. }

  (** Root resources supply the unshifted ambient context and the final
      goal's coverage fact. *)
  pose proof (raw_proofEndpoint_exE_case M root context a b c t
    child1 child2 (rawFormulaExCode M a) hcode) as hrootEndpoint.
  destruct (raw_restrictedProofCovered_endpoint_context_data M hPA
    level root coverageBound context b
    hrestricted hatomic hcoverage hrootEndpoint) as
    [hsourceContextBounded
      [hsourceContextAtomic
        [hsourceContextCoverage hgoalBelowCoverage]]].

  (** The first child provides the existential formula; the second provides
      coverage of [a :: shiftedContext] and of the shifted goal. *)
  destruct
    (raw_restrictedProofCovered_recursive_child_endpoint_context_data
      M hPA level root coverageBound
      hrestricted hatomic hcoverage
      context a b c t child1 child2 (rawFormulaExCode M a) hconstructor
      [rawNumeralValue M 14; context; a; b; child1; child2]
      [child1; child2] hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      context (rawFormulaExCode M a) hchild1Endpoint) as
    [_ [_ [_ hexBelowCoverage]]].
  destruct
    (raw_restrictedProofCovered_recursive_child_endpoint_context_data
      M hPA level root coverageBound
      hrestricted hatomic hcoverage
      context a b c t child1 child2 (rawFormulaExCode M a) hconstructor
      [rawNumeralValue M 14; context; a; b; child1; child2]
      [child1; child2] hentry hcode child2
      ltac:(solve_raw_special_constructor_membership)
      (rawListNode M a c) t hchild2Endpoint) as
    [_ [_ [hsecondContextCoverage hshiftedGoalBelowCoverage]]].
  pose proof (raw_contextShift_target_realizable M context c hcontextShift)
    as hshiftedContextRealizable.
  pose proof (raw_exE_contextAllCodesBelow_cons_tail M hPA
    a c coverageBound hshiftedContextRealizable hsecondContextCoverage)
    as hshiftedContextCoverage.

  (** Run the existential premise under the original assignment, then open
      its truth certificate to obtain the hidden witness assignment. *)
  pose proof
    (raw_restrictedProofCovered_recursive_child_endpoint_admissible
      M hPA level root coverageBound assignmentCode assignmentStep
      hrestricted hatomic hcoverage hdefined
      context a b c t child1 child2 (rawFormulaExCode M a) hconstructor
      [rawNumeralValue M 14; context; a; b; child1; child2]
      [child1; child2] hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      context (rawFormulaExCode M a) hchild1Endpoint) as hexAdmissible.
  pose proof (hrecursive
    context a b c t child1 child2 (rawFormulaExCode M a) hconstructor
    [rawNumeralValue M 14; context; a; b; child1; child2]
    [child1; child2] hentry hcode child1
    ltac:(solve_raw_special_constructor_membership)
    context (rawFormulaExCode M a) hchild1Endpoint
    assignmentCode assignmentStep hdefined hcontext) as hexSigma.
  destruct (raw_fixedLevelEx_sigma_witness M hPA level a
    assignmentCode assignmentStep hexAdmissible hexSigma) as
    (witness & hiddenCode & hiddenStep &
     hhiddenPrepend & hhiddenBodySigma).

  (** Construct the same witness prepend through the common proof-wide
      bound.  This is the assignment under which the second child runs. *)
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    assignmentCode assignmentStep witness coverageBound hdefined) as
    (coveredCode & coveredStep & hcoveredPrepend & _).
  pose proof (raw_codedAssignmentPrepend_target_definedThrough_bound M hPA
    assignmentCode assignmentStep witness coverageBound
    coveredCode coveredStep hdefined hcoveredPrepend) as hcoveredDefined.
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    assignmentCode assignmentStep witness (rawFormulaExCode M a)
    coverageBound coveredCode coveredStep
    hexBelowCoverage hcoveredPrepend) as hcoveredPrependEx.

  (** Both prepends make the body admissible.  Their beta codes may differ,
      so equality is deliberately replaced by prefix agreement and the
      represented assignment-invariance theorem. *)
  destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
    level a assignmentCode assignmentStep witness
    hiddenCode hiddenStep hexAdmissible hhiddenPrepend) as
    [hhiddenBodyAtomic [hhiddenBodyDefined hhiddenBodyDomain]].
  destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
    level a assignmentCode assignmentStep witness
    coveredCode coveredStep hexAdmissible hcoveredPrependEx) as
    [hcoveredBodyAtomic [hcoveredBodyDefined hcoveredBodyDomain]].
  assert (hhiddenBodyAdmissible : RawFixedLevelTruthAdmissible M level
      a hiddenCode hiddenStep).
  { exact (conj hhiddenBodyAtomic
      (conj hhiddenBodyDefined (or_introl hhiddenBodyDomain))). }
  assert (hcoveredBodyAdmissible : RawFixedLevelTruthAdmissible M level
      a coveredCode coveredStep).
  { exact (conj hcoveredBodyAtomic
      (conj hcoveredBodyDefined (or_introl hcoveredBodyDomain))). }
  assert (hbodyBelowEx : rawLt M a (rawFormulaExCode M a)).
  { exact (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 6) a). }
  assert (hbodyBelowCoverage : rawLt M a coverageBound).
  { exact (raw_assignment_lt_trans M hPA a
      (rawFormulaExCode M a) coverageBound
      hbodyBelowEx hexBelowCoverage). }
  pose proof (raw_codedAssignmentPrepends_agree_common_prefix M hPA
    assignmentCode assignmentStep witness a
    (rawFormulaExCode M a) coverageBound
    hiddenCode hiddenStep coveredCode coveredStep
    hbodyBelowEx hbodyBelowCoverage
    (proj1 (proj2 hexAdmissible)) hdefined
    hhiddenPrepend hcoveredPrepend) as hagreeBody.
  pose proof (raw_fixedLevelTruthCertificate_assignment_invariance
    M hPA level a hiddenCode hiddenStep coveredCode coveredStep
    hagreeBody hhiddenBodyAdmissible hcoveredBodyAdmissible)
    as hbodyTransport.
  pose proof (proj1 (proj1 hbodyTransport) hhiddenBodySigma)
    as hcoveredBodySigma.

  (** Shift the ambient context under the wide prepend, add the now-true
      existential body as its visible assumption, and invoke child two. *)
  pose proof (raw_eigenContextShift_sigma_true M hPA level
    context c coverageBound
    assignmentCode assignmentStep coveredCode coveredStep witness
    hcontextShift hsourceContextCoverage hshiftedContextCoverage
    hsourceContextAtomic hsourceContextBounded
    hdefined hcoveredPrepend hcontext) as hshiftedContextSigma.
  pose proof (raw_contextAllSigmaTrue_cons M hPA (S level)
    c a coveredCode coveredStep
    hshiftedContextSigma hcoveredBodySigma) as hsecondContextSigma.
  pose proof (hrecursive
    context a b c t child1 child2 (rawFormulaExCode M a) hconstructor
    [rawNumeralValue M 14; context; a; b; child1; child2]
    [child1; child2] hentry hcode child2
    ltac:(solve_raw_special_constructor_membership)
    (rawListNode M a c) t hchild2Endpoint
    coveredCode coveredStep hcoveredDefined hsecondContextSigma)
    as hshiftedGoalSigma.

  (** The concrete unit-shift Tarski theorem reverses the shifted goal [t]
      to the original conclusion [b] under the source assignment. *)
  exact (raw_fixedLevelSigmaTruthCertificate_unit_shift_back M hPA
    level b t coverageBound
    assignmentCode assignmentStep coveredCode coveredStep witness
    hgoalBelowCoverage hshiftedGoalBelowCoverage hgoalShift
    hdefined hcoveredPrepend hadmissible hshiftedGoalSigma).
Qed.

End PABoundedRawCodedRestrictedProofExERuleSoundness.
