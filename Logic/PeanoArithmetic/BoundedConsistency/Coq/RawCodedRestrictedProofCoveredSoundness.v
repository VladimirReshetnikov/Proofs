(**
  Nonstandard restricted-proof soundness with a proof-wide formula bound.

  A truth assignment used at a proof node must remain available throughout
  each premise derivation.  [RawProofFormulaCoverage] supplies one numeric
  carrier bound above every formula code in the supported proof, while the
  current beta assignment is required to be defined through that bound.
  This condition is stable under ordinary recursive descent and can be
  preserved by binder extension.

  The only remaining semantic seam is constructor-local rule soundness.
  Its recursive-premise callback no longer asks callers to postulate child
  admissibility: restricted rank, atomic adequacy, formula coverage, and
  assignment coverage derive it uniformly.  The prefix induction below is
  represented by a PA formula, so PA's induction applies through arbitrary
  nonstandard proof-code bounds.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedRestrictedProofTraversal RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage RawCodedProofRuleCoverage
  RawCodedRestrictedProofAdmissibility
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelContextTruth RawCodedRestrictedProofSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofCoveredSoundness.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedRestrictedProofSoundness.

(** ------------------------------------------------------------------
    Constructor-local interface. *)

Definition RawRestrictedProofCoveredRecursiveChildrenSigmaSound
    (M : RawPAModel) (level : nat)
    (root coverageBound assignmentCode assignmentStep : M) : Prop :=
  forall nodeContext a b c t child1 child2 child3,
    RawProofConstructorCode M
      root nodeContext a b c t child1 child2 child3 ->
  forall fields children,
    In (fields, children)
      (rawProofRecursiveCases M
        nodeContext a b c t child1 child2 child3) ->
    root = rawListCode M fields ->
  forall child,
    In child children ->
  forall childContext childConclusion,
    RawProofEndpoint M child childContext childConclusion ->
    RawContextAllSigmaTrue M (S level)
      childContext assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      childConclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofCoveredRecursiveChildrenSigmaSound
  M level root coverageBound assignmentCode assignmentStep
  : clear implicits.

(** The local theorem receives every structural resource explicitly.  The
    conclusion admissibility premise is redundant from those resources, but
    exposing it keeps constructor proofs focused on Tarski laws. *)
Definition RawRestrictedProofCoveredRuleTruthSound
    (M : RawPAModel) (level : nat) : Prop :=
  forall root coverageBound context conclusion assignmentCode assignmentStep,
    RawRestrictedProof M level root ->
    RawProofAtomicallyAdequate M root ->
    RawProofFormulaCoverage M root coverageBound ->
    RawProofRuleCoverage M root ->
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep coverageBound ->
    RawProofRuleValid M root context conclusion ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawRestrictedProofCoveredRecursiveChildrenSigmaSound M level
      root coverageBound assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofCoveredRuleTruthSound M level : clear implicits.

(** ------------------------------------------------------------------
    Represented prefix invariant. *)

Lemma raw_coveredSoundness_eval_liftTerm_six : forall
    (M : RawPAModel) a b c d f g (e : nat -> M) termCode,
  raw_term_eval M
    (scons M a (scons M b (scons M c
      (scons M d (scons M f (scons M g e))))))
    (liftTerm 6 termCode) = raw_term_eval M e termCode.
Proof.
  intros M a b c d f g e termCode. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 6) with (S (S (S (S (S (S index)))))) by lia.
  reflexivity.
Qed.

(** Binder order: proof, coverage bound, context, conclusion, assignment
    code, assignment step. *)
Definition coveredSoundnessAll6 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll body))))).

Definition coveredSoundnessImp7
    (a b c d f g h conclusion : formula) : formula :=
  pImp a (pImp b (pImp c (pImp d (pImp f (pImp g (pImp h conclusion)))))).

Definition coveredSoundnessImp8
    (a b c d f g h i conclusion : formula) : formula :=
  pImp a
    (pImp b
      (pImp c
        (pImp d
          (pImp f
            (pImp g (pImp h (pImp i conclusion))))))).

Definition restrictedProofCoveredSigmaSoundBelowTermAt
    (level : nat) (current : term) : formula :=
  coveredSoundnessAll6
    (coveredSoundnessImp8
      (Formula.ltTermAt (tVar 5) (liftTerm 6 current))
      (restrictedProofTermAt level (tVar 5))
      (proofAtomicallyAdequateTermAt (tVar 5))
      (proofFormulaCoverageTermAt (tVar 5) (tVar 4))
      (proofRuleCoverageTermAt (tVar 5))
      (codedAssignmentDefinedThroughTermAt
        (tVar 1) (tVar 0) (tVar 4))
      (proofRuleValidTermAt (tVar 5) (tVar 3) (tVar 2))
      (contextAllSigmaTrueTermAt (S level)
        (tVar 3) (tVar 1) (tVar 0))
      (fixedLevelSigmaTruthCertificateTermAt (S level)
        (tVar 2) (tVar 1) (tVar 0))).

Definition RawRestrictedProofCoveredSigmaSoundBelow
    (M : RawPAModel) (level : nat) (current : M) : Prop :=
  forall proof coverageBound context conclusion
      assignmentCode assignmentStep,
    rawLt M proof current ->
    RawRestrictedProof M level proof ->
    RawProofAtomicallyAdequate M proof ->
    RawProofFormulaCoverage M proof coverageBound ->
    RawProofRuleCoverage M proof ->
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep coverageBound ->
    RawProofRuleValid M proof context conclusion ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofCoveredSigmaSoundBelow M level current
  : clear implicits.

Lemma raw_sat_restrictedProofCoveredSigmaSoundBelowTermAt_iff : forall
    (M : RawPAModel) e level current,
  raw_formula_sat M e
    (restrictedProofCoveredSigmaSoundBelowTermAt level current) <->
  RawRestrictedProofCoveredSigmaSoundBelow M level
    (raw_term_eval M e current).
Proof.
  intros M e level current.
  unfold restrictedProofCoveredSigmaSoundBelowTermAt,
    coveredSoundnessAll6, coveredSoundnessImp8,
    RawRestrictedProofCoveredSigmaSoundBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_proofFormulaCoverageTermAt_iff.
  setoid_rewrite raw_sat_proofRuleCoverageTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_contextAllSigmaTrueTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_coveredSoundness_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedProofCoveredSigmaSoundBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSigmaSoundBelow M level (raw_zero M).
Proof.
  intros M hPA level proof coverageBound context conclusion
    assignmentCode assignmentStep hproof.
  exfalso. exact (raw_not_lt_zero M hPA proof hproof).
Qed.

Theorem raw_restrictedProofCoveredSigmaSoundBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level ->
  forall current,
  RawRestrictedProofCoveredSigmaSoundBelow M level current ->
  RawRestrictedProofCoveredSigmaSoundBelow M level (raw_succ M current).
Proof.
  intros M hPA level hlocal current hbelow
    root coverageBound context conclusion assignmentCode assignmentStep
    hrootBelow hrestricted hatomic hcoverage hruleCoverage
    hdefined hvalid hcontext.
  destruct (raw_lt_succ_cases M hPA root current hrootBelow)
    as [hrootCurrent | hrootCurrent].
  - exact (hbelow root coverageBound context conclusion
      assignmentCode assignmentStep hrootCurrent hrestricted hatomic
      hcoverage hruleCoverage hdefined hvalid hcontext).
  - subst root.
    pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
      current coverageBound hcoverage context conclusion
      (raw_proofRuleValid_endpoint M current context conclusion hvalid))
      as [_ hconclusionBelow].
    assert (hconclusionDefined : RawCodedAssignmentDefinedThrough M
        assignmentCode assignmentStep conclusion).
    {
      exact (raw_codedAssignmentDefinedThrough_of_lt M hPA
        assignmentCode assignmentStep conclusion coverageBound
        hconclusionBelow hdefined).
    }
    pose proof (raw_restrictedProof_rule_endpoint_admissible M hPA
      level current hrestricted hatomic context conclusion hvalid
      assignmentCode assignmentStep hconclusionDefined) as hadmissible.
    apply (hlocal current coverageBound context conclusion
      assignmentCode assignmentStep hrestricted hatomic hcoverage
      hruleCoverage hdefined hvalid hadmissible hcontext).
    intros nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild
      childContext childConclusion hchildEndpoint hchildContext.
    destruct (raw_restrictedProofAtomicallyAdequate_recursive_child M hPA
      level current hrestricted hatomic
      nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild)
      as [hchildRestricted [hchildAtomic hchildBelow]].
    destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
      current coverageBound hcoverage
      nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild)
      as [hchildCoverage _].
    destruct (raw_proofRuleCoverage_public_recursive_child M hPA
      current hruleCoverage
      nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild)
      as [hchildRuleCoverage _].
    pose proof (raw_proofRuleCoverage_public_root_complete M hPA
      child hchildRuleCoverage childContext childConclusion
      hchildEndpoint) as hchildValid.
    exact (hbelow child coverageBound childContext childConclusion
      assignmentCode assignmentStep hchildBelow
      hchildRestricted hchildAtomic hchildCoverage hchildRuleCoverage hdefined
      hchildValid hchildContext).
Qed.

(** PA's definable induction reaches arbitrary nonstandard carrier bounds. *)
Theorem raw_restrictedProofCoveredSigmaSoundBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level ->
  forall current,
    RawRestrictedProofCoveredSigmaSoundBelow M level current.
Proof.
  intros M hPA level hlocal.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := restrictedProofCoveredSigmaSoundBelowTermAt
    level (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_restrictedProofCoveredSigmaSoundBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_restrictedProofCoveredSigmaSoundBelow_zero M hPA level).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_restrictedProofCoveredSigmaSoundBelowTermAt_iff M
          (scons M current parameterEnv) level (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_restrictedProofCoveredSigmaSoundBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_restrictedProofCoveredSigmaSoundBelow_succ M hPA
        level hlocal current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_restrictedProofCoveredSigmaSoundBelowTermAt_iff M
      (scons M current parameterEnv) level (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_restrictedProofCovered_root_sigma_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level ->
  forall root coverageBound context conclusion assignmentCode assignmentStep,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  RawProofRuleValid M root context conclusion ->
  RawContextAllSigmaTrue M (S level)
    context assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    conclusion assignmentCode assignmentStep.
Proof.
  intros M hPA level hlocal root coverageBound context conclusion
    assignmentCode assignmentStep hrestricted hatomic hcoverage
    hruleCoverage hdefined hvalid hcontext.
  exact (raw_restrictedProofCoveredSigmaSoundBelow_all M hPA level hlocal
    (raw_succ M root) root coverageBound context conclusion
    assignmentCode assignmentStep
    (raw_assignment_lt_self_succ M hPA root)
    hrestricted hatomic hcoverage hruleCoverage hdefined hvalid hcontext).
Qed.

Theorem raw_restrictedProofCovered_bottom_exclusion : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level ->
  RawFixedLevelSigmaBottomFalse M (S level) ->
  forall root coverageBound context assignmentCode assignmentStep,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  RawProofRuleValid M root context (rawFormulaBotCode M) ->
  RawContextAllSigmaTrue M (S level)
    context assignmentCode assignmentStep ->
  False.
Proof.
  intros M hPA level hlocal hbottom root coverageBound context
    assignmentCode assignmentStep hrestricted hatomic hcoverage
    hruleCoverage hdefined hvalid hcontext.
  apply (hbottom assignmentCode assignmentStep).
  exact (raw_restrictedProofCovered_root_sigma_sound M hPA level hlocal
    root coverageBound context (rawFormulaBotCode M)
    assignmentCode assignmentStep hrestricted hatomic hcoverage
    hruleCoverage hdefined hvalid hcontext).
Qed.

End PABoundedRawCodedRestrictedProofCoveredSoundness.
