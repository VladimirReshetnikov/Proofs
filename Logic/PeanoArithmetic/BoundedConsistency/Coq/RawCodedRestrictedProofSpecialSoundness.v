(**
  Constructor-local soundness for the quantified and equality rules.

  The propositional layer deliberately exposes these six rules through
  [RawProofSpecialRuleValidCases].  Four of them (All-E, Ex-I, Eq-Refl, and
  Eq-Elim) are local once formula substitution and term evaluation satisfy
  their represented Tarski laws.  All-I and Ex-E additionally run a proof
  under a binder while retaining a shifted ambient context; their exact
  proof-wide binder requirement is kept explicit below.

  Keeping that requirement named is important.  A quantified truth row only
  promises that its hidden assignment is a prepend through the quantified
  formula code.  An ambient context formula can have a larger code, so this
  finite promise cannot by itself justify shift transport for every context
  member merely from proof-wide *definedness*.  The two eigenvariable rules
  must therefore be supplied by a binder/context theorem whose contract is
  stated explicitly, rather than by silently extending the prepend bound.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedListInjectivity
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedAssignmentUniversalDefinedness
  RawCodedFormulaOperations
  RawCodedFormulaRankTraversal
  RawCodedContextShift
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedProofAdmissibility
  RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationCapacity
  RawCodedRankZeroTruthStep
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelContextTruth
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelEqualityLaws
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarski
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFixedLevelTruthOperationTarskiSubstitutionPositive
  RawCodedRestrictedProofCoveredSoundness
  RawCodedRestrictedProofPropositionalSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofSpecialSoundness.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentUniversalDefinedness.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationCapacity.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelEqualityLaws.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarski.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.
Import PABoundedRawCodedRestrictedProofPropositionalSoundness.

(** Equality of two finite raw list codes identifies their standard head
    tags, independently of the (model-internal) payload fields. *)
Lemma raw_proofPayload_listCode_tag : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftTag rightTag leftTail rightTail,
  rawListCode M (rawNumeralValue M leftTag :: leftTail) =
  rawListCode M (rawNumeralValue M rightTag :: rightTail) ->
  leftTag = rightTag.
Proof.
  intros M hPA leftTag rightTag leftTail rightTail hcode.
  pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  inversion hfields as [[htag]].
  exact (rawNumeralValue_injective M hPA _ _ htag).
Qed.

Ltac refute_raw_proof_payload_tag hPA hactual hexpected :=
  exfalso;
  let hcodes := fresh "hcodes" in
  pose proof (eq_trans (eq_sym hactual) hexpected) as hcodes;
  let htags := fresh "htags" in
  pose proof (raw_proofPayload_listCode_tag _ hPA _ _ _ _ hcodes)
    as htags;
  discriminate htags.

(** Exact constructor-payload projections.  The proof-wide certificate is a
    disjunction over all seventeen tags; raw-list and numeral injectivity
    make the advertised tag select the intended branch. *)
Lemma raw_proofPayload_allE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code context a b c t child1 child2 child3,
  code = rawListCode M
    [rawNumeralValue M 12; context; a; t; child1] ->
  RawProofConstructorPayloadAtomicallyAdequate M
    code context a b c t child1 child2 child3 ->
  RawCodedFormulaAtomicallyAdequate M a /\
  RawCodedTermUniversallyAdequate M t.
Proof.
  intros M hPA code context a b c t child1 child2 child3
    hcode hpayload.
  unfold RawProofConstructorPayloadAtomicallyAdequate in hpayload.
  destruct hpayload as
    [h | [h | [h | [h | [h | [h | [h | [h | [h | [h |
     [h | [h | [h | [h | [h | [h | h]]]]]]]]]]]]]]]].
  all: destruct h as [htag hdata].
  all: try (refute_raw_proof_payload_tag hPA htag hcode).
  exact hdata.
Qed.

Lemma raw_proofPayload_exI : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code context a b c t child1 child2 child3,
  code = rawListCode M
    [rawNumeralValue M 13; context; a; t; child1] ->
  RawProofConstructorPayloadAtomicallyAdequate M
    code context a b c t child1 child2 child3 ->
  RawCodedFormulaAtomicallyAdequate M a /\
  RawCodedTermUniversallyAdequate M t.
Proof.
  intros M hPA code context a b c t child1 child2 child3
    hcode hpayload.
  unfold RawProofConstructorPayloadAtomicallyAdequate in hpayload.
  destruct hpayload as
    [h | [h | [h | [h | [h | [h | [h | [h | [h | [h |
     [h | [h | [h | [h | [h | [h | h]]]]]]]]]]]]]]]].
  all: destruct h as [htag hdata].
  all: try (refute_raw_proof_payload_tag hPA htag hcode).
  exact hdata.
Qed.

Lemma raw_proofPayload_eqRefl : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code context a b c t child1 child2 child3,
  code = rawListCode M [rawNumeralValue M 15; context; t] ->
  RawProofConstructorPayloadAtomicallyAdequate M
    code context a b c t child1 child2 child3 ->
  RawCodedTermUniversallyAdequate M t.
Proof.
  intros M hPA code context a b c t child1 child2 child3
    hcode hpayload.
  unfold RawProofConstructorPayloadAtomicallyAdequate in hpayload.
  destruct hpayload as
    [h | [h | [h | [h | [h | [h | [h | [h | [h | [h |
     [h | [h | [h | [h | [h | [h | h]]]]]]]]]]]]]]]].
  all: destruct h as [htag hdata].
  all: try (refute_raw_proof_payload_tag hPA htag hcode).
  exact hdata.
Qed.

Lemma raw_proofPayload_eqElim : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code context a b c t child1 child2 child3,
  code = rawListCode M
    [rawNumeralValue M 16; context; a; b; c; child1; child2] ->
  RawProofConstructorPayloadAtomicallyAdequate M
    code context a b c t child1 child2 child3 ->
  RawCodedTermUniversallyAdequate M a /\
  RawCodedTermUniversallyAdequate M b /\
  RawCodedFormulaAtomicallyAdequate M c.
Proof.
  intros M hPA code context a b c t child1 child2 child3
    hcode hpayload.
  unfold RawProofConstructorPayloadAtomicallyAdequate in hpayload.
  destruct hpayload as
    [h | [h | [h | [h | [h | [h | [h | [h | [h | [h |
     [h | [h | [h | [h | [h | [h | h]]]]]]]]]]]]]]]].
  all: destruct h as [htag hdata].
  all: try (refute_raw_proof_payload_tag hPA htag hcode).
  exact hdata.
Qed.

(** Universal term adequacy can be consumed under any beta-coded assignment:
    the preceding total-definedness theorem supplies its assignment premise,
    and the capacity construction turns the syntax certificate into an
    evaluator certificate. *)
Lemma raw_termUniversallyAdequate_evaluation_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      termCode assignmentCode assignmentStep,
  RawCodedTermUniversallyAdequate M termCode ->
  exists value : M,
    RawTermEvaluationCertificate M termCode value
      assignmentCode assignmentStep.
Proof.
  intros M hPA termCode assignmentCode assignmentStep hadequate.
  specialize (hadequate assignmentCode assignmentStep
    (raw_codedAssignment_definedThrough_all M hPA
      assignmentCode assignmentStep (raw_succ M termCode))).
  destruct hadequate as
    (supportCode & supportStep & hsyntax).
  exact (raw_termEvaluationCertificate_exists_of_syntax M hPA
    termCode assignmentCode assignmentStep supportCode supportStep
    hsyntax).
Qed.

(** Pairwise rank agreement is symmetric even though its public definition
    is oriented from the operation source to its target. *)
Lemma raw_codedFormulaRankAgreement_sym : forall
    (M : RawPAModel) source target,
  RawCodedFormulaRankAgreement M source target ->
  RawCodedFormulaRankAgreement M target source.
Proof.
  intros M source target hagreement
    targetSigma targetPi sourceSigma sourcePi
    htargetRank hsourceRank.
  destruct (hagreement sourceSigma sourcePi targetSigma targetPi
    hsourceRank htargetRank) as [hsigma hpi].
  split; symmetry; assumption.
Qed.

(** Opening a positive Sigma equality row exposes evaluations of its two
    terms.  Since the Sigma output bit is one, the false-equality alternative
    is impossible. *)
Lemma raw_fixedLevelEq_sigma_evaluations_equal : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right
      assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S level)
    (rawFormulaEqCode M left right) assignmentCode assignmentStep ->
  exists leftValue rightValue : M,
    RawTermEvaluationCertificate M left leftValue
      assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M right rightValue
      assignmentCode assignmentStep /\
    leftValue = rightValue.
Proof.
  intros M hPA level left right assignmentCode assignmentStep hsigma.
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      level (rawShapeEq left right) assignmentCode assignmentStep hsigma)
    as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | himpossible]; [| contradiction].
  destruct (raw_rankZeroTruthCertificate_eq_view M hPA
    (rawFormulaEqCode M left right) (rawNumeralValue M 1)
    assignmentCode assignmentStep left right eq_refl hrankZero)
    as (leftValue & rightValue & hleft & hright & htruth).
  unfold RawEqualityTruth in htruth.
  destruct htruth as [[hvalues _] | [_ honeZero]].
  - exists leftValue, rightValue. repeat split; assumption.
  - exfalso. apply (raw_zero_neq_truthOne M hPA).
    symmetry. exact honeZero.
Qed.

(** The positive substitution theorem naturally runs one level above the
    admissibility schedule used to prepare its source and target.  This is
    the exact endpoint supplied by the represented operation-table proof. *)
Definition RawFixedLevelFormulaSubstitutionScheduledTarski
    (M : RawPAModel) : Prop :=
  forall inputLevel replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaSubstitutionTransportReady M inputLevel
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Arguments RawFixedLevelFormulaSubstitutionScheduledTarski M
  : clear implicits.

(** The two rules that retain a shifted ambient context are named separately
    so their stronger binder contract cannot be confused with the four local
    rules proved below. *)
Definition RawProofAllIRuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M
      [rawNumeralValue M 11; context; a; child1] /\
  conclusion = rawFormulaAllCode M a /\
  RawContextShift M context b /\
  RawProofEndpoint M child1 b a.

Definition RawProofAllERuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M
      [rawNumeralValue M 12; context; a; t; child1] /\
  RawCodedFormulaSingleSubstitution M t a conclusion /\
  b = rawFormulaAllCode M a /\
  RawProofEndpoint M child1 context b.

Definition RawProofExIRuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M
      [rawNumeralValue M 13; context; a; t; child1] /\
  conclusion = rawFormulaExCode M a /\
  RawCodedFormulaSingleSubstitution M t a b /\
  RawProofEndpoint M child1 context b.

Definition RawProofExERuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M
      [rawNumeralValue M 14; context; a; b; child1; child2] /\
  conclusion = b /\
  child3 = rawFormulaExCode M a /\
  RawProofEndpoint M child1 context child3 /\
  RawContextShift M context c /\
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) b t /\
  RawProofEndpoint M child2 (rawListNode M a c) t.

Definition RawProofEqReflRuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M [rawNumeralValue M 15; context; t] /\
  conclusion = rawFormulaEqCode M t t.

Definition RawProofEqElimRuleValidCase (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M
      [rawNumeralValue M 16; context; a; b; c; child1; child2] /\
  RawCodedFormulaSingleSubstitution M b c conclusion /\
  t = rawFormulaEqCode M a b /\
  RawProofEndpoint M child1 context t /\
  RawCodedFormulaSingleSubstitution M a c child3 /\
  RawProofEndpoint M child2 context child3.

Arguments RawProofAllIRuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.
Arguments RawProofAllERuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.
Arguments RawProofExIRuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.
Arguments RawProofExERuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.
Arguments RawProofEqReflRuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.
Arguments RawProofEqElimRuleValidCase
  M code context conclusion a b c t child1 child2 child3 : clear implicits.

Definition RawRestrictedProofCoveredSelectedSpecialCaseTruthSound
    (M : RawPAModel) (level : nat)
    (selectedCase : M -> M -> M -> M -> M -> M -> M -> M -> M -> M ->
      Prop) : Prop :=
  forall root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3,
    RawRestrictedProof M level root ->
    RawProofAtomicallyAdequate M root ->
    RawProofFormulaCoverage M root coverageBound ->
    RawProofRuleCoverage M root ->
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep coverageBound ->
    selectedCase root context conclusion a b c t child1 child2 child3 ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawRestrictedProofCoveredRecursiveChildrenSigmaSound M level
      root coverageBound assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofCoveredSelectedSpecialCaseTruthSound
  M level selectedCase : clear implicits.

Ltac solve_raw_special_constructor_membership :=
  cbn [rawProofRecursiveCases];
  repeat first [left; reflexivity | right].

(** Universal elimination. *)
Lemma raw_restrictedProofCovered_allE_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  RawFixedLevelFormulaSubstitutionScheduledTarski M ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofAllERuleValidCase M).
Proof.
  intros M hPA level hrankPreserving hsubstitutionTarski
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as [hcode [hsubstitution [hb hchildEndpoint]]].
  subst b.
  assert (hconstructor : RawProofConstructorCode M root
      context a (rawFormulaAllCode M a) c t child1 child2 child3).
  { unfold RawProofConstructorCode. tauto. }
  assert (hentry : In
      ([rawNumeralValue M 12; context; a; t; child1], [child1])
      (rawProofRecursiveCases M context a (rawFormulaAllCode M a) c t
        child1 child2 child3)).
  { solve_raw_special_constructor_membership. }
  pose proof
    (raw_proofAtomicallyAdequate_root_constructor_payloads M hPA
      root hatomic context a (rawFormulaAllCode M a) c t
      child1 child2 child3 hconstructor) as hpayload.
  destruct (raw_proofPayload_allE M hPA root context a
    (rawFormulaAllCode M a) c t child1 child2 child3
    hcode hpayload) as [_ htermAdequate].
  destruct (raw_termUniversallyAdequate_evaluation_exists M hPA
    t assignmentCode assignmentStep htermAdequate)
    as [witness htermEvaluation].
  pose proof
    (raw_restrictedProofCovered_recursive_child_endpoint_admissible
      M hPA level root coverageBound assignmentCode assignmentStep
      hrestricted hatomic hcoverage hdefined
      context a (rawFormulaAllCode M a) c t child1 child2 child3
      hconstructor
      [rawNumeralValue M 12; context; a; t; child1] [child1]
      hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      context (rawFormulaAllCode M a) hchildEndpoint)
    as hallAdmissible.
  pose proof (hrecursive
    context a (rawFormulaAllCode M a) c t child1 child2 child3
    hconstructor
    [rawNumeralValue M 12; context; a; t; child1] [child1]
    hentry hcode child1 ltac:(solve_raw_special_constructor_membership)
    context (rawFormulaAllCode M a) hchildEndpoint
    assignmentCode assignmentStep hdefined hcontext) as hallSigma.
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    assignmentCode assignmentStep witness (rawFormulaAllCode M a)
    (proj1 (proj2 hallAdmissible)))
    as (binderAssignmentCode & binderAssignmentStep &
        hprepend & _).
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    assignmentCode assignmentStep witness a (rawFormulaAllCode M a)
    binderAssignmentCode binderAssignmentStep
    (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 5) a) hprepend) as hprependBody.
  pose proof (raw_fixedLevelAll_sigma_instantiate M hPA level a
    assignmentCode assignmentStep witness
    binderAssignmentCode binderAssignmentStep
    hallAdmissible hallSigma hprepend) as hbodySigma.
  destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
    level a assignmentCode assignmentStep witness
    binderAssignmentCode binderAssignmentStep hallAdmissible hprepend)
    as [hbodyAtomic [hbodyDefined hbodyDomain]].
  assert (hbodyAdmissible : RawFixedLevelTruthAdmissible M level a
      binderAssignmentCode binderAssignmentStep).
  { exact (conj hbodyAtomic
      (conj hbodyDefined (or_intror hbodyDomain))). }
  assert (htargetData : RawCodedFormulaTargetAdmissibilityData M
      conclusion assignmentCode assignmentStep).
  { exact (conj (proj1 hadmissible) (proj1 (proj2 hadmissible))). }
  assert (hassignmentRelation :
      RawCodedFormulaSubstitutionAssignmentRelation M t a
        binderAssignmentCode binderAssignmentStep
        assignmentCode assignmentStep).
  { exists witness. split; assumption. }
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
      M hrankPreserving level t a conclusion
      binderAssignmentCode binderAssignmentStep
      assignmentCode assignmentStep hsubstitution hassignmentRelation
      hbodyAdmissible htargetData) as hready.
  pose proof (hsubstitutionTarski level t a conclusion
    binderAssignmentCode binderAssignmentStep
    assignmentCode assignmentStep hready) as htransport.
  exact (proj1 (proj1 htransport) hbodySigma).
Qed.

(** Existential introduction. *)
Lemma raw_restrictedProofCovered_exI_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  RawFixedLevelFormulaSubstitutionScheduledTarski M ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExIRuleValidCase M).
Proof.
  intros M hPA level hrankPreserving hsubstitutionTarski
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as [hcode [hconclusion [hsubstitution hchildEndpoint]]].
  subst conclusion.
  assert (hconstructor : RawProofConstructorCode M root
      context a b c t child1 child2 child3).
  { unfold RawProofConstructorCode. tauto. }
  assert (hentry : In
      ([rawNumeralValue M 13; context; a; t; child1], [child1])
      (rawProofRecursiveCases M context a b c t
        child1 child2 child3)).
  { solve_raw_special_constructor_membership. }
  pose proof
    (raw_proofAtomicallyAdequate_root_constructor_payloads M hPA
      root hatomic context a b c t child1 child2 child3 hconstructor)
    as hpayload.
  destruct (raw_proofPayload_exI M hPA root context a b c t
    child1 child2 child3 hcode hpayload) as [_ htermAdequate].
  destruct (raw_termUniversallyAdequate_evaluation_exists M hPA
    t assignmentCode assignmentStep htermAdequate)
    as [witness htermEvaluation].
  pose proof
    (raw_restrictedProofCovered_recursive_child_endpoint_admissible
      M hPA level root coverageBound assignmentCode assignmentStep
      hrestricted hatomic hcoverage hdefined
      context a b c t child1 child2 child3 hconstructor
      [rawNumeralValue M 13; context; a; t; child1] [child1]
      hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      context b hchildEndpoint) as hchildAdmissible.
  pose proof (hrecursive context a b c t child1 child2 child3
    hconstructor
    [rawNumeralValue M 13; context; a; t; child1] [child1]
    hentry hcode child1 ltac:(solve_raw_special_constructor_membership)
    context b hchildEndpoint assignmentCode assignmentStep
    hdefined hcontext) as hchildSigma.
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    assignmentCode assignmentStep witness (rawFormulaExCode M a)
    (proj1 (proj2 hadmissible)))
    as (binderAssignmentCode & binderAssignmentStep &
        hprepend & _).
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    assignmentCode assignmentStep witness a (rawFormulaExCode M a)
    binderAssignmentCode binderAssignmentStep
    (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 6) a) hprepend) as hprependBody.
  destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
    level a assignmentCode assignmentStep witness
    binderAssignmentCode binderAssignmentStep hadmissible hprepend)
    as [hbodyAtomic [hbodyDefined hbodyDomain]].
  assert (hbodyAdmissible : RawFixedLevelTruthAdmissible M level a
      binderAssignmentCode binderAssignmentStep).
  { exact (conj hbodyAtomic
      (conj hbodyDefined (or_introl hbodyDomain))). }
  assert (htargetData : RawCodedFormulaTargetAdmissibilityData M
      b assignmentCode assignmentStep).
  { exact (conj (proj1 hchildAdmissible)
      (proj1 (proj2 hchildAdmissible))). }
  assert (hassignmentRelation :
      RawCodedFormulaSubstitutionAssignmentRelation M t a
        binderAssignmentCode binderAssignmentStep
        assignmentCode assignmentStep).
  { exists witness. split; assumption. }
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
      M hrankPreserving level t a b
      binderAssignmentCode binderAssignmentStep
      assignmentCode assignmentStep hsubstitution hassignmentRelation
      hbodyAdmissible htargetData) as hready.
  pose proof (hsubstitutionTarski level t a b
    binderAssignmentCode binderAssignmentStep
    assignmentCode assignmentStep hready) as htransport.
  assert (hbodySigma : RawFixedLevelSigmaTruthCertificate M (S level)
      a binderAssignmentCode binderAssignmentStep).
  { exact (proj2 (proj1 htransport) hchildSigma). }
  apply (proj2 (raw_fixedLevelEx_sigma_iff M hPA level a
    assignmentCode assignmentStep hadmissible)).
  exists witness, binderAssignmentCode, binderAssignmentStep.
  split; assumption.
Qed.

(** Equality reflexivity needs no recursive premise and is already an
    unconditional fixed-level law on the admissible equality domain. *)
Lemma raw_restrictedProofCovered_eqRefl_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofEqReflRuleValidCase M).
Proof.
  intros M hPA level
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as [_ hconclusion]. subst conclusion.
  exact (raw_fixedLevelEq_refl_sigma M hPA level t
    assignmentCode assignmentStep hadmissible).
Qed.

(** Equality elimination.  A true equality row supplies evaluations of both
    replacement terms with the same value.  One represented prepend can
    therefore serve both substitution traces: first open the schema using
    the left term, then close it using the right term. *)
Lemma raw_restrictedProofCovered_eqElim_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  RawFixedLevelFormulaSubstitutionScheduledTarski M ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofEqElimRuleValidCase M).
Proof.
  intros M hPA level hrankPreserving hsubstitutionTarski
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as
    [hcode [hsubstitutionRight [ht
      [hequalityEndpoint [hsubstitutionLeft hschemaEndpoint]]]]].
  subst t.
  assert (hconstructor : RawProofConstructorCode M root
      context a b c (rawFormulaEqCode M a b)
      child1 child2 child3).
  { unfold RawProofConstructorCode. tauto. }
  assert (hentry : In
      ([rawNumeralValue M 16; context; a; b; c; child1; child2],
       [child1; child2])
      (rawProofRecursiveCases M context a b c
        (rawFormulaEqCode M a b) child1 child2 child3)).
  { solve_raw_special_constructor_membership. }
  pose proof
    (raw_proofAtomicallyAdequate_root_constructor_payloads M hPA
      root hatomic context a b c (rawFormulaEqCode M a b)
      child1 child2 child3 hconstructor) as hpayload.
  destruct (raw_proofPayload_eqElim M hPA root context a b c
    (rawFormulaEqCode M a b) child1 child2 child3 hcode hpayload)
    as [_ [_ hschemaAtomic]].
  pose proof
    (raw_restrictedProofCovered_recursive_child_endpoint_admissible
      M hPA level root coverageBound assignmentCode assignmentStep
      hrestricted hatomic hcoverage hdefined
      context a b c (rawFormulaEqCode M a b) child1 child2 child3
      hconstructor
      [rawNumeralValue M 16; context; a; b; c; child1; child2]
      [child1; child2] hentry hcode child1
      ltac:(solve_raw_special_constructor_membership)
      context (rawFormulaEqCode M a b) hequalityEndpoint)
    as hequalityAdmissible.
  pose proof
    (raw_restrictedProofCovered_recursive_child_endpoint_admissible
      M hPA level root coverageBound assignmentCode assignmentStep
      hrestricted hatomic hcoverage hdefined
      context a b c (rawFormulaEqCode M a b) child1 child2 child3
      hconstructor
      [rawNumeralValue M 16; context; a; b; c; child1; child2]
      [child1; child2] hentry hcode child2
      ltac:(solve_raw_special_constructor_membership)
      context child3 hschemaEndpoint) as hschemaAdmissible.
  pose proof (hrecursive context a b c (rawFormulaEqCode M a b)
    child1 child2 child3 hconstructor
    [rawNumeralValue M 16; context; a; b; c; child1; child2]
    [child1; child2] hentry hcode child1
    ltac:(solve_raw_special_constructor_membership)
    context (rawFormulaEqCode M a b) hequalityEndpoint
    assignmentCode assignmentStep hdefined hcontext) as hequalitySigma.
  pose proof (hrecursive context a b c (rawFormulaEqCode M a b)
    child1 child2 child3 hconstructor
    [rawNumeralValue M 16; context; a; b; c; child1; child2]
    [child1; child2] hentry hcode child2
    ltac:(solve_raw_special_constructor_membership)
    context child3 hschemaEndpoint
    assignmentCode assignmentStep hdefined hcontext) as hschemaSigma.
  destruct (raw_fixedLevelEq_sigma_evaluations_equal M hPA level a b
    assignmentCode assignmentStep hequalitySigma)
    as (leftValue & rightValue & hleftEvaluation &
        hrightEvaluation & hvalues).
  subst rightValue.
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    assignmentCode assignmentStep leftValue c
    (raw_codedAssignment_definedThrough_all M hPA
      assignmentCode assignmentStep c))
    as (binderAssignmentCode & binderAssignmentStep &
        hprepend & _).
  pose proof (raw_codedFormulaSingleSubstitution_rankAgreement M
    hrankPreserving a c child3 hsubstitutionLeft) as hagreementLeft.
  assert (hschemaData : RawCodedFormulaTargetAdmissibilityData M c
      binderAssignmentCode binderAssignmentStep).
  { split; [exact hschemaAtomic |].
    exact (raw_codedAssignment_definedThrough_all M hPA
      binderAssignmentCode binderAssignmentStep c). }
  assert (hschemaBinderAdmissible : RawFixedLevelTruthAdmissible M level c
      binderAssignmentCode binderAssignmentStep).
  { exact (raw_fixedLevelTruthAdmissible_transport_of_rankAgreement
      M hPA level child3 c assignmentCode assignmentStep
      binderAssignmentCode binderAssignmentStep
      (raw_codedFormulaRankAgreement_sym M c child3 hagreementLeft)
      hschemaAdmissible hschemaData). }
  assert (hchildTargetData : RawCodedFormulaTargetAdmissibilityData M
      child3 assignmentCode assignmentStep).
  { exact (conj (proj1 hschemaAdmissible)
      (proj1 (proj2 hschemaAdmissible))). }
  assert (hleftAssignmentRelation :
      RawCodedFormulaSubstitutionAssignmentRelation M a c
        binderAssignmentCode binderAssignmentStep
        assignmentCode assignmentStep).
  { exists leftValue. split; assumption. }
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
      M hrankPreserving level a c child3
      binderAssignmentCode binderAssignmentStep
      assignmentCode assignmentStep hsubstitutionLeft
      hleftAssignmentRelation hschemaBinderAdmissible hchildTargetData)
    as hleftReady.
  pose proof (hsubstitutionTarski level a c child3
    binderAssignmentCode binderAssignmentStep
    assignmentCode assignmentStep hleftReady) as hleftTransport.
  assert (hschemaBinderSigma :
      RawFixedLevelSigmaTruthCertificate M (S level) c
        binderAssignmentCode binderAssignmentStep).
  { exact (proj2 (proj1 hleftTransport) hschemaSigma). }
  assert (hgoalTargetData : RawCodedFormulaTargetAdmissibilityData M
      conclusion assignmentCode assignmentStep).
  { exact (conj (proj1 hadmissible) (proj1 (proj2 hadmissible))). }
  assert (hrightAssignmentRelation :
      RawCodedFormulaSubstitutionAssignmentRelation M b c
        binderAssignmentCode binderAssignmentStep
        assignmentCode assignmentStep).
  { exists leftValue. split; assumption. }
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
      M hrankPreserving level b c conclusion
      binderAssignmentCode binderAssignmentStep
      assignmentCode assignmentStep hsubstitutionRight
      hrightAssignmentRelation hschemaBinderAdmissible hgoalTargetData)
    as hrightReady.
  pose proof (hsubstitutionTarski level b c conclusion
    binderAssignmentCode binderAssignmentStep
    assignmentCode assignmentStep hrightReady) as hrightTransport.
  exact (proj1 (proj1 hrightTransport) hschemaBinderSigma).
Qed.

(** Assemble all six special tags.  Only the two eigenvariable rules retain
    explicit hypotheses; the other four are discharged above from the
    represented substitution theorem and pairwise rank preservation. *)
Theorem raw_restrictedProofCovered_specialRuleTruthSound_of_eigen : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  RawFixedLevelFormulaSubstitutionScheduledTarski M ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofAllIRuleValidCase M) ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExERuleValidCase M) ->
  RawRestrictedProofCoveredSpecialRuleTruthSound M level.
Proof.
  intros M hPA level hrankPreserving hsubstitutionTarski
    hallISound hexESound
    root coverageBound context conclusion assignmentCode assignmentStep
    a b c t child1 child2 child3
    hrestricted hatomic hcoverage hruleCoverage hdefined hcase
    hadmissible hcontext hrecursive.
  destruct hcase as
    [hallI | [hallE | [hexI | [hexE | [heqRefl | heqElim]]]]].
  - exact (hallISound root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined hallI
      hadmissible hcontext hrecursive).
  - exact ((raw_restrictedProofCovered_allE_sound M hPA level
      hrankPreserving hsubstitutionTarski)
      root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined hallE
      hadmissible hcontext hrecursive).
  - exact ((raw_restrictedProofCovered_exI_sound M hPA level
      hrankPreserving hsubstitutionTarski)
      root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined hexI
      hadmissible hcontext hrecursive).
  - exact (hexESound root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined hexE
      hadmissible hcontext hrecursive).
  - exact ((raw_restrictedProofCovered_eqRefl_sound M hPA level)
      root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined heqRefl
      hadmissible hcontext hrecursive).
  - exact ((raw_restrictedProofCovered_eqElim_sound M hPA level
      hrankPreserving hsubstitutionTarski)
      root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined heqElim
      hadmissible hcontext hrecursive).
Qed.

(** Public checkpoint using the now-proved scheduled substitution endpoint.
    Concrete arbitrary-model rank preservation and the two binder/context
    rules remain explicit, genuine obligations. *)
Corollary
    raw_restrictedProofCovered_specialRuleTruthSound_of_rank_and_eigen :
  forall (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofAllIRuleValidCase M) ->
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExERuleValidCase M) ->
  RawRestrictedProofCoveredSpecialRuleTruthSound M level.
Proof.
  intros M hPA level hrankPreserving hallISound hexESound.
  apply (raw_restrictedProofCovered_specialRuleTruthSound_of_eigen
    M hPA level hrankPreserving).
  - exact (raw_fixedLevelFormulaSingleSubstitutionTarskiStep_scheduled
      M hPA).
  - exact hallISound.
  - exact hexESound.
Qed.

End PABoundedRawCodedRestrictedProofSpecialSoundness.
