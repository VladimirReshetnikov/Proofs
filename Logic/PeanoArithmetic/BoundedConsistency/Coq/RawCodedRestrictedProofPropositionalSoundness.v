(**
  Constructor-local soundness for the propositional proof rules.

  The nonstandard proof induction supplies truth for genuine recursive
  children, but the Boolean Tarski eliminators also require admissibility of
  the formula displayed at an eliminating premise.  The helper below derives
  that admissibility from the same proof-wide restricted-rank, atomic-syntax,
  formula-coverage, and assignment-coverage certificates used by the global
  induction.  Thus no premise formula is silently assumed to be a standard
  code.

  The six quantifier/equality constructors are isolated by the exact
  [RawProofSpecialRuleValidCases] relation.  Any implementation of their
  local semantics can be plugged into the theorem at the end of this file;
  the first eleven constructors are discharged here without an additional
  hypothesis.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextShift
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedRestrictedProofTraversal
  RawCodedProofAtomicAdequacy
  RawCodedProofRuleCoverage
  RawCodedRestrictedProofAdmissibility
  RawCodedProofFormulaCoverage
  RawCodedFixedLevelContextTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelBottomLaws
  RawCodedRestrictedProofCoveredSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofPropositionalSoundness.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelBottomLaws.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.

(** Exactly the suffix of [RawProofRuleValidCases] consisting of All-I,
    All-E, Ex-I, Ex-E, equality reflexivity, and equality elimination.  It is
    deliberately not phrased as "not one of the propositional cases": every
    field equation and premise endpoint needed by a semantic implementation
    remains available. *)
Definition RawProofSpecialRuleValidCases (M : RawPAModel)
    (code context conclusion a b c t child1 child2 child3 : M) : Prop :=
  (code = rawListCode M
      [rawNumeralValue M 11; context; a; child1] /\
    conclusion = rawFormulaAllCode M a /\
    RawContextShift M context b /\
    RawProofEndpoint M child1 b a) \/
  (code = rawListCode M
      [rawNumeralValue M 12; context; a; t; child1] /\
    RawCodedFormulaSingleSubstitution M t a conclusion /\
    b = rawFormulaAllCode M a /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 13; context; a; t; child1] /\
    conclusion = rawFormulaExCode M a /\
    RawCodedFormulaSingleSubstitution M t a b /\
    RawProofEndpoint M child1 context b) \/
  (code = rawListCode M
      [rawNumeralValue M 14; context; a; b; child1; child2] /\
    conclusion = b /\
    child3 = rawFormulaExCode M a /\
    RawProofEndpoint M child1 context child3 /\
    RawContextShift M context c /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) b t /\
    RawProofEndpoint M child2 (rawListNode M a c) t) \/
  (code = rawListCode M [rawNumeralValue M 15; context; t] /\
    conclusion = rawFormulaEqCode M t t) \/
  (code = rawListCode M
      [rawNumeralValue M 16; context; a; b; c; child1; child2] /\
    RawCodedFormulaSingleSubstitution M b c conclusion /\
    t = rawFormulaEqCode M a b /\
    RawProofEndpoint M child1 context t /\
    RawCodedFormulaSingleSubstitution M a c child3 /\
    RawProofEndpoint M child2 context child3).

Arguments RawProofSpecialRuleValidCases
  M code context conclusion a b c t child1 child2 child3 : clear implicits.

(** The plug-in interface for the six rules whose proofs use formula shift,
    substitution, or term-evaluation Tarski transport.  All global resources
    are retained so the implementation can extend assignments through a
    proof-wide formula bound and then invoke recursive premise soundness. *)
Definition RawRestrictedProofCoveredSpecialRuleTruthSound
    (M : RawPAModel) (level : nat) : Prop :=
  forall root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3,
    RawRestrictedProof M level root ->
    RawProofAtomicallyAdequate M root ->
    RawProofFormulaCoverage M root coverageBound ->
    RawProofRuleCoverage M root ->
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep coverageBound ->
    RawProofSpecialRuleValidCases M
      root context conclusion a b c t child1 child2 child3 ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawRestrictedProofCoveredRecursiveChildrenSigmaSound M level
      root coverageBound assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofCoveredSpecialRuleTruthSound M level
  : clear implicits.

(** Membership in the fixed metatheoretic constructor table is computation,
    not an appeal to any model-internal list decoder. *)
Ltac solve_raw_constructor_table_membership :=
  cbn [rawProofRecursiveCases];
  repeat first [left; reflexivity | right].

(** A covered recursive endpoint is admissible under the current assignment.
    Coverage is first rerooted to the named child; its endpoint conclusion is
    below the common bound, so assignment definedness restricts to that
    formula code. *)
Lemma raw_restrictedProofCovered_recursive_child_endpoint_admissible :
    forall (M : RawPAModel), RawPASatisfies M -> forall level root
      coverageBound assignmentCode assignmentStep,
  RawRestrictedProof M level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  forall nodeContext a b c t child1 child2 child3,
  RawProofConstructorCode M
    root nodeContext a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      nodeContext a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
  forall childContext childConclusion,
  RawProofEndpoint M child childContext childConclusion ->
  RawFixedLevelTruthAdmissible M level childConclusion
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root coverageBound assignmentCode assignmentStep
    hrestricted hatomic hcoverage hdefined
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild
    childContext childConclusion hendpoint.
  destruct (raw_proofFormulaCoverage_public_recursive_child M hPA
    root coverageBound hcoverage
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildCoverage _].
  pose proof (raw_proofFormulaCoverage_public_root_endpoint M hPA
    child coverageBound hchildCoverage childContext childConclusion
    hendpoint) as [_ hconclusionBelow].
  assert (hconclusionDefined : RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep childConclusion).
  {
    exact (raw_codedAssignmentDefinedThrough_of_lt M hPA
      assignmentCode assignmentStep childConclusion coverageBound
      hconclusionBelow hdefined).
  }
  exact (raw_restrictedProof_recursive_child_endpoint_admissible M hPA
    level root hrestricted hatomic
    nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild
    childContext childConclusion hendpoint
    assignmentCode assignmentStep hconclusionDefined).
Qed.

(** Soundness of all seventeen constructors, parametrized only by the exact
    six special cases. *)
Theorem raw_restrictedProofCovered_ruleTruthSound_of_special : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSpecialRuleTruthSound M level ->
  RawRestrictedProofCoveredRuleTruthSound M level.
Proof.
  intros M hPA level hspecial
    root coverageBound context conclusion assignmentCode assignmentStep
    hrestricted hatomic hcoverage hruleCoverage hdefined hvalid
    hadmissible hcontext hrecursive.
  destruct hvalid as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcase).
  subst rowContext.
  unfold RawProofRuleValidCases in hcase.
  destruct hcase as
    [hass |
     [himpI |
      [himpE |
       [hbotE |
        [hlem |
         [handI |
          [handE1 |
           [handE2 |
            [horI1 |
             [horI2 |
              [horE |
               [hallI |
                [hallE |
                 [hexI |
                  [hexE |
                   [heqRefl | heqElim]]]]]]]]]]]]]]]].
  - (** Assumption. *)
    destruct hass as [hcode [-> hmember]].
    exact (raw_contextAllSigmaTrue_member M hPA (S level)
      context assignmentCode assignmentStep a hcontext hmember).
  - (** Implication introduction. *)
    destruct himpI as [hcode [-> hchildEndpoint]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b c t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA level
      a b assignmentCode assignmentStep hadmissible)
      as [haAdmissible _].
    apply (proj2 (raw_fixedLevelImp_sigma_iff M hPA level a b
      assignmentCode assignmentStep hadmissible)).
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      level M hPA a assignmentCode assignmentStep haAdmissible)
      as [haSigma | haPi].
    + right.
      eapply (hrecursive context a b c t child1 child2 child3
        hconstructor
        [rawNumeralValue M 1; context; a; b; child1] [child1]).
      * solve_raw_constructor_table_membership.
      * exact hcode.
      * solve_raw_constructor_table_membership.
      * exact hchildEndpoint.
      * exact hdefined.
      * exact (raw_contextAllSigmaTrue_cons M hPA (S level)
          context a assignmentCode assignmentStep hcontext haSigma).
    + now left.
  - (** Implication elimination. *)
    destruct himpE as [hcode [-> [-> [himpEndpoint haEndpoint]]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b (rawFormulaImpCode M a b) t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    assert (hentry : In
        ([rawNumeralValue M 2; context; a; b; child1; child2],
         [child1; child2])
        (rawProofRecursiveCases M context a b
          (rawFormulaImpCode M a b) t child1 child2 child3)).
    { solve_raw_constructor_table_membership. }
    pose proof (hrecursive context a b (rawFormulaImpCode M a b) t
      child1 child2 child3 hconstructor
      [rawNumeralValue M 2; context; a; b; child1; child2]
      [child1; child2] hentry hcode child1
      ltac:(solve_raw_constructor_table_membership)
      context (rawFormulaImpCode M a b) himpEndpoint
      assignmentCode assignmentStep hdefined hcontext)
      as himpSigma.
    pose proof (hrecursive context a b (rawFormulaImpCode M a b) t
      child1 child2 child3 hconstructor
      [rawNumeralValue M 2; context; a; b; child1; child2]
      [child1; child2] hentry hcode child2
      ltac:(solve_raw_constructor_table_membership)
      context a haEndpoint assignmentCode assignmentStep hdefined hcontext)
      as haSigma.
    pose proof
      (raw_restrictedProofCovered_recursive_child_endpoint_admissible
        M hPA level root coverageBound assignmentCode assignmentStep
        hrestricted hatomic hcoverage hdefined
        context a b (rawFormulaImpCode M a b) t child1 child2 child3
        hconstructor
        [rawNumeralValue M 2; context; a; b; child1; child2]
        [child1; child2] hentry hcode child1
        ltac:(solve_raw_constructor_table_membership)
        context (rawFormulaImpCode M a b) himpEndpoint)
      as himpAdmissible.
    exact (raw_fixedLevelImp_sigma_modus_ponens M hPA level a b
      assignmentCode assignmentStep himpAdmissible himpSigma haSigma).
  - (** Explosion. *)
    destruct hbotE as [hcode [-> [-> hbotEndpoint]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a (rawFormulaBotCode M) c t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    exfalso.
    apply (raw_fixedLevelSigmaBottomFalse_successor M hPA level
      assignmentCode assignmentStep).
    eapply (hrecursive context a (rawFormulaBotCode M) c t
      child1 child2 child3 hconstructor
      [rawNumeralValue M 3; context; a; child1] [child1]).
    + solve_raw_constructor_table_membership.
    + exact hcode.
    + solve_raw_constructor_table_membership.
    + exact hbotEndpoint.
    + exact hdefined.
    + exact hcontext.
  - (** Classical excluded middle, encoded as [a \/ (a -> Bot)]. *)
    destruct hlem as [hcode [-> [-> ->]]].
    destruct (raw_fixedLevelTruthAdmissible_or_children M hPA level
      a (rawFormulaImpCode M a (rawFormulaBotCode M))
      assignmentCode assignmentStep hadmissible)
      as [haAdmissible himpAdmissible].
    apply (proj2 (raw_fixedLevelOr_sigma_iff M hPA level
      a (rawFormulaImpCode M a (rawFormulaBotCode M))
      assignmentCode assignmentStep hadmissible)).
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      level M hPA a assignmentCode assignmentStep haAdmissible)
      as [haSigma | haPi].
    + now left.
    + right. apply (proj2 (raw_fixedLevelImp_sigma_iff M hPA level
        a (rawFormulaBotCode M) assignmentCode assignmentStep
        himpAdmissible)).
      now left.
  - (** Conjunction introduction. *)
    destruct handI as [hcode [-> [hleftEndpoint hrightEndpoint]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b c t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    assert (hentry : In
        ([rawNumeralValue M 5; context; a; b; child1; child2],
         [child1; child2])
        (rawProofRecursiveCases M context a b c t
          child1 child2 child3)).
    { solve_raw_constructor_table_membership. }
    apply (proj2 (raw_fixedLevelAnd_sigma_iff M hPA level a b
      assignmentCode assignmentStep hadmissible)). split.
    + eapply (hrecursive context a b c t child1 child2 child3
        hconstructor
        [rawNumeralValue M 5; context; a; b; child1; child2]
        [child1; child2] hentry hcode child1).
      * solve_raw_constructor_table_membership.
      * exact hleftEndpoint.
      * exact hdefined.
      * exact hcontext.
    + eapply (hrecursive context a b c t child1 child2 child3
        hconstructor
        [rawNumeralValue M 5; context; a; b; child1; child2]
        [child1; child2] hentry hcode child2).
      * solve_raw_constructor_table_membership.
      * exact hrightEndpoint.
      * exact hdefined.
      * exact hcontext.
  - (** Left conjunction elimination. *)
    destruct handE1 as [hcode [-> [-> hchildEndpoint]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b (rawFormulaAndCode M a b) t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    assert (hentry : In
        ([rawNumeralValue M 6; context; a; b; child1], [child1])
        (rawProofRecursiveCases M context a b
          (rawFormulaAndCode M a b) t child1 child2 child3)).
    { solve_raw_constructor_table_membership. }
    pose proof (hrecursive context a b (rawFormulaAndCode M a b) t
      child1 child2 child3 hconstructor
      [rawNumeralValue M 6; context; a; b; child1] [child1]
      hentry hcode child1 ltac:(solve_raw_constructor_table_membership)
      context (rawFormulaAndCode M a b) hchildEndpoint
      assignmentCode assignmentStep hdefined hcontext)
      as handSigma.
    pose proof
      (raw_restrictedProofCovered_recursive_child_endpoint_admissible
        M hPA level root coverageBound assignmentCode assignmentStep
        hrestricted hatomic hcoverage hdefined
        context a b (rawFormulaAndCode M a b) t child1 child2 child3
        hconstructor [rawNumeralValue M 6; context; a; b; child1]
        [child1] hentry hcode child1
        ltac:(solve_raw_constructor_table_membership)
        context (rawFormulaAndCode M a b) hchildEndpoint)
      as handAdmissible.
    exact (proj1 (raw_fixedLevelAnd_sigma_elim M hPA level a b
      assignmentCode assignmentStep handAdmissible handSigma)).
  - (** Right conjunction elimination. *)
    destruct handE2 as [hcode [-> [-> hchildEndpoint]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b (rawFormulaAndCode M a b) t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    assert (hentry : In
        ([rawNumeralValue M 7; context; a; b; child1], [child1])
        (rawProofRecursiveCases M context a b
          (rawFormulaAndCode M a b) t child1 child2 child3)).
    { solve_raw_constructor_table_membership. }
    pose proof (hrecursive context a b (rawFormulaAndCode M a b) t
      child1 child2 child3 hconstructor
      [rawNumeralValue M 7; context; a; b; child1] [child1]
      hentry hcode child1 ltac:(solve_raw_constructor_table_membership)
      context (rawFormulaAndCode M a b) hchildEndpoint
      assignmentCode assignmentStep hdefined hcontext)
      as handSigma.
    pose proof
      (raw_restrictedProofCovered_recursive_child_endpoint_admissible
        M hPA level root coverageBound assignmentCode assignmentStep
        hrestricted hatomic hcoverage hdefined
        context a b (rawFormulaAndCode M a b) t child1 child2 child3
        hconstructor [rawNumeralValue M 7; context; a; b; child1]
        [child1] hentry hcode child1
        ltac:(solve_raw_constructor_table_membership)
        context (rawFormulaAndCode M a b) hchildEndpoint)
      as handAdmissible.
    exact (proj2 (raw_fixedLevelAnd_sigma_elim M hPA level a b
      assignmentCode assignmentStep handAdmissible handSigma)).
  - (** Left disjunction introduction. *)
    destruct horI1 as [hcode [-> hchildEndpoint]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b c t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    apply (proj2 (raw_fixedLevelOr_sigma_iff M hPA level a b
      assignmentCode assignmentStep hadmissible)). left.
    eapply (hrecursive context a b c t child1 child2 child3
      hconstructor [rawNumeralValue M 8; context; a; b; child1]
      [child1]).
    + solve_raw_constructor_table_membership.
    + exact hcode.
    + solve_raw_constructor_table_membership.
    + exact hchildEndpoint.
    + exact hdefined.
    + exact hcontext.
  - (** Right disjunction introduction. *)
    destruct horI2 as [hcode [-> hchildEndpoint]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b c t child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    apply (proj2 (raw_fixedLevelOr_sigma_iff M hPA level a b
      assignmentCode assignmentStep hadmissible)). right.
    eapply (hrecursive context a b c t child1 child2 child3
      hconstructor [rawNumeralValue M 9; context; a; b; child1]
      [child1]).
    + solve_raw_constructor_table_membership.
    + exact hcode.
    + solve_raw_constructor_table_membership.
    + exact hchildEndpoint.
    + exact hdefined.
    + exact hcontext.
  - (** Disjunction elimination. *)
    destruct horE as
      [hcode [-> [-> [horEndpoint [hleftEndpoint hrightEndpoint]]]]].
    assert (hconstructor : RawProofConstructorCode M root
        context a b c (rawFormulaOrCode M a b)
        child1 child2 child3).
    { unfold RawProofConstructorCode. tauto. }
    assert (hentry : In
        ([rawNumeralValue M 10; context; a; b; c;
          child1; child2; child3], [child1; child2; child3])
        (rawProofRecursiveCases M context a b c
          (rawFormulaOrCode M a b) child1 child2 child3)).
    { solve_raw_constructor_table_membership. }
    pose proof (hrecursive context a b c
      (rawFormulaOrCode M a b) child1 child2 child3 hconstructor
      [rawNumeralValue M 10; context; a; b; c;
       child1; child2; child3] [child1; child2; child3]
      hentry hcode child1 ltac:(solve_raw_constructor_table_membership)
      context (rawFormulaOrCode M a b) horEndpoint
      assignmentCode assignmentStep hdefined hcontext)
      as horSigma.
    pose proof
      (raw_restrictedProofCovered_recursive_child_endpoint_admissible
        M hPA level root coverageBound assignmentCode assignmentStep
        hrestricted hatomic hcoverage hdefined
        context a b c (rawFormulaOrCode M a b)
        child1 child2 child3 hconstructor
        [rawNumeralValue M 10; context; a; b; c;
         child1; child2; child3] [child1; child2; child3]
        hentry hcode child1 ltac:(solve_raw_constructor_table_membership)
        context (rawFormulaOrCode M a b) horEndpoint)
      as horAdmissible.
    destruct (raw_fixedLevelOr_sigma_elim M hPA level a b
      assignmentCode assignmentStep horAdmissible horSigma)
      as [haSigma | hbSigma].
    + eapply (hrecursive context a b c
        (rawFormulaOrCode M a b) child1 child2 child3 hconstructor
        [rawNumeralValue M 10; context; a; b; c;
         child1; child2; child3] [child1; child2; child3]
        hentry hcode child2).
      * solve_raw_constructor_table_membership.
      * exact hleftEndpoint.
      * exact hdefined.
      * exact (raw_contextAllSigmaTrue_cons M hPA (S level)
          context a assignmentCode assignmentStep hcontext haSigma).
    + eapply (hrecursive context a b c
        (rawFormulaOrCode M a b) child1 child2 child3 hconstructor
        [rawNumeralValue M 10; context; a; b; c;
         child1; child2; child3] [child1; child2; child3]
        hentry hcode child3).
      * solve_raw_constructor_table_membership.
      * exact hrightEndpoint.
      * exact hdefined.
      * exact (raw_contextAllSigmaTrue_cons M hPA (S level)
          context b assignmentCode assignmentStep hcontext hbSigma).
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
  - apply (hspecial root coverageBound context conclusion
      assignmentCode assignmentStep a b c t child1 child2 child3
      hrestricted hatomic hcoverage hruleCoverage hdefined).
    + unfold RawProofSpecialRuleValidCases. tauto.
    + exact hadmissible.
    + exact hcontext.
    + exact hrecursive.
Qed.

End PABoundedRawCodedRestrictedProofPropositionalSoundness.
