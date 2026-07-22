(**
  Coverage-certified assumption leaves for model-coded PA proofs.

  An assumption node is valid only when its formula occurs in its coded
  context.  The generic constructor accepts an honest model-internal
  membership witness.  The head-specialized constructor then uses the
  existing beta-table context-cons extension to show that a newly adjoined
  formula is a member of [formula :: context], including for nonstandard
  context lengths.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFixedLevelTruthTotality
  RawCodedSyntaxConstructors RawCodedProofConstructors RawCodedProofDescent
  RawCodedProofTraversal RawCodedProofEndpoints RawCodedProofRules
  RawCodedProofRuleCoverage RawCodedListInjectivity
  RawCodedContextLists RawCodedContextStructure
  RawCodedProofLeafConstructors.

Import ListNotations.

Module PABoundedRawCodedProofAssumptionLeaf.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofLeafConstructors.

Definition rawProofAssumptionRoot
    (M : RawPAModel) (context formulaCode : M) : M :=
  rawListCode M [rawNumeralValue M 0; context; formulaCode].

Arguments rawProofAssumptionRoot M context formulaCode : clear implicits.

Lemma raw_proofAssumptionRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context formulaCode tag payload,
  rawProofAssumptionRoot M context formulaCode =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 0 /\ payload = [context; formulaCode].
Proof.
  intros M hPA context formulaCode tag payload hcode.
  unfold rawProofAssumptionRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 0; context; formulaCode]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 0 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; formulaCode] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofAssumptionRoot_not_recursive_case : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formulaCode
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofAssumptionRoot M context formulaCode = rawListCode M fields ->
  False.
Proof.
  intros M hPA context formulaCode rowContext a b c t
    child1 child2 child3 fields children hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofAssumptionRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields;
    discriminate hfields.
Qed.

Lemma raw_proofAssumption_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formulaCode
      supportCode supportStep,
  RawProofSyntaxStep M
    (rawProofAssumptionRoot M context formulaCode)
    supportCode supportStep.
Proof.
  intros M hPA context formulaCode supportCode supportStep.
  split.
  - exists context, formulaCode,
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofAssumptionRoot.
    left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofAssumptionRoot M context formulaCode)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode. exfalso.
      exact (raw_proofAssumptionRoot_not_recursive_case M hPA
        context formulaCode rowContext a b c t
        child1 child2 child3 fields children hentry hcode).
Qed.

Lemma raw_proofAssumption_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formulaCode,
  RawContextListMember M context formulaCode ->
  RawProofEndpointRuleComplete M
    (rawProofAssumptionRoot M context formulaCode).
Proof.
  intros M hPA context formulaCode hmember
    endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofAssumptionRoot_list_view M hPA
    context formulaCode _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a.
  subst endpointConclusion.
  exists context, formulaCode,
    (raw_zero M), (raw_zero M), (raw_zero M),
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofAssumptionRoot.
  left. repeat split; assumption || reflexivity.
Qed.

Theorem raw_proofAssumption_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formulaCode,
  RawContextListMember M context formulaCode ->
  RawProofRuleCoverage M
    (rawProofAssumptionRoot M context formulaCode).
Proof.
  intros M hPA context formulaCode hmember.
  set (root := rawProofAssumptionRoot M context formulaCode).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    (raw_zero M) (raw_zero M) root (rawNumeralValue M 1)
    (raw_codedZeroAssignment_defined_all M hPA root))
    as (supportCode & supportStep & hdefined & hprefix & hroot).
  exists supportCode, supportStep. split.
  - split.
    + split; [exact hdefined |].
      intros code hbelow hsupported.
      assert (code = root) as ->.
      {
        exact (raw_singleProofRoot_supported_eq M hPA
          root supportCode supportStep hdefined hprefix hroot
          code hbelow hsupported).
      }
      unfold root.
      exact (raw_proofAssumption_syntax_step M hPA
        context formulaCode supportCode supportStep).
    + unfold rawProofCodeSupported. exact hroot.
  - intros code hbelow hsupported.
    assert (code = root) as ->.
    {
      exact (raw_singleProofRoot_supported_eq M hPA
        root supportCode supportStep hdefined hprefix hroot
        code hbelow hsupported).
    }
    unfold root.
    exact (raw_proofAssumption_endpoint_rule_complete M hPA
      context formulaCode hmember).
Qed.

Corollary raw_proofAssumption_endpoint : forall
    (M : RawPAModel) context formulaCode,
  RawProofEndpoint M
    (rawProofAssumptionRoot M context formulaCode)
    context formulaCode.
Proof.
  intros M context formulaCode.
  exists context, formulaCode,
    (raw_zero M), (raw_zero M), (raw_zero M),
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofAssumptionRoot.
  left. split; reflexivity.
Qed.

(** The deduction-theorem specialization: the head of a newly extended
    realizable context is immediately available as an honest proof leaf. *)
Corollary raw_proofAssumption_cons_head_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context formulaCode,
  RawContextListRealizable M context ->
  RawProofRuleCoverage M
    (rawProofAssumptionRoot M
      (rawListNode M formulaCode context) formulaCode).
Proof.
  intros M hPA context formulaCode hcontext.
  exact (raw_proofAssumption_ruleCoverage M hPA
    (rawListNode M formulaCode context) formulaCode
    (raw_contextList_cons_head_member M hPA
      context formulaCode hcontext)).
Qed.

End PABoundedRawCodedProofAssumptionLeaf.
