(**
  Coverage-certified conjunction introduction for model-coded PA proofs.

  The constructor is valid for arbitrary formula and context codes in an
  arbitrary model of PA.  Its two premise proofs may carry different
  nonstandard support tables; [raw_proofBinary_ruleCoverage] merges those
  tables and adds exactly the new [RP_andI] parent.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofBinaryCoverage.

Import ListNotations.

Module PABoundedRawCodedProofAndIConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofBinaryCoverage.

Definition rawProofAndIRoot (M : RawPAModel)
    (context left right leftChild rightChild : M) : M :=
  rawListCode M
    [rawNumeralValue M 5; context; left; right; leftChild; rightChild].

Arguments rawProofAndIRoot M context left right leftChild rightChild
  : clear implicits.

Lemma raw_proofAndIRoot_left_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild,
  rawLt M leftChild
    (rawProofAndIRoot M context left right leftChild rightChild).
Proof.
  intros M hPA context left right leftChild rightChild.
  unfold rawProofAndIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofAndIRoot_right_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild,
  rawLt M rightChild
    (rawProofAndIRoot M context left right leftChild rightChild).
Proof.
  intros M hPA context left right leftChild rightChild.
  unfold rawProofAndIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** Constructor-tag injectivity prevents the same parent code from being
    interpreted as any other recursive proof rule, even in a nonstandard
    model. *)
Lemma raw_proofAndIRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild tag payload,
  rawProofAndIRoot M context left right leftChild rightChild =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 5 /\
  payload = [context; left; right; leftChild; rightChild].
Proof.
  intros M hPA context left right leftChild rightChild tag payload hcode.
  unfold rawProofAndIRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 5; context; left; right; leftChild; rightChild]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 5 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail :
      [context; left; right; leftChild; rightChild] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofAndIRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofAndIRoot M context left right leftChild rightChild =
    rawListCode M fields ->
  children = [leftChild; rightChild].
Proof.
  intros M hPA context left right leftChild rightChild
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofAndIRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofAndI_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep leftChild ->
  rawProofCodeSupported M supportCode supportStep rightChild ->
  RawProofSyntaxStep M
    (rawProofAndIRoot M context left right leftChild rightChild)
    supportCode supportStep.
Proof.
  intros M hPA context left right leftChild rightChild
    supportCode supportStep hleftSupported hrightSupported.
  split.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), leftChild, rightChild, (raw_zero M).
    unfold RawProofConstructorCode, rawProofAndIRoot.
    do 5 right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofAndIRoot M context left right leftChild rightChild)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofAndIRoot_recursive_children M hPA
        context left right leftChild rightChild
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hleftSupported |].
        exact (raw_proofAndIRoot_left_child_lt M hPA
          context left right leftChild rightChild).
      * constructor.
        -- split; [exact hrightSupported |].
           exact (raw_proofAndIRoot_right_child_lt M hPA
             context left right leftChild rightChild).
        -- constructor.
Qed.

Lemma raw_proofAndI_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild,
  RawProofEndpoint M leftChild context left ->
  RawProofEndpoint M rightChild context right ->
  RawProofEndpointRuleComplete M
    (rawProofAndIRoot M context left right leftChild rightChild).
Proof.
  intros M hPA context left right leftChild rightChild
    hleftEndpoint hrightEndpoint
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
  all: pose proof (raw_proofAndIRoot_list_view M hPA
    context left right leftChild rightChild _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a b child1 child2.
  subst endpointConclusion.
  exists context, left, right,
    (raw_zero M), (raw_zero M), leftChild, rightChild, (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofAndIRoot.
  do 5 right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofAndI_endpoint : forall
    (M : RawPAModel) context left right leftChild rightChild,
  RawProofEndpoint M
    (rawProofAndIRoot M context left right leftChild rightChild)
    context (rawFormulaAndCode M left right).
Proof.
  intros M context left right leftChild rightChild.
  exists context, left, right,
    (raw_zero M), (raw_zero M), leftChild, rightChild, (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofAndIRoot.
  do 5 right. left. split; reflexivity.
Qed.

Theorem raw_proofAndI_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right leftChild rightChild,
  RawProofRuleCoverage M leftChild ->
  RawProofEndpoint M leftChild context left ->
  RawProofRuleCoverage M rightChild ->
  RawProofEndpoint M rightChild context right ->
  RawProofRuleCoverage M
    (rawProofAndIRoot M context left right leftChild rightChild).
Proof.
  intros M hPA context left right leftChild rightChild
    hleftCoverage hleftEndpoint hrightCoverage hrightEndpoint.
  exact (raw_proofBinary_ruleCoverage M hPA
    leftChild rightChild
    (rawProofAndIRoot M context left right leftChild rightChild)
    hleftCoverage hrightCoverage
    (raw_proofAndIRoot_left_child_lt M hPA
      context left right leftChild rightChild)
    (raw_proofAndIRoot_right_child_lt M hPA
      context left right leftChild rightChild)
    (raw_proofAndI_syntax_step M hPA
      context left right leftChild rightChild)
    (raw_proofAndI_endpoint_rule_complete M hPA
      context left right leftChild rightChild
      hleftEndpoint hrightEndpoint)).
Qed.

End PABoundedRawCodedProofAndIConstructor.
