(**
  Coverage-certified leaf constructors for model-coded PA proofs.

  Standard quotations already provide certificates for fixed derivations,
  but a uniform proof compiler has to construct proof nodes whose formula
  fields may be nonstandard elements of a PA model.  This file begins that
  constructor API with excluded middle, the most useful premise-free rule.

  The support table is honest.  It is the all-zero beta assignment below the
  root, extended by a single [1] flag at the root itself.  Injectivity of the
  polynomial list code then proves that the advertised excluded-middle node
  cannot secretly expose any recursive proof children through an alternative
  constructor view.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFixedLevelTruthTotality RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity.

Import ListNotations.

Module PABoundedRawCodedProofLeafConstructors.

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

Definition rawProofLemRoot (M : RawPAModel) (context body : M) : M :=
  rawListCode M [rawNumeralValue M 4; context; body].

Definition rawProofLemConclusion (M : RawPAModel) (body : M) : M :=
  rawFormulaOrCode M body
    (rawFormulaImpCode M body (rawFormulaBotCode M)).

Arguments rawProofLemRoot M context body : clear implicits.
Arguments rawProofLemConclusion M body : clear implicits.

(** Any list-constructor view of the leaf root has exactly tag [4] and the
    two advertised payload fields.  This one inversion lemma keeps all later
    constructor case splits independent of polynomial-code arithmetic. *)
Lemma raw_proofLemRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body tag payload,
  rawProofLemRoot M context body =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 4 /\ payload = [context; body].
Proof.
  intros M hPA context body tag payload hcode.
  unfold rawProofLemRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 4; context; body]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 4 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; body] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

(** None of the fourteen recursive constructor rows can denote the
    premise-free excluded-middle root. *)
Lemma raw_proofLemRoot_not_recursive_case : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofLemRoot M context body = rawListCode M fields ->
  False.
Proof.
  intros M hPA context body rowContext a b c t
    child1 child2 child3 fields children hentry hcode.
  unfold rawProofLemRoot in hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields;
    discriminate hfields.
Qed.

(** The one-point support table has no supported row below its root. *)
Lemma raw_singleProofRoot_supported_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall root supportCode supportStep,
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (raw_succ M root) ->
  (forall index value,
    rawLt M index root ->
    RawCodedAssignmentLookup M
      (raw_zero M) (raw_zero M) index value ->
    RawCodedAssignmentLookup M supportCode supportStep index value) ->
  RawCodedAssignmentLookup M supportCode supportStep root
    (rawNumeralValue M 1) ->
  forall code,
    rawLt M code (raw_succ M root) ->
    rawProofCodeSupported M supportCode supportStep code ->
    code = root.
Proof.
  intros M hPA root supportCode supportStep _ hprefix hroot
    code hbelow hsupported.
  destruct (raw_lt_succ_cases M hPA code root hbelow)
    as [hstrict | heq]; [| exact heq].
  pose proof (raw_codedZeroAssignment_lookup M hPA code) as hzeroOld.
  pose proof (hprefix code (raw_zero M) hstrict hzeroOld) as hzeroNew.
  unfold rawProofCodeSupported in hsupported.
  assert (honeZero : rawNumeralValue M 1 = raw_zero M).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      supportCode supportStep code
      (rawNumeralValue M 1) (raw_zero M)
      hsupported hzeroNew).
  }
  change (rawNumeralValue M 1 = rawNumeralValue M 0) in honeZero.
  apply (rawNumeralValue_injective M hPA 1 0) in honeZero.
  discriminate.
Qed.

Lemma raw_proofLem_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body
      supportCode supportStep,
  RawProofSyntaxStep M
    (rawProofLemRoot M context body) supportCode supportStep.
Proof.
  intros M hPA context body supportCode supportStep.
  split.
  - exists context, body,
      (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofLemRoot.
    right. right. right. right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofLemRoot M context body)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      exfalso.
      exact (raw_proofLemRoot_not_recursive_case M hPA context body
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode).
Qed.

(** Every endpoint advertised by the leaf is its excluded-middle endpoint,
    so its local rule row is valid without assumptions on [body]. *)
Lemma raw_proofLem_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body,
  RawProofEndpointRuleComplete M (rawProofLemRoot M context body).
Proof.
  intros M hPA context body rowContext conclusion hendpoint.
  destruct hendpoint as
    (endpointContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst endpointContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofLemRoot_list_view M hPA context body
    _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  destruct hrest as [hc [hb hconclusion]].
  inversion hpayload; subst rowContext a.
  subst c. subst b. subst conclusion.
  exists context, body,
    (rawFormulaImpCode M body (rawFormulaBotCode M)),
    (rawFormulaBotCode M), (raw_zero M),
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofLemRoot,
    rawProofLemConclusion in *.
  right. right. right. right. left.
  repeat split; assumption || reflexivity.
Qed.

(** Public leaf constructor.  The result is the exact proof-wide coverage
    relation consumed by [RawCodedPAProofOf]. *)
Theorem raw_proofLem_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body,
  RawProofRuleCoverage M (rawProofLemRoot M context body).
Proof.
  intros M hPA context body.
  set (root := rawProofLemRoot M context body).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    (raw_zero M) (raw_zero M) root (rawNumeralValue M 1)
    (raw_codedZeroAssignment_defined_all M hPA root))
    as (supportCode & supportStep & hdefined & hprefix & hroot).
  exists supportCode, supportStep.
  split.
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
      exact (raw_proofLem_syntax_step M hPA
        context body supportCode supportStep).
    + unfold rawProofCodeSupported. exact hroot.
  - intros code hbelow hsupported.
    assert (code = root) as ->.
    {
      exact (raw_singleProofRoot_supported_eq M hPA
        root supportCode supportStep hdefined hprefix hroot
        code hbelow hsupported).
    }
    unfold root.
    exact (raw_proofLem_endpoint_rule_complete M hPA context body).
Qed.

Corollary raw_proofLem_endpoint : forall
    (M : RawPAModel) context body,
  RawProofEndpoint M
    (rawProofLemRoot M context body) context
    (rawProofLemConclusion M body).
Proof.
  intros M context body.
  exists context, body,
    (rawFormulaImpCode M body (rawFormulaBotCode M)),
    (rawFormulaBotCode M), (raw_zero M),
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofLemRoot,
    rawProofLemConclusion.
  right. right. right. right. left.
  repeat split; reflexivity.
Qed.

End PABoundedRawCodedProofLeafConstructors.
