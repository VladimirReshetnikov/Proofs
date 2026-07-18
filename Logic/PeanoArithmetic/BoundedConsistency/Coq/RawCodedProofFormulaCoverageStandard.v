(**
  Standard quotations have one standard proof-wide formula-code bound.

  [RawCodedProofStandardSupport] deliberately marks every canonical proof
  code below the quoted root, rather than only the recursive subtree.  The
  coverage bound below follows that design exactly: externally, it decodes
  the finite interval of natural codes below the root successor, collects
  every displayed endpoint formula, and takes one plus their maximum.

  This is still a metatheoretic construction over an ordinary finite list.
  Inside an arbitrary PA model the resulting carrier is a standard numeral;
  no possibly nonstandard model element is ever passed to a Rocq decoder.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedAssignment RawCodedFormulaOperations
  RawCodedContextLists RawCodedContextFunctionality
  RawCodedProofConstructors RawCodedProofTraversal RawCodedProofEndpoints
  RawCodedProofStandardSupport RawCodedProofStandardSyntax
  RawCodedRestrictedProofStandardAdequacy
  RawCodedProofAtomicAdequacyStandard RawCodedProofFormulaCoverage.

Import ListNotations.

Module PABoundedRawCodedProofFormulaCoverageStandard.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofStandardSupport.
Import PABoundedRawCodedProofStandardSyntax.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofFormulaCoverage.

(** The endpoint formula codes displayed by one ordinary raw proof node. *)
Definition rawProofEndpointFormulaCodes (derivation : RawProof) : list nat :=
  formulaCode (rawConclusion derivation) ::
  map formulaCode (rawContext derivation).

(** All endpoint formula codes belonging to canonical proof codes in the
    half-open interval [[0, proofBound)].  Malformed codes contribute no
    entries. *)
Definition rawProofFormulaCodesBelow (proofBound : nat) : list nat :=
  flat_map
    (fun code =>
      match decodeRawProof code with
      | Some derivation => rawProofEndpointFormulaCodes derivation
      | None => []
      end)
    (seq 0 proofBound).

(** One strict upper bound for every formula occurrence advertised by the
    standard support table of [root]. *)
Definition rawProofFormulaCoverageNatBound (root : RawProof) : nat :=
  S (fold_right Nat.max 0
    (rawProofFormulaCodesBelow (S (rawProofCode root)))).

Lemma raw_in_fold_right_max_le : forall values value,
  In value values -> value <= fold_right Nat.max 0 values.
Proof.
  intros values value hin. induction values as [|head tail IH]; cbn in *.
  - contradiction.
  - destruct hin as [-> | hin].
    + apply Nat.le_max_l.
    + exact (Nat.le_trans _ _ _ (IH hin) (Nat.le_max_r _ _)).
Qed.

Lemma rawProofFormulaCoverageNatBound_covers : forall root derivation phi,
  rawProofCode derivation < S (rawProofCode root) ->
  In phi (rawConclusion derivation :: rawContext derivation) ->
  formulaCode phi < rawProofFormulaCoverageNatBound root.
Proof.
  intros root derivation phi hcode hphi.
  unfold rawProofFormulaCoverageNatBound.
  apply Nat.lt_succ_r.
  apply raw_in_fold_right_max_le.
  unfold rawProofFormulaCodesBelow.
  apply in_flat_map.
  exists (rawProofCode derivation). split.
  - apply in_seq. lia.
  - rewrite decodeRawProof_rawProofCode.
    unfold rawProofEndpointFormulaCodes.
    cbn. destruct hphi as [-> | hphi].
    + now left.
    + right. now apply in_map.
Qed.

(** Public membership in a standard quoted context has no nonstandard
    impostors.  Traversal functionality reduces a cons context to its head
    or tail, after which ordinary list induction identifies the quotation. *)
Lemma raw_quotedContext_member_inv : forall (M : RawPAModel),
  RawPASatisfies M -> forall context code,
  RawContextListMember M (rawQuotedContextCode M context) code ->
  exists phi,
    In phi context /\ code = rawQuotedFormulaCode M phi.
Proof.
  intros M hPA context. induction context as [|head tail IH];
    intros code hmember.
  - cbn [rawQuotedContextCode] in hmember.
    exfalso. exact (raw_contextListMember_zero_false M hPA code hmember).
  - cbn [rawQuotedContextCode] in hmember.
    pose proof (proj1 (raw_contextListMember_cons_iff M hPA
      (rawQuotedContextCode M tail) (rawQuotedFormulaCode M head) code
      (raw_quotedContext_realizable M hPA tail)) hmember) as hcases.
    destruct hcases as [-> | htail].
    + exists head. split; [now left | reflexivity].
    + destruct (IH code htail) as [phi [hin ->]].
      exists phi. split; [now right | reflexivity].
Qed.

(** The particular traversal hidden in [RawContextAllCodesBelow] may be any
    complete traversal of the quoted context.  Turning one of its head rows
    into public membership lets the preceding theorem identify that row with
    a standard formula quotation. *)
Lemma raw_quotedContext_all_codes_below : forall (M : RawPAModel),
  RawPASatisfies M -> forall root derivation,
  rawProofCode derivation < S (rawProofCode root) ->
  RawContextAllCodesBelow M
    (rawQuotedContextCode M (rawContext derivation))
    (rawNumeralValue M (rawProofFormulaCoverageNatBound root)).
Proof.
  intros M hPA root derivation hcode.
  destruct (raw_quotedContext_realizable M hPA (rawContext derivation))
    as (contextLength & tailCode & tailStep & headCode & headStep &
      htraversal).
  exists contextLength, tailCode, tailStep, headCode, headStep.
  split; [exact htraversal |].
  intros index hindex code hlookup.
  assert (hmember : RawContextListMember M
      (rawQuotedContextCode M (rawContext derivation)) code).
  {
    exists contextLength, tailCode, tailStep, headCode, headStep.
    split; [exact htraversal |].
    exists index. split; assumption.
  }
  destruct (raw_quotedContext_member_inv M hPA
    (rawContext derivation) code hmember) as [phi [hphi ->]].
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  apply raw_lt_numeralValue_of_lt; [exact hPA |].
  apply rawProofFormulaCoverageNatBound_covers with
    (derivation := derivation); [exact hcode |].
  now right.
Qed.

(** Endpoint decoding is functional on an externally quoted proof code.
    Most rules reduce by injectivity of the finite list constructor.  The two
    substitution-producing rules additionally use arbitrary-trace standard
    output soundness: merely exhibiting a canonical trace would not identify
    the output of the independently advertised endpoint trace. *)
Lemma raw_quotedProof_endpoint_functional : forall (M : RawPAModel),
  RawPASatisfies M -> forall derivation context conclusion,
  RawProofEndpoint M (rawQuotedProofCode M derivation)
    context conclusion ->
  context = rawQuotedContextCode M (rawContext derivation) /\
  conclusion = rawQuotedFormulaCode M (rawConclusion derivation).
Proof.
  intros M hPA derivation context conclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat destruct hcases as [hcases | hcases]; try contradiction.
  all: destruct hcases as [hcode hrest].
  all: destruct derivation.
  all: cbn [rawQuotedProofCode rawListCode] in hcode.
  all: repeat match goal with
  | hnodes : rawListNode ?model ?head ?tail =
      rawListNode ?model ?head' ?tail' |- _ =>
      destruct (rawListNode_injective model hPA
        head tail head' tail' hnodes) as [? ?]; clear hnodes
  end.
  all: try match goal with
  | hnil : raw_zero ?model = rawListNode ?model ?head ?tail |- _ =>
      exfalso; exact (rawListNode_not_zero model hPA head tail hnil)
  | hnil : rawListNode ?model ?head ?tail = raw_zero ?model |- _ =>
      exfalso; apply (rawListNode_not_zero model hPA head tail);
      exact hnil
  end.
  all: subst.
  all: cbn [rawNumeralValue] in *.
  all: repeat match goal with
  | htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hPA) in htag
  end.
  all: try match goal with
  | htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hPA value htag)
  | htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hPA value);
      symmetry; exact htag
  end.
  all: split.
  all: try
    (rewrite rawQuotedContextCode_standard by exact hPA; reflexivity).
  all: repeat match type of hrest with
  | _ /\ _ => destruct hrest as [? hrest]
  end.
  all: subst.
  all: cbn [rawConclusion].
  all: try match goal with
  | hop : RawCodedFormulaSingleSubstitution ?model
      (rawQuotedTermCode ?model ?replacement)
      (rawQuotedFormulaCode ?model ?phi) ?output
      |- ?output = rawQuotedFormulaCode ?model
          (Formula.subst (Formula.instTerm ?replacement) ?phi) =>
      exact (raw_codedFormulaSingleSubstitution_quoted_sound
        model hPA replacement phi output hop)
  end.
  all: reflexivity.
Qed.

Lemma raw_quotedProof_endpoint_formula_coverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall root derivation,
  rawProofCode derivation < S (rawProofCode root) ->
  RawProofEndpointFormulaCoverage M
    (rawQuotedProofCode M derivation)
    (rawNumeralValue M (rawProofFormulaCoverageNatBound root)).
Proof.
  intros M hPA root derivation hcode context conclusion hendpoint.
  destruct (raw_quotedProof_endpoint_functional M hPA derivation
    context conclusion hendpoint) as [hcontext hconclusion].
  rewrite hcontext, hconclusion. split.
  - exact (raw_quotedContext_all_codes_below M hPA root derivation hcode).
  - rewrite rawQuotedFormulaCode_standard by exact hPA.
    apply raw_lt_numeralValue_of_lt; [exact hPA |].
    apply rawProofFormulaCoverageNatBound_covers with
      (derivation := derivation); [exact hcode |].
    now left.
Qed.

(** The exact standard support table and the finite maximum use the same
    external interval.  Consequently every marked model-internal row is a
    quotation covered by the common standard numeral. *)
Theorem raw_quotedProof_formula_coverage : forall (M : RawPAModel),
  RawPASatisfies M -> forall root,
  RawProofFormulaCoverage M
    (rawQuotedProofCode M root)
    (rawNumeralValue M (rawProofFormulaCoverageNatBound root)).
Proof.
  intros M hPA root.
  destruct (raw_standardProofSupportTable_for_quotation M hPA root)
    as (supportCode & supportStep & htable & hrootSupported).
  destruct htable as [hdefined hexact].
  exists supportCode, supportStep. split.
  - split.
    + split.
      * rewrite rawQuotedProofCode_standard by exact hPA.
        change (RawCodedAssignmentDefinedThrough M supportCode supportStep
          (rawNumeralValue M (S (rawProofCode root)))).
        exact hdefined.
      * intros code hcode hsupported.
        assert (hcodeBound : rawLt M code
            (rawNumeralValue M (S (rawProofCode root)))).
        {
          rewrite rawQuotedProofCode_standard in hcode by exact hPA.
          change (rawLt M code
            (rawNumeralValue M (S (rawProofCode root)))) in hcode.
          exact hcode.
        }
        destruct (proj1 (hexact code hcodeBound) hsupported)
          as [derivation [-> hderivationBound]].
        apply (raw_quotedProof_syntax_step M hPA
          (S (rawProofCode root)) supportCode supportStep).
        -- split; assumption.
        -- exact hderivationBound.
    + exact hrootSupported.
  - intros code hcode hsupported.
    assert (hcodeBound : rawLt M code
        (rawNumeralValue M (S (rawProofCode root)))).
    {
      rewrite rawQuotedProofCode_standard in hcode by exact hPA.
      change (rawLt M code
        (rawNumeralValue M (S (rawProofCode root)))) in hcode.
      exact hcode.
    }
    destruct (proj1 (hexact code hcodeBound) hsupported)
      as [derivation [-> hderivationBound]].
    exact (raw_quotedProof_endpoint_formula_coverage
      M hPA root derivation hderivationBound).
Qed.

End PABoundedRawCodedProofFormulaCoverageStandard.
