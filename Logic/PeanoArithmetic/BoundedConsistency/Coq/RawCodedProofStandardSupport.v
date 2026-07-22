(**
  Standard-bound support tables for coded proof syntax.

  To realize a quoted finite proof inside an arbitrary PA model, we need a
  beta table marking its recursively available proof codes.  Marking only the
  syntactic subtree is possible but unnecessarily brittle.  The table built
  here marks *every canonical decodable proof code* below a fixed external
  natural bound.  Genuine recursive children are then supported for free:
  their codes are strictly smaller and decoding followed by re-encoding is
  canonical.

  Crucially, the only conversion of a carrier element back to a Rocq natural
  occurs below an externally standard numeral.  PA proves that such an
  element is itself one of the finitely many standard predecessors.  No
  decoder is ever applied to a genuinely nonstandard carrier value.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawCodedAssignment
  RawCodedSyntaxConstructorSeparation RawCodedProofConstructors
  RawCodedProofTraversal.

Module PABoundedRawCodedProofStandardSupport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofTraversal.

(** The decoder alone need not advertise a re-encoding theorem.  This Boolean
    deliberately checks both directions, so its positive specification is
    exactly the canonical-code property needed by the support table. *)
Definition canonicalRawProofCodeb (code : nat) : bool :=
  match decodeRawProof code with
  | Some derivation => Nat.eqb (rawProofCode derivation) code
  | None => false
  end.

Lemma canonicalRawProofCodeb_spec : forall code,
  canonicalRawProofCodeb code = true <->
  exists derivation,
    decodeRawProof code = Some derivation /\
    rawProofCode derivation = code.
Proof.
  intros code. unfold canonicalRawProofCodeb.
  destruct (decodeRawProof code) as [derivation|] eqn:hdecode.
  - rewrite Nat.eqb_eq. split.
    + intro hcode. exists derivation. split.
      * reflexivity.
      * exact hcode.
    + intros [other [hother hcode]].
      inversion hother. exact hcode.
  - split; [discriminate |].
    intros [derivation [hdecode' _]].
    discriminate.
Qed.

Lemma canonicalRawProofCodeb_quoted : forall derivation,
  canonicalRawProofCodeb (rawProofCode derivation) = true.
Proof.
  intro derivation. apply canonicalRawProofCodeb_spec.
  exists derivation. split.
  - exact (decodeRawProof_rawProofCode derivation).
  - reflexivity.
Qed.

Definition rawStandardProofSupportValue (M : RawPAModel)
    (code : nat) : M :=
  if canonicalRawProofCodeb code
  then rawNumeralValue M 1
  else raw_zero M.

(** A table is exact below the standard bound: support is equivalent to
    being the quotation of some canonical raw proof. *)
Definition RawStandardProofSupportTable (M : RawPAModel) (bound : nat)
    (supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (rawNumeralValue M bound) /\
  forall code,
    rawLt M code (rawNumeralValue M bound) ->
    (rawProofCodeSupported M supportCode supportStep code <->
     exists derivation,
       code = rawQuotedProofCode M derivation /\
       rawProofCode derivation < bound).

Arguments RawStandardProofSupportTable M bound supportCode supportStep
  : clear implicits.

Theorem raw_standardProofSupportTable_exists : forall (M : RawPAModel),
  RawPASatisfies M -> forall bound,
  exists supportCode supportStep,
    RawStandardProofSupportTable M bound supportCode supportStep.
Proof.
  intros M hPA bound.
  destruct (finite_vector_beta_code M hPA bound
    (rawStandardProofSupportValue M)) as
    (supportCode & supportStep & htable).
  exists supportCode, supportStep. split.
  - intros code hcode.
    destruct (raw_lt_numeralValue_cases M hPA code bound hcode) as
      (index & hindex & ->).
    exists (rawStandardProofSupportValue M index).
    exact (htable index hindex).
  - intros code hcode.
    destruct (raw_lt_numeralValue_cases M hPA code bound hcode) as
      (index & hindex & ->).
    specialize (htable index hindex).
    split.
    + intro hsupported.
      unfold rawProofCodeSupported in hsupported.
      assert (hvalue : rawStandardProofSupportValue M index =
          rawNumeralValue M 1).
      {
        symmetry. exact (raw_codedAssignmentLookup_functional M hPA
          supportCode supportStep (rawNumeralValue M index)
          (rawNumeralValue M 1) (rawStandardProofSupportValue M index)
          hsupported htable).
      }
      unfold rawStandardProofSupportValue in hvalue.
      destruct (canonicalRawProofCodeb index) eqn:hcanonical.
      * apply canonicalRawProofCodeb_spec in hcanonical.
        destruct hcanonical as [derivation [hdecode hreencode]].
        exists derivation. split.
        -- rewrite rawQuotedProofCode_standard by exact hPA.
           now rewrite hreencode.
        -- now rewrite hreencode.
      * exfalso.
        change (raw_zero M = raw_succ M (raw_zero M)) in hvalue.
        exact (raw_zero_not_succ_syntax M hPA (raw_zero M) hvalue).
    + intros [derivation [hquoted hderivationBound]].
      rewrite rawQuotedProofCode_standard in hquoted by exact hPA.
      pose proof (rawNumeralValue_injective M hPA
        index (rawProofCode derivation) hquoted) as hindexCode.
      subst index.
      unfold rawProofCodeSupported.
      unfold rawStandardProofSupportValue in htable.
      rewrite canonicalRawProofCodeb_quoted in htable.
      exact htable.
Qed.

Corollary raw_standardProofSupportTable_for_quotation : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  exists supportCode supportStep,
    RawStandardProofSupportTable M (S (rawProofCode derivation))
      supportCode supportStep /\
    rawProofCodeSupported M supportCode supportStep
      (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation.
  destruct (raw_standardProofSupportTable_exists M hPA
    (S (rawProofCode derivation))) as
    (supportCode & supportStep & htable).
  exists supportCode, supportStep. split; [exact htable |].
  destruct htable as [_ hexact].
  assert (hrootBelow : rawLt M (rawQuotedProofCode M derivation)
      (rawNumeralValue M (S (rawProofCode derivation)))).
  {
    rewrite rawQuotedProofCode_standard by exact hPA.
    apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
  }
  apply (proj2 (hexact (rawQuotedProofCode M derivation) hrootBelow)).
  exists derivation. split; [reflexivity | lia].
Qed.

(** Every genuine child of any quoted proof below the common standard bound
    is supported by the same table.  This is the closure fact used by the
    forthcoming standard syntax-row realization. *)
Corollary raw_standardProofSupportTable_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound supportCode supportStep,
  RawStandardProofSupportTable M bound supportCode supportStep ->
  forall derivation child,
  rawProofCode derivation < bound ->
  In child (rawChildren derivation) ->
  rawProofCodeSupported M supportCode supportStep
    (rawQuotedProofCode M child).
Proof.
  intros M hPA bound supportCode supportStep [_ hexact]
    derivation child hbound hchild.
  assert (hchildBound : rawProofCode child < bound).
  {
    exact (Nat.lt_trans _ _ _
      (rawProofCode_child_lt derivation child hchild) hbound).
  }
  assert (hchildBelow : rawLt M (rawQuotedProofCode M child)
      (rawNumeralValue M bound)).
  {
    rewrite rawQuotedProofCode_standard by exact hPA.
    apply raw_lt_numeralValue_of_lt; assumption.
  }
  apply (proj2 (hexact (rawQuotedProofCode M child) hchildBelow)).
  exists child. split; [reflexivity | exact hchildBound].
Qed.

End PABoundedRawCodedProofStandardSupport.
