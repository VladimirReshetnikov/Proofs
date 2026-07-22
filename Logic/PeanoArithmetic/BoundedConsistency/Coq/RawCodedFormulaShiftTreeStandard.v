(**
  Standard formulas embedded into the carrier-valued shift-tree interface.

  A restricted target context contains opaque [RTFCFixed] subformulas.  They
  must still be expanded into individual operation rows when inserted into a
  larger formula trace.  This file turns an ordinary quoted formula into the
  generic finite shift tree while retaining the expected source, target, and
  binder-depth equations.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaShiftTreeRealization.

Module PABoundedRawCodedFormulaShiftTreeStandard.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaShiftTreeRealization.

Fixpoint rawStandardFormulaShiftTree (M : RawPAModel)
    (cutoff amount : nat) (phi : formula) : RawFormulaShiftTree M :=
  match phi with
  | pEq lhs rhs =>
      RFSTEq M (rawNumeralValue M cutoff)
        (rawQuotedTermCode M lhs)
        (rawQuotedTermCode M (standardTermShift cutoff amount lhs))
        (rawQuotedTermCode M rhs)
        (rawQuotedTermCode M (standardTermShift cutoff amount rhs))
  | pBot => RFSTBot M (rawNumeralValue M cutoff)
  | pImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M cutoff)
        (rawStandardFormulaShiftTree M cutoff amount lhs)
        (rawStandardFormulaShiftTree M cutoff amount rhs)
  | pAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M cutoff)
        (rawStandardFormulaShiftTree M cutoff amount lhs)
        (rawStandardFormulaShiftTree M cutoff amount rhs)
  | pOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M cutoff)
        (rawStandardFormulaShiftTree M cutoff amount lhs)
        (rawStandardFormulaShiftTree M cutoff amount rhs)
  | pAll child =>
      RFSTUnary M RFSUAll (rawNumeralValue M cutoff)
        (rawStandardFormulaShiftTree M (S cutoff) amount child)
  | pEx child =>
      RFSTUnary M RFSUEx (rawNumeralValue M cutoff)
        (rawStandardFormulaShiftTree M (S cutoff) amount child)
  end.

Lemma rawStandardFormulaShiftTree_depth : forall M cutoff amount phi,
  rawFormulaShiftTreeDepth M
    (rawStandardFormulaShiftTree M cutoff amount phi) =
  rawNumeralValue M cutoff.
Proof. intros M cutoff amount phi. now destruct phi. Qed.

Lemma rawStandardFormulaShiftTree_source : forall M cutoff amount phi,
  rawFormulaShiftTreeSource M
    (rawStandardFormulaShiftTree M cutoff amount phi) =
  rawQuotedFormulaCode M phi.
Proof.
  intros M cutoff amount phi. revert cutoff.
  induction phi as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro cutoff;
    cbn [rawStandardFormulaShiftTree rawFormulaShiftTreeSource
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawQuotedFormulaCode];
    now rewrite ?IHleft, ?IHright, ?IHchild.
Qed.

Lemma rawStandardFormulaShiftTree_target : forall M cutoff amount phi,
  rawFormulaShiftTreeTarget M
    (rawStandardFormulaShiftTree M cutoff amount phi) =
  rawQuotedFormulaCode M (standardFormulaShift cutoff amount phi).
Proof.
  intros M cutoff amount phi. revert cutoff.
  induction phi as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro cutoff;
    cbn [rawStandardFormulaShiftTree rawFormulaShiftTreeTarget
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawQuotedFormulaCode standardFormulaShift];
    now rewrite ?IHleft, ?IHright, ?IHchild.
Qed.

Theorem rawStandardFormulaShiftTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount phi,
  RawFormulaShiftTreeValid M (rawNumeralValue M amount)
    (rawStandardFormulaShiftTree M cutoff amount phi).
Proof.
  intros M hPA cutoff amount phi. revert cutoff.
  induction phi as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild]; intro cutoff;
    cbn [rawStandardFormulaShiftTree RawFormulaShiftTreeValid
      rawFormulaShiftTreeDepth].
  - split; apply raw_codedTermShift_standard; exact hPA.
  - exact I.
  - repeat split.
    + apply rawStandardFormulaShiftTree_depth.
    + apply rawStandardFormulaShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - repeat split.
    + apply rawStandardFormulaShiftTree_depth.
    + apply rawStandardFormulaShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - repeat split.
    + apply rawStandardFormulaShiftTree_depth.
    + apply rawStandardFormulaShiftTree_depth.
    + apply IHleft.
    + apply IHright.
  - split.
    + rewrite rawStandardFormulaShiftTree_depth. reflexivity.
    + apply IHchild.
  - split.
    + rewrite rawStandardFormulaShiftTree_depth. reflexivity.
    + apply IHchild.
Qed.

(** Re-derive the standard quotation theorem through the generic tree.  This
    endpoint is also a compact integration test for all three tree views. *)
Corollary raw_codedFormulaShift_standard_via_tree : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount phi,
  RawCodedFormulaShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M (standardFormulaShift cutoff amount phi)).
Proof.
  intros M hPA cutoff amount phi.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA
    (rawNumeralValue M amount)
    (rawStandardFormulaShiftTree M cutoff amount phi)
    (rawStandardFormulaShiftTree_valid M hPA cutoff amount phi)) as hshift.
  rewrite rawStandardFormulaShiftTree_depth,
    rawStandardFormulaShiftTree_source,
    rawStandardFormulaShiftTree_target in hshift.
  exact hshift.
Qed.

End PABoundedRawCodedFormulaShiftTreeStandard.
