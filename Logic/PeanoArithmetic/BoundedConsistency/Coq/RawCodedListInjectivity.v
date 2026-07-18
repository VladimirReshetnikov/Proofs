(**
  Injectivity of arbitrary finite raw list codes in every PA model.

  Several standard-quotation arguments compare a canonical finite proof or
  context code with an alternative constructor view whose fields are carrier
  elements.  Fixed arity lemmas are insufficient for the proof constructors,
  whose rows have up to eight fields.  This module proves the uniform list
  theorem once, directly from the already established injectivity of the
  polynomial list node.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation.

Module PABoundedRawCodedListInjectivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.

Lemma rawListNode_not_zero : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail,
  rawListNode M head tail <> raw_zero M.
Proof.
  intros M hPA head tail heq.
  apply (raw_zero_not_succ_syntax M hPA
    (rawPolynomialPair M head tail)).
  symmetry. exact heq.
Qed.

Theorem rawListCode_injective : forall (M : RawPAModel),
  RawPASatisfies M -> forall xs ys : list M,
  rawListCode M xs = rawListCode M ys -> xs = ys.
Proof.
  intros M hPA xs. induction xs as [|head tail IH]; intros ys hcode;
    destruct ys as [|head' tail']; cbn [rawListCode] in hcode |- *.
  - reflexivity.
  - exfalso. apply (rawListNode_not_zero M hPA head' (rawListCode M tail')).
    symmetry. exact hcode.
  - exfalso. apply (rawListNode_not_zero M hPA head (rawListCode M tail)).
    exact hcode.
  - destruct (rawListNode_injective M hPA
      head (rawListCode M tail) head' (rawListCode M tail') hcode)
      as [hhead htail].
    subst head'. f_equal. exact (IH tail' htail).
Qed.

Corollary rawListCode_cons_injective : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail head' tail',
  rawListCode M (head :: tail) = rawListCode M (head' :: tail') ->
  head = head' /\ tail = tail'.
Proof.
  intros M hPA head tail head' tail' hcode.
  pose proof (rawListCode_injective M hPA
    (head :: tail) (head' :: tail') hcode) as hlist.
  inversion hlist. split; reflexivity.
Qed.

(** A particularly common form compares a canonical numeral list against
    an arbitrary carrier-valued constructor payload. *)
Corollary rawListCode_standard_payload : forall (M : RawPAModel),
  RawPASatisfies M -> forall (standard : list nat) (payload : list M),
  rawListCode M (map (rawNumeralValue M) standard) =
    rawListCode M payload ->
  payload = map (rawNumeralValue M) standard.
Proof.
  intros M hPA standard payload hcode.
  symmetry. exact (rawListCode_injective M hPA
    (map (rawNumeralValue M) standard) payload hcode).
Qed.

End PABoundedRawCodedListInjectivity.
