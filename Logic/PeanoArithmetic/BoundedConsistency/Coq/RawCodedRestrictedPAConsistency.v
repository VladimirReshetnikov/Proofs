(**
  The transparent fixed-level PA consistency sentence.

  This module only packages the nonexistence of the restricted-PA proof
  certificates defined in [RawCodedRestrictedPAProof].  It deliberately does
  not claim that those certificates are impossible.  The genuinely
  nonstandard exclusion statement remains an explicit premise of the final
  assembly theorem.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawModelCompleteness
  RawCodedRestrictedPAProof.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAConsistency.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedRestrictedPAProof.

(** ------------------------------------------------------------------
    Satisfaction of sentences is independent of the ambient assignment.

    The raw-model interface only had a full extensionality lemma requiring
    pointwise-equal assignments.  The two lemmas below record the sharper
    free-variable version needed to open a sealed formula from one arbitrary
    assignment. *)

Lemma raw_term_eval_free_ext : forall (M : RawPAModel) t
    (e e' : nat -> M),
  (forall index, Term.Free index t -> e index = e' index) ->
  raw_term_eval M e t = raw_term_eval M e' t.
Proof.
  intros M t. induction t as
      [index | | child IH | left IHl right IHr | left IHl right IHr];
    intros e e' hagree; cbn [raw_term_eval Term.Free].
  - apply hagree. reflexivity.
  - reflexivity.
  - f_equal. apply IH. exact hagree.
  - rewrite (IHl e e' (fun index hfree =>
        hagree index (or_introl hfree))).
    rewrite (IHr e e' (fun index hfree =>
        hagree index (or_intror hfree))).
    reflexivity.
  - rewrite (IHl e e' (fun index hfree =>
        hagree index (or_introl hfree))).
    rewrite (IHr e e' (fun index hfree =>
        hagree index (or_intror hfree))).
    reflexivity.
Qed.

Lemma raw_formula_sat_free_ext : forall (M : RawPAModel) phi
    (e e' : nat -> M),
  (forall index, Formula.Free index phi -> e index = e' index) ->
  (raw_formula_sat M e phi <-> raw_formula_sat M e' phi).
Proof.
  intros M phi. induction phi as
      [left right | | left IHl right IHr | left IHl right IHr |
       left IHl right IHr | child IH | child IH];
    intros e e' hagree; cbn [raw_formula_sat Formula.Free].
  - rewrite (raw_term_eval_free_ext M left e e'
      (fun index hfree => hagree index (or_introl hfree))).
    rewrite (raw_term_eval_free_ext M right e e'
      (fun index hfree => hagree index (or_intror hfree))).
    reflexivity.
  - reflexivity.
  - rewrite (IHl e e' (fun index hfree =>
        hagree index (or_introl hfree))).
    rewrite (IHr e e' (fun index hfree =>
        hagree index (or_intror hfree))).
    reflexivity.
  - rewrite (IHl e e' (fun index hfree =>
        hagree index (or_introl hfree))).
    rewrite (IHr e e' (fun index hfree =>
        hagree index (or_intror hfree))).
    reflexivity.
  - rewrite (IHl e e' (fun index hfree =>
        hagree index (or_introl hfree))).
    rewrite (IHr e e' (fun index hfree =>
        hagree index (or_intror hfree))).
    reflexivity.
  - split; intros hall value.
    + assert (hshift : forall index,
          Formula.Free index child ->
          scons M value e index = scons M value e' index).
      {
        intros [|index] hfree; cbn [scons].
        - reflexivity.
        - apply hagree. exact hfree.
      }
      exact (proj1 (IH (scons M value e) (scons M value e') hshift)
        (hall value)).
    + assert (hshift : forall index,
          Formula.Free index child ->
          scons M value e index = scons M value e' index).
      {
        intros [|index] hfree; cbn [scons].
        - reflexivity.
        - apply hagree. exact hfree.
      }
      exact (proj2 (IH (scons M value e) (scons M value e') hshift)
        (hall value)).
  - split; intros [value hvalue]; exists value.
    + assert (hshift : forall index,
          Formula.Free index child ->
          scons M value e index = scons M value e' index).
      {
        intros [|index] hfree; cbn [scons].
        - reflexivity.
        - apply hagree. exact hfree.
      }
      exact (proj1 (IH (scons M value e) (scons M value e') hshift)
        hvalue).
    + assert (hshift : forall index,
          Formula.Free index child ->
          scons M value e index = scons M value e' index).
      {
        intros [|index] hfree; cbn [scons].
        - reflexivity.
        - apply hagree. exact hfree.
      }
      exact (proj2 (IH (scons M value e) (scons M value e') hshift)
        hvalue).
Qed.

Corollary raw_formula_sat_sentence_ext : forall
    (M : RawPAModel) phi,
  Formula.Sentence phi -> forall e e' : nat -> M,
  (raw_formula_sat M e phi <-> raw_formula_sat M e' phi).
Proof.
  intros M phi hsentence e e'. apply raw_formula_sat_free_ext.
  intros index hfree. exfalso. exact (hsentence index hfree).
Qed.

(** Package the two directions for [sealPA] while the formula is still an
    abstract variable.  Besides being a useful semantic interface in its own
    right, this avoids asking conversion to normalize the very large concrete
    coded-proof formula when the consistency sentence is opened below. *)
Lemma raw_formula_sat_sealPA_iff_valid : forall
    (M : RawPAModel) phi (e : nat -> M),
  raw_formula_sat M e (Formula.sealPA phi) <->
  forall e' : nat -> M, raw_formula_sat M e' phi.
Proof.
  intros M phi e. split.
  - intro hsealed.
    apply (raw_sealPA_valid_inv M phi).
    intro e'.
    apply (proj1 (raw_formula_sat_sentence_ext M
      (Formula.sealPA phi) (Formula.sealPA_sentence phi) e e')).
    exact hsealed.
  - intro hvalid.
    exact (raw_formula_sat_sealPA_of_valid M phi hvalid e).
Qed.

(** ------------------------------------------------------------------
    Formula and exact arbitrary-model meaning. *)

Definition restrictedPAConsistencyBodyFormula (level : nat) : formula :=
  pAll
    (pImp
      (codedRestrictedPAProofTermAt level (tVar 0))
      pBot).

Definition restrictedPAConsistencyFormula (level : nat) : formula :=
  Formula.sealPA (restrictedPAConsistencyBodyFormula level).

Theorem restrictedPAConsistencyFormula_sentence : forall level,
  Formula.Sentence (restrictedPAConsistencyFormula level).
Proof.
  intro level. unfold restrictedPAConsistencyFormula.
  apply Formula.sealPA_sentence.
Qed.

Lemma raw_sat_restrictedPAConsistencyBodyFormula_iff : forall
    (M : RawPAModel) level (e : nat -> M),
  raw_formula_sat M e (restrictedPAConsistencyBodyFormula level) <->
  forall certificate : M,
    ~ RawCodedRestrictedPAProof M level certificate.
Proof.
  intros M level e.
  unfold restrictedPAConsistencyBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedRestrictedPAProofTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Although [sealPA] makes closure robust against future changes to the
    wrapper implementation, it does not alter the exact model-theoretic
    meaning: satisfaction at any assignment is precisely nonexistence of a
    carrier-level restricted proof certificate. *)
Theorem raw_sat_restrictedPAConsistencyFormula_iff : forall
    (M : RawPAModel) level (e : nat -> M),
  raw_formula_sat M e (restrictedPAConsistencyFormula level) <->
  forall certificate : M,
    ~ RawCodedRestrictedPAProof M level certificate.
Proof.
  intros M level e. unfold restrictedPAConsistencyFormula.
  rewrite raw_formula_sat_sealPA_iff_valid.
  split.
  - intros hvalid certificate.
    exact (proj1
      (raw_sat_restrictedPAConsistencyBodyFormula_iff M level e)
      (hvalid e) certificate).
  - intros hexclusion e'.
    apply (proj2
      (raw_sat_restrictedPAConsistencyBodyFormula_iff M level e')).
    exact hexclusion.
Qed.

(** ------------------------------------------------------------------
    Standard quotation exclusion consequences. *)

Theorem raw_restrictedPAConsistency_excludes_standard_rawProof : forall
    (M : RawPAModel), RawPASatisfies M -> forall level e witnesses derivation,
  raw_formula_sat M e (restrictedPAConsistencyFormula level) ->
  RawProofValid derivation ->
  rawContext derivation = map witnessedAxiom witnesses ->
  rawConclusion derivation = pBot ->
  rawProofOccurrenceRank derivation <= level ->
  False.
Proof.
  intros M hPA level e witnesses derivation hconsistency
    hvalid hcontext hconclusion hbounded.
  pose proof (proj1
    (raw_sat_restrictedPAConsistencyFormula_iff M level e)
    hconsistency) as hexclusion.
  apply (hexclusion
    (PAFiniteBetaCoding.rawNumeralValue M
      (restrictedPAProofCode witnesses derivation))).
  exact (raw_codedRestrictedPAProof_standard M hPA
    level witnesses derivation hvalid hcontext hconclusion hbounded).
Qed.

Theorem raw_restrictedPAConsistency_excludes_standard_provTree : forall
    (M : RawPAModel), RawPASatisfies M -> forall level e witnesses
      (derivation : ProvTree (map witnessedAxiom witnesses) pBot),
  raw_formula_sat M e (restrictedPAConsistencyFormula level) ->
  ProofAllBounded level derivation ->
  False.
Proof.
  intros M hPA level e witnesses derivation hconsistency hbounded.
  pose proof (proj1
    (raw_sat_restrictedPAConsistencyFormula_iff M level e)
    hconsistency) as hexclusion.
  apply (hexclusion
    (PAFiniteBetaCoding.rawNumeralValue M
      (restrictedPAProvTreeCode witnesses derivation))).
  exact (raw_codedRestrictedPAProvTree_standard
    M hPA level witnesses derivation hbounded).
Qed.

(** ------------------------------------------------------------------
    The explicit nonstandard soundness boundary and generic assembly. *)

Definition RawCodedRestrictedPAProofExclusion (level : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M -> forall certificate : M,
    RawCodedRestrictedPAProof M level certificate -> False.

Theorem PA_BProv_restrictedPAConsistencyFormula_of_raw_exclusion :
  forall level,
  RawCodedRestrictedPAProofExclusion level ->
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyFormula level).
Proof.
  intros level hexclusion.
  apply PA_BProv_of_raw_valid.
  - apply restrictedPAConsistencyFormula_sentence.
  - intros M hPA e.
    apply (proj2
      (raw_sat_restrictedPAConsistencyFormula_iff M level e)).
    exact (hexclusion M hPA).
Qed.

End PABoundedRawCodedRestrictedPAConsistency.
