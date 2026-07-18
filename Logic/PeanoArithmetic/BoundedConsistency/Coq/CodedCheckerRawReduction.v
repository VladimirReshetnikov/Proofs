(**
  Raw-model reduction for the bounded-PA checker sentence.

  The standard-model specification in [CodedCheckerFormula] is not enough
  for an object-language PA proof: a nonstandard model can contain candidate
  certificate codes which are not external natural-number certificates.
  This module records the exact remaining semantic obligation.

  There are three small but important pieces here.

  - [NoRestrictedPAProofFormula_sentence] verifies that the formula passed to
    raw-model completeness is actually closed.  The proof is independent of
    the opaque formula selected by the computability-to-Diophantine bridge:
    the outer substitution sends every variable either to a numeral, to the
    sole certificate variable, or to zero.
  - [raw_NoRestrictedPAProofFormula_iff] unfolds the closed sentence in an
    arbitrary law-free arithmetic structure.  It deliberately does not claim
    that the selected graph formula computes the Rocq checker in that model.
  - [PA_BProv_NoRestrictedPAProofFormula_iff_raw_rejection] combines raw
    soundness and raw-model completeness.  Thus a future fixed-level partial
    truth argument has one precise target: exclude the displayed internal
    graph at every element of every raw PA model.
*)

From Stdlib Require Import List Arith Lia Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedCheckerFormula RawModelCompleteness.

Set Implicit Arguments.

Import ListNotations.

Module PABoundedCodedCheckerRawReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedCheckerFormula.
Import PABoundedRawModelCompleteness.

(** A substitution is [d]-bounded when all variables occurring in every
    substituted term have index strictly below [d]. *)
Definition SubstitutionFreeBelow (d : nat) (sigma : nat -> term) : Prop :=
  forall i k, Term.Free k (sigma i) -> k < d.

Lemma term_free_rename_succ_inv : forall t k,
  Term.Free k (Term.rename S t) ->
  exists j, k = S j /\ Term.Free j t.
Proof.
  induction t as [i | | a IHa | a IHa b IHb | a IHa b IHb];
    cbn; intros k hk.
  - exists i. now split.
  - contradiction.
  - exact (IHa k hk).
  - destruct hk as [hk | hk].
    + destruct (IHa k hk) as [j [hj hfree]].
      exists j. split; [exact hj | now left].
    + destruct (IHb k hk) as [j [hj hfree]].
      exists j. split; [exact hj | now right].
  - destruct hk as [hk | hk].
    + destruct (IHa k hk) as [j [hj hfree]].
      exists j. split; [exact hj | now left].
    + destruct (IHb k hk) as [j [hj hfree]].
      exists j. split; [exact hj | now right].
Qed.

Lemma upSubst_free_below : forall d sigma,
  SubstitutionFreeBelow d sigma ->
  SubstitutionFreeBelow (S d) (Term.upSubst sigma).
Proof.
  intros d sigma hsigma [|i] k hfree.
  - cbn in hfree. subst k. lia.
  - cbn in hfree.
    destruct (term_free_rename_succ_inv hfree)
      as [j [hj hjfree]].
    subst k.
    specialize (hsigma i j hjfree).
    lia.
Qed.

(** Term substitution cannot create a variable outside the common bound of
    the substituted terms. *)
Lemma term_free_subst_below : forall t d sigma k,
  SubstitutionFreeBelow d sigma ->
  Term.Free k (Term.subst sigma t) ->
  k < d.
Proof.
  induction t as [i | | a IHa | a IHa b IHb | a IHa b IHb];
    cbn; intros d sigma k hsigma hfree.
  - exact (hsigma i k hfree).
  - contradiction.
  - exact (IHa d sigma k hsigma hfree).
  - destruct hfree as [hfree | hfree].
    + exact (IHa d sigma k hsigma hfree).
    + exact (IHb d sigma k hsigma hfree).
  - destruct hfree as [hfree | hfree].
    + exact (IHa d sigma k hsigma hfree).
    + exact (IHb d sigma k hsigma hfree).
Qed.

(** Formula substitution has the analogous property.  At a binder the
    lifted substitution is bounded by [S d], exactly matching the shifted
    free-variable index in [Formula.Free]. *)
Lemma formula_free_subst_below : forall phi d sigma k,
  SubstitutionFreeBelow d sigma ->
  Formula.Free k (Formula.subst sigma phi) ->
  k < d.
Proof.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    cbn; intros d sigma k hsigma hfree.
  - destruct hfree as [hfree | hfree].
    + exact (@term_free_subst_below a d sigma k hsigma hfree).
    + exact (@term_free_subst_below b d sigma k hsigma hfree).
  - contradiction.
  - destruct hfree as [hfree | hfree].
    + exact (@IHa d sigma k hsigma hfree).
    + exact (@IHb d sigma k hsigma hfree).
  - destruct hfree as [hfree | hfree].
    + exact (@IHa d sigma k hsigma hfree).
    + exact (@IHb d sigma k hsigma hfree).
  - destruct hfree as [hfree | hfree].
    + exact (@IHa d sigma k hsigma hfree).
    + exact (@IHb d sigma k hsigma hfree).
  - specialize (@IHa (S d) (Term.upSubst sigma) (S k)
      (@upSubst_free_below d sigma hsigma) hfree).
    lia.
  - specialize (@IHa (S d) (Term.upSubst sigma) (S k)
      (@upSubst_free_below d sigma hsigma) hfree).
    lia.
Qed.

Lemma numeral_not_free : forall n k,
  ~ Term.Free k (Term.numeral n).
Proof.
  induction n as [|n IH]; cbn; intros k hfree.
  - exact hfree.
  - exact (IH k hfree).
Qed.

Lemma fixedBoundSubstitution_free_below_one : forall n,
  SubstitutionFreeBelow 1 (fixedBoundSubstitution n).
Proof.
  intros n [|[|i]] k hfree; cbn in hfree.
  - exfalso. exact (@numeral_not_free n k hfree).
  - subst k. lia.
  - contradiction.
Qed.

Theorem NoRestrictedPAProofFormula_sentence : forall n,
  Formula.Sentence (NoRestrictedPAProofFormula n).
Proof.
  intros n k hfree.
  unfold NoRestrictedPAProofFormula in hfree.
  cbn in hfree.
  destruct hfree as [hfree | hfree]; [| contradiction].
  pose proof (@formula_free_subst_below RestrictedPAProofFormula 1
    (fixedBoundSubstitution n) (S k)
    (@fixedBoundSubstitution_free_below_one n) hfree).
  lia.
Qed.

(** The interpretation of an external standard numeral needs no arithmetic
    laws, so we keep this tiny definition local instead of importing the much
    larger beta-coding development. *)
Fixpoint rawStandardNumeral (M : RawPAModel) (n : nat) : M :=
  match n with
  | 0 => raw_zero M
  | S k => raw_succ M (rawStandardNumeral M k)
  end.

Lemma raw_term_eval_standard_numeral : forall
    (M : RawPAModel) (e : nat -> M) n,
  raw_term_eval M e (Term.numeral n) = rawStandardNumeral M n.
Proof.
  intros M e n. induction n; cbn; congruence.
Qed.

(** Environment in which the opaque graph formula is evaluated after the
    outer substitution.  Entries beyond the bound and certificate inputs are
    zero because [fixedBoundSubstitution] normalizes all spare variables. *)
Definition rawRestrictedCheckerEnv (M : RawPAModel)
    (n : nat) (p : M) (k : nat) : M :=
  match k with
  | 0 => rawStandardNumeral M n
  | 1 => p
  | _ => raw_zero M
  end.

Lemma raw_fixedBoundSubstitution_env : forall
    (M : RawPAModel) n (p : M) (e : nat -> M),
  (fun k => raw_term_eval M (scons M p e)
    (fixedBoundSubstitution n k)) =
  @rawRestrictedCheckerEnv M n p.
Proof.
  intros M n p e.
  apply functional_extensionality. intros [|[|k]].
  - cbn [fixedBoundSubstitution rawRestrictedCheckerEnv].
    apply raw_term_eval_standard_numeral.
  - reflexivity.
  - reflexivity.
Qed.

Theorem raw_NoRestrictedPAProofFormula_iff : forall
    (M : RawPAModel) n (e : nat -> M),
  raw_formula_sat M e (NoRestrictedPAProofFormula n) <->
  forall p : M,
    ~ raw_formula_sat M (@rawRestrictedCheckerEnv M n p)
        RestrictedPAProofFormula.
Proof.
  intros M n e.
  unfold NoRestrictedPAProofFormula.
  cbn [raw_formula_sat].
  split.
  - intros hall p hgraph.
    apply (hall p).
    apply (proj2 (raw_formula_sat_subst M RestrictedPAProofFormula
      (fixedBoundSubstitution n) (scons M p e))).
    rewrite raw_fixedBoundSubstitution_env.
    exact hgraph.
  - intros hreject p hsubst.
    apply (hreject p).
    rewrite <- (@raw_fixedBoundSubstitution_env M n p e).
    apply (proj1 (raw_formula_sat_subst M RestrictedPAProofFormula
      (fixedBoundSubstitution n) (scons M p e))).
    exact hsubst.
Qed.

(** This is the genuinely nonstandard obligation.  It is intentionally
    phrased using satisfaction of the chosen graph formula, not evaluation of
    the external Rocq checker. *)
Definition RawRestrictedCheckerRejection (n : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M -> forall p : M,
    ~ raw_formula_sat M (@rawRestrictedCheckerEnv M n p)
        RestrictedPAProofFormula.

Theorem PA_BProv_NoRestrictedPAProofFormula_of_raw_rejection : forall n,
  RawRestrictedCheckerRejection n ->
  Formula.BProv Formula.Ax_s [] (NoRestrictedPAProofFormula n).
Proof.
  intros n hreject.
  apply PA_BProv_of_raw_valid.
  - apply NoRestrictedPAProofFormula_sentence.
  - intros M hPA e.
    apply (proj2 (@raw_NoRestrictedPAProofFormula_iff M n e)).
    exact (hreject M hPA).
Qed.

(** Raw soundness gives the converse, so the nonstandard rejection property
    is not merely a sufficient convenience: for this particular sentence it
    is equivalent to the desired PA theorem. *)
Theorem PA_BProv_NoRestrictedPAProofFormula_iff_raw_rejection : forall n,
  Formula.BProv Formula.Ax_s [] (NoRestrictedPAProofFormula n) <->
  RawRestrictedCheckerRejection n.
Proof.
  intro n. split.
  - intros hproof M hPA p hgraph.
    pose proof (@raw_sat_of_BProv_axs M
      (NoRestrictedPAProofFormula n) hPA hproof
      (fun _ => raw_zero M)) as hsat.
    apply (proj1 (@raw_NoRestrictedPAProofFormula_iff M n
      (fun _ => raw_zero M)) hsat p).
    exact hgraph.
  - apply PA_BProv_NoRestrictedPAProofFormula_of_raw_rejection.
Qed.

End PABoundedCodedCheckerRawReduction.
