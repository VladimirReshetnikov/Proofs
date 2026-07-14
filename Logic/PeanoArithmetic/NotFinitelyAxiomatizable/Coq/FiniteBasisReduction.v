(**
  Finite axiomatizability of Peano arithmetic: the exact reduction.

  The repository's PA development supplies syntax, a finite-context
  first-order calculus [PA.Formula.Prov], and provability from the (infinite)
  PA axiom predicate [PA.Formula.BProv PA.Formula.Ax_s].  It does not
  currently supply the arithmetized metamathematics needed to prove that the
  induction hierarchy is strict.

  This file proves everything around that missing mathematical core:

  - a precise, genuinely deductive notion of finite axiomatizability;
  - every finite axiomatization can be replaced by a finite list of actual
    axioms of the theory;
  - conversely, a finite fragment deriving all consequences is a finite
    axiomatization (for a sentence theory);
  - the standard finite-fragment strictness theorem for induction implies
    that PA is not finitely axiomatizable.

  Crucially, [PAInductionFragmentStrictness] below is a Definition of the
  missing proposition, not an Axiom.  Thus the final implication is honest:
  its kernel assumptions are empty, while its premise records exactly the
  theorem that a complete development must still establish.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.

Import ListNotations.

Module PAFiniteBasisReduction.

(** A finite list [Gamma] is a deductive axiomatization of [B] when its
    ordinary finite-context consequences are exactly the consequences of
    [B].  Requiring sentences rules out treating a formula with implicit free
    parameters as an axiom sentence. *)
Definition DeductivelyFinitelyAxiomatizable
    (B : PA.formula -> Prop) : Prop :=
  exists Gamma : list PA.formula,
    (forall gamma, In gamma Gamma -> PA.Formula.Sentence gamma) /\
    (forall phi, PA.Formula.Sentence phi ->
      PA.Formula.BProv B [] phi <->
      PA.Formula.Prov Gamma phi).

(** A finite fragment basis is stronger on its face: all members of [Delta]
    must literally be axioms of [B], and [Delta] must derive every consequence
    of [B]. *)
Definition HasFiniteFragmentBasis (B : PA.formula -> Prop) : Prop :=
  exists Delta : list PA.formula,
    (forall delta, In delta Delta -> B delta) /\
    (forall phi, PA.Formula.Sentence phi ->
      PA.Formula.BProv B [] phi ->
      PA.Formula.Prov Delta phi).

(** The nontrivial direction: arbitrary finite equivalent axioms can be
    replaced by finitely many actual [B]-axioms.

    Each member of [Gamma] has a [BProv] derivation and hence mentions only a
    finite list of [B]-axioms.  [BProv_bound_list] takes the finite union of
    those witnesses.  A final cut replaces all [Gamma]-assumptions by proofs
    from that one bounded list. *)
Theorem finite_axiomatization_gives_finite_fragment_basis :
  forall B : PA.formula -> Prop,
    DeductivelyFinitelyAxiomatizable B ->
    HasFiniteFragmentBasis B.
Proof.
  intros B [Gamma [hGammaSentences hEquiv]].
  assert (hGamma : forall gamma,
      In gamma Gamma -> PA.Formula.BProv B [] gamma).
  {
    intros gamma hIn.
    apply (proj2 (hEquiv gamma (hGammaSentences gamma hIn))).
    exact (PA.Formula.P_ass Gamma gamma hIn).
  }
  destruct (PA.Formula.BProv_bound_list B [] Gamma hGamma) as
      [Delta [hDelta hGammaFromDelta]].
  exists Delta.
  split.
  - exact hDelta.
  - intros phi hSentence hPhi.
    apply (PA.Formula.Prov_cut Gamma phi
      (proj1 (hEquiv phi hSentence) hPhi) Delta).
    intros gamma hIn.
    specialize (hGammaFromDelta gamma hIn).
    rewrite app_nil_r in hGammaFromDelta.
    exact hGammaFromDelta.
Qed.

(** A finite fragment basis is itself a finite axiomatization whenever [B]
    consists of sentences.  The reverse implication uses [BProv_cut] to
    discharge each literal [B]-axiom in the finite context. *)
Theorem finite_fragment_basis_gives_finite_axiomatization :
  forall B : PA.formula -> Prop,
    PA.Formula.Sentences B ->
    HasFiniteFragmentBasis B ->
    DeductivelyFinitelyAxiomatizable B.
Proof.
  intros B hSentences [Delta [hDelta hBasis]].
  exists Delta.
  split.
  - intros delta hIn.
    exact (hSentences delta (hDelta delta hIn)).
  - intros phi hSentence.
    split.
    + exact (hBasis phi hSentence).
    + intro hProv.
      apply (PA.Formula.BProv_cut B Delta [] phi).
      * exact (PA.Formula.BProv_of_Prov B Delta phi hProv).
      * intros delta hIn.
        exact (PA.Formula.BProv_ax B [] delta (hDelta delta hIn)).
Qed.

(** For sentence theories, "finite equivalent axioms" and "a finite basis
    selected from the original theory" are therefore exactly equivalent. *)
Theorem finite_axiomatizable_iff_has_finite_fragment_basis :
  forall B : PA.formula -> Prop,
    PA.Formula.Sentences B ->
    (DeductivelyFinitelyAxiomatizable B <->
      HasFiniteFragmentBasis B).
Proof.
  intros B hSentences.
  split.
  - apply finite_axiomatization_gives_finite_fragment_basis.
  - apply finite_fragment_basis_gives_finite_axiomatization.
    exact hSentences.
Qed.

(** The exact missing arithmetic/metamathematical theorem.

    It says that no finite list of genuine PA axioms proves every induction
    instance.  Standard proofs establish this via strictness of fragments of
    induction (often using Goedel's second incompleteness theorem).  Neither
    that strictness theorem nor the required arithmetization of syntax is
    currently present in the repository. *)
Definition PAInductionFragmentStrictness : Prop :=
  forall Delta : list PA.formula,
    (forall delta, In delta Delta -> PA.Formula.Ax_s delta) ->
    exists phi : PA.formula,
      ~ PA.Formula.Prov Delta
          (PA.Formula.sealPA (PA.Formula.inductionForm phi)).

(** Strictness immediately excludes a finite fragment basis for PA. *)
Theorem PA_induction_fragment_strictness_excludes_finite_basis :
  PAInductionFragmentStrictness ->
  ~ HasFiniteFragmentBasis PA.Formula.Ax_s.
Proof.
  intros hStrict [Delta [hDelta hBasis]].
  destruct (hStrict Delta hDelta) as [phi hNotProvable].
  apply hNotProvable.
  apply hBasis.
  - apply PA.Formula.sealPA_sentence.
  - exact (PA.Formula.BProv_ax PA.Formula.Ax_s []
      (PA.Formula.sealPA (PA.Formula.inductionForm phi))
      (PA.Formula.Ax_s_induction phi)).
Qed.

(** Honest headline reduction.  Once [PAInductionFragmentStrictness] is
    proved, PA's non-finite-axiomatizability follows without any further
    metamathematics. *)
Theorem peano_arithmetic_not_finitely_axiomatizable_of_induction_strictness :
  PAInductionFragmentStrictness ->
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  intros hStrict hFinite.
  apply (PA_induction_fragment_strictness_excludes_finite_basis hStrict).
  apply finite_axiomatization_gives_finite_fragment_basis.
  exact hFinite.
Qed.

(** PA is a sentence theory, so the generic equivalence specializes without
    any additional premise. *)
Corollary PA_finite_axiomatizable_iff_has_finite_fragment_basis :
  DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s <->
  HasFiniteFragmentBasis PA.Formula.Ax_s.
Proof.
  apply finite_axiomatizable_iff_has_finite_fragment_basis.
  exact PA.Formula.sentence_ax_s.
Qed.

End PAFiniteBasisReduction.
