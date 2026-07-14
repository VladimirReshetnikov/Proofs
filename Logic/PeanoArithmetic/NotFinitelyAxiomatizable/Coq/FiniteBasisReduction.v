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

From Stdlib Require Import List Classical_Prop.
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

(** The stronger Ryll--Nardzewski arithmetic theorem.

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

(** The exact separation statement needed by the finite-basis reduction.
    Mostowski's witness is a canonical consistency sentence, so requiring it
    to be an induction instance would be unnecessarily strong. *)
Definition PAFiniteFragmentStrictness : Prop :=
  forall Delta : list PA.formula,
    (forall delta, In delta Delta -> PA.Formula.Ax_s delta) ->
    exists psi : PA.formula,
      PA.Formula.Sentence psi /\
      PA.Formula.BProv PA.Formula.Ax_s [] psi /\
      ~ PA.Formula.Prov Delta psi.

(** Ordinary syntactic consistency for a finite PA context. *)
Definition ConsistentList (Gamma : list PA.formula) : Prop :=
  ~ PA.Formula.Prov Gamma PA.pBot.

(** Every finite list of genuine PA axioms is consistent.  This follows
    directly from soundness in the standard natural-number model and does not
    require an arithmetized reflection theorem. *)
Theorem PA_finite_fragment_consistent :
  forall Gamma : list PA.formula,
    (forall gamma, In gamma Gamma -> PA.Formula.Ax_s gamma) ->
    ConsistentList Gamma.
Proof.
  intros Gamma hGamma hBot.
  pose proof (PA.Formula.soundness PA.natModel Gamma PA.pBot hBot
    (fun _ => 0)
    (fun gamma hIn =>
      PA.Formula.sat_axiom_s PA.natModel (fun _ => 0) gamma
        (hGamma gamma hIn))) as hFalse.
  exact hFalse.
Qed.

(** The induction-instance version implies exact sentence separation. *)
Theorem finite_fragment_strictness_of_induction_fragment_strictness :
  PAInductionFragmentStrictness -> PAFiniteFragmentStrictness.
Proof.
  intros hStrict Delta hDelta.
  destruct (hStrict Delta hDelta) as [phi hNot].
  exists (PA.Formula.sealPA (PA.Formula.inductionForm phi)).
  split.
  - apply PA.Formula.sealPA_sentence.
  - split.
    + exact (PA.Formula.BProv_ax PA.Formula.Ax_s []
        (PA.Formula.sealPA (PA.Formula.inductionForm phi))
        (PA.Formula.Ax_s_induction phi)).
    + exact hNot.
Qed.

(** The fixed-base step of Mostowski's proof.

    [Base] is a finite PA fragment strong enough for the chosen formalization
    of Goedel II.  Reflection and second incompleteness must refer to exactly
    the same sentence [con T].  For [T = Base ++ Delta], a hypothetical
    [Delta]-proof of [con T] weakens to a [T]-proof of its own consistency. *)
Theorem finite_fragment_strictness_of_mostowski :
  forall (Base : list PA.formula)
      (con : list PA.formula -> PA.formula),
    (forall beta, In beta Base -> PA.Formula.Ax_s beta) ->
    (forall T, PA.Formula.Sentence (con T)) ->
    (forall T,
      (forall theta, In theta T -> PA.Formula.Ax_s theta) ->
      PA.Formula.BProv PA.Formula.Ax_s [] (con T)) ->
    (forall T,
      (forall theta, In theta T -> PA.Formula.Sentence theta) ->
      (forall beta, In beta Base -> In beta T) ->
      ConsistentList T ->
      ~ PA.Formula.Prov T (con T)) ->
    PAFiniteFragmentStrictness.
Proof.
  intros Base con hBase hConSentence hReflect hG2 Delta hDelta.
  set (T := Base ++ Delta).
  assert (hTpa : forall theta, In theta T -> PA.Formula.Ax_s theta).
  {
    intros theta hTheta.
    unfold T in hTheta.
    apply in_app_or in hTheta.
    destruct hTheta as [hTheta | hTheta].
    - exact (hBase theta hTheta).
    - exact (hDelta theta hTheta).
  }
  assert (hTsent : forall theta, In theta T ->
      PA.Formula.Sentence theta).
  {
    intros theta hTheta.
    exact (PA.Formula.sentence_ax_s theta (hTpa theta hTheta)).
  }
  assert (hBaseT : forall beta, In beta Base -> In beta T).
  {
    intros beta hBeta.
    unfold T.
    apply in_or_app. left. exact hBeta.
  }
  assert (hNotT : ~ PA.Formula.Prov T (con T)).
  {
    apply hG2.
    - exact hTsent.
    - exact hBaseT.
    - exact (PA_finite_fragment_consistent T hTpa).
  }
  exists (con T).
  split.
  - exact (hConSentence T).
  - split.
    + exact (hReflect T hTpa).
    + intro hDeltaCon.
      apply hNotT.
      apply (PA.Formula.Prov_weaken Delta (con T) hDeltaCon T).
      intros theta hTheta.
      unfold T.
      apply in_or_app. right. exact hTheta.
Qed.

(** Exact finite-fragment sentence separation excludes a finite basis. *)
Theorem PA_finite_fragment_strictness_excludes_finite_basis :
  PAFiniteFragmentStrictness ->
  ~ HasFiniteFragmentBasis PA.Formula.Ax_s.
Proof.
  intros hStrict [Delta [hDelta hBasis]].
  destruct (hStrict Delta hDelta) as
      [psi [hSentence [hPA hNotProvable]]].
  apply hNotProvable.
  exact (hBasis psi hSentence hPA).
Qed.

(** Exactness of the arithmetic boundary.  In classical logic, failure of a
    finite fragment to be a basis supplies precisely a PA sentence which that
    fragment does not prove. *)
Theorem PA_finite_fragment_strictness_iff_no_finite_basis :
  PAFiniteFragmentStrictness <->
  ~ HasFiniteFragmentBasis PA.Formula.Ax_s.
Proof.
  split.
  - exact PA_finite_fragment_strictness_excludes_finite_basis.
  - intros hNoBasis Delta hDelta.
    destruct (classic (exists psi : PA.formula,
      PA.Formula.Sentence psi /\
      PA.Formula.BProv PA.Formula.Ax_s [] psi /\
      ~ PA.Formula.Prov Delta psi)) as [hMissing | hNoMissing].
    + exact hMissing.
    + exfalso.
      apply hNoBasis.
      exists Delta.
      split.
      * exact hDelta.
      * intros phi hSentence hPA.
        apply NNPP.
        intro hNotProvable.
        apply hNoMissing.
        exists phi.
        repeat split; assumption.
Qed.

(** Strictness immediately excludes a finite fragment basis for PA. *)
Theorem PA_induction_fragment_strictness_excludes_finite_basis :
  PAInductionFragmentStrictness ->
  ~ HasFiniteFragmentBasis PA.Formula.Ax_s.
Proof.
  intro hStrict.
  apply PA_finite_fragment_strictness_excludes_finite_basis.
  exact (finite_fragment_strictness_of_induction_fragment_strictness
    hStrict).
Qed.

(** Mostowski's exact final reduction: arbitrary PA sentence separation is
    sufficient. *)
Theorem peano_arithmetic_not_finitely_axiomatizable_of_fragment_strictness :
  PAFiniteFragmentStrictness ->
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  intros hStrict hFinite.
  apply (PA_finite_fragment_strictness_excludes_finite_basis hStrict).
  apply finite_axiomatization_gives_finite_fragment_basis.
  exact hFinite.
Qed.

(** Consequently the exact finite-fragment separation statement is
    classically equivalent to the advertised theorem. *)
Theorem peano_arithmetic_not_finitely_axiomatizable_iff_fragment_strictness :
  (~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s) <->
  PAFiniteFragmentStrictness.
Proof.
  split.
  - intro hNotFinite.
    apply (proj2 PA_finite_fragment_strictness_iff_no_finite_basis).
    intro hBasis.
    apply hNotFinite.
    apply finite_fragment_basis_gives_finite_axiomatization.
    + exact PA.Formula.sentence_ax_s.
    + exact hBasis.
  - exact peano_arithmetic_not_finitely_axiomatizable_of_fragment_strictness.
Qed.

(** Honest headline reduction.  Once [PAInductionFragmentStrictness] is
    proved, PA's non-finite-axiomatizability follows without any further
    metamathematics. *)
Theorem peano_arithmetic_not_finitely_axiomatizable_of_induction_strictness :
  PAInductionFragmentStrictness ->
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  intro hStrict.
  apply peano_arithmetic_not_finitely_axiomatizable_of_fragment_strictness.
  exact (finite_fragment_strictness_of_induction_fragment_strictness
    hStrict).
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
