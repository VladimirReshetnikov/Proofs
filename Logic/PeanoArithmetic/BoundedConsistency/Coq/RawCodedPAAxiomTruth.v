(**
  Fixed-level truth of transparently witnessed PA axioms.

  The six fixed axioms are standard closed formulae, so their truth follows
  from [RawCodedFixedLevelTruthStandardAdequacy] and the assumption that the
  ambient raw model satisfies PA.  An induction witness may instead contain
  a genuinely nonstandard source-formula code.  Its soundness requires the
  all-level shift/substitution Tarski theorem and PA-definable induction; the
  exact remaining semantic obligation is isolated below as
  [RawFixedLevelPAAxiomInductionSigmaSound].

  The context theorem is otherwise complete.  It synchronizes the witness
  and axiom beta tables row by row and reuses the axiom traversal itself as
  the traversal hidden by [RawContextAllSigmaTrue].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedAssignmentTotality
  RawCodedContextLists RawCodedContextBounds RawCodedContextFunctionality
  RawCodedProofAtomicAdequacy RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelContextTruth
  RawCodedPAAxiomWitness RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthStandardAdequacy.

Module PABoundedRawCodedPAAxiomTruth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthStandardAdequacy.

(** The exact nonstandard induction-schema obligation.  This is a named
    semantic interface, not an axiom: a later theorem supplies a term of this
    type from positive-level operation Tarski transport. *)
Definition RawFixedLevelPAAxiomInductionSigmaSound
    (M : RawPAModel) (level : nat) : Prop :=
  forall source axiom : M,
    RawCodedPAAxiomInduction M source axiom ->
    RawFixedLevelTruthAdmissible M level axiom
      (raw_zero M) (raw_zero M) ->
    RawFixedLevelSigmaTruthCertificate M (S level) axiom
      (raw_zero M) (raw_zero M).

Arguments RawFixedLevelPAAxiomInductionSigmaSound M level : clear implicits.

(** A model-internal zero beta table represents the external all-zero
    environment through every standard finite limit. *)
Lemma raw_standardZeroAssignment_represents : forall
    (M : RawPAModel), RawPASatisfies M -> forall limit,
  RawStandardAssignmentRepresents M (fun _ => raw_zero M)
    (raw_zero M) (raw_zero M) limit.
Proof.
  intros M hPA limit index _.
  exact (raw_codedZeroAssignment_lookup M hPA
    (rawNumeralValue M index)).
Qed.

(** A generic fixed-axiom row.  The membership hypothesis is kept explicit
    so the following seven-way witness theorem can provide each of the six
    disjuncts without duplicating the adequacy argument. *)
Theorem raw_codedPAAxiomFiniteWitness_sigma_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level tag axiomFormula
      witness axiom,
  PA.Formula.Ax_s (Formula.sealPA axiomFormula) ->
  RawCodedPAAxiomFiniteWitness M tag axiomFormula witness axiom ->
  RawFixedLevelTruthAdmissible M level axiom
    (raw_zero M) (raw_zero M) ->
  RawFixedLevelSigmaTruthCertificate M (S level) axiom
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level tag axiomFormula witness axiom haxiom
    [_ ->] hadmissible.
  rewrite <- rawQuotedFormulaCode_standard in hadmissible |- *
    by exact hPA.
  apply (raw_fixedLevelSigmaTruthCertificate_standard_of_sat
    M hPA level (Formula.sealPA axiomFormula)
    (fun _ => raw_zero M) (raw_zero M) (raw_zero M)).
  - exact hadmissible.
  - apply raw_standardZeroAssignment_represents. exact hPA.
  - exact (hPA (Formula.sealPA axiomFormula) haxiom
      (fun _ => raw_zero M)).
Qed.

(** As a useful boundary check, every externally given induction instance
    already follows from standard adequacy.  The unresolved part of the
    interface is therefore precisely a nonstandard source code occurring in
    a nonstandard proof, not the ordinary PA induction schema. *)
Theorem raw_codedPAAxiomInduction_standard_sigma_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level phi,
  RawFixedLevelTruthAdmissible M level
    (rawQuotedFormulaCode M
      (Formula.sealPA (Formula.inductionForm phi)))
    (raw_zero M) (raw_zero M) ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    (rawQuotedFormulaCode M
      (Formula.sealPA (Formula.inductionForm phi)))
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level phi hadmissible.
  apply (raw_fixedLevelSigmaTruthCertificate_standard_of_sat
    M hPA level (Formula.sealPA (Formula.inductionForm phi))
    (fun _ => raw_zero M) (raw_zero M) (raw_zero M));
    [exact hadmissible | |].
  - apply raw_standardZeroAssignment_represents. exact hPA.
  - apply hPA. right; right; right; right; right; right.
    exists phi. reflexivity.
Qed.

(** Every transparent PA witness denotes a true axiom.  All work except the
    nonstandard induction disjunct is discharged here. *)
Theorem raw_codedPAAxiomWitness_sigma_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelPAAxiomInductionSigmaSound M level ->
  forall witness axiom,
  RawCodedPAAxiomWitness M witness axiom ->
  RawFixedLevelTruthAdmissible M level axiom
    (raw_zero M) (raw_zero M) ->
  RawFixedLevelSigmaTruthCertificate M (S level) axiom
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level hinduction witness axiom hwitness hadmissible.
  destruct hwitness as
    [hfinite | [hfinite | [hfinite | [hfinite | [hfinite | [hfinite |
      (source & _ & hinductionWitness)]]]]]].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | left; reflexivity | exact hfinite | exact hadmissible].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | right; left; reflexivity | exact hfinite |
       exact hadmissible].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | right; right; left; reflexivity | exact hfinite |
       exact hadmissible].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | right; right; right; left; reflexivity | exact hfinite |
       exact hadmissible].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | right; right; right; right; left; reflexivity |
       exact hfinite | exact hadmissible].
  - eapply raw_codedPAAxiomFiniteWitness_sigma_zero;
      [exact hPA | right; right; right; right; right; left; reflexivity |
       exact hfinite | exact hadmissible].
  - exact (hinduction source axiom hinductionWitness hadmissible).
Qed.

(** Pointwise admissibility on the concrete head table hidden in a context
    traversal.  Restricted-proof occurrence bounds plus proof-wide atomic
    adequacy supply this predicate at the root endpoint. *)
Definition RawContextAllFixedLevelAdmissibleWithTables (M : RawPAModel)
    (level : nat) (bound headCode headStep : M) : Prop :=
  forall index axiom : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M headCode headStep index axiom ->
    RawFixedLevelTruthAdmissible M level axiom
      (raw_zero M) (raw_zero M).

Arguments RawContextAllFixedLevelAdmissibleWithTables
  M level bound headCode headStep : clear implicits.

(** The table-exposing form is the useful integration theorem: the caller
    may derive admissibility directly on the axiom head table already stored
    in the witnessed-context certificate. *)
Theorem raw_codedPAAxiomWitnessContextWithTables_sigma_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelPAAxiomInductionSigmaSound M level ->
  forall witnessList context bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep,
  RawCodedPAAxiomWitnessContextWithTables M witnessList context bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep ->
  RawContextAllFixedLevelAdmissibleWithTables M level
    bound axiomHeadCode axiomHeadStep ->
  RawContextAllSigmaTrue M (S level) context
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level hinduction witnessList context bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    [hwitnessTraversal [haxiomTraversal hrows]] hadmissible.
  exists bound, axiomTailCode, axiomTailStep, axiomHeadCode, axiomHeadStep.
  split; [exact haxiomTraversal |].
  intros index hindex axiom haxiomLookup.
  destruct hwitnessTraversal as [_ [_ [hwitnessDefined _]]].
  destruct (hwitnessDefined index hindex) as [witness hwitnessLookup].
  apply (raw_codedPAAxiomWitness_sigma_zero M hPA level hinduction
    witness axiom).
  - exact (hrows index witness axiom hindex
      hwitnessLookup haxiomLookup).
  - exact (hadmissible index axiom hindex haxiomLookup).
Qed.

(** Public witnessed contexts existentially hide their synchronized tables.
    The admissibility premise therefore quantifies over every such package;
    this avoids any choice of a model-internal traversal in the statement. *)
Definition RawCodedPAAxiomWitnessContextAdmissible
    (M : RawPAModel) (level : nat)
    (witnessList context : M) : Prop :=
  forall bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep,
  RawCodedPAAxiomWitnessContextWithTables M witnessList context bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep ->
  RawContextAllFixedLevelAdmissibleWithTables M level
    bound axiomHeadCode axiomHeadStep.

Arguments RawCodedPAAxiomWitnessContextAdmissible
  M level witnessList context : clear implicits.

(** Public context membership can be transported into the independently
    hidden traversal used by proof-wide atomic adequacy. *)
Lemma raw_contextAllAtomicallyAdequate_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall context axiom,
  RawContextAllAtomicallyAdequate M context ->
  RawContextListMember M context axiom ->
  RawCodedFormulaAtomicallyAdequate M axiom.
Proof.
  intros M hPA context axiom
    (bound & tailCode & tailStep & headCode & headStep &
     htraversal & hall) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    context axiom bound tailCode tailStep headCode headStep htraversal)
    hmember) as [index [hindex hlookup]].
  exact (hall index hindex axiom hlookup).
Qed.

Lemma raw_contextAllBounded_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall level context axiom,
  RawContextAllBounded M level context ->
  RawContextListMember M context axiom ->
  RawFormulaQuantifierBounded M level axiom.
Proof.
  intros M hPA level context axiom
    (bound & tailCode & tailStep & headCode & headStep &
     htraversal & hall) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    context axiom bound tailCode tailStep headCode headStep htraversal)
    hmember) as hmemberWithTables.
  exact (raw_contextAllBoundedWithTables_member M level
    bound headCode headStep axiom hall hmemberWithTables).
Qed.

(** This is the integration lemma used by restricted-proof soundness.  The
    endpoint's all-occurrence rank bound and proof-wide atomic certificate
    imply exactly the rowwise admissibility predicate above; the zero beta
    assignment supplies every (including nonstandard) variable index. *)
Theorem raw_codedPAAxiomWitnessContext_admissible_of_bounded_atomic : forall
    (M : RawPAModel), RawPASatisfies M -> forall level witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextAllBounded M level context ->
  RawContextAllAtomicallyAdequate M context ->
  RawCodedPAAxiomWitnessContextAdmissible M level witnessList context.
Proof.
  intros M hPA level witnessList context _ hbounded hatomic
    bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    [_ [haxiomTraversal _]] index axiom hindex hlookup.
  assert (hmember : RawContextListMember M context axiom).
  {
    apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      context axiom bound axiomTailCode axiomTailStep
      axiomHeadCode axiomHeadStep haxiomTraversal)).
    exists index. split; assumption.
  }
  repeat split.
  - exact (raw_contextAllAtomicallyAdequate_member M hPA
      context axiom hatomic hmember).
  - exact (raw_codedZeroAssignment_defined_all M hPA axiom).
  - exact (raw_contextAllBounded_member M hPA
      level context axiom hbounded hmember).
Qed.

Theorem raw_codedPAAxiomWitnessContext_sigma_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelPAAxiomInductionSigmaSound M level ->
  forall witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPAAxiomWitnessContextAdmissible M level witnessList context ->
  RawContextAllSigmaTrue M (S level) context
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level hinduction witnessList context
    (bound & witnessTailCode & witnessTailStep & witnessHeadCode &
     witnessHeadStep & axiomTailCode & axiomTailStep & axiomHeadCode &
     axiomHeadStep & htables) hadmissible.
  eapply raw_codedPAAxiomWitnessContextWithTables_sigma_zero;
    [exact hPA | exact hinduction | exact htables |].
  exact (hadmissible bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep htables).
Qed.

Corollary raw_codedPAAxiomWitnessContext_sigma_zero_of_bounded_atomic :
    forall (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelPAAxiomInductionSigmaSound M level ->
  forall witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextAllBounded M level context ->
  RawContextAllAtomicallyAdequate M context ->
  RawContextAllSigmaTrue M (S level) context
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA level hinduction witnessList context
    hwitnessed hbounded hatomic.
  apply (raw_codedPAAxiomWitnessContext_sigma_zero M hPA level hinduction
    witnessList context hwitnessed).
  exact (raw_codedPAAxiomWitnessContext_admissible_of_bounded_atomic
    M hPA level witnessList context hwitnessed hbounded hatomic).
Qed.

End PABoundedRawCodedPAAxiomTruth.
