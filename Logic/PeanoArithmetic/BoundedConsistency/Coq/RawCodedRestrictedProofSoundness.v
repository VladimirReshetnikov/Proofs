(**
  Premise-driven soundness induction for restricted raw proof codes.

  This file deliberately separates the nonstandard induction argument from
  the constructor-specific truth laws.  [RawRestrictedProofRuleTruthSound]
  is the only local semantic seam: later rule modules may discharge it one
  constructor at a time.  Here it always remains an explicit hypothesis.

  A crucial extra premise is endpoint truth admissibility.  The current
  restricted-proof traversal bounds quantifier alternation, but equality
  atoms may still contain arbitrary term payloads.  Consequently neither
  atomic adequacy nor assignment coverage follows from its occurrence-bound
  fields.  Both are bundled explicitly in [RawFixedLevelTruthAdmissible].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedProofConstructors RawCodedProofDescent
  RawCodedProofEndpoints RawCodedProofRules
  RawCodedRestrictedProofTraversal RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelContextTruth.

Import ListNotations.

Module PABoundedRawCodedRestrictedProofSoundness.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.

(** ------------------------------------------------------------------
    The exact constructor-local seam. *)

(** The induction hypothesis exposed to one local rule ranges only over
    fields which are listed as genuine recursive children of a constructor
    occurrence for [root].  Endpoint admissibility is a premise for every
    use, rather than an illicit consequence of quantifier boundedness. *)
Definition RawRestrictedProofRecursiveChildrenSigmaSound
    (M : RawPAModel) (level : nat)
    (root assignmentCode assignmentStep : M) : Prop :=
  forall nodeContext a b c t child1 child2 child3,
    RawProofConstructorCode M
      root nodeContext a b c t child1 child2 child3 ->
  forall fields children,
    In (fields, children)
      (rawProofRecursiveCases M
        nodeContext a b c t child1 child2 child3) ->
    root = rawListCode M fields ->
  forall child,
    In child children ->
  forall childContext childConclusion,
    RawProofRuleValid M child childContext childConclusion ->
    RawFixedLevelTruthAdmissible M level
      childConclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      childContext assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      childConclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofRecursiveChildrenSigmaSound
  M level root assignmentCode assignmentStep : clear implicits.

(** This premise is intentionally model-local and higher order.  It says
    exactly that a valid restricted node preserves Sigma truth once its true
    recursive premises are supplied.  No constructor law is postulated by
    this module. *)
Definition RawRestrictedProofRuleTruthSound
    (M : RawPAModel) (level : nat) : Prop :=
  forall root context conclusion assignmentCode assignmentStep,
    RawRestrictedProof M level root ->
    RawProofRuleValid M root context conclusion ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawRestrictedProofRecursiveChildrenSigmaSound M level
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofRuleTruthSound M level : clear implicits.

(** ------------------------------------------------------------------
    A represented prefix invariant. *)

Lemma raw_restrictedProofSoundness_eval_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) termCode,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 termCode) = raw_term_eval M e termCode.
Proof.
  intros M a b c d f e termCode. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 5) with (S (S (S (S (S index))))) by lia.
  reflexivity.
Qed.

(** Binder order after all five universal quantifiers:
    proof, context, conclusion, assignment code, assignment step. *)
Definition restrictedProofSigmaSoundBelowTermAt
    (level : nat) (current : term) : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (restrictedProofTermAt level (tVar 4))
        (pImp
          (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2))
          (pImp
            (fixedLevelTruthAdmissibleTermAt level
              (tVar 2) (tVar 1) (tVar 0))
            (pImp
              (contextAllSigmaTrueTermAt (S level)
                (tVar 3) (tVar 1) (tVar 0))
              (fixedLevelSigmaTruthCertificateTermAt (S level)
                (tVar 2) (tVar 1) (tVar 0))))))))))).

Definition RawRestrictedProofSigmaSoundBelow
    (M : RawPAModel) (level : nat) (current : M) : Prop :=
  forall proof context conclusion assignmentCode assignmentStep,
    rawLt M proof current ->
    RawRestrictedProof M level proof ->
    RawProofRuleValid M proof context conclusion ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedProofSigmaSoundBelow M level current
  : clear implicits.

Lemma raw_sat_restrictedProofSigmaSoundBelowTermAt_iff : forall
    (M : RawPAModel) e level current,
  raw_formula_sat M e
    (restrictedProofSigmaSoundBelowTermAt level current) <->
  RawRestrictedProofSigmaSoundBelow M level
    (raw_term_eval M e current).
Proof.
  intros M e level current.
  unfold restrictedProofSigmaSoundBelowTermAt,
    RawRestrictedProofSigmaSoundBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_contextAllSigmaTrueTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_restrictedProofSoundness_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedProofSigmaSoundBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofSigmaSoundBelow M level (raw_zero M).
Proof.
  intros M hPA level proof context conclusion assignmentCode assignmentStep
    hproof.
  exfalso. exact (raw_not_lt_zero M hPA proof hproof).
Qed.

(** Recursive-child descent is the only structural fact used in the fresh
    endpoint case.  It converts a child named by the local rule into a
    restricted proof strictly below [current], where [hbelow] applies. *)
Theorem raw_restrictedProofSigmaSoundBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  forall current,
  RawRestrictedProofSigmaSoundBelow M level current ->
  RawRestrictedProofSigmaSoundBelow M level (raw_succ M current).
Proof.
  intros M hPA level hlocal current hbelow
    root context conclusion assignmentCode assignmentStep
    hrootBelow hrestricted hvalid hadmissible hcontext.
  destruct (raw_lt_succ_cases M hPA root current hrootBelow)
    as [hrootCurrent | hrootCurrent].
  - exact (hbelow root context conclusion assignmentCode assignmentStep
      hrootCurrent hrestricted hvalid hadmissible hcontext).
  - subst root.
    apply (hlocal current context conclusion assignmentCode assignmentStep
      hrestricted hvalid hadmissible hcontext).
    intros nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild
      childContext childConclusion hchildValid
      hchildAdmissible hchildContext.
    destruct (raw_restrictedProof_recursive_child M hPA level current
      hrestricted nodeContext a b c t child1 child2 child3 hconstructor
      fields children hentry hfields child hchild)
      as [hchildRestricted hchildBelow].
    exact (hbelow child childContext childConclusion
      assignmentCode assignmentStep hchildBelow hchildRestricted
      hchildValid hchildAdmissible hchildContext).
Qed.

(** PA's own induction crosses nonstandard carrier elements because the
    invariant immediately above is represented by a first-order formula. *)
Theorem raw_restrictedProofSigmaSoundBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  forall current, RawRestrictedProofSigmaSoundBelow M level current.
Proof.
  intros M hPA level hlocal.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := restrictedProofSigmaSoundBelowTermAt level (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_restrictedProofSigmaSoundBelow_zero M hPA level).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
          (scons M current parameterEnv) level (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_restrictedProofSigmaSoundBelow_succ M hPA level
        hlocal current hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
      (scons M current parameterEnv) level (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** ------------------------------------------------------------------
    Root soundness and explicit falsity seams. *)

Theorem raw_restrictedProof_root_sigma_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  forall root context conclusion assignmentCode assignmentStep,
  RawRestrictedProof M level root ->
  RawProofRuleValid M root context conclusion ->
  RawFixedLevelTruthAdmissible M level
    conclusion assignmentCode assignmentStep ->
  RawContextAllSigmaTrue M (S level)
    context assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    conclusion assignmentCode assignmentStep.
Proof.
  intros M hPA level hlocal root context conclusion
    assignmentCode assignmentStep hrestricted hvalid hadmissible hcontext.
  exact (raw_restrictedProofSigmaSoundBelow_all M hPA level hlocal
    (raw_succ M root) root context conclusion assignmentCode assignmentStep
    (raw_assignment_lt_self_succ M hPA root)
    hrestricted hvalid hadmissible hcontext).
Qed.

Definition RawFixedLevelTruthCertificateExclusive
    (M : RawPAModel) (truthLevel : nat) : Prop :=
  forall root assignmentCode assignmentStep,
    RawFixedLevelSigmaTruthCertificate M truthLevel
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M truthLevel
      root assignmentCode assignmentStep ->
    False.

Definition RawFixedLevelBottomPiFalsity
    (M : RawPAModel) (truthLevel : nat) : Prop :=
  forall assignmentCode assignmentStep,
    RawFixedLevelPiFalsityCertificate M truthLevel
      (rawFormulaBotCode M) assignmentCode assignmentStep.

Definition RawFixedLevelSigmaBottomFalse
    (M : RawPAModel) (truthLevel : nat) : Prop :=
  forall assignmentCode assignmentStep,
    RawFixedLevelSigmaTruthCertificate M truthLevel
      (rawFormulaBotCode M) assignmentCode assignmentStep ->
    False.

Lemma raw_fixedLevelSigmaBottomFalse_of_exclusive_pi : forall
    (M : RawPAModel) truthLevel,
  RawFixedLevelTruthCertificateExclusive M truthLevel ->
  RawFixedLevelBottomPiFalsity M truthLevel ->
  RawFixedLevelSigmaBottomFalse M truthLevel.
Proof.
  intros M truthLevel hexclusive hpi assignmentCode assignmentStep hsigma.
  exact (hexclusive (rawFormulaBotCode M) assignmentCode assignmentStep
    hsigma (hpi assignmentCode assignmentStep)).
Qed.

Theorem raw_restrictedProof_bottom_exclusion : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  RawFixedLevelSigmaBottomFalse M (S level) ->
  forall root context assignmentCode assignmentStep,
  RawRestrictedProof M level root ->
  RawProofRuleValid M root context (rawFormulaBotCode M) ->
  RawFixedLevelTruthAdmissible M level
    (rawFormulaBotCode M) assignmentCode assignmentStep ->
  RawContextAllSigmaTrue M (S level)
    context assignmentCode assignmentStep ->
  False.
Proof.
  intros M hPA level hlocal hbottom root context
    assignmentCode assignmentStep hrestricted hvalid
    hadmissible hcontext.
  apply (hbottom assignmentCode assignmentStep).
  exact (raw_restrictedProof_root_sigma_sound M hPA level hlocal
    root context (rawFormulaBotCode M) assignmentCode assignmentStep
    hrestricted hvalid hadmissible hcontext).
Qed.

(** To connect the generic root theorem to a complete restricted-PA proof,
    the witnessed PA context must be made true under some represented
    assignment, and bottom must be admissible under that same assignment.
    This is another explicit semantic input, not a consequence of the
    current traversal certificate. *)
Definition RawRestrictedPAProofTruthInputs
    (M : RawPAModel) (level : nat) : Prop :=
  forall witnessList context,
    RawCodedPAAxiomWitnessContext M witnessList context ->
    exists assignmentCode assignmentStep,
      RawFixedLevelTruthAdmissible M level
        (rawFormulaBotCode M) assignmentCode assignmentStep /\
      RawContextAllSigmaTrue M (S level)
        context assignmentCode assignmentStep.

Arguments RawRestrictedPAProofTruthInputs M level : clear implicits.

Theorem raw_codedRestrictedPAProof_excluded : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  RawRestrictedPAProofTruthInputs M level ->
  RawFixedLevelSigmaBottomFalse M (S level) ->
  forall certificate,
    RawCodedRestrictedPAProof M level certificate -> False.
Proof.
  intros M hPA level hlocal hinputs hbottom certificate
    (witnessList & proof & context & _ & hwitnessed &
      hrestricted & hvalid).
  destruct (hinputs witnessList context hwitnessed)
    as (assignmentCode & assignmentStep & hadmissible & hcontext).
  exact (raw_restrictedProof_bottom_exclusion M hPA level
    hlocal hbottom proof context assignmentCode assignmentStep
    hrestricted hvalid hadmissible hcontext).
Qed.

(** ------------------------------------------------------------------
    A closed PA theorem for the generic induction implication.

    This formula does not encode the higher-order local-rule seam.  It states
    the purely arithmetical induction layer: successor preservation of the
    represented prefix invariant implies that the invariant holds everywhere.
*)

Definition restrictedProofSigmaSoundInductionBodyFormula
    (level : nat) : formula :=
  pImp
    (pAll
      (pImp
        (restrictedProofSigmaSoundBelowTermAt level (tVar 0))
        (restrictedProofSigmaSoundBelowTermAt level (tSucc (tVar 0)))))
    (pAll
      (restrictedProofSigmaSoundBelowTermAt level (tVar 0))).

Lemma raw_sat_restrictedProofSigmaSoundInductionBodyFormula_iff : forall
    (M : RawPAModel) e level,
  raw_formula_sat M e
    (restrictedProofSigmaSoundInductionBodyFormula level) <->
  ((forall current,
      RawRestrictedProofSigmaSoundBelow M level current ->
      RawRestrictedProofSigmaSoundBelow M level (raw_succ M current)) ->
    forall current, RawRestrictedProofSigmaSoundBelow M level current).
Proof.
  intros M e level.
  unfold restrictedProofSigmaSoundInductionBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_restrictedProofSigmaSoundBelowTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition restrictedProofSigmaSoundInductionFormula
    (level : nat) : formula :=
  Formula.sealPA
    (restrictedProofSigmaSoundInductionBodyFormula level).

Theorem restrictedProofSigmaSoundInductionFormula_sentence : forall level,
  Formula.Sentence (restrictedProofSigmaSoundInductionFormula level).
Proof.
  intro level. unfold restrictedProofSigmaSoundInductionFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem restrictedProofSigmaSoundInductionFormula_raw_valid : forall
    level (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (restrictedProofSigmaSoundInductionFormula level).
Proof.
  intros level M hPA e.
  unfold restrictedProofSigmaSoundInductionFormula.
  apply raw_formula_sat_sealPA_of_valid. intro e'.
  apply (proj2
    (raw_sat_restrictedProofSigmaSoundInductionBodyFormula_iff
      M e' level)).
  intros hsucc.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := restrictedProofSigmaSoundBelowTermAt level (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_restrictedProofSigmaSoundBelow_zero M hPA level).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
          (scons M current parameterEnv) level (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) level (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (hsucc current hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_restrictedProofSigmaSoundBelowTermAt_iff M
      (scons M current parameterEnv) level (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem PA_proves_restrictedProofSigmaSoundInductionFormula : forall level,
  Formula.BProv Formula.Ax_s []
    (restrictedProofSigmaSoundInductionFormula level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - apply restrictedProofSigmaSoundInductionFormula_sentence.
  - intros M hPA e.
    exact (restrictedProofSigmaSoundInductionFormula_raw_valid
      level M hPA e).
Qed.

End PABoundedRawCodedRestrictedProofSoundness.
