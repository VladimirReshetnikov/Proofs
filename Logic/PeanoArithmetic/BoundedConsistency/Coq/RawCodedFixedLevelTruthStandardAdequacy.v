(**
  External standard-formula adequacy for positive fixed-level truth.

  The main nonstandard soundness theorem must reason about model-internal
  formula codes, but the six non-induction axioms of PA are genuine finite
  Rocq formulae.  This module supplies the bridge needed for those six rows:
  a standard formula which is true in the ordinary raw semantics has a Sigma
  certificate one level above every level at which it is admissible.

  The assignment hypothesis deliberately mentions only standard indices.
  Quantifier steps extend the represented assignment through the entire
  parent formula code, so every standard index needed by the child remains
  available.  No model element is decoded anywhere in this proof.
*)

From Stdlib Require Import Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedRankZeroTruthStandardAdequacy
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthConstruction
  RawCodedFixedLevelTruthBooleanConstruction
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthLaws.

Module PABoundedRawCodedFixedLevelTruthStandardAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthStandardAdequacy.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthConstruction.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthLaws.

(** A finite standard-index view of one possibly nonstandard beta table. *)
Definition RawStandardAssignmentRepresents (M : RawPAModel)
    (env : nat -> M) (assignmentCode assignmentStep : M)
    (limit : nat) : Prop :=
  forall index,
    index < limit ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index).

Arguments RawStandardAssignmentRepresents
  M env assignmentCode assignmentStep limit : clear implicits.

Lemma raw_standardAssignmentRepresents_restrict : forall
    (M : RawPAModel) env assignmentCode assignmentStep larger smaller,
  RawStandardAssignmentRepresents M env
    assignmentCode assignmentStep larger ->
  smaller <= larger ->
  RawStandardAssignmentRepresents M env
    assignmentCode assignmentStep smaller.
Proof.
  intros M env assignmentCode assignmentStep larger smaller
    hrep hle index hindex.
  apply hrep. lia.
Qed.

(** Prepending a model element represents [scons] on every standard child
    slot.  The operation's model-internal bound is the parent formula code;
    the elementary subcode inequalities justify every tail lookup. *)
Lemma raw_standardAssignmentRepresents_prepend_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    env assignmentCode assignmentStep child witness
    newAssignmentCode newAssignmentStep,
  RawStandardAssignmentRepresents M env assignmentCode assignmentStep
    (S (formulaCode (pAll child))) ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawQuotedFormulaCode M (pAll child))
    newAssignmentCode newAssignmentStep ->
  RawStandardAssignmentRepresents M (scons M witness env)
    newAssignmentCode newAssignmentStep (S (formulaCode child)).
Proof.
  intros M hPA env assignmentCode assignmentStep child witness
    newAssignmentCode newAssignmentStep hrep hprepend index hindex.
  destruct index as [|index].
  - cbn [rawNumeralValue scons].
    exact (raw_codedAssignmentPrepend_head M
      assignmentCode assignmentStep witness
      (rawQuotedFormulaCode M (pAll child))
      newAssignmentCode newAssignmentStep hprepend).
  - cbn [rawNumeralValue scons].
    apply (raw_codedAssignmentPrepend_tail M
      assignmentCode assignmentStep witness
      (rawQuotedFormulaCode M (pAll child))
      newAssignmentCode newAssignmentStep
      (rawNumeralValue M index) (env index) hprepend).
    + rewrite rawQuotedFormulaCode_standard by exact hPA.
      apply raw_lt_numeralValue_of_lt; [exact hPA |].
      pose proof (formulaCode_all_child_lt child). lia.
    + apply hrep. pose proof (formulaCode_all_child_lt child). lia.
Qed.

Lemma raw_standardAssignmentRepresents_prepend_ex : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    env assignmentCode assignmentStep child witness
    newAssignmentCode newAssignmentStep,
  RawStandardAssignmentRepresents M env assignmentCode assignmentStep
    (S (formulaCode (pEx child))) ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawQuotedFormulaCode M (pEx child))
    newAssignmentCode newAssignmentStep ->
  RawStandardAssignmentRepresents M (scons M witness env)
    newAssignmentCode newAssignmentStep (S (formulaCode child)).
Proof.
  intros M hPA env assignmentCode assignmentStep child witness
    newAssignmentCode newAssignmentStep hrep hprepend index hindex.
  destruct index as [|index].
  - cbn [rawNumeralValue scons].
    exact (raw_codedAssignmentPrepend_head M
      assignmentCode assignmentStep witness
      (rawQuotedFormulaCode M (pEx child))
      newAssignmentCode newAssignmentStep hprepend).
  - cbn [rawNumeralValue scons].
    apply (raw_codedAssignmentPrepend_tail M
      assignmentCode assignmentStep witness
      (rawQuotedFormulaCode M (pEx child))
      newAssignmentCode newAssignmentStep
      (rawNumeralValue M index) (env index) hprepend).
    + rewrite rawQuotedFormulaCode_standard by exact hPA.
      apply raw_lt_numeralValue_of_lt; [exact hPA |].
      pose proof (formulaCode_ex_child_lt child). lia.
    + apply hrep. pose proof (formulaCode_ex_child_lt child). lia.
Qed.

(** Simultaneous truth and falsity adequacy.  Proving both polarities is what
    makes Boolean and quantified negative cases compositional. *)
Theorem raw_fixedLevelTruthCertificate_standard_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall level phi
    env assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawQuotedFormulaCode M phi) assignmentCode assignmentStep ->
  RawStandardAssignmentRepresents M env assignmentCode assignmentStep
    (S (formulaCode phi)) ->
  (raw_formula_sat M env phi ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      (rawQuotedFormulaCode M phi) assignmentCode assignmentStep) /\
  (~ raw_formula_sat M env phi ->
    RawFixedLevelPiFalsityCertificate M (S level)
      (rawQuotedFormulaCode M phi) assignmentCode assignmentStep).
Proof.
  intros M hPA level phi.
  induction phi as [left right | | left IHleft right IHright |
      left IHleft right IHright | left IHleft right IHright |
      child IHchild | child IHchild];
    intros env assignmentCode assignmentStep hadmissible hrep.
  - split; intro hsemantic.
    + apply (raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero
        M hPA level (rawQuotedFormulaCode M (pEq left right))
        assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pEq left right))
          assignmentCode assignmentStep hadmissible)).
      * pose proof
          (raw_rankZeroTruthCertificate_standard_of_assignment
            M hPA env assignmentCode assignmentStep (pEq left right)
            eq_refl hrep) as hcertificate.
        rewrite (rawStandardFormulaTruthValue_of_sat M env
          (pEq left right) hsemantic) in hcertificate.
        exact hcertificate.
    + apply (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero
        M hPA level (rawQuotedFormulaCode M (pEq left right))
        assignmentCode assignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pEq left right))
          assignmentCode assignmentStep hadmissible)).
      * pose proof
          (raw_rankZeroTruthCertificate_standard_of_assignment
            M hPA env assignmentCode assignmentStep (pEq left right)
            eq_refl hrep) as hcertificate.
        rewrite (rawStandardFormulaTruthValue_of_not_sat M env
          (pEq left right) hsemantic) in hcertificate.
        exact hcertificate.
  - split; intro hsemantic.
    + contradiction.
    + apply (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero
        M hPA level (rawQuotedFormulaCode M pBot)
        assignmentCode assignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M pBot)
          assignmentCode assignmentStep hadmissible)).
      * pose proof
          (raw_rankZeroTruthCertificate_standard_of_assignment
            M hPA env assignmentCode assignmentStep pBot
            eq_refl hrep) as hcertificate.
        rewrite (rawStandardFormulaTruthValue_of_not_sat M env
          pBot hsemantic) in hcertificate.
        exact hcertificate.
  - destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA level
      (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
      assignmentCode assignmentStep hadmissible)
      as [hleftAdmissible hrightAdmissible].
    assert (hleftRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode left))).
    { apply (raw_standardAssignmentRepresents_restrict M env
        assignmentCode assignmentStep (S (formulaCode (pImp left right))));
        [exact hrep |].
      pose proof (formulaCode_imp_left_lt left right). lia. }
    assert (hrightRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode right))).
    { apply (raw_standardAssignmentRepresents_restrict M env
        assignmentCode assignmentStep (S (formulaCode (pImp left right))));
        [exact hrep |].
      pose proof (formulaCode_imp_right_lt left right). lia. }
    specialize (IHleft env assignmentCode assignmentStep
      hleftAdmissible hleftRep).
    specialize (IHright env assignmentCode assignmentStep
      hrightAdmissible hrightRep).
    split.
    + intro hsemantic. apply (proj2 (raw_fixedLevelImp_sigma_iff M hPA
        level (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
        assignmentCode assignmentStep hadmissible)).
      destruct (classic (raw_formula_sat M env left)) as [hleft | hnleft].
      * right. apply (proj1 IHright). cbn [raw_formula_sat] in hsemantic.
        exact (hsemantic hleft).
      * left. exact (proj2 IHleft hnleft).
    + intro hsemantic.
      assert (hleft : raw_formula_sat M env left).
      { cbn [raw_formula_sat] in hsemantic. tauto. }
      assert (hnright : ~ raw_formula_sat M env right).
      { cbn [raw_formula_sat] in hsemantic. tauto. }
      apply (raw_fixedLevelImp_pi_of_left_sigma_right_pi M hPA level
        (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
        assignmentCode assignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pImp left right))
          assignmentCode assignmentStep hadmissible)).
      * exact (proj1 IHleft hleft).
      * exact (proj2 IHright hnright).
  - destruct (raw_fixedLevelTruthAdmissible_and_children M hPA level
      (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
      assignmentCode assignmentStep hadmissible)
      as [hleftAdmissible hrightAdmissible].
    assert (hleftRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode left))).
    { eapply raw_standardAssignmentRepresents_restrict; [exact hrep |].
      pose proof (formulaCode_and_left_lt left right). lia. }
    assert (hrightRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode right))).
    { eapply raw_standardAssignmentRepresents_restrict; [exact hrep |].
      pose proof (formulaCode_and_right_lt left right). lia. }
    specialize (IHleft env assignmentCode assignmentStep
      hleftAdmissible hleftRep).
    specialize (IHright env assignmentCode assignmentStep
      hrightAdmissible hrightRep).
    split.
    + intro hsemantic. cbn [raw_formula_sat] in hsemantic.
      apply (proj2 (raw_fixedLevelAnd_sigma_iff M hPA level
        (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
        assignmentCode assignmentStep hadmissible)).
      split; [apply (proj1 IHleft) | apply (proj1 IHright)]; tauto.
    + intro hsemantic. cbn [raw_formula_sat] in hsemantic.
      destruct (classic (raw_formula_sat M env left)) as [hleft | hnleft].
      * apply (raw_fixedLevelAnd_pi_of_right_pi M hPA level
          (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
          assignmentCode assignmentStep).
        -- exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains
             M hPA level (rawQuotedFormulaCode M (pAnd left right))
             assignmentCode assignmentStep hadmissible)).
        -- apply (proj2 IHright). tauto.
      * apply (raw_fixedLevelAnd_pi_of_left_pi M hPA level
          (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
          assignmentCode assignmentStep).
        -- exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains
             M hPA level (rawQuotedFormulaCode M (pAnd left right))
             assignmentCode assignmentStep hadmissible)).
        -- exact (proj2 IHleft hnleft).
  - destruct (raw_fixedLevelTruthAdmissible_or_children M hPA level
      (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
      assignmentCode assignmentStep hadmissible)
      as [hleftAdmissible hrightAdmissible].
    assert (hleftRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode left))).
    { eapply raw_standardAssignmentRepresents_restrict; [exact hrep |].
      pose proof (formulaCode_or_left_lt left right). lia. }
    assert (hrightRep : RawStandardAssignmentRepresents M env
        assignmentCode assignmentStep (S (formulaCode right))).
    { eapply raw_standardAssignmentRepresents_restrict; [exact hrep |].
      pose proof (formulaCode_or_right_lt left right). lia. }
    specialize (IHleft env assignmentCode assignmentStep
      hleftAdmissible hleftRep).
    specialize (IHright env assignmentCode assignmentStep
      hrightAdmissible hrightRep).
    split.
    + intro hsemantic. cbn [raw_formula_sat] in hsemantic.
      apply (proj2 (raw_fixedLevelOr_sigma_iff M hPA level
        (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
        assignmentCode assignmentStep hadmissible)).
      destruct hsemantic as [hleft | hright].
      * left. exact (proj1 IHleft hleft).
      * right. exact (proj1 IHright hright).
    + intro hsemantic. cbn [raw_formula_sat] in hsemantic.
      apply (raw_fixedLevelOr_pi_of_both M hPA level
        (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right)
        assignmentCode assignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pOr left right))
          assignmentCode assignmentStep hadmissible)).
      * apply (proj2 IHleft). tauto.
      * apply (proj2 IHright). tauto.
  - split.
    + intro hsemantic.
      apply (raw_fixedLevelAll_sigma_of_no_lower_pi M hPA level
        (rawQuotedFormulaCode M child) assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pAll child))
          assignmentCode assignmentStep hadmissible)).
      * intros (witness & newAssignmentCode & newAssignmentStep &
          hprepend & hlowerPi).
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          level (rawQuotedFormulaCode M child)
          assignmentCode assignmentStep witness
          newAssignmentCode newAssignmentStep hadmissible hprepend)
          as [hchildAtomic [hchildDefined hchildPiDomain]].
        assert (hchildAdmissible : RawFixedLevelTruthAdmissible M level
            (rawQuotedFormulaCode M child)
            newAssignmentCode newAssignmentStep).
        { repeat split; try assumption. now right. }
        assert (hchildRep : RawStandardAssignmentRepresents M
            (scons M witness env) newAssignmentCode newAssignmentStep
            (S (formulaCode child))).
        { apply (raw_standardAssignmentRepresents_prepend_all M hPA
            env assignmentCode assignmentStep child witness
            newAssignmentCode newAssignmentStep hrep hprepend). }
        pose proof (proj1 (IHchild (scons M witness env)
          newAssignmentCode newAssignmentStep hchildAdmissible hchildRep)
          (hsemantic witness)) as hchildSigma.
        pose proof (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          level M hPA) as hcoherence.
        pose proof (proj2 (hcoherence (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep hchildAdmissible)
          hchildPiDomain) as hpiIff.
        exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive level
          M hPA (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep hchildAdmissible
          hchildSigma (proj1 hpiIff hlowerPi)).
    + intro hsemantic.
      apply not_all_ex_not in hsemantic.
      destruct hsemantic as [witness hchildFalse].
      destruct (raw_codedAssignmentPrepend_exists M hPA
        assignmentCode assignmentStep witness
        (rawQuotedFormulaCode M (pAll child)))
        as [newAssignmentCode [newAssignmentStep hprepend]].
      destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
        level (rawQuotedFormulaCode M child)
        assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep hadmissible hprepend)
        as [hchildAtomic [hchildDefined hchildPiDomain]].
      assert (hchildAdmissible : RawFixedLevelTruthAdmissible M level
          (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep).
      { repeat split; try assumption. now right. }
      assert (hchildRep : RawStandardAssignmentRepresents M
          (scons M witness env) newAssignmentCode newAssignmentStep
          (S (formulaCode child))).
      { apply (raw_standardAssignmentRepresents_prepend_all M hPA
          env assignmentCode assignmentStep child witness
          newAssignmentCode newAssignmentStep hrep hprepend). }
      apply (raw_fixedLevelAll_pi_of_witness M hPA level
        (rawQuotedFormulaCode M child) assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pAll child))
          assignmentCode assignmentStep hadmissible)).
      * exact hprepend.
      * exact (proj2 (IHchild (scons M witness env)
          newAssignmentCode newAssignmentStep hchildAdmissible hchildRep)
          hchildFalse).
  - split.
    + intro hsemantic. cbn [raw_formula_sat] in hsemantic.
      destruct hsemantic as [witness hchildTrue].
      destruct (raw_codedAssignmentPrepend_exists M hPA
        assignmentCode assignmentStep witness
        (rawQuotedFormulaCode M (pEx child)))
        as [newAssignmentCode [newAssignmentStep hprepend]].
      destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
        level (rawQuotedFormulaCode M child)
        assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep hadmissible hprepend)
        as [hchildAtomic [hchildDefined hchildSigmaDomain]].
      assert (hchildAdmissible : RawFixedLevelTruthAdmissible M level
          (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep).
      { repeat split; try assumption. now left. }
      assert (hchildRep : RawStandardAssignmentRepresents M
          (scons M witness env) newAssignmentCode newAssignmentStep
          (S (formulaCode child))).
      { apply (raw_standardAssignmentRepresents_prepend_ex M hPA
          env assignmentCode assignmentStep child witness
          newAssignmentCode newAssignmentStep hrep hprepend). }
      apply (raw_fixedLevelEx_sigma_of_witness M hPA level
        (rawQuotedFormulaCode M child) assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pEx child))
          assignmentCode assignmentStep hadmissible)).
      * exact hprepend.
      * exact (proj1 (IHchild (scons M witness env)
          newAssignmentCode newAssignmentStep hchildAdmissible hchildRep)
          hchildTrue).
    + intro hsemantic.
      apply (raw_fixedLevelEx_pi_of_no_lower_sigma M hPA level
        (rawQuotedFormulaCode M child) assignmentCode assignmentStep).
      * exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          level (rawQuotedFormulaCode M (pEx child))
          assignmentCode assignmentStep hadmissible)).
      * intros (witness & newAssignmentCode & newAssignmentStep &
          hprepend & hlowerSigma).
        destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
          level (rawQuotedFormulaCode M child)
          assignmentCode assignmentStep witness
          newAssignmentCode newAssignmentStep hadmissible hprepend)
          as [hchildAtomic [hchildDefined hchildSigmaDomain]].
        assert (hchildAdmissible : RawFixedLevelTruthAdmissible M level
            (rawQuotedFormulaCode M child)
            newAssignmentCode newAssignmentStep).
        { repeat split; try assumption. now left. }
        assert (hchildRep : RawStandardAssignmentRepresents M
            (scons M witness env) newAssignmentCode newAssignmentStep
            (S (formulaCode child))).
        { apply (raw_standardAssignmentRepresents_prepend_ex M hPA
            env assignmentCode assignmentStep child witness
            newAssignmentCode newAssignmentStep hrep hprepend). }
        assert (hchildFalse : ~ raw_formula_sat M
            (scons M witness env) child).
        { intro htrue. apply hsemantic. exists witness. exact htrue. }
        pose proof (proj2 (IHchild (scons M witness env)
          newAssignmentCode newAssignmentStep hchildAdmissible hchildRep)
          hchildFalse) as hchildPi.
        pose proof (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          level M hPA) as hcoherence.
        pose proof (proj1 (hcoherence (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep hchildAdmissible)
          hchildSigmaDomain) as hsigmaIff.
        exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive level
          M hPA (rawQuotedFormulaCode M child)
          newAssignmentCode newAssignmentStep hchildAdmissible
          (proj1 hsigmaIff hlowerSigma) hchildPi).
Qed.

Corollary raw_fixedLevelSigmaTruthCertificate_standard_of_sat : forall
    (M : RawPAModel), RawPASatisfies M -> forall level phi
    env assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawQuotedFormulaCode M phi) assignmentCode assignmentStep ->
  RawStandardAssignmentRepresents M env assignmentCode assignmentStep
    (S (formulaCode phi)) ->
  raw_formula_sat M env phi ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    (rawQuotedFormulaCode M phi) assignmentCode assignmentStep.
Proof.
  intros M hPA level phi env assignmentCode assignmentStep
    hadmissible hrep hsat.
  exact (proj1 (raw_fixedLevelTruthCertificate_standard_adequacy
    M hPA level phi env assignmentCode assignmentStep hadmissible hrep)
    hsat).
Qed.

End PABoundedRawCodedFixedLevelTruthStandardAdequacy.
