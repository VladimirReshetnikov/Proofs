(**
  Positive fixed-level truth schedules and input-certificate totality.

  Formula codes in a nonstandard model of PA cannot be decoded by Rocq
  recursion.  We therefore use the represented numeric prefix invariant
  [RawFixedLevelPositiveTruthBelow] and let PA itself induct on the current
  code.  At a fresh code we inspect the root row of the honest formula-syntax
  traversal supplied by admissibility.  Boolean children have smaller codes
  and are already decided by the prefix hypothesis.  Quantifier rows instead
  use adjacent-level coherence under every represented binder extension.

  The endpoint is reflected back to an exact object-language PA proof for
  every externally fixed input level.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedProofDescent RawCodedSyntaxConstructors
  RawCodedFormulaRankTraversal RawCodedFormulaRankTotality
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelDomainLaws RawCodedFixedLevelTruthAtomicConstruction
  RawCodedFixedLevelTruthBooleanConstruction
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthScheduleInvariant.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthSchedule.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthAtomicConstruction.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthScheduleInvariant.

(** The only nontrivial induction step.  The syntax traversal is used solely
    to expose the constructor of the possibly nonstandard current code.
    Constructor-specific admissibility lemmas re-root atomic adequacy at each
    child and restrict the represented assignment to the smaller child code. *)
Lemma raw_fixedLevelPositiveTruthBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower current,
  RawFixedLevelPositiveTruthBelow M lower current ->
  RawFixedLevelPositiveTruthBelow M lower (raw_succ M current).
Proof.
  intros M hPA lower current hbelow
    root assignmentCode assignmentStep hrootSucc hadmissible.
  destruct (raw_lt_succ_cases M hPA root current hrootSucc)
    as [hrootCurrent | hrootCurrent].
  - exact (hbelow root assignmentCode assignmentStep
      hrootCurrent hadmissible).
  - subst root.
    pose proof hadmissible as hadmissibleFull.
    destruct hadmissible as
      [hatomic [hassignment hinputDomain]].
    destruct hatomic as
      (formulaCode & formulaStep & formulaBound & rootIndex &
       hsyntax & hatomicTerms).
    pose proof hsyntax as hsyntaxParts.
    destruct hsyntaxParts as
      [_ [hrootBelow [hrootLookup hsyntaxRows]]].
    pose proof (hsyntaxRows rootIndex current
      hrootBelow hrootLookup) as hrootRow.
    destruct (raw_codedFormulaSyntaxTraversalRow_shape M
      formulaCode formulaStep rootIndex current hrootRow) as
      (shape & hcurrentCode & hshape).
    destruct shape as
      [eqLeft eqRight
      | (* bottom *)
      | impLeft impRight
      | andLeft andRight
      | orLeft orRight
      | allChild
      | exChild];
      cbn [rawCodedFormulaShapeCode] in hcurrentCode;
      subst current.
    + exact (raw_fixedLevelEq_decides M hPA lower eqLeft eqRight
        assignmentCode assignmentStep hadmissibleFull).
    + exact (raw_fixedLevelBot_decides M hPA lower
        assignmentCode assignmentStep hadmissibleFull).
    + destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
        lower impLeft impRight assignmentCode assignmentStep
        hadmissibleFull) as
        [[hleftAtomic hleftAssignment]
         [hrightAtomic hrightAssignment]].
      assert (hleftAdmissible : RawFixedLevelTruthAdmissible M lower
          impLeft assignmentCode assignmentStep).
      {
        destruct hinputDomain as [hsigmaDomain | hpiDomain].
        - destruct (raw_fixedLevelSigmaDomain_imp M hPA lower
            impLeft impRight hsigmaDomain) as [hleftDomain _].
          exact (conj hleftAtomic
            (conj hleftAssignment (or_intror hleftDomain))).
        - destruct (raw_fixedLevelPiDomain_imp M hPA lower
            impLeft impRight hpiDomain) as [hleftDomain _].
          exact (conj hleftAtomic
            (conj hleftAssignment (or_introl hleftDomain))).
      }
      assert (hrightAdmissible : RawFixedLevelTruthAdmissible M lower
          impRight assignmentCode assignmentStep).
      {
        destruct hinputDomain as [hsigmaDomain | hpiDomain].
        - destruct (raw_fixedLevelSigmaDomain_imp M hPA lower
            impLeft impRight hsigmaDomain) as [_ hrightDomain].
          exact (conj hrightAtomic
            (conj hrightAssignment (or_introl hrightDomain))).
        - destruct (raw_fixedLevelPiDomain_imp M hPA lower
            impLeft impRight hpiDomain) as [_ hrightDomain].
          exact (conj hrightAtomic
            (conj hrightAssignment (or_intror hrightDomain))).
      }
      destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
        (rawFormulaImpCode M impLeft impRight)
        assignmentCode assignmentStep hadmissibleFull)
        as [hsigmaSuccessor hpiSuccessor].
      apply (raw_fixedLevelImp_decides M hPA lower impLeft impRight
        assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
      * exact (hbelow impLeft assignmentCode assignmentStep
          (raw_formulaCodeList3_left_lt M hPA
            (rawNumeralValue M 2) impLeft impRight)
          hleftAdmissible).
      * exact (hbelow impRight assignmentCode assignmentStep
          (raw_formulaCodeList3_right_lt M hPA
            (rawNumeralValue M 2) impLeft impRight)
          hrightAdmissible).
    + destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
        lower andLeft andRight assignmentCode assignmentStep
        hadmissibleFull) as
        [[hleftAtomic hleftAssignment]
         [hrightAtomic hrightAssignment]].
      destruct hinputDomain as [hsigmaDomain | hpiDomain].
      * destruct (raw_fixedLevelSigmaDomain_and M hPA lower
          andLeft andRight hsigmaDomain) as [hleftDomain hrightDomain].
        assert (hleftAdmissible : RawFixedLevelTruthAdmissible M lower
            andLeft assignmentCode assignmentStep)
          by exact (conj hleftAtomic
            (conj hleftAssignment (or_introl hleftDomain))).
        assert (hrightAdmissible : RawFixedLevelTruthAdmissible M lower
            andRight assignmentCode assignmentStep)
          by exact (conj hrightAtomic
            (conj hrightAssignment (or_introl hrightDomain))).
        destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
          (rawFormulaAndCode M andLeft andRight)
          assignmentCode assignmentStep hadmissibleFull)
          as [hsigmaSuccessor hpiSuccessor].
        apply (raw_fixedLevelAnd_decides M hPA lower andLeft andRight
          assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
        -- exact (hbelow andLeft assignmentCode assignmentStep
            (raw_formulaCodeList3_left_lt M hPA
              (rawNumeralValue M 3) andLeft andRight)
            hleftAdmissible).
        -- exact (hbelow andRight assignmentCode assignmentStep
            (raw_formulaCodeList3_right_lt M hPA
              (rawNumeralValue M 3) andLeft andRight)
            hrightAdmissible).
      * destruct (raw_fixedLevelPiDomain_and M hPA lower
          andLeft andRight hpiDomain) as [hleftDomain hrightDomain].
        assert (hleftAdmissible : RawFixedLevelTruthAdmissible M lower
            andLeft assignmentCode assignmentStep)
          by exact (conj hleftAtomic
            (conj hleftAssignment (or_intror hleftDomain))).
        assert (hrightAdmissible : RawFixedLevelTruthAdmissible M lower
            andRight assignmentCode assignmentStep)
          by exact (conj hrightAtomic
            (conj hrightAssignment (or_intror hrightDomain))).
        destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
          (rawFormulaAndCode M andLeft andRight)
          assignmentCode assignmentStep hadmissibleFull)
          as [hsigmaSuccessor hpiSuccessor].
        apply (raw_fixedLevelAnd_decides M hPA lower andLeft andRight
          assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
        -- exact (hbelow andLeft assignmentCode assignmentStep
            (raw_formulaCodeList3_left_lt M hPA
              (rawNumeralValue M 3) andLeft andRight)
            hleftAdmissible).
        -- exact (hbelow andRight assignmentCode assignmentStep
            (raw_formulaCodeList3_right_lt M hPA
              (rawNumeralValue M 3) andLeft andRight)
            hrightAdmissible).
    + destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
        lower orLeft orRight assignmentCode assignmentStep
        hadmissibleFull) as
        [[hleftAtomic hleftAssignment]
         [hrightAtomic hrightAssignment]].
      destruct hinputDomain as [hsigmaDomain | hpiDomain].
      * destruct (raw_fixedLevelSigmaDomain_or M hPA lower
          orLeft orRight hsigmaDomain) as [hleftDomain hrightDomain].
        assert (hleftAdmissible : RawFixedLevelTruthAdmissible M lower
            orLeft assignmentCode assignmentStep)
          by exact (conj hleftAtomic
            (conj hleftAssignment (or_introl hleftDomain))).
        assert (hrightAdmissible : RawFixedLevelTruthAdmissible M lower
            orRight assignmentCode assignmentStep)
          by exact (conj hrightAtomic
            (conj hrightAssignment (or_introl hrightDomain))).
        destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
          (rawFormulaOrCode M orLeft orRight)
          assignmentCode assignmentStep hadmissibleFull)
          as [hsigmaSuccessor hpiSuccessor].
        apply (raw_fixedLevelOr_decides M hPA lower orLeft orRight
          assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
        -- exact (hbelow orLeft assignmentCode assignmentStep
            (raw_formulaCodeList3_left_lt M hPA
              (rawNumeralValue M 4) orLeft orRight)
            hleftAdmissible).
        -- exact (hbelow orRight assignmentCode assignmentStep
            (raw_formulaCodeList3_right_lt M hPA
              (rawNumeralValue M 4) orLeft orRight)
            hrightAdmissible).
      * destruct (raw_fixedLevelPiDomain_or M hPA lower
          orLeft orRight hpiDomain) as [hleftDomain hrightDomain].
        assert (hleftAdmissible : RawFixedLevelTruthAdmissible M lower
            orLeft assignmentCode assignmentStep)
          by exact (conj hleftAtomic
            (conj hleftAssignment (or_intror hleftDomain))).
        assert (hrightAdmissible : RawFixedLevelTruthAdmissible M lower
            orRight assignmentCode assignmentStep)
          by exact (conj hrightAtomic
            (conj hrightAssignment (or_intror hrightDomain))).
        destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
          (rawFormulaOrCode M orLeft orRight)
          assignmentCode assignmentStep hadmissibleFull)
          as [hsigmaSuccessor hpiSuccessor].
        apply (raw_fixedLevelOr_decides M hPA lower orLeft orRight
          assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
        -- exact (hbelow orLeft assignmentCode assignmentStep
            (raw_formulaCodeList3_left_lt M hPA
              (rawNumeralValue M 4) orLeft orRight)
            hleftAdmissible).
        -- exact (hbelow orRight assignmentCode assignmentStep
            (raw_formulaCodeList3_right_lt M hPA
              (rawNumeralValue M 4) orLeft orRight)
            hrightAdmissible).
    + destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
        lower allChild assignmentCode assignmentStep hadmissibleFull)
        as [hchildAtomic _].
      destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
        (rawFormulaAllCode M allChild)
        assignmentCode assignmentStep hadmissibleFull)
        as [hsigmaSuccessor hpiSuccessor].
      pose proof (raw_fixedLevelSigmaDomain_all_successor M hPA lower
        allChild hsigmaSuccessor) as hchildPiDomain.
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all lower M hPA)
        as hcoherence.
      apply (raw_fixedLevelAll_decides_from_lower M hPA lower allChild
        assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
      intros witness newAssignmentCode newAssignmentStep
        hprepend hlowerCertificate.
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          newAssignmentCode newAssignmentStep allChild).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep witness
          (rawFormulaAllCode M allChild)
          newAssignmentCode newAssignmentStep allChild
          hassignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) allChild).
      }
      destruct (hcoherence allChild newAssignmentCode newAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_intror hchildPiDomain)))) as [_ hpi].
      exact (proj1 (hpi hchildPiDomain) hlowerCertificate).
    + destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
        lower exChild assignmentCode assignmentStep hadmissibleFull)
        as [hchildAtomic _].
      destruct (raw_fixedLevelTruthAdmissible_successor_domains M hPA lower
        (rawFormulaExCode M exChild)
        assignmentCode assignmentStep hadmissibleFull)
        as [hsigmaSuccessor hpiSuccessor].
      pose proof (raw_fixedLevelPiDomain_ex_successor M hPA lower
        exChild hpiSuccessor) as hchildSigmaDomain.
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all lower M hPA)
        as hcoherence.
      apply (raw_fixedLevelEx_decides_from_lower M hPA lower exChild
        assignmentCode assignmentStep hsigmaSuccessor hpiSuccessor).
      intros witness newAssignmentCode newAssignmentStep
        hprepend hlowerCertificate.
      assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
          newAssignmentCode newAssignmentStep exChild).
      {
        apply (raw_codedAssignmentPrepend_child_defined M hPA
          assignmentCode assignmentStep witness
          (rawFormulaExCode M exChild)
          newAssignmentCode newAssignmentStep exChild
          hassignment hprepend).
        exact (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) exChild).
      }
      destruct (hcoherence exChild newAssignmentCode newAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_introl hchildSigmaDomain)))) as
        [hsigma _].
      exact (proj1 (hsigma hchildSigmaDomain) hlowerCertificate).
Qed.

(** PA's definable induction crosses every carrier element [current], not
    merely the standard numerals visible to Rocq.  The invariant has no model
    parameters besides [current], so the parameter environment is arbitrary. *)
Theorem raw_fixedLevelPositiveTruthBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower current,
  RawFixedLevelPositiveTruthBelow M lower current.
Proof.
  intros M hPA lower.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := fixedLevelPositiveTruthBelowTermAt lower (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_fixedLevelPositiveTruthBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) lower (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_fixedLevelPositiveTruthBelow_zero M hPA lower).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelPositiveTruthBelowTermAt_iff M
          (scons M current parameterEnv) lower (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_fixedLevelPositiveTruthBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) lower (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelPositiveTruthBelow_succ M hPA lower
        current hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelPositiveTruthBelowTermAt_iff M
      (scons M current parameterEnv) lower (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Choosing [S root] as the terminal prefix includes the requested root. *)
Theorem raw_fixedLevelInputTruthCertificateTotalityAt_all :
  forall inputLevel (M : RawPAModel), RawPASatisfies M ->
    RawFixedLevelInputTruthCertificateTotalityAt M inputLevel.
Proof.
  intros inputLevel M hPA root assignmentCode assignmentStep hadmissible.
  exact (raw_fixedLevelPositiveTruthBelow_all M hPA inputLevel
    (raw_succ M root) root assignmentCode assignmentStep
    (raw_assignment_lt_self_succ M hPA root) hadmissible).
Qed.

(** The older global interface from the totality module is propositionally
    the same decision, with the external input level universally quantified. *)
Theorem raw_fixedLevelInputTruthCertificate_totality :
  forall (M : RawPAModel), RawPASatisfies M ->
    RawFixedLevelInputTruthCertificateTotalityFor M.
Proof.
  intros M hPA inputLevel root assignmentCode assignmentStep hadmissible.
  exact (raw_fixedLevelInputTruthCertificateTotalityAt_all
    inputLevel M hPA root assignmentCode assignmentStep hadmissible).
Qed.

(** ------------------------------------------------------------------
    Exact object-language PA theorem for each external input level. *)

Theorem fixedLevelInputTruthCertificateTotalityFormula_raw_valid :
  forall inputLevel (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel).
Proof.
  intros inputLevel M hPA e.
  apply (proj2
    (raw_sat_fixedLevelInputTruthCertificateTotalityFormula_iff
      M e inputLevel)).
  exact (raw_fixedLevelInputTruthCertificateTotalityAt_all
    inputLevel M hPA).
Qed.

Definition fixedLevelInputTruthCertificateTotalityFormula_closed
    (inputLevel : nat) : formula :=
  Formula.sealPA
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel).

Theorem fixedLevelInputTruthCertificateTotalityFormula_closed_sentence :
  forall inputLevel,
  Formula.Sentence
    (fixedLevelInputTruthCertificateTotalityFormula_closed inputLevel).
Proof.
  intros inputLevel.
  unfold fixedLevelInputTruthCertificateTotalityFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem fixedLevelInputTruthCertificateTotalityFormula_closed_raw_valid :
  forall inputLevel (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelInputTruthCertificateTotalityFormula_closed inputLevel).
Proof.
  intros inputLevel M hPA e.
  unfold fixedLevelInputTruthCertificateTotalityFormula_closed.
  apply (raw_formula_sat_sealPA_of_valid M).
  intros e'.
  exact (fixedLevelInputTruthCertificateTotalityFormula_raw_valid
    inputLevel M hPA e').
Qed.

Theorem PA_proves_fixedLevelInputTruthCertificateTotalityFormula_closed :
  forall inputLevel,
  Formula.BProv Formula.Ax_s []
    (fixedLevelInputTruthCertificateTotalityFormula_closed inputLevel).
Proof.
  intros inputLevel.
  apply PA_BProv_of_raw_valid.
  - exact (fixedLevelInputTruthCertificateTotalityFormula_closed_sentence
      inputLevel).
  - exact (fixedLevelInputTruthCertificateTotalityFormula_closed_raw_valid
      inputLevel).
Qed.

(** Eliminate the mechanical universal closure to recover exactly the public
    three-variable-closed formula from the invariant module. *)
Theorem PA_proves_fixedLevelInputTruthCertificateTotalityFormula :
  forall inputLevel,
  Formula.BProv Formula.Ax_s []
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel).
Proof.
  intros inputLevel.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s []
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel)
    (fun n => n)
    (PA_proves_fixedLevelInputTruthCertificateTotalityFormula_closed
      inputLevel)) as hclosed.
  now rewrite Formula.rename_id in hclosed.
Qed.

End PABoundedRawCodedFixedLevelTruthSchedule.
