(**
  Accumulator primitives for concatenating fixed-level truth traversals.

  Boolean Tarski clauses often need two independently constructed child
  certificates in one common state table.  This module starts the honest
  concatenation construction.  Its append theorem strengthens the earlier
  root-oriented append operation by returning the full prefix embedding from
  the old tables into the new ones.  That extra data is what preserves every
  previously chosen child root while subsequent traversals are copied after
  it.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedFormulaRankTotality RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing.

Module PABoundedRawCodedFixedLevelTruthConcatenation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.

(** A positive-level table bundle omits a distinguished root: it consists of
    four defined state columns and closure of every live row. *)
Definition RawFixedLevelPositiveTraversalBundle (M : RawPAModel)
    (lower : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : M) : Prop :=
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound /\
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound /\
  RawFixedLevelSuccessorTruthTraversalRows M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound.

Arguments RawFixedLevelPositiveTraversalBundle M lower
  modeCode modeStep formulaCode formulaStep
  assignmentCodeCode assignmentCodeStep
  assignmentStepCode assignmentStepStep bound : clear implicits.

Lemma raw_fixedLevelPositiveTraversalBundle_of_traversal : forall
    (M : RawPAModel) lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound.
Proof.
  intros M lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep [_ [_ hrows]]]]]].
  repeat split; assumption.
Qed.

(** Append one already closed row and retain both the resulting bundle and
    the exact old-prefix embedding.  The proof uses arbitrary-value beta
    append for all four columns and rechecks every old row against the new
    tables; no external finite-vector construction is hidden here. *)
Theorem raw_fixedLevelPositiveTraversalBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode code assignmentCode assignmentStep,
  RawFixedLevelPositiveTraversalBundle M lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound ->
  RawFixedLevelClosedSuccessorRow M lower
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelSigmaTruthCertificate M lower
        child childAssignmentCode childAssignmentStep)
    (fun child childAssignmentCode childAssignmentStep =>
      RawFixedLevelPiFalsityCertificate M lower
        child childAssignmentCode childAssignmentStep)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep : M,
    RawFixedLevelPositiveTraversalBundle M lower
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep (raw_succ M bound) /\
    RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep /\
    RawFixedLevelStateLookup M
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep
      bound mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode code assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined
      [hassignmentCodeDefined [hassignmentStepDefined hrows]]]] hclosed.
  destruct (raw_fixedLevelStateTablesAppend M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode code assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewModeDefined & hnewFormulaDefined &
        hnewAssignmentCodeDefined & hnewAssignmentStepDefined &
        hmodePrefix & hformulaPrefix &
        hassignmentCodePrefix & hassignmentStepPrefix & hnewLookup).
  assert (hext : RawFixedLevelStateTablePrefixExtension M bound
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      newModeCode newModeStep newFormulaCode newFormulaStep
      newAssignmentCodeCode newAssignmentCodeStep
      newAssignmentStepCode newAssignmentStepStep).
  { repeat split; assumption. }
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  split.
  - repeat split; try assumption.
    intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hindex hrowLookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexBound | ->].
    + pose proof (raw_fixedLevelStateLookup_prefix_reflect M hPA bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        index rowMode rowCode rowAssignmentCode rowAssignmentStep
        hmodeDefined hformulaDefined
        hassignmentCodeDefined hassignmentStepDefined
        hext hindexBound hrowLookup) as holdLookup.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound index
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hext (raw_lt_to_le M index bound hindexBound)
        (hrows index rowMode rowCode rowAssignmentCode rowAssignmentStep
          hindexBound holdLookup)).
    + destruct (raw_fixedLevelStateLookup_functional M hPA
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        bound mode code assignmentCode assignmentStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hnewLookup hrowLookup)
        as [hmode [hcode [hassignmentCode hassignmentStep]]].
      subst rowMode. subst rowCode.
      subst rowAssignmentCode. subst rowAssignmentStep.
      exact (raw_fixedLevelClosedSuccessorRow_prefix_extend M hPA
        lower
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        bound bound
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        newModeCode newModeStep newFormulaCode newFormulaStep
        newAssignmentCodeCode newAssignmentCodeStep
        newAssignmentStepCode newAssignmentStepStep
        mode code assignmentCode assignmentStep
        hext (raw_rank_le_refl M hPA bound) hclosed).
  - split; assumption.
Qed.

End PABoundedRawCodedFixedLevelTruthConcatenation.
