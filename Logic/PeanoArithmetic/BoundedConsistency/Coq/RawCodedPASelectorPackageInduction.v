(**
  Reduction of the uniform proof compiler to package base and successor.

  A selector need not be represented by a deterministic function.  It is
  enough to define a formula saying that a target-code/proof-certificate
  package exists and to prove that this property holds at zero and is closed
  under successor.  PA's definable induction then covers nonstandard levels.

  The two construction laws remain explicit premises.  In particular, the
  current classically selected target-code graph does not itself supply their
  arbitrary-model proofs.  This module therefore isolates a genuine reusable
  induction seam without claiming the proof-package compiler is complete.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPAProvability RawCodedPAUniformProvability.

Import ListNotations.

Module PABoundedRawCodedPASelectorPackageInduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAUniformProvability.

Definition selectorPackageFormula : formula :=
  pEx
    (pAnd
      restrictedPAConsistencyFormulaCodeGraph
      (codedPAProvabilityTermAt (tVar 0))).

Definition RawSelectorPackageAt (M : RawPAModel)
    (tail : nat -> M) (level : M) : Prop :=
  exists target certificate : M,
    raw_formula_sat M
      (scons M target (scons M level tail))
      restrictedPAConsistencyFormulaCodeGraph /\
    RawCodedPAProofOf M target certificate.

Arguments RawSelectorPackageAt M tail level : clear implicits.

Lemma raw_sat_selectorPackageFormula_iff : forall
    (M : RawPAModel) (tail : nat -> M) level,
  raw_formula_sat M (scons M level tail) selectorPackageFormula <->
  RawSelectorPackageAt M tail level.
Proof.
  intros M tail level.
  unfold selectorPackageFormula, RawSelectorPackageAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros [target [hgraph [certificate hproof]]].
    exists target, certificate. split; assumption.
  - intros [target [certificate [hgraph hproof]]].
    exists target. split; [exact hgraph |].
    exists certificate. exact hproof.
Qed.

Definition RawSelectorPackageBase (M : RawPAModel)
    (tail : nat -> M) : Prop :=
  RawSelectorPackageAt M tail (raw_zero M).

Definition RawSelectorPackageSuccessorClosed (M : RawPAModel)
    (tail : nat -> M) : Prop :=
  forall level,
    RawSelectorPackageAt M tail level ->
    RawSelectorPackageAt M tail (raw_succ M level).

Arguments RawSelectorPackageBase M tail : clear implicits.
Arguments RawSelectorPackageSuccessorClosed M tail : clear implicits.

(** This theorem is the reusable nonstandard induction seam.  Once concrete
    raw proof constructors establish the two package laws, no further appeal
    to metatheoretic recursion over levels is needed. *)
Theorem raw_selectorPackages_all_of_base_and_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  RawSelectorPackageBase M tail ->
  RawSelectorPackageSuccessorClosed M tail ->
  forall level, RawSelectorPackageAt M tail level.
Proof.
  intros M hPA tail hbase hstep.
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail) selectorPackageFormula).
  {
    apply (raw_definable_induction M hPA selectorPackageFormula tail).
    - apply (proj2
        (@raw_sat_selectorPackageFormula_iff M tail (raw_zero M))).
      exact hbase.
    - intros level hlevelSat.
      apply (proj2
        (@raw_sat_selectorPackageFormula_iff M tail
          (raw_succ M level))).
      apply hstep.
      exact (proj1
        (@raw_sat_selectorPackageFormula_iff M tail level)
        hlevelSat).
  }
  intro level.
  exact (proj1
    (@raw_sat_selectorPackageFormula_iff M tail level)
    (hall level)).
Qed.

Definition RawSelectorPackageBaseInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M -> forall tail,
    RawSelectorPackageBase M tail.

Definition RawSelectorPackageSuccessorClosedInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M -> forall tail,
    RawSelectorPackageSuccessorClosed M tail.

(** Exact reduction to the two constructor laws.  This is not an
    unconditional compiler theorem: both premises still need syntactic proof
    packages whose checker correctness PA can verify. *)
Theorem raw_restrictedPAConsistencyCompiler_of_package_induction :
  RawSelectorPackageBaseInAllModels ->
  RawSelectorPackageSuccessorClosedInAllModels ->
  RawRestrictedPAConsistencyProvabilityCompilerInAllModels.
Proof.
  intros hbase hstep M hPA tail level.
  exact (@raw_selectorPackages_all_of_base_and_successor M hPA tail
    (hbase M hPA tail) (hstep M hPA tail) level).
Qed.

End PABoundedRawCodedPASelectorPackageInduction.
