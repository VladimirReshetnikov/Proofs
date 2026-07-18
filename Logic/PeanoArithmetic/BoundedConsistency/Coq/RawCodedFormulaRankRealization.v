(**
  Model-internal functionality and the exact realization boundary for coded
  formula ranks.

  A carrier element of a nonstandard PA model need not be the code of any
  formula constructor.  Consequently the unrestricted assertion that every
  carrier element has a rank certificate is not the right totality theorem.
  This file instead proves the nontrivial half which *is* unconditional:
  any two certificates for the same (possibly nonstandard) root have the
  same Sigma/Pi output.

  The proof uses a genuine instance of PA induction.  Its induction measure
  is the designated root-row index of the first traversal.  Each recursive
  child of that traversal occurs at a strictly smaller index; the second
  traversal may use completely unrelated tables and indices.  Thus the
  argument compares arbitrary nonstandard certificates without decoding
  their roots in Coq's meta-theory.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAssignment
  RawCodedFormulaRankStepFunctionality RawCodedFormulaRankTraversal.

Import ListNotations.

Module PABoundedRawCodedFormulaRankRealization.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStepFunctionality.
Import PABoundedRawCodedFormulaRankTraversal.

Lemma raw_rankRealization_eval_liftTerm_thirteen : forall
    (M : RawPAModel) a b c d f g h i j k l m n
    (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M m
          (scons M n e)))))))))))))
    (liftTerm 13 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l m n e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 13) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))
    by lia.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    A first-order induction invariant.

    Thirteen universal binders, from outermost to innermost, stand for

      formulaCode, formulaStep, sigmaCode, sigmaStep, piCode, piStep,
      bound, rootIndex, root, sigma, pi, otherSigma, otherPi.

    At the body they therefore occupy variables 12 down to 0.  [current]
    is lifted past the whole block.  Keeping this invariant as an actual PA
    formula is essential: meta-level induction on the carrier of a raw model
    would be invalid for nonstandard elements.
*)

Definition rankRealizationAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

Definition rankRealizationAll13 (body : formula) : formula :=
  pAll (rankRealizationAll4
    (rankRealizationAll4 (rankRealizationAll4 body))).

Definition codedFormulaRankIndexFunctionalBelowTermAt
    (current : term) : formula :=
  rankRealizationAll13
    (pImp
      (Formula.ltTermAt (tVar 5) (liftTerm 13 current))
      (pImp
        (codedFormulaRankTraversalTermAt
          (tVar 12) (tVar 11) (tVar 10) (tVar 9)
          (tVar 8) (tVar 7) (tVar 6) (tVar 5)
          (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (codedFormulaRankTermAt (tVar 4) (tVar 1) (tVar 0))
          (pAnd (pEq (tVar 3) (tVar 1))
            (pEq (tVar 2) (tVar 0)))))).

Definition RawCodedFormulaRankIndexFunctionalBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi otherSigma otherPi : M,
    rawLt M rootIndex current ->
    RawCodedFormulaRankTraversal M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi ->
    RawCodedFormulaRank M root otherSigma otherPi ->
    sigma = otherSigma /\ pi = otherPi.

Arguments RawCodedFormulaRankIndexFunctionalBelow M current
  : clear implicits.

Lemma raw_sat_codedFormulaRankIndexFunctionalBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedFormulaRankIndexFunctionalBelowTermAt current) <->
  RawCodedFormulaRankIndexFunctionalBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedFormulaRankIndexFunctionalBelowTermAt,
    rankRealizationAll13, rankRealizationAll4,
    RawCodedFormulaRankIndexFunctionalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTraversalTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  repeat setoid_rewrite raw_rankRealization_eval_liftTerm_thirteen.
  cbn [raw_term_eval scons].
  split; intros h formulaCode formulaStep sigmaCode sigmaStep
    piCode piStep bound rootIndex root sigma pi otherSigma otherPi;
    exact (h formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi otherSigma otherPi).
Qed.

(** Extract a public rank certificate for a recursive row.  This small
    wrapper records the transitivity step from [childIndex < rootIndex] and
    [rootIndex < bound], which is needed before the traversal restriction
    theorem can expose the child. *)
Lemma raw_rank_child_certificate : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  forall childIndex child childSigma childPi,
    rawLt M childIndex rootIndex ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      childIndex child childSigma childPi ->
    RawCodedFormulaRank M child childSigma childPi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal
    childIndex child childSigma childPi hchild hlookup.
  pose proof htraversal as hfacts.
  destruct hfacts as [_ [_ [_ [hrootBound _]]]].
  assert (hchildBound : rawLt M childIndex bound).
  {
    exact (raw_assignment_lt_trans M hPA
      childIndex rootIndex bound hchild hrootBound).
  }
  exact (raw_codedFormulaRank_of_traversal_row M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal
    childIndex child childSigma childPi hchildBound hlookup).
Qed.

(** The successor step of the induction invariant.  The large proof is
    structural only at the seven constructor shapes.  Constructor-code
    injectivity identifies the corresponding children of the two unrelated
    traversals; the induction hypothesis then identifies their ranks. *)
Theorem raw_codedFormulaRankIndexFunctionalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current,
    RawCodedFormulaRankIndexFunctionalBelow M current ->
    RawCodedFormulaRankIndexFunctionalBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi otherSigma otherPi
    hrootIndex hleftTraversal hrightRank.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent formulaCode formulaStep sigmaCode sigmaStep
      piCode piStep bound rootIndex root sigma pi otherSigma otherPi
      hbefore hleftTraversal hrightRank).
  - subst rootIndex.
    destruct hrightRank as
      (rightFormulaCode & rightFormulaStep &
       rightSigmaCode & rightSigmaStep & rightPiCode & rightPiStep &
       rightBound & rightRootIndex & hrightTraversal).
    pose proof (raw_codedFormulaRankTraversal_root_row M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound current root sigma pi hleftTraversal) as hleftRow.
    pose proof (raw_codedFormulaRankTraversal_root_row M
      rightFormulaCode rightFormulaStep rightSigmaCode rightSigmaStep
      rightPiCode rightPiStep rightBound rightRootIndex
      root otherSigma otherPi hrightTraversal) as hrightRow.
    apply raw_codedFormulaRankTraversalRow_shape_iff in hleftRow.
    apply raw_codedFormulaRankTraversalRow_shape_iff in hrightRow.
    destruct hleftRow as [leftShape [hleftCode hleftRank]].
    destruct hrightRow as [rightShape [hrightCode hrightRank]].
    assert (hshape : leftShape = rightShape).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      rewrite <- hleftCode, <- hrightCode. reflexivity.
    }
    subst rightShape.
    destruct leftShape as
      [eqLeft eqRight
      | (* bottom *)
      | impLeft impRight
      | andLeft andRight
      | orLeft orRight
      | allChild
      | exChild];
      cbn [RawCodedFormulaShapeRankRow] in hleftRank, hrightRank.
    + exact (raw_formulaRankZero_functional M
        sigma pi otherSigma otherPi hleftRank hrightRank).
    + exact (raw_formulaRankZero_functional M
        sigma pi otherSigma otherPi hleftRank hrightRank).
    + destruct hleftRank as
        (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hleftEq).
      destruct hrightRank as
        (otherLeftIndex & otherLeftSigma & otherLeftPi &
         otherRightIndex & otherRightSigma & otherRightPi &
         hotherLeftIndex & hotherLeftLookup &
         hotherRightIndex & hotherRightLookup & hrightEq).
      assert (hleftChild : leftSigma = otherLeftSigma /\
          leftPi = otherLeftPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M leftIndex) leftIndex
          impLeft leftSigma leftPi otherLeftSigma otherLeftPi hleftIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            leftIndex impLeft leftSigma leftPi
            (raw_assignment_lt_trans M hPA leftIndex current bound
              hleftIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hleftLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherLeftIndex impLeft
            otherLeftSigma otherLeftPi hotherLeftIndex hotherLeftLookup).
      }
      assert (hrightChild : rightSigma = otherRightSigma /\
          rightPi = otherRightPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M rightIndex) rightIndex
          impRight rightSigma rightPi otherRightSigma otherRightPi
          hrightIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            rightIndex impRight rightSigma rightPi
            (raw_assignment_lt_trans M hPA rightIndex current bound
              hrightIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hrightLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherRightIndex impRight
            otherRightSigma otherRightPi hotherRightIndex hotherRightLookup).
      }
      destruct hleftChild as [-> ->].
      destruct hrightChild as [-> ->].
      exact (raw_formulaRankImp_functional M hPA
        sigma pi otherSigma otherPi
        otherLeftSigma otherLeftPi otherRightSigma otherRightPi
        hleftEq hrightEq).
    + destruct hleftRank as
        (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hleftEq).
      destruct hrightRank as
        (otherLeftIndex & otherLeftSigma & otherLeftPi &
         otherRightIndex & otherRightSigma & otherRightPi &
         hotherLeftIndex & hotherLeftLookup &
         hotherRightIndex & hotherRightLookup & hrightEq).
      assert (hleftChild : leftSigma = otherLeftSigma /\
          leftPi = otherLeftPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M leftIndex) leftIndex
          andLeft leftSigma leftPi otherLeftSigma otherLeftPi hleftIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            leftIndex andLeft leftSigma leftPi
            (raw_assignment_lt_trans M hPA leftIndex current bound
              hleftIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hleftLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherLeftIndex andLeft
            otherLeftSigma otherLeftPi hotherLeftIndex hotherLeftLookup).
      }
      assert (hrightChild : rightSigma = otherRightSigma /\
          rightPi = otherRightPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M rightIndex) rightIndex
          andRight rightSigma rightPi otherRightSigma otherRightPi
          hrightIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            rightIndex andRight rightSigma rightPi
            (raw_assignment_lt_trans M hPA rightIndex current bound
              hrightIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hrightLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherRightIndex andRight
            otherRightSigma otherRightPi hotherRightIndex hotherRightLookup).
      }
      destruct hleftChild as [-> ->].
      destruct hrightChild as [-> ->].
      exact (raw_formulaRankAndOr_functional M hPA
        sigma pi otherSigma otherPi
        otherLeftSigma otherLeftPi otherRightSigma otherRightPi
        hleftEq hrightEq).
    + destruct hleftRank as
        (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hleftEq).
      destruct hrightRank as
        (otherLeftIndex & otherLeftSigma & otherLeftPi &
         otherRightIndex & otherRightSigma & otherRightPi &
         hotherLeftIndex & hotherLeftLookup &
         hotherRightIndex & hotherRightLookup & hrightEq).
      assert (hleftChild : leftSigma = otherLeftSigma /\
          leftPi = otherLeftPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M leftIndex) leftIndex
          orLeft leftSigma leftPi otherLeftSigma otherLeftPi hleftIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            leftIndex orLeft leftSigma leftPi
            (raw_assignment_lt_trans M hPA leftIndex current bound
              hleftIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hleftLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherLeftIndex orLeft
            otherLeftSigma otherLeftPi hotherLeftIndex hotherLeftLookup).
      }
      assert (hrightChild : rightSigma = otherRightSigma /\
          rightPi = otherRightPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M rightIndex) rightIndex
          orRight rightSigma rightPi otherRightSigma otherRightPi
          hrightIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            rightIndex orRight rightSigma rightPi
            (raw_assignment_lt_trans M hPA rightIndex current bound
              hrightIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hrightLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherRightIndex orRight
            otherRightSigma otherRightPi hotherRightIndex hotherRightLookup).
      }
      destruct hleftChild as [-> ->].
      destruct hrightChild as [-> ->].
      exact (raw_formulaRankAndOr_functional M hPA
        sigma pi otherSigma otherPi
        otherLeftSigma otherLeftPi otherRightSigma otherRightPi
        hleftEq hrightEq).
    + destruct hleftRank as
        (childIndex & childSigma & childPi &
         hchildIndex & hchildLookup & hleftEq).
      destruct hrightRank as
        (otherChildIndex & otherChildSigma & otherChildPi &
         hotherChildIndex & hotherChildLookup & hrightEq).
      assert (hchild : childSigma = otherChildSigma /\
          childPi = otherChildPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M childIndex) childIndex
          allChild childSigma childPi otherChildSigma otherChildPi
          hchildIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            childIndex allChild childSigma childPi
            (raw_assignment_lt_trans M hPA childIndex current bound
              hchildIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hchildLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherChildIndex allChild
            otherChildSigma otherChildPi hotherChildIndex hotherChildLookup).
      }
      destruct hchild as [-> ->].
      exact (raw_formulaRankAll_functional M hPA
        sigma pi otherSigma otherPi otherChildSigma otherChildPi
        hleftEq hrightEq).
    + destruct hleftRank as
        (childIndex & childSigma & childPi &
         hchildIndex & hchildLookup & hleftEq).
      destruct hrightRank as
        (otherChildIndex & otherChildSigma & otherChildPi &
         hotherChildIndex & hotherChildLookup & hrightEq).
      assert (hchild : childSigma = otherChildSigma /\
          childPi = otherChildPi).
      {
        apply (hcurrent formulaCode formulaStep sigmaCode sigmaStep
          piCode piStep (raw_succ M childIndex) childIndex
          exChild childSigma childPi otherChildSigma otherChildPi
          hchildIndex).
        - exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
            formulaCode formulaStep sigmaCode sigmaStep piCode piStep
            bound current root sigma pi hleftTraversal
            childIndex exChild childSigma childPi
            (raw_assignment_lt_trans M hPA childIndex current bound
              hchildIndex
              (proj1 (proj2 (proj2 (proj2 hleftTraversal)))))
            hchildLookup).
        - exact (raw_rank_child_certificate M hPA
            rightFormulaCode rightFormulaStep
            rightSigmaCode rightSigmaStep rightPiCode rightPiStep
            rightBound rightRootIndex root otherSigma otherPi
            hrightTraversal otherChildIndex exChild
            otherChildSigma otherChildPi hotherChildIndex hotherChildLookup).
      }
      destruct hchild as [-> ->].
      exact (raw_formulaRankEx_functional M hPA
        sigma pi otherSigma otherPi otherChildSigma otherChildPi
        hleftEq hrightEq).
Qed.

(** PA induction supplies the invariant at every, including nonstandard,
    row index. *)
Theorem raw_codedFormulaRankIndexFunctionalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current,
    RawCodedFormulaRankIndexFunctionalBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaRankIndexFunctionalBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedFormulaRankIndexFunctionalBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex root sigma pi otherSigma otherPi hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedFormulaRankIndexFunctionalBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedFormulaRankIndexFunctionalBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedFormulaRankIndexFunctionalBelow_succ M hPA
        current hraw).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaRankIndexFunctionalBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** Main result: the previously isolated cross-certificate functionality
    seam is discharged for every raw model of PA. *)
Theorem raw_codedFormulaRank_functional : forall (M : RawPAModel),
  RawPASatisfies M -> RawCodedFormulaRankFunctional M.
Proof.
  intros M hPA root sigma pi otherSigma otherPi
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & hleftTraversal)
    hrightRank.
  exact (raw_codedFormulaRankIndexFunctionalBelow_all M hPA
    (raw_succ M rootIndex)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi otherSigma otherPi
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hleftTraversal hrightRank).
Qed.

(** The cross-certificate result is itself expressible and provable inside
    PA.  The five binders are [root,sigma,pi,otherSigma,otherPi], hence at
    the body their de Bruijn indices are 4 down to 0. *)
Definition codedFormulaRankFunctionalFormula : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (codedFormulaRankTermAt (tVar 4) (tVar 3) (tVar 2))
      (pImp
        (codedFormulaRankTermAt (tVar 4) (tVar 1) (tVar 0))
        (pAnd (pEq (tVar 3) (tVar 1))
          (pEq (tVar 2) (tVar 0))))))))) .

Lemma raw_sat_codedFormulaRankFunctionalFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedFormulaRankFunctionalFormula <->
  RawCodedFormulaRankFunctional M.
Proof.
  intros M e.
  unfold codedFormulaRankFunctionalFormula,
    RawCodedFormulaRankFunctional.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedFormulaRankFunctionalFormula_sentence :
  Formula.Sentence codedFormulaRankFunctionalFormula.
Proof.
  intros k hfree.
  unfold codedFormulaRankFunctionalFormula in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedFormulaRankFunctionalFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedFormulaRankFunctionalFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_codedFormulaRankFunctionalFormula_iff M e)).
  exact (raw_codedFormulaRank_functional M hPA).
Qed.

Theorem PA_proves_codedFormulaRankFunctionalFormula :
  Formula.BProv Formula.Ax_s [] codedFormulaRankFunctionalFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedFormulaRankFunctionalFormula_sentence.
  - exact codedFormulaRankFunctionalFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    The honest totality domain.

    [RawCodedFormulaRankTotal] quantifies over every carrier element and is
    intentionally not asserted: malformed elements need not have any root
    row.  The following genuine PA formula names exactly the carrier-domain
    on which realization exists.  Functionality above turns that existential
    graph domain into a unique-output domain without any extra premise.
*)

Definition codedFormulaRankRealizableTermAt (root : term) : formula :=
  pEx (pEx
    (codedFormulaRankTermAt (liftTerm 2 root) (tVar 1) (tVar 0))).

Definition RawCodedFormulaRankRealizable (M : RawPAModel)
    (root : M) : Prop :=
  exists sigma pi : M, RawCodedFormulaRank M root sigma pi.

Arguments RawCodedFormulaRankRealizable M root : clear implicits.

Lemma raw_sat_codedFormulaRankRealizableTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) root,
  raw_formula_sat M e (codedFormulaRankRealizableTermAt root) <->
  RawCodedFormulaRankRealizable M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold codedFormulaRankRealizableTermAt,
    RawCodedFormulaRankRealizable.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Corollary raw_codedFormulaRank_exists_unique_of_realizable : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root,
    RawCodedFormulaRankRealizable M root ->
    exists sigma pi,
      RawCodedFormulaRank M root sigma pi /\
      forall otherSigma otherPi,
        RawCodedFormulaRank M root otherSigma otherPi ->
        sigma = otherSigma /\ pi = otherPi.
Proof.
  intros M hPA root [sigma [pi hrank]].
  exists sigma, pi. split; [exact hrank |].
  intros otherSigma otherPi hother.
  exact (raw_codedFormulaRank_functional M hPA
    root sigma pi otherSigma otherPi hrank hother).
Qed.

End PABoundedRawCodedFormulaRankRealization.
