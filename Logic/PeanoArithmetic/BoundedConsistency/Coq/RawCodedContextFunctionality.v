(**
  Functionality of model-internal canonical context traversals.

  Context tables may have nonstandard lengths and unrelated Goedel-beta
  moduli.  Two complete traversals beginning at the same public list code
  nevertheless describe the same spine.  The proof below compares their
  tail and head tables by a genuine PA-definable induction on the common
  prefix.  It never recursively analyzes a carrier element in Rocq.

  At prefix [current], tail entries agree through [current], while head
  entries agree strictly below it.  If [current] is live on both sides, the
  two row equations expose equal list nodes.  Injectivity of the polynomial
  node then identifies both the next tail and the current head, exactly the
  data needed for the successor invariant.

  Agreement at the shorter termination index rules out unequal lengths: the
  longer traversal would identify zero with a live list node.  Membership
  and all-occurrences bounds can therefore be transported between arbitrary
  certificates rather than depending on the beta tables that witnessed
  them.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedAssignment
  RawCodedProofDescent RawCodedContextLists RawCodedContextBounds
  RawCodedContextStructure.

Import ListNotations.

Module PABoundedRawCodedContextFunctionality.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedContextStructure.

(** ------------------------------------------------------------------
    Formula-level agreement of two arbitrary beta tables. *)

Definition RawContextTableAgreeBelow (M : RawPAModel)
    (bound leftCode leftStep rightCode rightStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall leftValue rightValue,
      RawCodedAssignmentLookup M leftCode leftStep index leftValue ->
      RawCodedAssignmentLookup M rightCode rightStep index rightValue ->
      leftValue = rightValue.

Arguments RawContextTableAgreeBelow
  M bound leftCode leftStep rightCode rightStep : clear implicits.

Definition contextTableAgreeBelowTermAt
    (bound leftCode leftStep rightCode rightStep : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 leftCode) (liftTerm 2 leftStep)
            (tVar 1) (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 3 rightCode) (liftTerm 3 rightStep)
                (tVar 2) (tVar 0))
              (pEq (tVar 1) (tVar 0))))))).

Lemma raw_contextFunctionality_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_contextTableAgreeBelowTermAt_iff : forall
    (M : RawPAModel) e bound leftCode leftStep rightCode rightStep,
  raw_formula_sat M e
    (contextTableAgreeBelowTermAt
      bound leftCode leftStep rightCode rightStep) <->
  RawContextTableAgreeBelow M
    (raw_term_eval M e bound)
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep).
Proof.
  intros M e bound leftCode leftStep rightCode rightStep.
  unfold contextTableAgreeBelowTermAt, RawContextTableAgreeBelow.
  cbn [raw_formula_sat]. split.
  - intros hall index hindex leftValue rightValue hleft hright.
    assert (hltSat : raw_formula_sat M (scons M index e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_contextList_eval_liftTerm_one.
      cbn [raw_term_eval scons]. exact hindex.
    }
    pose proof (hall index hltSat leftValue) as hleftImp.
    assert (hleftSat : raw_formula_sat M
        (scons M leftValue (scons M index e))
        (codedAssignmentLookupTermAt
          (liftTerm 2 leftCode) (liftTerm 2 leftStep)
          (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_contextFunctionality_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hleft.
    }
    pose proof (hleftImp hleftSat rightValue) as hrightImp.
    assert (hrightSat : raw_formula_sat M
        (scons M rightValue
          (scons M leftValue (scons M index e)))
        (codedAssignmentLookupTermAt
          (liftTerm 3 rightCode) (liftTerm 3 rightStep)
          (tVar 2) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_contextList_eval_liftTerm_three.
      cbn [raw_term_eval scons]. exact hright.
    }
    exact (hrightImp hrightSat).
  - intros hagree index hltSat leftValue hleftSat rightValue hrightSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat)
      as hindex.
    rewrite raw_contextList_eval_liftTerm_one in hindex.
    cbn [raw_term_eval scons] in hindex.
    pose proof (proj1
      (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      hleftSat) as hleft.
    rewrite !raw_contextFunctionality_eval_liftTerm_two in hleft.
    cbn [raw_term_eval scons] in hleft.
    pose proof (proj1
      (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      hrightSat) as hright.
    rewrite !raw_contextList_eval_liftTerm_three in hright.
    cbn [raw_term_eval scons] in hright.
    exact (hagree index hindex leftValue rightValue hleft hright).
Qed.

(** Tails are compared through [current], represented by the strict bound
    [S current].  Heads are compared below [current]. *)
Definition RawContextTraversalTablesAgreePrefix (M : RawPAModel)
    (current
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep : M) : Prop :=
  RawContextTableAgreeBelow M (raw_succ M current)
    leftTailCode leftTailStep rightTailCode rightTailStep /\
  RawContextTableAgreeBelow M current
    leftHeadCode leftHeadStep rightHeadCode rightHeadStep.

Arguments RawContextTraversalTablesAgreePrefix
  M current leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep
  : clear implicits.

Definition contextTraversalTablesAgreePrefixTermAt
    (current
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep : term)
    : formula :=
  pAnd
    (contextTableAgreeBelowTermAt (tSucc current)
      leftTailCode leftTailStep rightTailCode rightTailStep)
    (contextTableAgreeBelowTermAt current
      leftHeadCode leftHeadStep rightHeadCode rightHeadStep).

Lemma raw_sat_contextTraversalTablesAgreePrefixTermAt_iff : forall
    (M : RawPAModel) e current
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep,
  raw_formula_sat M e
    (contextTraversalTablesAgreePrefixTermAt current
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep) <->
  RawContextTraversalTablesAgreePrefix M
    (raw_term_eval M e current)
    (raw_term_eval M e leftTailCode)
    (raw_term_eval M e leftTailStep)
    (raw_term_eval M e leftHeadCode)
    (raw_term_eval M e leftHeadStep)
    (raw_term_eval M e rightTailCode)
    (raw_term_eval M e rightTailStep)
    (raw_term_eval M e rightHeadCode)
    (raw_term_eval M e rightHeadStep).
Proof.
  intros. unfold contextTraversalTablesAgreePrefixTermAt,
    RawContextTraversalTablesAgreePrefix.
  cbn [raw_formula_sat].
  rewrite !raw_sat_contextTableAgreeBelowTermAt_iff.
  reflexivity.
Qed.

(** The induction predicate is guarded by both traversal lengths.  PA
    induction can therefore run through all carrier elements, while the
    structural successor argument is requested only inside the common live
    prefix. *)
Definition RawContextTraversalTablesAgreeThrough (M : RawPAModel)
    (current leftBound rightBound
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep : M) : Prop :=
  rawLe M current leftBound /\ rawLe M current rightBound ->
  RawContextTraversalTablesAgreePrefix M current
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep.

Arguments RawContextTraversalTablesAgreeThrough
  M current leftBound rightBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep
  : clear implicits.

Definition contextTraversalTablesAgreeThroughTermAt
    (current leftBound rightBound
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep : term)
    : formula :=
  pImp
    (pAnd
      (Formula.leTermAt current leftBound)
      (Formula.leTermAt current rightBound))
    (contextTraversalTablesAgreePrefixTermAt current
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep).

Lemma raw_sat_context_leTermAt_iff : forall
    (M : RawPAModel) (a b : term) e,
  raw_formula_sat M e (Formula.leTermAt a b) <->
  rawLe M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e. unfold Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval]. split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_contextTraversalTablesAgreeThroughTermAt_iff : forall
    (M : RawPAModel) e current leftBound rightBound
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep,
  raw_formula_sat M e
    (contextTraversalTablesAgreeThroughTermAt
      current leftBound rightBound
      leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightTailCode rightTailStep rightHeadCode rightHeadStep) <->
  RawContextTraversalTablesAgreeThrough M
    (raw_term_eval M e current)
    (raw_term_eval M e leftBound) (raw_term_eval M e rightBound)
    (raw_term_eval M e leftTailCode)
    (raw_term_eval M e leftTailStep)
    (raw_term_eval M e leftHeadCode)
    (raw_term_eval M e leftHeadStep)
    (raw_term_eval M e rightTailCode)
    (raw_term_eval M e rightTailStep)
    (raw_term_eval M e rightHeadCode)
    (raw_term_eval M e rightHeadStep).
Proof.
  intros. unfold contextTraversalTablesAgreeThroughTermAt,
    RawContextTraversalTablesAgreeThrough.
  cbn [raw_formula_sat].
  rewrite !raw_sat_context_leTermAt_iff,
    raw_sat_contextTraversalTablesAgreePrefixTermAt_iff.
  tauto.
Qed.

(** ------------------------------------------------------------------
    Raw arithmetic helpers used by the induction. *)

Lemma raw_context_le_refl : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M x x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_refl [] (tVar 0)) e) as hle.
  change (rawLe M x x) in hle. exact hle.
Qed.

Lemma raw_context_lt_of_succ_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y,
  rawLe M (raw_succ M x) y -> rawLt M x y.
Proof.
  intros M hPA x y [gap hgap]. exists gap.
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_succ_add_pair by exact hPA.
  exact hgap.
Qed.

Lemma raw_context_zero_neq_listNode : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail,
  raw_zero M <> rawListNode M head tail.
Proof.
  intros M hPA head tail heq.
  pose proof (rawListNode_tail_lt M hPA head tail) as htail.
  rewrite <- heq in htail.
  exact (raw_not_lt_zero M hPA tail htail).
Qed.

(** ------------------------------------------------------------------
    Base and successor of the common-prefix invariant. *)

Lemma raw_contextTraversalTablesAgreePrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  RawContextTraversalTablesAgreePrefix M (raw_zero M)
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep.
Proof.
  intros M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    [hleftRoot _] [hrightRoot _].
  split.
  - intros index hindex leftValue rightValue hleft hright.
    destruct (raw_lt_succ_cases M hPA index (raw_zero M) hindex)
      as [hbelow | ->].
    + exfalso. exact (raw_not_lt_zero M hPA index hbelow).
    + assert (hleftEq : leftValue = root).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          leftTailCode leftTailStep (raw_zero M) leftValue root
          hleft hleftRoot).
      }
      assert (hrightEq : rightValue = root).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          rightTailCode rightTailStep (raw_zero M) rightValue root
          hright hrightRoot).
      }
      congruence.
  - intros index hindex.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_contextTraversalTablesAgreePrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    current,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  rawLt M current leftBound ->
  rawLt M current rightBound ->
  RawContextTraversalTablesAgreePrefix M current
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  RawContextTraversalTablesAgreePrefix M (raw_succ M current)
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep.
Proof.
  intros M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    current hleftTraversal hrightTraversal
    hcurrentLeft hcurrentRight [htailAgree hheadAgree].
  destruct hleftTraversal as
    [hleftRoot [hleftEnd [hleftHeadDefined hleftRows]]].
  destruct hrightTraversal as
    [hrightRoot [hrightEnd [hrightHeadDefined hrightRows]]].
  destruct (hleftRows current hcurrentLeft) as
    (leftCurrent & leftNext & leftHead &
      hleftCurrent & hleftNext & hleftHead & hleftNode).
  destruct (hrightRows current hcurrentRight) as
    (rightCurrent & rightNext & rightHead &
      hrightCurrent & hrightNext & hrightHead & hrightNode).
  assert (hcurrentEq : leftCurrent = rightCurrent).
  {
    exact (htailAgree current
      (raw_assignment_lt_self_succ M hPA current)
      leftCurrent rightCurrent hleftCurrent hrightCurrent).
  }
  assert (hnodes : rawListNode M leftHead leftNext =
      rawListNode M rightHead rightNext).
  {
    rewrite <- hleftNode, <- hrightNode. exact hcurrentEq.
  }
  destruct (rawListNode_injective M hPA
    leftHead leftNext rightHead rightNext hnodes)
    as [hheadEq hnextEq].
  split.
  - intros index hindex leftValue rightValue hleft hright.
    destruct (raw_lt_succ_cases M hPA index (raw_succ M current) hindex)
      as [hbelow | ->].
    + exact (htailAgree index hbelow
        leftValue rightValue hleft hright).
    + assert (hleftEq : leftValue = leftNext).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          leftTailCode leftTailStep (raw_succ M current)
          leftValue leftNext hleft hleftNext).
      }
      assert (hrightEq : rightValue = rightNext).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          rightTailCode rightTailStep (raw_succ M current)
          rightValue rightNext hright hrightNext).
      }
      congruence.
  - intros index hindex leftValue rightValue hleft hright.
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hbelow | ->].
    + exact (hheadAgree index hbelow
        leftValue rightValue hleft hright).
    + assert (hleftEq : leftValue = leftHead).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          leftHeadCode leftHeadStep current
          leftValue leftHead hleft hleftHead).
      }
      assert (hrightEq : rightValue = rightHead).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          rightHeadCode rightHeadStep current
          rightValue rightHead hright hrightHead).
      }
      congruence.
Qed.

(** Genuine PA induction across a possibly nonstandard common prefix. *)
Theorem raw_contextListTraversals_agree_prefix : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  forall current,
  rawLe M current leftBound ->
  rawLe M current rightBound ->
  RawContextTraversalTablesAgreePrefix M current
    leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightTailCode rightTailStep rightHeadCode rightHeadStep.
Proof.
  intros M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal.
  set (parameterEnv := scons M leftBound
    (scons M rightBound
      (scons M leftTailCode (scons M leftTailStep
        (scons M leftHeadCode (scons M leftHeadStep
          (scons M rightTailCode (scons M rightTailStep
            (scons M rightHeadCode (scons M rightHeadStep
              (fun _ : nat => raw_zero M))))))))))).
  set (phi := contextTraversalTablesAgreeThroughTermAt
    (tVar 0) (tVar 1) (tVar 2)
    (tVar 3) (tVar 4) (tVar 5) (tVar 6)
    (tVar 7) (tVar 8) (tVar 9) (tVar 10)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_contextTraversalTablesAgreeThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2)
          (tVar 3) (tVar 4) (tVar 5) (tVar 6)
          (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _.
      exact (raw_contextTraversalTablesAgreePrefix_zero M hPA root
        leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
        rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
        hleftTraversal hrightTraversal).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_contextTraversalTablesAgreeThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2)
          (tVar 3) (tVar 4) (tVar 5) (tVar 6)
          (tVar 7) (tVar 8) (tVar 9) (tVar 10))
        hcurrentSat) as hcurrentRaw.
      apply (proj2
        (raw_sat_contextTraversalTablesAgreeThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2)
          (tVar 3) (tVar 4) (tVar 5) (tVar 6)
          (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intros [hsuccLeft hsuccRight].
      assert (hcurrentLeft : rawLt M current leftBound).
      { exact (raw_context_lt_of_succ_le M hPA
          current leftBound hsuccLeft). }
      assert (hcurrentRight : rawLt M current rightBound).
      { exact (raw_context_lt_of_succ_le M hPA
          current rightBound hsuccRight). }
      apply (raw_contextTraversalTablesAgreePrefix_succ M hPA root
        leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
        rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
        current hleftTraversal hrightTraversal
        hcurrentLeft hcurrentRight).
      apply hcurrentRaw. split.
      + exact (raw_lt_to_le M current leftBound hcurrentLeft).
      + exact (raw_lt_to_le M current rightBound hcurrentRight).
  }
  intros current hcurrentLeft hcurrentRight.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_contextTraversalTablesAgreeThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2)
      (tVar 3) (tVar 4) (tVar 5) (tVar 6)
      (tVar 7) (tVar 8) (tVar 9) (tVar 10))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw.
  exact (hraw (conj hcurrentLeft hcurrentRight)).
Qed.

(** ------------------------------------------------------------------
    Termination length and full traversal coherence. *)

Theorem raw_contextListTraversal_bound_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  leftBound = rightBound.
Proof.
  intros M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal.
  destruct (raw_order_trichotomy M hPA leftBound rightBound)
    as [heq | [hleftShort | hrightShort]].
  - exact heq.
  - pose proof (raw_contextListTraversals_agree_prefix M hPA root
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      hleftTraversal hrightTraversal leftBound
      (raw_context_le_refl M hPA leftBound)
      (raw_lt_to_le M leftBound rightBound hleftShort))
      as [htailAgree _].
    pose proof hleftTraversal as hleftFacts.
    pose proof hrightTraversal as hrightFacts.
    destruct hleftFacts as [_ [hleftEnd _]].
    destruct hrightFacts as [_ [_ [_ hrightRows]]].
    destruct (hrightRows leftBound hleftShort) as
      (rightCurrent & rightNext & rightHead &
        hrightCurrent & _ & _ & hrightNode).
    assert (hzeroCurrent : raw_zero M = rightCurrent).
    {
      exact (htailAgree leftBound
        (raw_assignment_lt_self_succ M hPA leftBound)
        (raw_zero M) rightCurrent hleftEnd hrightCurrent).
    }
    exfalso. apply (raw_context_zero_neq_listNode M hPA
      rightHead rightNext).
    rewrite <- hrightNode. exact hzeroCurrent.
  - pose proof (raw_contextListTraversals_agree_prefix M hPA root
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      hleftTraversal hrightTraversal rightBound
      (raw_lt_to_le M rightBound leftBound hrightShort)
      (raw_context_le_refl M hPA rightBound))
      as [htailAgree _].
    pose proof hleftTraversal as hleftFacts.
    pose proof hrightTraversal as hrightFacts.
    destruct hleftFacts as [_ [_ [_ hleftRows]]].
    destruct hrightFacts as [_ [hrightEnd _]].
    destruct (hleftRows rightBound hrightShort) as
      (leftCurrent & leftNext & leftHead &
        hleftCurrent & _ & _ & hleftNode).
    assert (hcurrentZero : leftCurrent = raw_zero M).
    {
      exact (htailAgree rightBound
        (raw_assignment_lt_self_succ M hPA rightBound)
        leftCurrent (raw_zero M) hleftCurrent hrightEnd).
    }
    exfalso. apply (raw_context_zero_neq_listNode M hPA
      leftHead leftNext).
    rewrite <- hleftNode. symmetry. exact hcurrentZero.
Qed.

Definition RawContextListTraversalsCoherent (M : RawPAModel)
    (leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep : M)
    : Prop :=
  leftBound = rightBound /\
  RawContextTableAgreeBelow M (raw_succ M leftBound)
    leftTailCode leftTailStep rightTailCode rightTailStep /\
  RawContextTableAgreeBelow M leftBound
    leftHeadCode leftHeadStep rightHeadCode rightHeadStep.

Arguments RawContextListTraversalsCoherent
  M leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
  : clear implicits.

Theorem raw_contextListTraversals_coherent : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  RawContextListTraversalsCoherent M
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep.
Proof.
  intros M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal.
  assert (hbound : leftBound = rightBound).
  {
    exact (raw_contextListTraversal_bound_functional M hPA root
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      hleftTraversal hrightTraversal).
  }
  pose proof (raw_contextListTraversals_agree_prefix M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal leftBound
    (raw_context_le_refl M hPA leftBound)) as hagree.
  specialize (hagree ltac:(rewrite <- hbound;
    exact (raw_context_le_refl M hPA leftBound))).
  destruct hagree as [htails hheads].
  exact (conj hbound (conj htails hheads)).
Qed.

(** ------------------------------------------------------------------
    Membership is independent of its hidden certificate. *)

Theorem raw_contextListMemberWithTables_transport : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root member
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  RawContextListMemberWithTables M
    member leftBound leftHeadCode leftHeadStep ->
  RawContextListMemberWithTables M
    member rightBound rightHeadCode rightHeadStep.
Proof.
  intros M hPA root member
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal [index [hindex hleftLookup]].
  destruct (raw_contextListTraversals_coherent M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal)
    as [hbound [_ hheads]].
  assert (hindexRight : rawLt M index rightBound).
  { rewrite <- hbound. exact hindex. }
  pose proof hrightTraversal as hrightFacts.
  destruct hrightFacts as [_ [_ [hrightDefined _]]].
  destruct (hrightDefined index hindexRight)
    as [rightValue hrightLookup].
  assert (hmemberEq : member = rightValue).
  {
    exact (hheads index hindex member rightValue
      hleftLookup hrightLookup).
  }
  exists index. split; [exact hindexRight |].
  rewrite hmemberEq. exact hrightLookup.
Qed.

Theorem raw_contextListMemberWithTables_iff_of_traversals : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root member
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  (RawContextListMemberWithTables M
      member leftBound leftHeadCode leftHeadStep <->
   RawContextListMemberWithTables M
      member rightBound rightHeadCode rightHeadStep).
Proof.
  intros M hPA root member
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal.
  split; intro hmember.
  - exact (raw_contextListMemberWithTables_transport M hPA root member
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      hleftTraversal hrightTraversal hmember).
  - exact (raw_contextListMemberWithTables_transport M hPA root member
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      hrightTraversal hleftTraversal hmember).
Qed.

(** The strongest public form: once any complete traversal of [root] is in
    hand, public existential membership is equivalent to membership in that
    particular head table. *)
Theorem raw_contextListMember_iff_with_traversal : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root member bound tailCode tailStep headCode headStep,
  RawContextListTraversal M root bound
    tailCode tailStep headCode headStep ->
  (RawContextListMember M root member <->
   RawContextListMemberWithTables M member bound headCode headStep).
Proof.
  intros M hPA root member bound tailCode tailStep headCode headStep
    hchosen. split.
  - intros (otherBound & otherTailCode & otherTailStep &
      otherHeadCode & otherHeadStep & hother & hmember).
    exact (raw_contextListMemberWithTables_transport M hPA root member
      otherBound otherTailCode otherTailStep otherHeadCode otherHeadStep
      bound tailCode tailStep headCode headStep
      hother hchosen hmember).
  - intros hmember.
    exists bound, tailCode, tailStep, headCode, headStep.
    split; assumption.
Qed.

(** A fully explicit zero-length traversal is useful for eliminating public
    membership of the empty context. *)
Lemma raw_contextList_zero_traversal_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists tailCode tailStep : M,
    RawContextListTraversal M (raw_zero M) (raw_zero M)
      tailCode tailStep (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  destruct (raw_codedAssignmentPrepend_exists M hPA
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M))
    as [tailCode [tailStep htail]].
  exists tailCode, tailStep. repeat split.
  - exact (proj1 htail).
  - exact (proj1 htail).
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros index hindex.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Theorem raw_contextListMember_zero_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall member,
  ~ RawContextListMember M (raw_zero M) member.
Proof.
  intros M hPA member hmember.
  destruct (raw_contextList_zero_traversal_exists M hPA)
    as [tailCode [tailStep hzeroTraversal]].
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    (raw_zero M) member (raw_zero M) tailCode tailStep
    (raw_zero M) (raw_zero M) hzeroTraversal) hmember)
    as [index [hindex _]].
  exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Canonical cons membership.  The reverse direction needs the tail to lie
    in the honest context domain: an arbitrary carrier element cannot be
    promoted to a context merely because a head is proposed. *)
Theorem raw_contextListMember_cons_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail head member,
  RawContextListRealizable M tail ->
  (RawContextListMember M (rawListNode M head tail) member <->
   member = head \/ RawContextListMember M tail member).
Proof.
  intros M hPA tail head member
    (bound & tailCode & tailStep & headCode & headStep & htraversal).
  split.
  - intro hmember.
    destruct (raw_contextListConsExtension_exists M hPA
      tail head bound tailCode tailStep headCode headStep htraversal)
      as (newTailCode & newTailStep & newHeadCode & newHeadStep &
        _ & hheadPrepend & hnewTraversal).
    pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
      (rawListNode M head tail) member (raw_succ M bound)
      newTailCode newTailStep newHeadCode newHeadStep
      hnewTraversal) hmember) as hnewMember.
    destruct hnewMember as [index [hindex hlookup]].
    destruct (raw_assignment_zero_or_successor M hPA index)
      as [-> | [predecessor ->]].
    + left.
      exact (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
        headCode headStep head bound newHeadCode newHeadStep member
        hheadPrepend) hlookup).
    + right.
      assert (hpredSelf : rawLt M predecessor
          (raw_succ M predecessor)).
      { exact (raw_assignment_lt_self_succ M hPA predecessor). }
      assert (hpredBound : rawLt M predecessor bound).
      {
        destruct (raw_lt_succ_cases M hPA
          (raw_succ M predecessor) bound hindex) as [hlt | heq].
        - exact (raw_assignment_lt_trans M hPA predecessor
            (raw_succ M predecessor) bound hpredSelf hlt).
        - rewrite <- heq. exact hpredSelf.
      }
      assert (holdLookup : RawCodedAssignmentLookup M
          headCode headStep predecessor member).
      {
        exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
          headCode headStep head bound newHeadCode newHeadStep
          (proj1 (proj2 (proj2 htraversal))) hheadPrepend
          predecessor hpredBound member) hlookup).
      }
      exists bound, tailCode, tailStep, headCode, headStep.
      split; [exact htraversal |].
      exists predecessor. split; assumption.
  - intros [-> | htailMember].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      exists bound, tailCode, tailStep, headCode, headStep.
      exact htraversal.
    + exact (raw_contextList_cons_tail_member M hPA
        tail head member htailMember).
Qed.

(** ------------------------------------------------------------------
    Certificate-independent all-occurrences bounds. *)

Theorem raw_contextAllBoundedWithTables_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  RawContextListTraversal M root leftBound
    leftTailCode leftTailStep leftHeadCode leftHeadStep ->
  RawContextListTraversal M root rightBound
    rightTailCode rightTailStep rightHeadCode rightHeadStep ->
  RawContextAllBoundedWithTables M level
    leftBound leftHeadCode leftHeadStep ->
  RawContextAllBoundedWithTables M level
    rightBound rightHeadCode rightHeadStep.
Proof.
  intros M hPA level root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal hall
    index hindexRight code hrightLookup.
  destruct (raw_contextListTraversals_coherent M hPA root
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
    hleftTraversal hrightTraversal)
    as [hbound [_ hheads]].
  assert (hindexLeft : rawLt M index leftBound).
  { rewrite hbound. exact hindexRight. }
  pose proof hleftTraversal as hleftFacts.
  destruct hleftFacts as [_ [_ [hleftDefined _]]].
  destruct (hleftDefined index hindexLeft)
    as [leftValue hleftLookup].
  pose proof (hheads index hindexLeft leftValue code
    hleftLookup hrightLookup) as hvalue.
  rewrite <- hvalue.
  exact (hall index hindexLeft leftValue hleftLookup).
Qed.

Theorem raw_contextAllBounded_iff_with_traversal : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root
    bound tailCode tailStep headCode headStep,
  RawContextListTraversal M root bound
    tailCode tailStep headCode headStep ->
  (RawContextAllBounded M level root <->
   RawContextAllBoundedWithTables M level bound headCode headStep).
Proof.
  intros M hPA level root bound tailCode tailStep headCode headStep
    hchosen. split.
  - intros (otherBound & otherTailCode & otherTailStep &
      otherHeadCode & otherHeadStep & hother & hall).
    exact (raw_contextAllBoundedWithTables_transport M hPA level root
      otherBound otherTailCode otherTailStep otherHeadCode otherHeadStep
      bound tailCode tailStep headCode headStep
      hother hchosen hall).
  - intro hall.
    exists bound, tailCode, tailStep, headCode, headStep.
    split; assumption.
Qed.

(** This closes the certificate-dependence seam left explicitly in
    [RawCodedContextBounds]. *)
Theorem raw_contextAllBounded_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root member,
  RawContextAllBounded M level root ->
  RawContextListMember M root member ->
  RawFormulaQuantifierBounded M level member.
Proof.
  intros M hPA level root member
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall) hmember.
  apply (raw_contextAllBoundedWithTables_member M level
    bound headCode headStep member hall).
  exact (proj1 (raw_contextListMember_iff_with_traversal M hPA
    root member bound tailCode tailStep headCode headStep
    htraversal) hmember).
Qed.

(** Head elimination is unconditional: an all-bounded traversal rooted at a
    visible node must have positive length, and its row zero exposes that
    node's actual head. *)
Theorem raw_contextAllBounded_cons_head : forall
    (M : RawPAModel), RawPASatisfies M -> forall level head tail,
  RawContextAllBounded M level (rawListNode M head tail) ->
  RawFormulaQuantifierBounded M level head.
Proof.
  intros M hPA level head tail
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall).
  destruct htraversal as [hroot [hend [hheadDefined hrows]]].
  assert (hboundNonzero : bound <> raw_zero M).
  {
    intro hbound. subst bound.
    pose proof (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep (raw_zero M)
      (rawListNode M head tail) (raw_zero M) hroot hend) as hnodeZero.
    apply (raw_context_zero_neq_listNode M hPA head tail).
    symmetry. exact hnodeZero.
  }
  destruct (raw_assignment_zero_or_successor M hPA bound)
    as [hzero | [predecessor hsucc]].
  - contradiction.
  - rewrite hsucc in *.
    assert (hzeroBelow : rawLt M (raw_zero M)
        (raw_succ M predecessor)).
    {
      apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_proof_zero_le. exact hPA.
    }
    destruct (hrows (raw_zero M) hzeroBelow) as
      (currentTail & nextTail & rowHead &
        hcurrent & _ & hrowHead & hrowNode).
    assert (hcurrentRoot : currentTail = rawListNode M head tail).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        tailCode tailStep (raw_zero M)
        currentTail (rawListNode M head tail) hcurrent hroot).
    }
    assert (hnodes : rawListNode M head tail =
        rawListNode M rowHead nextTail).
    {
      rewrite <- hrowNode. symmetry. exact hcurrentRoot.
    }
    destruct (rawListNode_injective M hPA
      head tail rowHead nextTail hnodes) as [hhead _].
    rewrite hhead.
    exact (hall (raw_zero M) hzeroBelow rowHead hrowHead).
Qed.

(** Tail elimination uses an independently honest tail traversal.  This is
    the strongest direction available without adding a beta-table drop
    construction to the context interface. *)
Theorem raw_contextAllBounded_cons_tail : forall
    (M : RawPAModel), RawPASatisfies M -> forall level head tail,
  RawContextAllBounded M level (rawListNode M head tail) ->
  RawContextListRealizable M tail ->
  RawContextAllBounded M level tail.
Proof.
  intros M hPA level head tail hall
    (bound & tailCode & tailStep & headCode & headStep & htraversal).
  destruct (raw_contextListConsExtension_exists M hPA
    tail head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  pose proof (proj1 (raw_contextAllBounded_iff_with_traversal M hPA
    level (rawListNode M head tail) (raw_succ M bound)
    newTailCode newTailStep newHeadCode newHeadStep
    hnewTraversal) hall) as hnewAll.
  exists bound, tailCode, tailStep, headCode, headStep.
  split; [exact htraversal |].
  intros index hindex code hlookup.
  apply (hnewAll (raw_succ M index)).
  - apply raw_lt_succ_of_le; [exact hPA |].
    exact (raw_succ_le_of_lt_pair M hPA index bound hindex).
  - exact (raw_codedAssignmentPrepend_tail M
      headCode headStep head bound newHeadCode newHeadStep
      index code hheadPrepend hindex hlookup).
Qed.

End PABoundedRawCodedContextFunctionality.
