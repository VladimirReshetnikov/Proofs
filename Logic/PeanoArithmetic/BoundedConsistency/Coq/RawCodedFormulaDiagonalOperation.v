(**
  Diagonal formula-operation traces and quantifier constructors.

  A relation [RawCodedFormulaOperation atom parameter depth input input]
  says that an operation fixes one formula, but its existential source and
  target tables need not coincide.  For constructor-by-constructor
  composition we retain the stronger certificate below: one formula table is
  used for both columns, together with the usual depth table.  This makes it
  possible to append an [all] or [exists] row without decoding the child.

  The development is generic in the atomic term operation.  The final
  specialization is capture-avoiding single substitution, which is the
  syntax certificate required by universal-closure unsealing.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomContextSelfShift.

Module PABoundedRawCodedFormulaDiagonalOperation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomContextSelfShift.

(** A lookup in the shared formula table and the depth table. *)
Definition RawDiagonalFormulaOperationLookup (M : RawPAModel)
    (formulaCode formulaStep depthCode depthStep index input depth : M)
    : Prop :=
  RawCodedTermOperationPairLookup M
    formulaCode formulaStep depthCode depthStep index input depth.

Arguments RawDiagonalFormulaOperationLookup M
  formulaCode formulaStep depthCode depthStep index input depth
  : clear implicits.

Definition diagonalFormulaOperationLookupTermAt
    (formulaCode formulaStep depthCode depthStep index input depth : term)
    : formula :=
  codedTermOperationPairLookupTermAt
    formulaCode formulaStep depthCode depthStep index input depth.

Lemma raw_sat_diagonalFormulaOperationLookupTermAt_iff : forall
    (M : RawPAModel) e
      formulaCode formulaStep depthCode depthStep index input depth,
  raw_formula_sat M e
    (diagonalFormulaOperationLookupTermAt
      formulaCode formulaStep depthCode depthStep index input depth) <->
  RawDiagonalFormulaOperationLookup M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e depth).
Proof. intros. apply raw_sat_codedTermOperationPairLookupTermAt_iff. Qed.

Definition RawDiagonalFormulaOperationTraversalRow (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter formulaCode formulaStep depthCode depthStep
      index input depth : M) : Prop :=
  RawCodedFormulaOperationTraversalRow M atom parameter
    formulaCode formulaStep formulaCode formulaStep depthCode depthStep
    index input input depth.

Arguments RawDiagonalFormulaOperationTraversalRow M atom parameter
  formulaCode formulaStep depthCode depthStep index input depth
  : clear implicits.

Definition diagonalFormulaOperationTraversalRowTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter formulaCode formulaStep depthCode depthStep
      index input depth : term) : formula :=
  codedFormulaOperationTraversalRowTermAt atom parameter
    formulaCode formulaStep formulaCode formulaStep depthCode depthStep
    index input input depth.

Lemma raw_sat_diagonalFormulaOperationTraversalRowTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter formulaCode formulaStep depthCode depthStep
      index input depth,
  raw_formula_sat M e
    (diagonalFormulaOperationTraversalRowTermAt atom parameter
      formulaCode formulaStep depthCode depthStep index input depth) <->
  RawDiagonalFormulaOperationTraversalRow M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e depth).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold diagonalFormulaOperationTraversalRowTermAt,
    RawDiagonalFormulaOperationTraversalRow.
  apply (raw_sat_codedFormulaOperationTraversalRowTermAt_iff
    M e atom rawAtom hatom).
Qed.

(** Prefix transport for a shared formula/depth table. *)
Lemma raw_diagonalFormulaOperationLookup_prefix_extend : forall
    (M : RawPAModel) bound
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      index input depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLt M index bound ->
  RawDiagonalFormulaOperationLookup M
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    index input depth ->
  RawDiagonalFormulaOperationLookup M
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    index input depth.
Proof. exact raw_termShiftPairLookup_prefix_extend. Qed.

Lemma raw_diagonalFormulaOperationTriple_prefix_extend : forall
    (M : RawPAModel) bound
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      index input output depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLt M index bound ->
  RawCodedFormulaOperationTripleLookup M
    oldFormulaCode oldFormulaStep oldFormulaCode oldFormulaStep
    oldDepthCode oldDepthStep index input output depth ->
  RawCodedFormulaOperationTripleLookup M
    newFormulaCode newFormulaStep newFormulaCode newFormulaStep
    newDepthCode newDepthStep index input output depth.
Proof.
  intros M bound oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    index input output depth [hformula hdepth] hindex
    [hinput [houtput hdepthLookup]].
  repeat split.
  - exact (hformula index input hindex hinput).
  - exact (hformula index output hindex houtput).
  - exact (hdepth index depth hindex hdepthLookup).
Qed.

Lemma raw_diagonalFormulaOperationTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter bound current
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep input depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLe M current bound ->
  RawDiagonalFormulaOperationTraversalRow M atom parameter
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    current input depth ->
  RawDiagonalFormulaOperationTraversalRow M atom parameter
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    current input depth.
Proof.
  intros M hPA atom parameter bound current
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    input depth hext hcurrent hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. exact heq.
  - right. left. exact hbot.
  - right. right. left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists childIndex, inputChild, outputChild, childDepth.
    split; [exact hchild |]. split.
    + apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        childIndex inputChild outputChild childDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hchildLookup.
    + repeat split; assumption.
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists childIndex, inputChild, outputChild, childDepth.
    split; [exact hchild |]. split.
    + apply (raw_diagonalFormulaOperationTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        childIndex inputChild outputChild childDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hchildLookup.
    + repeat split; assumption.
Qed.

Definition RawDiagonalFormulaOperationRows (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter formulaCode formulaStep depthCode depthStep bound : M)
    : Prop :=
  forall index input depth,
    rawLt M index bound ->
    RawDiagonalFormulaOperationLookup M
      formulaCode formulaStep depthCode depthStep index input depth ->
    RawDiagonalFormulaOperationTraversalRow M atom parameter
      formulaCode formulaStep depthCode depthStep index input depth.

Arguments RawDiagonalFormulaOperationRows M atom parameter
  formulaCode formulaStep depthCode depthStep bound : clear implicits.

Definition diagonalFormulaOperationRowsTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter formulaCode formulaStep depthCode depthStep bound : term)
    : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (diagonalFormulaOperationLookupTermAt
          (liftTerm 3 formulaCode) (liftTerm 3 formulaStep)
          (liftTerm 3 depthCode) (liftTerm 3 depthStep)
          (tVar 2) (tVar 1) (tVar 0))
        (diagonalFormulaOperationTraversalRowTermAt atom
          (liftTerm 3 parameter)
          (liftTerm 3 formulaCode) (liftTerm 3 formulaStep)
          (liftTerm 3 depthCode) (liftTerm 3 depthStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_diagonalFormulaOperationRowsTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter formulaCode formulaStep depthCode depthStep bound,
  raw_formula_sat M e
    (diagonalFormulaOperationRowsTermAt atom parameter
      formulaCode formulaStep depthCode depthStep bound) <->
  RawDiagonalFormulaOperationRows M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold diagonalFormulaOperationRowsTermAt,
    RawDiagonalFormulaOperationRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_diagonalFormulaOperationLookupTermAt_iff.
  setoid_rewrite (raw_sat_diagonalFormulaOperationTraversalRowTermAt_iff
    M _ atom rawAtom hatom).
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawDiagonalFormulaOperationBundle (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter formulaCode formulaStep depthCode depthStep bound : M)
    : Prop :=
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M depthCode depthStep bound /\
  RawDiagonalFormulaOperationRows M atom parameter
    formulaCode formulaStep depthCode depthStep bound.

Arguments RawDiagonalFormulaOperationBundle M atom parameter
  formulaCode formulaStep depthCode depthStep bound : clear implicits.

Theorem raw_diagonalFormulaOperationBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop)
      parameter formulaCode formulaStep depthCode depthStep bound input depth,
  RawDiagonalFormulaOperationBundle M atom parameter
    formulaCode formulaStep depthCode depthStep bound ->
  RawDiagonalFormulaOperationTraversalRow M atom parameter
    formulaCode formulaStep depthCode depthStep bound input depth ->
  exists newFormulaCode newFormulaStep newDepthCode newDepthStep : M,
    RawDiagonalFormulaOperationBundle M atom parameter
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      (raw_succ M bound) /\
    RawTermShiftTablePrefixExtension M bound
      formulaCode formulaStep depthCode depthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep /\
    RawDiagonalFormulaOperationLookup M
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      bound input depth.
Proof.
  intros M hPA atom parameter formulaCode formulaStep depthCode depthStep
    bound input depth [hformulaDefined [hdepthDefined hrows]] hclosed.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    formulaCode formulaStep bound input hformulaDefined)
    as [newFormulaCode [newFormulaStep
      [hnewFormulaDefined [hformulaPrefix hformulaRoot]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    depthCode depthStep bound depth hdepthDefined)
    as [newDepthCode [newDepthStep
      [hnewDepthDefined [hdepthPrefix hdepthRoot]]]].
  set (hext := conj hformulaPrefix hdepthPrefix).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep.
  split.
  - split; [exact hnewFormulaDefined |].
    split; [exact hnewDepthDefined |].
    intros index rowInput rowDepth hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexOld | ->].
    + destruct (hformulaDefined index hindexOld)
        as [oldInput holdInput].
      destruct (hdepthDefined index hindexOld)
        as [oldDepth holdDepth].
      assert (hnewOld : RawDiagonalFormulaOperationLookup M
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          index oldInput oldDepth).
      {
        apply (raw_diagonalFormulaOperationLookup_prefix_extend M bound
          formulaCode formulaStep depthCode depthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          index oldInput oldDepth hext hindexOld).
        split; assumption.
      }
      destruct hlookup as [hlookupInput hlookupDepth].
      destruct hnewOld as [hnewOldInput hnewOldDepth].
      assert (hinputEq : rowInput = oldInput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newFormulaCode newFormulaStep index rowInput oldInput
          hlookupInput hnewOldInput).
      }
      assert (hdepthEq : rowDepth = oldDepth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep index rowDepth oldDepth
          hlookupDepth hnewOldDepth).
      }
      subst rowInput. subst rowDepth.
      apply (raw_diagonalFormulaOperationTraversalRow_prefix_extend
        M hPA atom parameter bound index
        formulaCode formulaStep depthCode depthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        oldInput oldDepth hext).
      * exact (raw_lt_to_le M index bound hindexOld).
      * apply (hrows index oldInput oldDepth hindexOld).
        split; assumption.
    + destruct hlookup as [hlookupInput hlookupDepth].
      assert (hinputEq : rowInput = input).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newFormulaCode newFormulaStep bound rowInput input
          hlookupInput hformulaRoot).
      }
      assert (hdepthEq : rowDepth = depth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep bound rowDepth depth
          hlookupDepth hdepthRoot).
      }
      subst rowInput. subst rowDepth.
      apply (raw_diagonalFormulaOperationTraversalRow_prefix_extend
        M hPA atom parameter bound bound
        formulaCode formulaStep depthCode depthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        input depth hext).
      * apply raw_rank_le_refl. exact hPA.
      * exact hclosed.
  - split; [exact hext |]. split; assumption.
Qed.

Definition RawDiagonalFormulaOperationTrace (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input : M) : Prop :=
  RawDiagonalFormulaOperationBundle M atom parameter
    formulaCode formulaStep depthCode depthStep bound /\
  rawLt M rootIndex bound /\
  RawDiagonalFormulaOperationLookup M
    formulaCode formulaStep depthCode depthStep rootIndex input rootDepth.

Arguments RawDiagonalFormulaOperationTrace M atom parameter rootDepth
  formulaCode formulaStep depthCode depthStep bound rootIndex input
  : clear implicits.

Lemma raw_codedFormulaOperation_of_diagonal_trace : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop)
      parameter rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input,
  RawDiagonalFormulaOperationTrace M atom parameter rootDepth
    formulaCode formulaStep depthCode depthStep bound rootIndex input ->
  RawCodedFormulaOperation M atom parameter rootDepth input input.
Proof.
  intros M hPA atom parameter rootDepth formulaCode formulaStep
    depthCode depthStep bound rootIndex input
    [[hformulaDefined [hdepthDefined hrows]] [hrootBelow hroot]].
  exists formulaCode, formulaStep, formulaCode, formulaStep,
    depthCode, depthStep, bound, rootIndex.
  split; [exact hformulaDefined |].
  split; [exact hformulaDefined |].
  split; [exact hdepthDefined |].
  split; [exact hrootBelow |]. split.
  - destruct hroot as [hformula hdepth].
    split; [exact hformula |]. split; assumption.
  - intros index rowInput rowOutput rowDepth hindex
      [hinput [houtput hdepth]].
    assert (houtputEq : rowOutput = rowInput).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        formulaCode formulaStep index rowOutput rowInput houtput hinput).
    }
    subst rowOutput.
    exact (hrows index rowInput rowDepth hindex (conj hinput hdepth)).
Qed.

Definition RawCodedFormulaDiagonalOperation (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter rootDepth input : M) : Prop :=
  exists formulaCode formulaStep depthCode depthStep bound rootIndex : M,
    RawDiagonalFormulaOperationTrace M atom parameter rootDepth
      formulaCode formulaStep depthCode depthStep bound rootIndex input.

Arguments RawCodedFormulaDiagonalOperation M atom
  parameter rootDepth input : clear implicits.

Lemma raw_codedFormulaOperation_of_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter rootDepth input,
  RawCodedFormulaDiagonalOperation M atom parameter rootDepth input ->
  RawCodedFormulaOperation M atom parameter rootDepth input input.
Proof.
  intros M hPA atom parameter rootDepth input
    (formulaCode & formulaStep & depthCode & depthStep & bound &
     rootIndex & htrace).
  exact (raw_codedFormulaOperation_of_diagonal_trace M hPA atom
    parameter rootDepth formulaCode formulaStep depthCode depthStep
    bound rootIndex input htrace).
Qed.

(** Append a unary formula constructor.  The child's operation runs one
    binder deeper, exactly matching the row graph for [all] and [exists]. *)
Lemma raw_codedFormulaDiagonalOperation_unary : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter depth
      (constructor : M -> M),
  (forall formulaCode formulaStep depthCode depthStep
      index input rowDepth,
    RawCodedFormulaUnaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      index input input rowDepth ->
    RawDiagonalFormulaOperationTraversalRow M atom parameter
      formulaCode formulaStep depthCode depthStep
      index input rowDepth) ->
  forall child,
  RawCodedFormulaDiagonalOperation M atom parameter
    (raw_succ M depth) child ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (constructor child).
Proof.
  intros M hPA atom parameter depth constructor hinject child
    (formulaCode & formulaStep & depthCode & depthStep &
     bound & rootIndex & hchild).
  destruct hchild as [hbundle [hrootBelow hroot]].
  assert (hunary : RawCodedFormulaUnaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      bound (constructor child) (constructor child) depth).
  {
    exists rootIndex, child, child, (raw_succ M depth).
    split; [exact hrootBelow |]. split.
    - destruct hroot as [hformula hdepth].
      split; [exact hformula |]. split; assumption.
    - repeat split; reflexivity.
  }
  pose proof (hinject formulaCode formulaStep depthCode depthStep
    bound (constructor child) depth hunary) as hrow.
  destruct (raw_diagonalFormulaOperationBundle_append M hPA atom parameter
    formulaCode formulaStep depthCode depthStep bound
    (constructor child) depth hbundle hrow)
    as (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
        hnewBundle & _ & hnewRoot).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep,
    (raw_succ M bound), bound.
  split; [exact hnewBundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA bound).
  - exact hnewRoot.
Qed.

Corollary raw_codedFormulaDiagonalOperation_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter depth child,
  RawCodedFormulaDiagonalOperation M atom parameter
    (raw_succ M depth) child ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaAllCode M child).
Proof.
  intros M hPA atom parameter depth child hchild.
  apply (raw_codedFormulaDiagonalOperation_unary M hPA atom parameter depth
    (rawFormulaAllCode M)).
  - intros. right. right. right. right. right. left. exact H.
  - exact hchild.
Qed.

(** Capture-avoiding substitution specialization. *)
Definition RawCodedFormulaDiagonalSubstitution (M : RawPAModel)
    (replacement depth input : M) : Prop :=
  RawCodedFormulaDiagonalOperation M
    (RawCodedFormulaSubstitutionAtom M) replacement depth input.

Arguments RawCodedFormulaDiagonalSubstitution M replacement depth input
  : clear implicits.

Lemma raw_codedFormulaDiagonalSubstitution_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth child,
  RawCodedFormulaDiagonalSubstitution M replacement
    (raw_succ M depth) child ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaAllCode M child).
Proof.
  exact (fun M hPA replacement depth child =>
    raw_codedFormulaDiagonalOperation_all M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement depth child).
Qed.

Lemma raw_codedFormulaSingleSubstitution_of_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement input,
  RawCodedFormulaDiagonalSubstitution M replacement (raw_zero M) input ->
  RawCodedFormulaSingleSubstitution M replacement input input.
Proof.
  intros M hPA replacement input hdiagonal.
  exact (raw_codedFormulaOperation_of_diagonal M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement
    (raw_zero M) input hdiagonal).
Qed.

End PABoundedRawCodedFormulaDiagonalOperation.
