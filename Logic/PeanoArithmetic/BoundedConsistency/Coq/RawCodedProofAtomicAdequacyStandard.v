(**
  Atomic adequacy for externally quoted PA syntax and proofs.

  The theorems in this file are deliberately restricted to standard
  quotations.  Finite metatheoretic syntax trees can be beta-coded inside
  every model of PA; no claim is made that an arbitrary, possibly
  nonstandard, carrier element admits an external decoder.
*)

From Stdlib Require Import List Arith Lia Classical ClassicalChoice.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax CodedProof PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedAssignment RawCodedTermEvaluationStep
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedTermEvaluationStandardAdequacy
  RawCodedTermEvaluationStepFunctionality
  RawCodedProofConstructors RawCodedProofTraversal RawCodedProofEndpoints
  RawCodedProofDescent RawCodedContextFunctionality RawCodedContextStructure
  RawCodedFormulaRankTraversal RawCodedFormulaRankTotality
  RawCodedFormulaOperations RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaOperationQuotedRankSound
  RawCodedRestrictedProofStandardAdequacy
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy.

Import ListNotations.

Module PABoundedRawCodedProofAtomicAdequacyStandard.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermEvaluationStandardAdequacy.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaOperationQuotedRankSound.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.

(** ------------------------------------------------------------------
    Standard quoted terms. *)

(** Erasing the value column and all value-table lookups from one closed
    evaluator row leaves exactly the syntax row used by
    [RawTermSyntaxRealizable]. *)
Lemma raw_termEvaluationClosedStep_forget_to_syntax : forall
    (M : RawPAModel) code value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  RawTermEvaluationClosedStep M code value
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  RawTermSyntaxStep M code supportCode supportStep.
Proof.
  intros M code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep
    (left & leftValue & right & rightValue & hrow).
  exists left, right.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact (proj1 hvar).
  - right; left. exact (proj1 hzero).
  - right; right; left.
    destruct hsucc as [hoperation [hsupport hlt]].
    split; [exact (proj1 hoperation) |]. split; assumption.
  - right; right; right; left.
    destruct hadd as
      [hoperation [hleftSupport [hrightSupport [hleft hright]]]].
    split; [exact (proj1 hoperation) |].
    repeat split; assumption.
  - right; right; right; right.
    destruct hmul as
      [hoperation [hleftSupport [hrightSupport [hleft hright]]]].
    split; [exact (proj1 hoperation) |].
    repeat split; assumption.
Qed.

Lemma raw_termEvaluationTraversal_forget_to_syntax : forall
    (M : RawPAModel) bound assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  RawTermEvaluationTraversal M bound
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  RawTermSyntaxTraversal M bound supportCode supportStep.
Proof.
  intros M bound assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep [hsupport [_ hrows]].
  split; [exact hsupport |].
  intros code hcode hsupported.
  destruct (hrows code hcode hsupported) as [value [_ hstep]].
  exact (raw_termEvaluationClosedStep_forget_to_syntax M
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep hstep).
Qed.

(** Assignment definedness is contravariant in its strict bound. *)
Lemma raw_codedAssignmentDefinedThrough_weaken : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      code step small large,
  rawLe M small large ->
  RawCodedAssignmentDefinedThrough M code step large ->
  RawCodedAssignmentDefinedThrough M code step small.
Proof.
  intros M hPA code step small large hle hdefined index hindex.
  apply hdefined.
  exact (raw_lt_le_trans_pair M hPA index small large hindex hle).
Qed.

(** This is the precise meaning of "defined far enough" for a quoted term:
    the assignment must be defined below the successor of its code. *)
Theorem raw_quotedTerm_syntax_realizable_of_assignment : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      quoted assignmentCode assignmentStep,
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
    (raw_succ M (rawQuotedTermCode M quoted)) ->
  RawTermSyntaxRealizable M (rawQuotedTermCode M quoted)
    assignmentCode assignmentStep.
Proof.
  intros M hPA quoted assignmentCode assignmentStep hdefined.
  set (limit := S (termCode quoted)).
  assert (hfamily : forall index : nat, exists value : M,
      index < limit ->
      RawCodedAssignmentLookup M assignmentCode assignmentStep
        (rawNumeralValue M index) value).
  {
    intro index. destruct (lt_dec index limit) as [hindex | hindex].
    - assert (hbelow : rawLt M (rawNumeralValue M index)
          (raw_succ M (rawQuotedTermCode M quoted))).
      {
        rewrite rawQuotedTermCode_standard by exact hPA.
        change (rawLt M (rawNumeralValue M index)
          (rawNumeralValue M (S (termCode quoted)))).
        apply raw_lt_numeralValue_of_lt; [exact hPA |].
        unfold limit in hindex. exact hindex.
      }
      destruct (hdefined (rawNumeralValue M index) hbelow)
        as [value hlookup].
      exists value. intros _. exact hlookup.
    - exists (raw_zero M). intros hcontra. lia.
  }
  destruct (@choice nat M
    (fun index value => index < limit ->
      RawCodedAssignmentLookup M assignmentCode assignmentStep
        (rawNumeralValue M index) value) hfamily)
    as [environment henvironment].
  assert (hroot : termCode quoted < limit).
  { unfold limit. lia. }
  destruct
    (raw_termEvaluationCertificateWithTables_standard_of_assignment
      M hPA environment limit assignmentCode assignmentStep
      (fun index hindex => henvironment index hindex)
      quoted hroot)
    as (supportCode & supportStep & tableCode & tableStep &
      _ & _ & hcertificate).
  exists supportCode, supportStep.
  unfold RawTermSyntaxCertificateWithSupport.
  destruct hcertificate as [htraversal [hrootSupported _]].
  split.
  - exact (raw_termEvaluationTraversal_forget_to_syntax M
      (raw_succ M (rawQuotedTermCode M quoted))
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep htraversal).
  - split; [| exact hrootSupported].
    intros code hcode _ index hvar.
    assert (hindexCode : rawLt M index code).
    {
      rewrite hvar. unfold rawTermVarCode, rawCodeList2.
      apply rawProofListCode_member_lt; [exact hPA |].
      cbn. tauto.
    }
    apply hdefined.
    exact (raw_assignment_lt_trans M hPA index code
      (raw_succ M (rawQuotedTermCode M quoted)) hindexCode hcode).
Qed.

(** Quoted terms satisfy the assignment-parametric payload condition used
    by proof atomic adequacy. *)
Theorem raw_quotedTerm_universally_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall quoted,
  RawCodedTermUniversallyAdequate M (rawQuotedTermCode M quoted).
Proof.
  intros M hPA quoted assignmentCode assignmentStep hdefined.
  exact (raw_quotedTerm_syntax_realizable_of_assignment M hPA
    quoted assignmentCode assignmentStep hdefined).
Qed.

(** ------------------------------------------------------------------
    Standard quoted formulae. *)

Definition standardFormulaIdentity (_ : nat) (phi : formula) : formula :=
  phi.

Definition RawCodedFormulaIdentityAtom (M : RawPAModel)
    (_parameter _depth input output : M) : Prop := input = output.

Lemma standardFormulaIdentity_operation_shape :
  StandardFormulaOperationShape standardFormulaIdentity.
Proof. constructor; intros; reflexivity. Qed.

Lemma raw_standardFormulaIdentity_eq_row : forall
    (M : RawPAModel) depth lhs rhs,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaIdentityAtom M)
    (raw_zero M) (rawNumeralValue M depth)
    (rawQuotedFormulaCode M (pEq lhs rhs))
    (rawQuotedFormulaCode M
      (standardFormulaIdentity depth (pEq lhs rhs))).
Proof.
  intros M depth lhs rhs.
  exists (rawQuotedTermCode M lhs), (rawQuotedTermCode M lhs),
    (rawQuotedTermCode M rhs), (rawQuotedTermCode M rhs).
  repeat split; reflexivity.
Qed.

Lemma raw_quotedFormulaCode_eq_code_inv : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi left right,
  rawQuotedFormulaCode M phi = rawFormulaEqCode M left right ->
  exists quotedLeft quotedRight,
    phi = pEq quotedLeft quotedRight /\
    left = rawQuotedTermCode M quotedLeft /\
    right = rawQuotedTermCode M quotedRight.
Proof.
  intros M hPA phi left right hcode.
  destruct phi as
    [quotedLeft quotedRight | | lhs rhs | lhs rhs | lhs rhs | child | child];
    cbn [rawQuotedFormulaCode] in hcode.
  - exists quotedLeft, quotedRight. split; [reflexivity |].
    unfold rawFormulaEqCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [_ [hleft hright]].
    split; symmetry; assumption.
  - exfalso.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact hcode.
  - exfalso.
    unfold rawFormulaImpCode, rawFormulaEqCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [htag _].
    apply (rawNumeralValue_injective M hPA 2 0) in htag. discriminate.
  - exfalso.
    unfold rawFormulaAndCode, rawFormulaEqCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [htag _].
    apply (rawNumeralValue_injective M hPA 3 0) in htag. discriminate.
  - exfalso.
    unfold rawFormulaOrCode, rawFormulaEqCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [htag _].
    apply (rawNumeralValue_injective M hPA 4 0) in htag. discriminate.
  - exfalso.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) (rawQuotedFormulaCode M child)
      (rawNumeralValue M 0) left right).
    exact hcode.
  - exfalso.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) (rawQuotedFormulaCode M child)
      (rawNumeralValue M 0) left right).
    exact hcode.
Qed.

Lemma raw_quotedFormula_eq_left_term_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M (rawQuotedTermCode M left)
    (rawQuotedFormulaCode M (pEq left right)).
Proof.
  intros M hPA left right. cbn [rawQuotedFormulaCode].
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_quotedFormula_eq_right_term_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M (rawQuotedTermCode M right)
    (rawQuotedFormulaCode M (pEq left right)).
Proof.
  intros M hPA left right. cbn [rawQuotedFormulaCode].
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

(** The identity-operation schedule is only a convenient finite postorder
    enumeration.  Its target and depth tables let the generic operation-row
    theorem establish each source syntax row; atomic adequacy uses the exact
    source-table lookup retained below. *)
Theorem raw_quotedFormula_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  RawCodedFormulaAtomicallyAdequate M (rawQuotedFormulaCode M phi).
Proof.
  intros M hPA phi.
  set (schedule := standardFormulaOperationSchedule
    standardFormulaIdentity 0 phi).
  set (limit := length schedule).
  assert (hlimitPositive : 0 < limit).
  {
    unfold limit, schedule.
    apply standardFormulaOperationSchedule_length_positive.
  }
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationSourceAt M schedule)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationTargetAt M schedule)) as
    [targetCode [targetStep htarget]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaOperationDepthAt M schedule)) as
    [depthCode [depthStep hdepth]].
  assert (hscheduleLookup : forall index occurrence,
      nth_error schedule index = Some occurrence ->
      RawCodedFormulaOperationTripleLookup M
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        (rawNumeralValue M index)
        (rawQuotedFormulaCode M (standardOccurrenceSource occurrence))
        (rawQuotedFormulaCode M (standardOccurrenceTarget occurrence))
        (rawNumeralValue M (standardOccurrenceDepth occurrence))).
  {
    intros index occurrence hnth.
    assert (hindex : index < limit).
    {
      unfold limit. apply (proj1 (nth_error_Some schedule index)).
      now rewrite hnth.
    }
    split.
    - rewrite <- (rawStandardFormulaOperationSourceAt_nth_error
        M schedule index occurrence hnth).
      exact (hsource index hindex).
    - split.
      + rewrite <- (rawStandardFormulaOperationTargetAt_nth_error
          M schedule index occurrence hnth).
        exact (htarget index hindex).
      + rewrite <- (rawStandardFormulaOperationDepthAt_nth_error
          M schedule index occurrence hnth).
        exact (hdepth index hindex).
  }
  exists sourceCode, sourceStep, (rawNumeralValue M limit),
    (rawNumeralValue M (Nat.pred limit)).
  split.
  - unfold RawCodedFormulaSyntaxTraversal.
    split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
        as [k [hk ->]].
      exists (rawStandardFormulaOperationSourceAt M schedule k).
      exact (hsource k hk).
    + split.
      * apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
      * split.
        -- assert (hrootNth : nth_error schedule (Nat.pred limit) =
              Some (standardFormulaOperationRoot
                standardFormulaIdentity 0 phi)).
           {
             unfold schedule, limit.
             apply standardFormulaOperationSchedule_root.
           }
           pose proof (hscheduleLookup _ _ hrootNth) as hrootLookup.
           unfold standardFormulaOperationRoot,
             standardFormulaIdentity in hrootLookup.
           exact (proj1 hrootLookup).
        -- intros index code hindex hcode.
           destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
             as [k [hk ->]].
           assert (hnonempty : nth_error schedule k <> None).
           {
             apply (proj2 (nth_error_Some schedule k)). exact hk.
           }
           destruct (nth_error schedule k) as [occurrence |]
             eqn:hnth; [|contradiction].
           pose proof (hscheduleLookup k occurrence hnth) as
             hcanonical.
           assert (hcodeEq : code = rawQuotedFormulaCode M
               (standardOccurrenceSource occurrence)).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               sourceCode sourceStep (rawNumeralValue M k) code
               (rawQuotedFormulaCode M
                 (standardOccurrenceSource occurrence))
               hcode (proj1 hcanonical)).
           }
           subst code.
           apply (raw_formulaOperationTraversalRow_source_syntax M
             (RawCodedFormulaIdentityAtom M) (raw_zero M)
             sourceCode sourceStep targetCode targetStep
             depthCode depthStep (rawNumeralValue M k)
             (rawQuotedFormulaCode M
               (standardOccurrenceSource occurrence))
             (rawQuotedFormulaCode M
               (standardOccurrenceTarget occurrence))
             (rawNumeralValue M
               (standardOccurrenceDepth occurrence))).
           apply (raw_standardFormulaOperation_segment_row M hPA
             (RawCodedFormulaIdentityAtom M) (raw_zero M)
             standardFormulaIdentity
             standardFormulaIdentity_operation_shape
             (raw_standardFormulaIdentity_eq_row M)
             sourceCode sourceStep targetCode targetStep
             depthCode depthStep 0 0 phi).
           ++ unfold RawStandardFormulaOperationSegmentLookup.
              intros local localOccurrence hlocal. cbn.
              exact (hscheduleLookup local localOccurrence hlocal).
           ++ exact hnth.
  - unfold RawCodedFormulaAtomicTermAdequate.
    intros index code left right assignmentCode assignmentStep
      hindex hcode hequality hassignment.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    assert (hnonempty : nth_error schedule k <> None).
    {
      apply (proj2 (nth_error_Some schedule k)). exact hk.
    }
    destruct (nth_error schedule k) as [occurrence |]
      eqn:hnth; [|contradiction].
    pose proof (hscheduleLookup k occurrence hnth) as hcanonical.
    assert (hcodeEq : code = rawQuotedFormulaCode M
        (standardOccurrenceSource occurrence)).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceCode sourceStep (rawNumeralValue M k) code
        (rawQuotedFormulaCode M (standardOccurrenceSource occurrence))
        hcode (proj1 hcanonical)).
    }
    assert (hquotedEq : rawQuotedFormulaCode M
        (standardOccurrenceSource occurrence) =
        rawFormulaEqCode M left right).
    { exact (eq_trans (eq_sym hcodeEq) hequality). }
    destruct (raw_quotedFormulaCode_eq_code_inv M hPA
      (standardOccurrenceSource occurrence) left right hquotedEq)
      as (quotedLeft & quotedRight & hsourceShape & hleft & hright).
    subst left. subst right. subst code.
    split.
    + apply raw_quotedTerm_syntax_realizable_of_assignment; [exact hPA |].
      eapply raw_codedAssignmentDefinedThrough_weaken;
        [exact hPA | | exact hassignment].
      apply raw_succ_le_of_lt_pair; [exact hPA |].
      unfold rawFormulaEqCode, rawCodeList3.
      apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
    + apply raw_quotedTerm_syntax_realizable_of_assignment; [exact hPA |].
      eapply raw_codedAssignmentDefinedThrough_weaken;
        [exact hPA | | exact hassignment].
      apply raw_succ_le_of_lt_pair; [exact hPA |].
      unfold rawFormulaEqCode, rawCodeList3.
      apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

(** ------------------------------------------------------------------
    Standard quoted contexts. *)

Theorem raw_contextAllAtomicallyAdequate_empty : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextAllAtomicallyAdequate M (raw_zero M).
Proof.
  intros M hPA.
  destruct (raw_contextList_zero_traversal_exists M hPA)
    as (tailCode & tailStep & htraversal).
  exists (raw_zero M), tailCode, tailStep, (raw_zero M), (raw_zero M).
  split; [exact htraversal |].
  intros index hindex code _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Theorem raw_contextAllAtomicallyAdequate_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall root head,
  RawContextAllAtomicallyAdequate M root ->
  RawCodedFormulaAtomicallyAdequate M head ->
  RawContextAllAtomicallyAdequate M (rawListNode M head root).
Proof.
  intros M hPA root head
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall) hhead.
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  intros index hindex code hlookup.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - apply (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep code
      hheadPrepend)) in hlookup.
    subst code. exact hhead.
  - assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
    { exact (raw_assignment_lt_self_succ M hPA predecessor). }
    assert (hpredBound : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound hpredSelf hlt).
      - rewrite <- heq. exact hpredSelf.
    }
    apply (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep
      (proj1 (proj2 (proj2 htraversal))) hheadPrepend
      predecessor hpredBound code)) in hlookup.
    exact (hall predecessor hpredBound code hlookup).
Qed.

Theorem raw_quotedContext_all_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall context,
  RawContextAllAtomicallyAdequate M (rawQuotedContextCode M context).
Proof.
  intros M hPA context. induction context as [|head tail IH].
  - cbn [rawQuotedContextCode].
    apply raw_contextAllAtomicallyAdequate_empty. exact hPA.
  - cbn [rawQuotedContextCode].
    apply raw_contextAllAtomicallyAdequate_cons; [exact hPA | exact IH |].
    apply raw_quotedFormula_atomically_adequate. exact hPA.
Qed.

(** ------------------------------------------------------------------
    Standard-output soundness for arbitrary term-operation traces.

    The public operation relations existentially hide their beta tables.
    Merely exhibiting the canonical finite trace therefore does not identify
    the output of a second advertised trace.  The next theorem instead
    follows that second trace itself, by induction on the external input
    term.  Constructor separation selects its unique source row, and the
    strictly smaller occurrence indices justify rerooting at children. *)

Ltac raw_standard_term_shape_contradiction M hPA h :=
  first
    [ exact (raw_termVarCode_neq_termZeroCode M hPA _ h)
    | exact (raw_termVarCode_neq_termZeroCode M hPA _ (eq_sym h))
    | exact (raw_termVarCode_neq_termSuccCode M hPA _ _ h)
    | exact (raw_termVarCode_neq_termSuccCode M hPA _ _ (eq_sym h))
    | exact (raw_termVarCode_neq_termAddCode M hPA _ _ _ h)
    | exact (raw_termVarCode_neq_termAddCode M hPA _ _ _ (eq_sym h))
    | exact (raw_termVarCode_neq_termMulCode M hPA _ _ _ h)
    | exact (raw_termVarCode_neq_termMulCode M hPA _ _ _ (eq_sym h))
    | exact (raw_termZeroCode_neq_termSuccCode M hPA _ h)
    | exact (raw_termZeroCode_neq_termSuccCode M hPA _ (eq_sym h))
    | exact (raw_termZeroCode_neq_termAddCode M hPA _ _ h)
    | exact (raw_termZeroCode_neq_termAddCode M hPA _ _ (eq_sym h))
    | exact (raw_termZeroCode_neq_termMulCode M hPA _ _ h)
    | exact (raw_termZeroCode_neq_termMulCode M hPA _ _ (eq_sym h))
    | exact (raw_termSuccCode_neq_termAddCode M hPA _ _ _ h)
    | exact (raw_termSuccCode_neq_termAddCode M hPA _ _ _ (eq_sym h))
    | exact (raw_termSuccCode_neq_termMulCode M hPA _ _ _ h)
    | exact (raw_termSuccCode_neq_termMulCode M hPA _ _ _ (eq_sym h))
    | exact (raw_termAddCode_neq_termMulCode M hPA _ _ _ _ h)
    | exact (raw_termAddCode_neq_termMulCode M hPA _ _ _ _ (eq_sym h)) ].

Theorem raw_codedTermOperation_quoted_sound_generic : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (variableRow : M -> M -> Prop) (transform : term -> term),
  (forall quoted output,
    variableRow (rawQuotedTermCode M quoted) output ->
    output = rawQuotedTermCode M (transform quoted)) ->
  transform tZero = tZero ->
  (forall child,
    transform (tSucc child) = tSucc (transform child)) ->
  (forall left right,
    transform (tAdd left right) =
      tAdd (transform left) (transform right)) ->
  (forall left right,
    transform (tMul left right) =
      tMul (transform left) (transform right)) ->
  forall sourceCode sourceStep targetCode targetStep bound,
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep bound ->
  forall quoted rootIndex output,
  rawLt M rootIndex bound ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep
    rootIndex (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M (transform quoted).
Proof.
  intros M hPA variableRow transform hvariable
    hzeroTransform hsuccTransform haddTransform hmulTransform
    sourceCode sourceStep targetCode targetStep bound hrows quoted.
  induction quoted as
    [index | | child IH | left IHleft right IHright |
      left IHleft right IHright];
    intros rootIndex output hroot hlookup;
    pose proof (hrows rootIndex _ output hroot hlookup) as hrow;
    cbn [rawQuotedTermCode] in hrow |- *.
  - destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable (tVar index) output hvar).
    + exfalso. destruct hzero as [hinput _].
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hsucc as
        (childIndex & inputChild & outputChild & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable tZero output hvar).
    + destruct hzero as [_ houtput].
      rewrite hzeroTransform. exact houtput.
    + exfalso. destruct hsucc as
        (childIndex & inputChild & outputChild & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable (tSucc child) output hvar).
    + exfalso. destruct hzero as [hinput _].
      raw_standard_term_shape_contradiction M hPA hinput.
    + destruct hsucc as
        (childIndex & inputChild & outputChild & hchildIndex &
          hchildLookup & hinput & houtput).
      unfold rawTermSuccCode in hinput.
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ hinput) as [_ hchild].
      subst inputChild.
      assert (hchildRoot : rawLt M childIndex bound).
      { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
          hchildIndex hroot). }
      pose proof (IH childIndex outputChild hchildRoot hchildLookup)
        as hchildOutput.
      rewrite houtput, hsuccTransform.
      cbn [rawQuotedTermCode]. now rewrite hchildOutput.
    + exfalso. destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable (tAdd left right) output hvar).
    + exfalso. destruct hzero as [hinput _].
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hsucc as
        (childIndex & inputChild & outputChild & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & hleftIndex & hleftLookup & hrightIndex &
          hrightLookup & hinput & houtput).
      unfold rawTermAddCode in hinput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ hinput) as [_ [hleft hright]].
      subst inputLeft. subst inputRight.
      assert (hleftRoot : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hroot). }
      assert (hrightRoot : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hroot). }
      pose proof (IHleft leftIndex outputLeft hleftRoot hleftLookup)
        as hleftOutput.
      pose proof (IHright rightIndex outputRight hrightRoot hrightLookup)
        as hrightOutput.
      rewrite houtput, haddTransform.
      cbn [rawQuotedTermCode]. now rewrite hleftOutput, hrightOutput.
    + exfalso. destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable (tMul left right) output hvar).
    + exfalso. destruct hzero as [hinput _].
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hsucc as
        (childIndex & inputChild & outputChild & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + exfalso. destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & _ & _ & _ & _ & hinput & _).
      raw_standard_term_shape_contradiction M hPA hinput.
    + destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
          outputRight & hleftIndex & hleftLookup & hrightIndex &
          hrightLookup & hinput & houtput).
      unfold rawTermMulCode in hinput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ hinput) as [_ [hleft hright]].
      subst inputLeft. subst inputRight.
      assert (hleftRoot : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hroot). }
      assert (hrightRoot : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hroot). }
      pose proof (IHleft leftIndex outputLeft hleftRoot hleftLookup)
        as hleftOutput.
      pose proof (IHright rightIndex outputRight hrightRoot hrightLookup)
        as hrightOutput.
      rewrite houtput, hmulTransform.
      cbn [rawQuotedTermCode]. now rewrite hleftOutput, hrightOutput.
Qed.

Lemma raw_lt_numeral_values_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower upper,
  rawLt M (rawNumeralValue M lower) (rawNumeralValue M upper) ->
  lower < upper.
Proof.
  intros M hPA lower upper hlt.
  destruct (raw_lt_numeralValue_cases M hPA
    (rawNumeralValue M lower) upper hlt) as [actual [hactual heq]].
  apply (rawNumeralValue_injective M hPA lower actual) in heq.
  lia.
Qed.

Lemma raw_shiftedIndex_standard_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output,
  RawShiftedIndex M (rawNumeralValue M cutoff)
    (rawNumeralValue M amount) (rawNumeralValue M input) output ->
  output = rawNumeralValue M
    (if input <? cutoff then input else input + amount).
Proof.
  intros M hPA cutoff amount input output
    [[hlow ->] | [hhigh ->]].
  - assert (hmeta : input < cutoff).
    { exact (raw_lt_numeral_values_sound M hPA input cutoff hlow). }
    assert (hcheck : (input <? cutoff) = true).
    { apply Nat.ltb_lt. exact hmeta. }
    now rewrite hcheck.
  - assert (hnotLow : ~ input < cutoff).
    {
      intro hmeta.
      pose proof (raw_lt_numeralValue_of_lt M hPA input cutoff hmeta)
        as hrawLow.
      apply (raw_not_lt_self M hPA (rawNumeralValue M input)).
      exact (raw_lt_le_trans_pair M hPA
        (rawNumeralValue M input) (rawNumeralValue M cutoff)
        (rawNumeralValue M input) hrawLow hhigh).
    }
    assert (hcheck : (input <? cutoff) = false).
    { apply Nat.ltb_ge. lia. }
    rewrite hcheck.
    apply raw_add_numeral_values_syntax. exact hPA.
Qed.

Lemma raw_codedTermShiftVariableRow_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount quoted output,
  RawCodedTermShiftVariableRow M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M
    (standardTermShift cutoff amount quoted).
Proof.
  intros M hPA cutoff amount quoted output
    (inputIndex & outputIndex & hinput & houtput & hshift).
  destruct quoted as [index | | child | left right | left right];
    cbn [rawQuotedTermCode standardTermShift] in hinput |- *.
  - unfold rawTermVarCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hindex].
    subst inputIndex.
    rewrite houtput.
    unfold rawTermVarCode.
    rewrite (raw_shiftedIndex_standard_sound M hPA
      cutoff amount index outputIndex hshift).
    destruct (index <? cutoff); reflexivity.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Theorem raw_codedTermShift_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount quoted output,
  RawCodedTermShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M
    (standardTermShift cutoff amount quoted).
Proof.
  intros M hPA cutoff amount quoted output
    (sourceCode & sourceStep & targetCode & targetStep & bound & rootIndex &
      _ & _ & hroot & hlookup & hrows & _).
  eapply (raw_codedTermOperation_quoted_sound_generic M hPA
    (RawCodedTermShiftVariableRow M
      (rawNumeralValue M cutoff) (rawNumeralValue M amount))
    (standardTermShift cutoff amount)).
  - apply raw_codedTermShiftVariableRow_quoted_sound. exact hPA.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - unfold RawCodedTermShiftRows,
      RawCodedTermShiftTraversalRow in hrows.
    exact hrows.
  - exact hroot.
  - exact hlookup.
Qed.

Lemma raw_codedTermOpeningVariableRow_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff replacement quoted output,
  RawCodedTermOpeningVariableRow M
    (rawNumeralValue M cutoff) (rawQuotedTermCode M replacement)
    (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M
    (standardTermOpening cutoff replacement quoted).
Proof.
  intros M hPA cutoff replacement quoted output
    (inputIndex & hinput & hcases).
  destruct quoted as [index | | child | left right | left right];
    cbn [rawQuotedTermCode standardTermOpening] in hinput |- *.
  - unfold rawTermVarCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hindex].
    subst inputIndex.
    destruct hcases as [[hlow houtput] |
      [[hequal houtput] | [predecessor [hsucc [hhigh houtput]]]]].
    + assert (hmeta : index < cutoff).
      { exact (raw_lt_numeral_values_sound M hPA index cutoff hlow). }
      assert (hcheck : (index <? cutoff) = true).
      { apply Nat.ltb_lt. exact hmeta. }
      rewrite hcheck.
      exact houtput.
    + apply (rawNumeralValue_injective M hPA index cutoff) in hequal.
      subst index.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. exact houtput.
    + destruct index as [|index].
      * cbn [rawNumeralValue] in hsucc.
        exfalso. exact (raw_zero_not_succ_syntax M hPA predecessor hsucc).
      * cbn [rawNumeralValue] in hsucc.
        apply (raw_succ_injective_syntax M hPA) in hsucc.
        subst predecessor.
        assert (hmeta : cutoff < S index).
        {
          exact (raw_lt_numeral_values_sound M hPA cutoff (S index)
            hhigh).
        }
        assert (hlowCheck : (S index <? cutoff) = false).
        { apply Nat.ltb_ge. lia. }
        assert (heqCheck : (S index =? cutoff) = false).
        { apply Nat.eqb_neq. lia. }
        rewrite hlowCheck, heqCheck.
        cbn [Nat.pred]. exact houtput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Theorem raw_codedTermOpening_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff replacement quoted output,
  RawCodedTermOpening M
    (rawNumeralValue M cutoff) (rawQuotedTermCode M replacement)
    (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M
    (standardTermOpening cutoff replacement quoted).
Proof.
  intros M hPA cutoff replacement quoted output
    (sourceCode & sourceStep & targetCode & targetStep & bound & rootIndex &
      _ & _ & hroot & hlookup & hrows).
  eapply (raw_codedTermOperation_quoted_sound_generic M hPA
    (RawCodedTermOpeningVariableRow M
      (rawNumeralValue M cutoff) (rawQuotedTermCode M replacement))
    (standardTermOpening cutoff replacement)).
  - apply raw_codedTermOpeningVariableRow_quoted_sound. exact hPA.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - unfold RawCodedTermOpeningRows,
      RawCodedTermOpeningTraversalRow in hrows.
    exact hrows.
  - exact hroot.
  - exact hlookup.
Qed.

Lemma raw_codedFormulaSubstitutionAtom_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth quoted output,
  RawCodedFormulaSubstitutionAtom M
    (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
    (rawQuotedTermCode M quoted) output ->
  output = rawQuotedTermCode M
    (standardTermOpening depth
      (standardTermShift 0 depth replacement) quoted).
Proof.
  intros M hPA replacement depth quoted output
    (liftedReplacement & hshift & hopening).
  change (rawNumeralValue M 0) with (raw_zero M) in hshift.
  pose proof (raw_codedTermShift_quoted_sound M hPA
    0 depth replacement liftedReplacement hshift) as hlifted.
  rewrite hlifted in hopening.
  exact (raw_codedTermOpening_quoted_sound M hPA depth
    (standardTermShift 0 depth replacement) quoted output hopening).
Qed.

Ltac raw_standard_formula_shape_contradiction M hPA h :=
  unfold rawFormulaEqCode, rawFormulaBotCode, rawFormulaImpCode,
    rawFormulaAndCode, rawFormulaOrCode, rawFormulaAllCode,
    rawFormulaExCode in h;
  first
    [ exact (raw_codeList1_neq_codeList2 M hPA
        (rawListNode_injective M hPA) _ _ _ h)
    | exact (raw_codeList1_neq_codeList2 M hPA
        (rawListNode_injective M hPA) _ _ _ (eq_sym h))
    | exact (raw_codeList1_neq_codeList3 M hPA
        (rawListNode_injective M hPA) _ _ _ _ h)
    | exact (raw_codeList1_neq_codeList3 M hPA
        (rawListNode_injective M hPA) _ _ _ _ (eq_sym h))
    | exact (raw_codeList2_neq_codeList3 M hPA
        (rawListNode_injective M hPA) _ _ _ _ _ h)
    | exact (raw_codeList2_neq_codeList3 M hPA
        (rawListNode_injective M hPA) _ _ _ _ _ (eq_sym h))
    | let htag := fresh "htag" in
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ h) as [htag _];
      apply (rawNumeralValue_injective M hPA _ _) in htag;
      discriminate
    | let htag := fresh "htag" in
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ h) as [htag _];
      apply (rawNumeralValue_injective M hPA _ _) in htag;
      discriminate ].

Ltac raw_standard_formula_row_contradiction M hPA :=
  match goal with
  | h : RawCodedFormulaEqOperationRow _ _ _ _ _ _ |- False =>
      let inputLeft := fresh "inputLeft" in
      let outputLeft := fresh "outputLeft" in
      let inputRight := fresh "inputRight" in
      let outputRight := fresh "outputRight" in
      let hinput := fresh "hinput" in
      destruct h as
        (inputLeft & outputLeft & inputRight & outputRight & hinput & _);
      raw_standard_formula_shape_contradiction M hPA hinput
  | h : RawCodedFormulaBotOperationRow _ _ _ |- False =>
      let hinput := fresh "hinput" in
      destruct h as [hinput _];
      raw_standard_formula_shape_contradiction M hPA hinput
  | h : RawCodedFormulaBinaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _
      |- False =>
      let leftIndex := fresh "leftIndex" in
      let inputLeft := fresh "inputLeft" in
      let outputLeft := fresh "outputLeft" in
      let leftDepth := fresh "leftDepth" in
      let rightIndex := fresh "rightIndex" in
      let inputRight := fresh "inputRight" in
      let outputRight := fresh "outputRight" in
      let rightDepth := fresh "rightDepth" in
      let hinput := fresh "hinput" in
      destruct h as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         _ & _ & _ & _ & _ & _ & hinput & _);
      raw_standard_formula_shape_contradiction M hPA hinput
  | h : RawCodedFormulaUnaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _
      |- False =>
      let childIndex := fresh "childIndex" in
      let inputChild := fresh "inputChild" in
      let outputChild := fresh "outputChild" in
      let childDepth := fresh "childDepth" in
      let hinput := fresh "hinput" in
      destruct h as
        (childIndex & inputChild & outputChild & childDepth &
         _ & _ & _ & hinput & _);
      raw_standard_formula_shape_contradiction M hPA hinput
  end.

(** Arbitrary traces of single substitution are functional on standard
    inputs.  This is stronger than existence of the canonical trace: the
    advertised trace itself is rerooted at its child occurrences. *)
Theorem raw_codedFormulaSingleSubstitution_at_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement phi,
  forall depth output,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
    (rawQuotedFormulaCode M phi) output ->
  output = rawQuotedFormulaCode M
    (standardFormulaSingleSubstitution replacement depth phi).
Proof.
  intros M hPA replacement phi.
  induction phi as
    [leftTerm rightTerm
    | (* bottom *)
    | leftFormula IHleft rightFormula IHright
    | leftFormula IHleft rightFormula IHright
    | leftFormula IHleft rightFormula IHright
    | child IHchild
    | child IHchild];
    intros depth output
      (sourceCode & sourceStep & targetCode & targetStep &
       depthCode & depthStep & bound & rootIndex & htrace).
  all: pose proof htrace as htraceFacts.
  all: destruct htraceFacts as
      (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
       hrootLookup & hrows).
  all: pose proof (hrows rootIndex _ _ _ hrootBelow hrootLookup) as hrow.
  all: cbn [rawQuotedFormulaCode standardFormulaSingleSubstitution]
      in hrow |- *.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
        hinput & houtput & hleftAtom & hrightAtom).
    unfold rawFormulaEqCode in hinput.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hinput) as [_ [hleft hright]].
    subst inputLeft. subst inputRight.
    pose proof (raw_codedFormulaSubstitutionAtom_quoted_sound M hPA
      replacement depth leftTerm outputLeft hleftAtom) as hleftOutput.
    pose proof (raw_codedFormulaSubstitutionAtom_quoted_sound M hPA
      replacement depth rightTerm outputRight hrightAtom) as hrightOutput.
    rewrite houtput, hleftOutput, hrightOutput. reflexivity.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    exact (proj2 hbot).
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct himp as
        (leftIndex & inputLeft & outputLeft & leftDepth &
          rightIndex & inputRight & outputRight & rightDepth &
          hleftIndex & hleftLookup & hleftDepth & hrightIndex &
          hrightLookup & hrightDepth & hinput & houtput).
      unfold rawFormulaImpCode in hinput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ hinput) as [_ [hleft hright]].
      subst inputLeft. subst inputRight. subst leftDepth. subst rightDepth.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace leftIndex
        (rawQuotedFormulaCode M leftFormula) outputLeft
        (rawNumeralValue M depth) hleftIndex hleftLookup) as hleftOperation.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace rightIndex
        (rawQuotedFormulaCode M rightFormula) outputRight
        (rawNumeralValue M depth) hrightIndex hrightLookup) as hrightOperation.
      pose proof (IHleft depth outputLeft hleftOperation) as hleftOutput.
      pose proof (IHright depth outputRight hrightOperation) as hrightOutput.
    rewrite houtput, hleftOutput, hrightOutput. reflexivity.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct hand as
        (leftIndex & inputLeft & outputLeft & leftDepth &
          rightIndex & inputRight & outputRight & rightDepth &
          hleftIndex & hleftLookup & hleftDepth & hrightIndex &
          hrightLookup & hrightDepth & hinput & houtput).
      unfold rawFormulaAndCode in hinput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ hinput) as [_ [hleft hright]].
      subst inputLeft. subst inputRight. subst leftDepth. subst rightDepth.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace leftIndex
        (rawQuotedFormulaCode M leftFormula) outputLeft
        (rawNumeralValue M depth) hleftIndex hleftLookup) as hleftOperation.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace rightIndex
        (rawQuotedFormulaCode M rightFormula) outputRight
        (rawNumeralValue M depth) hrightIndex hrightLookup) as hrightOperation.
      pose proof (IHleft depth outputLeft hleftOperation) as hleftOutput.
    pose proof (IHright depth outputRight hrightOperation) as hrightOutput.
    rewrite houtput, hleftOutput, hrightOutput. reflexivity.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct hor as
        (leftIndex & inputLeft & outputLeft & leftDepth &
          rightIndex & inputRight & outputRight & rightDepth &
          hleftIndex & hleftLookup & hleftDepth & hrightIndex &
          hrightLookup & hrightDepth & hinput & houtput).
      unfold rawFormulaOrCode in hinput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ hinput) as [_ [hleft hright]].
      subst inputLeft. subst inputRight. subst leftDepth. subst rightDepth.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace leftIndex
        (rawQuotedFormulaCode M leftFormula) outputLeft
        (rawNumeralValue M depth) hleftIndex hleftLookup) as hleftOperation.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace rightIndex
        (rawQuotedFormulaCode M rightFormula) outputRight
        (rawNumeralValue M depth) hrightIndex hrightLookup) as hrightOperation.
      pose proof (IHleft depth outputLeft hleftOperation) as hleftOutput.
    pose proof (IHright depth outputRight hrightOperation) as hrightOutput.
    rewrite houtput, hleftOutput, hrightOutput. reflexivity.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct hall as
        (childIndex & inputChild & outputChild & childDepth &
          hchildIndex & hchildLookup & hchildDepth & hinput & houtput).
      unfold rawFormulaAllCode in hinput.
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ hinput) as [_ hchild].
      subst inputChild. subst childDepth.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace childIndex
        (rawQuotedFormulaCode M child) outputChild
        (raw_succ M (rawNumeralValue M depth))
        hchildIndex hchildLookup) as hchildOperation.
      change (RawCodedFormulaOperation M
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M (S depth))
        (rawQuotedFormulaCode M child) outputChild) in hchildOperation.
    pose proof (IHchild (S depth) outputChild hchildOperation)
      as hchildOutput.
    rewrite houtput, hchildOutput. reflexivity.
  - destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    all: try solve [exfalso;
      raw_standard_formula_row_contradiction M hPA].
    destruct hex as
        (childIndex & inputChild & outputChild & childDepth &
          hchildIndex & hchildLookup & hchildDepth & hinput & houtput).
      unfold rawFormulaExCode in hinput.
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ hinput) as [_ hchild].
      subst inputChild. subst childDepth.
      pose proof (raw_formulaOperationTrace_reroot M hPA
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M depth)
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex _ output htrace childIndex
        (rawQuotedFormulaCode M child) outputChild
        (raw_succ M (rawNumeralValue M depth))
        hchildIndex hchildLookup) as hchildOperation.
      change (RawCodedFormulaOperation M
        (RawCodedFormulaSubstitutionAtom M)
        (rawQuotedTermCode M replacement) (rawNumeralValue M (S depth))
        (rawQuotedFormulaCode M child) outputChild) in hchildOperation.
    pose proof (IHchild (S depth) outputChild hchildOperation)
      as hchildOutput.
    rewrite houtput, hchildOutput. reflexivity.
Qed.

Theorem raw_codedFormulaSingleSubstitution_quoted_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement phi output,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M replacement) (rawQuotedFormulaCode M phi) output ->
  output = rawQuotedFormulaCode M
    (Formula.subst (Formula.instTerm replacement) phi).
Proof.
  intros M hPA replacement phi output hsubstitution.
  unfold RawCodedFormulaSingleSubstitution in hsubstitution.
  change (rawNumeralValue M 0) with (raw_zero M) in hsubstitution.
  pose proof (raw_codedFormulaSingleSubstitution_at_quoted_sound
    M hPA replacement phi 0 output hsubstitution) as hsound.
  rewrite standardFormulaSingleSubstitution_zero in hsound.
  exact hsound.
Qed.

(** Every endpoint admitted by a standard proof constructor is standard as
    well.  The two rules whose endpoint relation contains an existential
    substitution output use the arbitrary-trace soundness theorem above. *)
Lemma raw_quotedProof_endpoint_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  RawProofEndpointAtomicallyAdequate M
    (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation context conclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hrowContext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat destruct hcases as [hcases | hcases]; try contradiction.
  all: destruct hcases as [hcode hrest].
  all: destruct derivation.
  all: cbn [rawQuotedProofCode rawListCode] in hcode.
  all: repeat match goal with
  | hnodes : rawListNode ?model ?head ?tail =
      rawListNode ?model ?head' ?tail' |- _ =>
      destruct (rawListNode_injective model hPA
        head tail head' tail' hnodes) as [? ?]; clear hnodes
  end.
  all: try match goal with
  | hnil : raw_zero ?model = rawListNode ?model ?head ?tail |- _ =>
      exfalso; exact (rawListNode_not_zero model hPA head tail hnil)
  | hnil : rawListNode ?model ?head ?tail = raw_zero ?model |- _ =>
      exfalso; apply (rawListNode_not_zero model hPA head tail);
      exact hnil
  end.
  all: subst.
  all: cbn [rawNumeralValue] in *.
  all: repeat match goal with
  | htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hPA) in htag
  end.
  all: try match goal with
  | htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hPA value htag)
  | htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hPA value);
      symmetry; exact htag
  end.
  all: split.
  all: try
    (rewrite <- rawQuotedContextCode_standard by exact hPA;
     apply raw_quotedContext_all_atomically_adequate; exact hPA).
  all: repeat match type of hrest with
  | _ /\ _ => destruct hrest as [? hrest]
  end.
  all: subst.
  all: try match goal with
  | hop : RawCodedFormulaSingleSubstitution ?model
      (rawQuotedTermCode ?model ?replacement)
      (rawQuotedFormulaCode ?model ?phi) ?operationOutput
      |- RawCodedFormulaAtomicallyAdequate ?model ?operationOutput =>
      let hsound := fresh "hsound" in
      pose proof (raw_codedFormulaSingleSubstitution_quoted_sound
        model hPA replacement phi operationOutput hop) as hsound;
      rewrite hsound;
      apply raw_quotedFormula_atomically_adequate; exact hPA
  end.
  all: match goal with
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaEqCode ?model
        (rawQuotedTermCode ?model ?left)
        (rawQuotedTermCode ?model ?right)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pEq left right)))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaBotCode ?model) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model pBot))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaImpCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pImp left right)))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaAndCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pAnd left right)))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaOrCode ?model
        (rawQuotedFormulaCode ?model ?body)
        (rawFormulaImpCode ?model
          (rawQuotedFormulaCode ?model ?body)
          (rawFormulaBotCode ?model))) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pOr body (pImp body pBot))))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaOrCode ?model
        (rawQuotedFormulaCode ?model ?left)
        (rawQuotedFormulaCode ?model ?right)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pOr left right)))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaAllCode ?model (rawQuotedFormulaCode ?model ?child)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pAll child)))
  | |- RawCodedFormulaAtomicallyAdequate ?model
      (rawFormulaExCode ?model (rawQuotedFormulaCode ?model ?child)) =>
      change (RawCodedFormulaAtomicallyAdequate model
        (rawQuotedFormulaCode model (pEx child)))
  | _ => idtac
  end.
  all: apply raw_quotedFormula_atomically_adequate; exact hPA.
Qed.

(** Every formula and term carried directly by a standard constructor is a
    standard quotation.  The generic constructor relation has eight witness
    fields, many of which are unconstrained in a particular rule; list-code
    injectivity is therefore used to identify only the fields actually
    stored by the matching constructor before proving their adequacy. *)
Ltac solve_raw_quoted_constructor_payload hPA :=
  first
    [ left; repeat split;
        first
          [ reflexivity
          | apply raw_quotedFormula_atomically_adequate; exact hPA
          | apply raw_quotedTerm_universally_adequate; exact hPA ]
    | right; solve_raw_quoted_constructor_payload hPA ].

Lemma raw_quotedProof_constructor_payloads_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  RawProofConstructorPayloadsAtomicallyAdequate M
    (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation context a b c t child1 child2 child3
    hconstructor.
  unfold RawProofConstructorCode in hconstructor.
  unfold RawProofConstructorPayloadAtomicallyAdequate.
  destruct hconstructor as
    [hcode |
     [hcode |
      [hcode |
       [hcode |
        [hcode |
         [hcode |
          [hcode |
           [hcode |
            [hcode |
             [hcode |
              [hcode |
               [hcode |
                [hcode |
                 [hcode |
                  [hcode |
                   [hcode | hcode]]]]]]]]]]]]]]]].
  all: destruct derivation.
  all: cbn [rawQuotedProofCode rawListCode] in *.
  all: repeat match goal with
  | hnodes : rawListNode ?model ?head ?tail =
      rawListNode ?model ?head' ?tail' |- _ =>
      destruct (rawListNode_injective model hPA
        head tail head' tail' hnodes) as [? ?]; clear hnodes
  end.
  all: try match goal with
  | hnil : raw_zero ?model = rawListNode ?model ?head ?tail |- _ =>
      exfalso; exact (rawListNode_not_zero model hPA head tail hnil)
  | hnil : rawListNode ?model ?head ?tail = raw_zero ?model |- _ =>
      exfalso; apply (rawListNode_not_zero model hPA head tail);
      exact hnil
  end.
  all: subst.
  all: cbn [rawNumeralValue] in *.
  all: repeat match goal with
  | htag : raw_succ ?model ?left = raw_succ ?model ?right |- _ =>
      apply (raw_succ_injective_syntax model hPA) in htag
  end.
  all: try match goal with
  | htag : raw_zero ?model = raw_succ ?model ?value |- _ =>
      exfalso; exact (raw_zero_not_succ_syntax model hPA value htag)
  | htag : raw_succ ?model ?value = raw_zero ?model |- _ =>
      exfalso; apply (raw_zero_not_succ_syntax model hPA value);
      symmetry; exact htag
  end.
  all: try solve_raw_quoted_constructor_payload hPA.
  do 16 right. repeat split.
  - apply raw_quotedTerm_universally_adequate. exact hPA.
  - apply raw_quotedTerm_universally_adequate. exact hPA.
  - apply raw_quotedFormula_atomically_adequate. exact hPA.
Qed.

(** The exact support selector from standard restricted-proof adequacy marks
    precisely valid quoted derivations below the external root bound.  It
    therefore supplies both syntax closure and the universal endpoint
    condition required by [RawProofAtomicallyAdequate]. *)
Theorem raw_proofAtomicallyAdequate_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall derivation,
  RawProofValid derivation ->
  RawProofAtomicallyAdequate M (rawQuotedProofCode M derivation).
Proof.
  intros M hPA derivation hvalid.
  set (level := rawProofOccurrenceRank derivation).
  destruct (raw_standardRestrictedProofSupportTable_for_quotation
    M hPA level derivation hvalid (Nat.le_refl level)) as
    (supportCode & supportStep & htable & hroot).
  exists supportCode, supportStep.
  unfold RawProofAtomicAdequacyWithSupport.
  destruct htable as [hdefined hexact].
  split.
  - unfold RawProofSyntaxCertificateWithSupport.
    split; [| exact hroot].
    unfold RawProofSyntaxTraversal.
    split.
    + rewrite rawQuotedProofCode_standard by exact hPA.
      change (RawCodedAssignmentDefinedThrough M supportCode supportStep
        (rawNumeralValue M (S (rawProofCode derivation)))).
      exact hdefined.
    + intros code hcode hsupported.
      assert (hcodeBound : rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))).
      {
        rewrite rawQuotedProofCode_standard in hcode by exact hPA.
        change (rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))) in hcode.
        exact hcode.
      }
      destruct (proj1 (hexact code hcodeBound) hsupported) as
        (row & hrow & hrowCodeBound & hrowValid & hrowRank).
      subst code.
      apply raw_quotedProof_syntax_step_of_children; [exact hPA |].
      intros child hchild.
      exact (raw_standardRestrictedProofSupportTable_child M hPA
        level (S (rawProofCode derivation)) supportCode supportStep
        (conj hdefined hexact) row child hrowCodeBound
        hrowValid hrowRank hchild).
  - split.
    + intros code hcode hsupported.
      assert (hcodeBound : rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))).
      {
        rewrite rawQuotedProofCode_standard in hcode by exact hPA.
        change (rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))) in hcode.
        exact hcode.
      }
      destruct (proj1 (hexact code hcodeBound) hsupported) as
        (row & hrow & _ & _ & _).
      subst code.
      apply raw_quotedProof_endpoint_atomically_adequate. exact hPA.
    + intros code hcode hsupported.
      assert (hcodeBound : rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))).
      {
        rewrite rawQuotedProofCode_standard in hcode by exact hPA.
        change (rawLt M code
          (rawNumeralValue M (S (rawProofCode derivation)))) in hcode.
        exact hcode.
      }
      destruct (proj1 (hexact code hcodeBound) hsupported) as
        (row & hrow & _ & _ & _).
      subst code.
      apply raw_quotedProof_constructor_payloads_atomically_adequate.
      exact hPA.
Qed.

End PABoundedRawCodedProofAtomicAdequacyStandard.
