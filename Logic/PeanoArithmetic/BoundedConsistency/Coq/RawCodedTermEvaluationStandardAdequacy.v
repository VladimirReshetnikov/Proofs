(**
  Standard-quotation realization for the global coded-term evaluator.

  The global evaluator is intentionally stated for arbitrary, possibly
  nonstandard, carrier codes.  This file proves its adequacy on the separate
  and strictly weaker domain of externally quoted PA terms.  For a standard
  root code [termCode t], we beta-code every standard slot below
  [S (termCode t)].  A checked decoder marks exactly those slots whose
  decoded term re-encodes to the same number; malformed or noncanonical slots
  are unsupported and therefore require no traversal row.

  Nothing below asserts totality for an arbitrary nonstandard carrier code.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationStep RawCodedTermEvaluationTraversal.

Import ListNotations.

Module PABoundedRawCodedTermEvaluationStandardAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedRawCodedTermEvaluationTraversal.

(** [decodeTerm] is total as an option-valued function, but the explicit
    re-encoding check is useful here: support is granted only when the slot
    number is exactly the canonical code of the returned typed term. *)
Definition checkedDecodeTerm (code : nat) : option term :=
  match decodeTerm code with
  | Some t =>
      if Nat.eqb (termCode t) code then Some t else None
  | None => None
  end.

Lemma checkedDecodeTerm_termCode : forall t,
  checkedDecodeTerm (termCode t) = Some t.
Proof.
  intro t. unfold checkedDecodeTerm.
  rewrite decodeTerm_termCode, Nat.eqb_refl. reflexivity.
Qed.

Lemma checkedDecodeTerm_sound : forall code t,
  checkedDecodeTerm code = Some t ->
  decodeTerm code = Some t /\ termCode t = code.
Proof.
  intros code t. unfold checkedDecodeTerm.
  destruct (decodeTerm code) as [decoded |] eqn:hdecode;
    [|discriminate].
  destruct (Nat.eqb (termCode decoded) code) eqn:hcode;
    [|discriminate].
  intro h. inversion h. subst decoded.
  split; [reflexivity | now apply Nat.eqb_eq].
Qed.

(** The three externally finite vectors which will be beta-coded. *)
Definition rawStandardTermSupportAt (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some _ => rawNumeralValue M 1
  | None => raw_zero M
  end.

Definition rawStandardTermValueAt (M : RawPAModel)
    (env : nat -> M) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t => raw_term_eval M env t
  | None => raw_zero M
  end.

Lemma rawStandardTermSupportAt_termCode : forall M t,
  rawStandardTermSupportAt M (termCode t) = rawNumeralValue M 1.
Proof.
  intros M t. unfold rawStandardTermSupportAt.
  rewrite checkedDecodeTerm_termCode. reflexivity.
Qed.

Lemma rawStandardTermValueAt_termCode : forall M env t,
  rawStandardTermValueAt M env (termCode t) = raw_term_eval M env t.
Proof.
  intros M env t. unfold rawStandardTermValueAt.
  rewrite checkedDecodeTerm_termCode. reflexivity.
Qed.

Lemma rawStandardTermValueAt_checked : forall M env code t,
  checkedDecodeTerm code = Some t ->
  rawStandardTermValueAt M env code = raw_term_eval M env t.
Proof.
  intros M env code t h.
  unfold rawStandardTermValueAt. now rewrite h.
Qed.

Lemma rawStandardTermSupportAt_one_has_term : forall
    (M : RawPAModel), RawPASatisfies M -> forall code,
  rawStandardTermSupportAt M code = rawNumeralValue M 1 ->
  exists t, checkedDecodeTerm code = Some t.
Proof.
  intros M hPA code.
  unfold rawStandardTermSupportAt.
  destruct (checkedDecodeTerm code) as [t |] eqn:hdecode.
  - intros _. now exists t.
  - intro hzero.
    exfalso.
    apply (rawNumeralValue_injective M hPA 0 1) in hzero.
    discriminate.
Qed.

(** A variable index is itself smaller than the canonical code of its
    variable term.  This lets the same finite bound code the external
    assignment as well as the support and value tables. *)
Lemma termCode_var_index_lt : forall index,
  index < termCode (tVar index).
Proof.
  intro index.
  change (index < PAListCode.listCode [0; index]).
  apply listCode_second_lt.
Qed.

(** Every ordinary typed term has its expected closed local row, provided
    the three beta tables contain their advertised standard-vector entries.
    The proof is ordinary structural induction over typed syntax; no carrier
    element is recursively decoded. *)
Lemma raw_standardTermEvaluation_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) limit
    assignmentCode assignmentStep tableCode tableStep supportCode supportStep,
  (forall index, index < limit ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M tableCode tableStep
      (rawNumeralValue M code) (rawStandardTermValueAt M env code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M supportCode supportStep
      (rawNumeralValue M code) (rawStandardTermSupportAt M code)) ->
  forall t, termCode t < limit ->
    RawTermEvaluationClosedStep M
      (rawNumeralValue M (termCode t)) (raw_term_eval M env t)
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.
Proof.
  intros M hPA env limit assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep
    hassignment htable hsupport t ht.
  destruct t as [index | | child | left right | left right].
  - exists (rawNumeralValue M index), (raw_zero M),
      (raw_zero M), (raw_zero M).
    left. split.
    + rewrite <- (rawQuotedTermCode_standard M hPA (tVar index)).
      reflexivity.
    + apply hassignment.
      pose proof (termCode_var_index_lt index). lia.
  - exists (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M).
    right. left. split.
    + rewrite <- (rawQuotedTermCode_standard M hPA tZero).
      reflexivity.
    + reflexivity.
  - exists (rawNumeralValue M (termCode child)),
      (raw_term_eval M env child), (raw_zero M), (raw_zero M).
    right. right. left. split.
    + split.
      * rewrite <- (rawQuotedTermCode_standard M hPA (tSucc child)).
        rewrite <- (rawQuotedTermCode_standard M hPA child).
        reflexivity.
      * split.
        -- rewrite <- (rawStandardTermValueAt_termCode M env child).
           apply htable. pose proof (termCode_succ_child_lt child). lia.
        -- reflexivity.
    + split.
      * unfold rawTermCodeSupported.
        rewrite <- (rawStandardTermSupportAt_termCode M child).
        apply hsupport. pose proof (termCode_succ_child_lt child). lia.
      * apply raw_lt_numeralValue_of_lt.
        -- exact hPA.
        -- apply termCode_succ_child_lt.
  - exists (rawNumeralValue M (termCode left)),
      (raw_term_eval M env left),
      (rawNumeralValue M (termCode right)),
      (raw_term_eval M env right).
    right. right. right. left. split.
    + split.
      * rewrite <- (rawQuotedTermCode_standard M hPA (tAdd left right)).
        rewrite <- (rawQuotedTermCode_standard M hPA left).
        rewrite <- (rawQuotedTermCode_standard M hPA right).
        reflexivity.
      * split.
        -- rewrite <- (rawStandardTermValueAt_termCode M env left).
           apply htable. pose proof (termCode_add_left_lt left right). lia.
        -- split.
           ++ rewrite <- (rawStandardTermValueAt_termCode M env right).
              apply htable. pose proof (termCode_add_right_lt left right). lia.
           ++ reflexivity.
    + split.
      * unfold rawTermCodeSupported.
        rewrite <- (rawStandardTermSupportAt_termCode M left).
        apply hsupport. pose proof (termCode_add_left_lt left right). lia.
      * split.
        -- unfold rawTermCodeSupported.
           rewrite <- (rawStandardTermSupportAt_termCode M right).
           apply hsupport. pose proof (termCode_add_right_lt left right). lia.
        -- split; apply raw_lt_numeralValue_of_lt; try exact hPA.
           ++ apply termCode_add_left_lt.
           ++ apply termCode_add_right_lt.
  - exists (rawNumeralValue M (termCode left)),
      (raw_term_eval M env left),
      (rawNumeralValue M (termCode right)),
      (raw_term_eval M env right).
    right. right. right. right. split.
    + split.
      * rewrite <- (rawQuotedTermCode_standard M hPA (tMul left right)).
        rewrite <- (rawQuotedTermCode_standard M hPA left).
        rewrite <- (rawQuotedTermCode_standard M hPA right).
        reflexivity.
      * split.
        -- rewrite <- (rawStandardTermValueAt_termCode M env left).
           apply htable. pose proof (termCode_mul_left_lt left right). lia.
        -- split.
           ++ rewrite <- (rawStandardTermValueAt_termCode M env right).
              apply htable. pose proof (termCode_mul_right_lt left right). lia.
           ++ reflexivity.
    + split.
      * unfold rawTermCodeSupported.
        rewrite <- (rawStandardTermSupportAt_termCode M left).
        apply hsupport. pose proof (termCode_mul_left_lt left right). lia.
      * split.
        -- unfold rawTermCodeSupported.
           rewrite <- (rawStandardTermSupportAt_termCode M right).
           apply hsupport. pose proof (termCode_mul_right_lt left right). lia.
        -- split; apply raw_lt_numeralValue_of_lt; try exact hPA.
           ++ apply termCode_mul_left_lt.
           ++ apply termCode_mul_right_lt.
Qed.

(** Fixed-assignment adequacy is the compositional interface needed by truth
    rows.  Once a supplied assignment table agrees with [env] through an
    external standard limit, every term whose code lies below that limit gets
    fresh support/value tables while retaining exactly that assignment pair.

    The first two conjuncts expose the finite-vector lookup equations for the
    newly constructed tables; the final conjunct is the actual global
    certificate with tables. *)
Theorem raw_termEvaluationCertificateWithTables_standard_of_assignment :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) limit assignmentCode assignmentStep,
  (forall index, index < limit ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  forall t, termCode t < limit ->
  exists supportCode supportStep tableCode tableStep : M,
    (forall code, code < S (termCode t) ->
      RawCodedAssignmentLookup M supportCode supportStep
        (rawNumeralValue M code) (rawStandardTermSupportAt M code)) /\
    (forall code, code < S (termCode t) ->
      RawCodedAssignmentLookup M tableCode tableStep
        (rawNumeralValue M code) (rawStandardTermValueAt M env code)) /\
    RawTermEvaluationCertificateWithTables M
      (rawQuotedTermCode M t) (raw_term_eval M env t)
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.
Proof.
  intros M hPA env limit assignmentCode assignmentStep
    hassignment rootTerm hrootLimit.
  assert (hassignmentRoot : forall index,
      index < S (termCode rootTerm) ->
      RawCodedAssignmentLookup M assignmentCode assignmentStep
        (rawNumeralValue M index) (env index)).
  {
    intros index hindex. apply hassignment. lia.
  }
  destruct (finite_vector_beta_code M hPA
    (S (termCode rootTerm)) (rawStandardTermSupportAt M)) as
    [supportCode [supportStep hsupport]].
  destruct (finite_vector_beta_code M hPA
    (S (termCode rootTerm)) (rawStandardTermValueAt M env)) as
    [tableCode [tableStep htable]].
  exists supportCode, supportStep, tableCode, tableStep.
  split; [exact hsupport |]. split; [exact htable |].
  rewrite rawQuotedTermCode_standard by exact hPA.
  unfold RawTermEvaluationCertificateWithTables.
  split.
  - change (RawTermEvaluationTraversal M
      (rawNumeralValue M (S (termCode rootTerm)))
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep).
    split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index
        (S (termCode rootTerm)) hindex) as [k [hk ->]].
      exists (rawStandardTermSupportAt M k).
      exact (hsupport k hk).
    + split.
      * intros index hindex.
        destruct (raw_lt_numeralValue_cases M hPA index
          (S (termCode rootTerm)) hindex) as [k [hk ->]].
        exists (rawStandardTermValueAt M env k).
        exact (htable k hk).
      * intros code hcode hsupported.
        destruct (raw_lt_numeralValue_cases M hPA code
          (S (termCode rootTerm)) hcode) as [k [hk ->]].
        assert (hsupportEntry :
            RawCodedAssignmentLookup M supportCode supportStep
              (rawNumeralValue M k)
              (rawStandardTermSupportAt M k)).
        { exact (hsupport k hk). }
        unfold rawTermCodeSupported in hsupported.
        assert (hsupportOne : rawStandardTermSupportAt M k =
            rawNumeralValue M 1).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            supportCode supportStep (rawNumeralValue M k)
            (rawStandardTermSupportAt M k) (rawNumeralValue M 1)
            hsupportEntry hsupported).
        }
        destruct (rawStandardTermSupportAt_one_has_term M hPA k
          hsupportOne) as [decoded hdecoded].
        pose proof (checkedDecodeTerm_sound k decoded hdecoded)
          as [_ hcanonical].
        exists (rawStandardTermValueAt M env k). split.
        -- exact (htable k hk).
        -- pose proof
             (raw_standardTermEvaluation_closed_step M hPA env
               (S (termCode rootTerm))
               assignmentCode assignmentStep tableCode tableStep
               supportCode supportStep
               hassignmentRoot htable hsupport decoded)
             as hstep.
           assert (hdecodedBound :
               termCode decoded < S (termCode rootTerm)).
           { now rewrite hcanonical. }
           specialize (hstep hdecodedBound).
           rewrite hcanonical in hstep.
           rewrite (rawStandardTermValueAt_checked
             M env k decoded hdecoded).
           exact hstep.
  - split.
    + unfold rawTermCodeSupported.
      rewrite <- (rawStandardTermSupportAt_termCode M rootTerm).
      exact (hsupport (termCode rootTerm) (Nat.lt_succ_diag_r _)).
    + rewrite <- (rawStandardTermValueAt_termCode M env rootTerm).
      exact (htable (termCode rootTerm) (Nat.lt_succ_diag_r _)).
Qed.

(** Hiding the freshly constructed tables yields a certificate over an
    already chosen assignment.  Reusing this theorem gives multiple terms
    certificates with literally the same [assignmentCode]/[assignmentStep]. *)
Corollary raw_termEvaluationCertificate_standard_of_assignment : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) limit assignmentCode assignmentStep,
  (forall index, index < limit ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  forall t, termCode t < limit ->
    RawTermEvaluationCertificate M
      (rawQuotedTermCode M t) (raw_term_eval M env t)
      assignmentCode assignmentStep.
Proof.
  intros M hPA env limit assignmentCode assignmentStep
    hassignment t ht.
  destruct (raw_termEvaluationCertificateWithTables_standard_of_assignment
    M hPA env limit assignmentCode assignmentStep hassignment t ht) as
    (supportCode & supportStep & tableCode & tableStep &
     _ & _ & hcertificate).
  exists supportCode, supportStep, tableCode, tableStep.
  exact hcertificate.
Qed.

(** The finite realization exposes all three beta tables.  The assignment
    table is additionally recorded as defined through the same standard
    bound; definedness of support and values is already part of
    [RawTermEvaluationCertificateWithTables]. *)
Theorem raw_termEvaluationCertificateWithTables_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) t,
  exists assignmentCode assignmentStep supportCode supportStep
      tableCode tableStep : M,
    RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
      (rawNumeralValue M (S (termCode t))) /\
    RawTermEvaluationCertificateWithTables M
      (rawQuotedTermCode M t) (raw_term_eval M env t)
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.
Proof.
  intros M hPA env rootTerm.
  destruct (finite_vector_beta_code M hPA
    (S (termCode rootTerm)) env) as
    [assignmentCode [assignmentStep hassignment]].
  destruct (finite_vector_beta_code M hPA
    (S (termCode rootTerm)) (rawStandardTermSupportAt M)) as
    [supportCode [supportStep hsupport]].
  destruct (finite_vector_beta_code M hPA
    (S (termCode rootTerm)) (rawStandardTermValueAt M env)) as
    [tableCode [tableStep htable]].
  exists assignmentCode, assignmentStep, supportCode, supportStep,
    tableCode, tableStep.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index
      (S (termCode rootTerm)) hindex) as [k [hk ->]].
    exists (env k). exact (hassignment k hk).
  - rewrite rawQuotedTermCode_standard by exact hPA.
    unfold RawTermEvaluationCertificateWithTables.
    split.
    + change (RawTermEvaluationTraversal M
        (rawNumeralValue M (S (termCode rootTerm)))
        assignmentCode assignmentStep tableCode tableStep
        supportCode supportStep).
      split.
      * intros index hindex.
        destruct (raw_lt_numeralValue_cases M hPA index
          (S (termCode rootTerm)) hindex) as [k [hk ->]].
        exists (rawStandardTermSupportAt M k).
        exact (hsupport k hk).
      * split.
        -- intros index hindex.
           destruct (raw_lt_numeralValue_cases M hPA index
             (S (termCode rootTerm)) hindex) as [k [hk ->]].
           exists (rawStandardTermValueAt M env k).
           exact (htable k hk).
        -- intros code hcode hsupported.
           destruct (raw_lt_numeralValue_cases M hPA code
             (S (termCode rootTerm)) hcode) as [k [hk ->]].
           assert (hsupportEntry :
               RawCodedAssignmentLookup M supportCode supportStep
                 (rawNumeralValue M k)
                 (rawStandardTermSupportAt M k)).
           { exact (hsupport k hk). }
           unfold rawTermCodeSupported in hsupported.
           assert (hsupportOne : rawStandardTermSupportAt M k =
               rawNumeralValue M 1).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               supportCode supportStep (rawNumeralValue M k)
               (rawStandardTermSupportAt M k) (rawNumeralValue M 1)
               hsupportEntry hsupported).
           }
           destruct (rawStandardTermSupportAt_one_has_term M hPA k
             hsupportOne) as [decoded hdecoded].
           pose proof (checkedDecodeTerm_sound k decoded hdecoded)
             as [_ hcanonical].
           exists (rawStandardTermValueAt M env k). split.
           ++ exact (htable k hk).
           ++ pose proof
                (raw_standardTermEvaluation_closed_step M hPA env
                  (S (termCode rootTerm))
                  assignmentCode assignmentStep tableCode tableStep
                  supportCode supportStep
                  hassignment htable hsupport decoded)
                as hstep.
              assert (hdecodedBound :
                  termCode decoded < S (termCode rootTerm)).
              { now rewrite hcanonical. }
              specialize (hstep hdecodedBound).
              rewrite hcanonical in hstep.
              rewrite (rawStandardTermValueAt_checked
                M env k decoded hdecoded).
              exact hstep.
    + split.
      * unfold rawTermCodeSupported.
        rewrite <- (rawStandardTermSupportAt_termCode M rootTerm).
        exact (hsupport (termCode rootTerm) (Nat.lt_succ_diag_r _)).
      * rewrite <- (rawStandardTermValueAt_termCode M env rootTerm).
        exact (htable (termCode rootTerm) (Nat.lt_succ_diag_r _)).
Qed.

(** Public certificate adequacy.  Support and value table parameters are
    existentially hidden by the original certificate relation, while the
    independently supplied variable assignment remains explicit. *)
Corollary raw_termEvaluationCertificate_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) t,
  exists assignmentCode assignmentStep : M,
    RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
      (rawNumeralValue M (S (termCode t))) /\
    RawTermEvaluationCertificate M
      (rawQuotedTermCode M t) (raw_term_eval M env t)
      assignmentCode assignmentStep.
Proof.
  intros M hPA env t.
  destruct (raw_termEvaluationCertificateWithTables_standard_exists
    M hPA env t) as
    (assignmentCode & assignmentStep & supportCode & supportStep &
     tableCode & tableStep & hassignment & hcertificate).
  exists assignmentCode, assignmentStep. split; [exact hassignment |].
  exists supportCode, supportStep, tableCode, tableStep.
  exact hcertificate.
Qed.

(** In particular, two standard subterms can be certified against one shared
    assignment table.  Their support/value traversals remain independent,
    which is exactly what the public certificate relation permits. *)
Corollary raw_termEvaluationCertificates_pair_standard_exists_same_assignment :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) left right,
  exists assignmentCode assignmentStep : M,
    RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
      (rawNumeralValue M
        (S (Nat.max (termCode left) (termCode right)))) /\
    RawTermEvaluationCertificate M
      (rawQuotedTermCode M left) (raw_term_eval M env left)
      assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M
      (rawQuotedTermCode M right) (raw_term_eval M env right)
      assignmentCode assignmentStep.
Proof.
  intros M hPA env left right.
  set (limit := S (Nat.max (termCode left) (termCode right))).
  destruct (finite_vector_beta_code M hPA limit env) as
    [assignmentCode [assignmentStep hassignment]].
  assert (hleftBound : termCode left < limit).
  { unfold limit. pose proof (Nat.le_max_l (termCode left) (termCode right)).
    lia. }
  assert (hrightBound : termCode right < limit).
  { unfold limit. pose proof (Nat.le_max_r (termCode left) (termCode right)).
    lia. }
  pose proof (raw_termEvaluationCertificate_standard_of_assignment
    M hPA env limit assignmentCode assignmentStep hassignment
    left hleftBound) as hleft.
  pose proof (raw_termEvaluationCertificate_standard_of_assignment
    M hPA env limit assignmentCode assignmentStep hassignment
    right hrightBound) as hright.
  exists assignmentCode, assignmentStep.
  split.
  - unfold limit.
    intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index
      (S (Nat.max (termCode left) (termCode right))) hindex)
      as [k [hk ->]].
    exists (env k). exact (hassignment k hk).
  - split; assumption.
Qed.

(** Environment used to expose the four public arguments of the
    object-language certificate formula as variables 0--3. *)
Definition rawStandardTermCertificateEnv (M : RawPAModel)
    (env : nat -> M) (t : term)
    (assignmentCode assignmentStep : M) (tail : nat -> M) : nat -> M :=
  scons M (rawQuotedTermCode M t)
    (scons M (raw_term_eval M env t)
      (scons M assignmentCode (scons M assignmentStep tail))).

Arguments rawStandardTermCertificateEnv
  M env t assignmentCode assignmentStep tail : clear implicits.

(** Formula-level adequacy is an immediate consequence of the exact raw
    semantics already proved for [termEvaluationCertificateTermAt]. *)
Corollary raw_sat_termEvaluationCertificateTermAt_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) t (tail : nat -> M),
  exists assignmentCode assignmentStep : M,
    raw_formula_sat M
      (rawStandardTermCertificateEnv M env t
        assignmentCode assignmentStep tail)
      (termEvaluationCertificateTermAt
        (tVar 0) (tVar 1) (tVar 2) (tVar 3)).
Proof.
  intros M hPA env t tail.
  destruct (raw_termEvaluationCertificate_standard_exists M hPA env t)
    as [assignmentCode [assignmentStep [_ hcertificate]]].
  exists assignmentCode, assignmentStep.
  apply (proj2 (raw_sat_termEvaluationCertificateTermAt_iff M
    (rawStandardTermCertificateEnv M env t
      assignmentCode assignmentStep tail)
    (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
  unfold rawStandardTermCertificateEnv.
  cbn [raw_term_eval scons]. exact hcertificate.
Qed.

End PABoundedRawCodedTermEvaluationStandardAdequacy.
