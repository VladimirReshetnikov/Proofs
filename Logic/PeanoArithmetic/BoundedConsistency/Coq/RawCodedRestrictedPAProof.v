(**
  Transparent wrappers for occurrence-restricted PA proofs.

  [restrictedPAProofCode] packages a list of PA-axiom witnesses and a raw
  derivation.  In a nonstandard model neither component can be decoded into
  a Rocq list or [RawProof].  This file instead traverses the witness list
  and the proof context in lockstep using synchronized beta tables.  At every
  model-internal index the corresponding heads must satisfy the transparent
  [RawCodedPAAxiomWitness] graph.

  The public wrapper additionally requires the existing global restricted
  proof certificate and a valid root rule with exactly that witnessed
  context and the code of falsity.  Thus arbitrary nonstandard certificates
  have the same internal contract as standard [restrictedPAProofCode]
  quotations, without any carrier-level decoder.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaOperations RawCodedContextLists RawCodedProofConstructors
  RawCodedProofRules RawCodedRestrictedProofTraversal
  RawCodedPAAxiomWitness RawCodedRestrictedProofStandardAdequacy
  RawCodedProofAtomicAdequacy RawCodedProofAtomicAdequacyStandard
  RawCodedProofFormulaCoverage RawCodedProofFormulaCoverageStandard
  RawCodedProofRuleCoverage RawCodedProofRuleCoverageStandard.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAProof.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofFormulaCoverageStandard.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRuleCoverageStandard.

(** ------------------------------------------------------------------
    Binder bookkeeping and small propositional combinators. *)

Definition restrictedPAAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition restrictedPAAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition restrictedPAAnd7
    (a b c d f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g h))))).

Definition restrictedPAEx3 (body : formula) : formula :=
  pEx (pEx (pEx body)).

Definition restrictedPAEx9 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body)))))))).

Definition restrictedPAAll3 (body : formula) : formula :=
  pAll (pAll (pAll body)).

Lemma raw_restrictedPA_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia. reflexivity.
Qed.

Lemma raw_restrictedPA_eval_liftTerm_one : forall
    (M : RawPAModel) value (e : nat -> M) t,
  raw_term_eval M (scons M value e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M value e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_restrictedPA_eval_liftTerm_nine : forall
    (M : RawPAModel) a b c d f g h i j (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i (scons M j e)))))))))
    (liftTerm 9 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 9) with
    (S (S (S (S (S (S (S (S (S index))))))))) by lia.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Rowwise agreement between the witness list and the proof context. *)

Definition codedPAAxiomWitnessContextRowsTermAt
    (bound witnessHeadCode witnessHeadStep
      axiomHeadCode axiomHeadStep : term) : formula :=
  restrictedPAAll3
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 3 witnessHeadCode) (liftTerm 3 witnessHeadStep)
          (tVar 2) (tVar 1))
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 3 axiomHeadCode) (liftTerm 3 axiomHeadStep)
            (tVar 2) (tVar 0))
          (codedPAAxiomWitnessTermAt (tVar 1) (tVar 0))))).

Definition RawCodedPAAxiomWitnessContextRows (M : RawPAModel)
    (bound witnessHeadCode witnessHeadStep
      axiomHeadCode axiomHeadStep : M) : Prop :=
  forall index witness axiom : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      witnessHeadCode witnessHeadStep index witness ->
    RawCodedAssignmentLookup M
      axiomHeadCode axiomHeadStep index axiom ->
    RawCodedPAAxiomWitness M witness axiom.

Arguments RawCodedPAAxiomWitnessContextRows
  M bound witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep
  : clear implicits.

Lemma raw_sat_codedPAAxiomWitnessContextRowsTermAt_iff : forall
    (M : RawPAModel) e bound witnessHeadCode witnessHeadStep
      axiomHeadCode axiomHeadStep,
  raw_formula_sat M e
    (codedPAAxiomWitnessContextRowsTermAt
      bound witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep) <->
  RawCodedPAAxiomWitnessContextRows M
    (raw_term_eval M e bound)
    (raw_term_eval M e witnessHeadCode)
    (raw_term_eval M e witnessHeadStep)
    (raw_term_eval M e axiomHeadCode)
    (raw_term_eval M e axiomHeadStep).
Proof.
  intros. unfold codedPAAxiomWitnessContextRowsTermAt,
    restrictedPAAll3, RawCodedPAAxiomWitnessContextRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_codedPAAxiomWitnessTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedPAAxiomWitnessContextWithTables (M : RawPAModel)
    (witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep : M) : Prop :=
  RawContextListTraversal M witnessList bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep /\
  RawContextListTraversal M context bound
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep /\
  RawCodedPAAxiomWitnessContextRows M bound
    witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep.

Arguments RawCodedPAAxiomWitnessContextWithTables
  M witnessList context bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
  : clear implicits.

Definition codedPAAxiomWitnessContextWithTablesTermAt
    (witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep : term)
    : formula :=
  restrictedPAAnd3
    (contextListTraversalTermAt witnessList bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep)
    (contextListTraversalTermAt context bound
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep)
    (codedPAAxiomWitnessContextRowsTermAt bound
      witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep).

Lemma raw_sat_codedPAAxiomWitnessContextWithTablesTermAt_iff : forall
    (M : RawPAModel) e witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep,
  raw_formula_sat M e
    (codedPAAxiomWitnessContextWithTablesTermAt
      witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep) <->
  RawCodedPAAxiomWitnessContextWithTables M
    (raw_term_eval M e witnessList) (raw_term_eval M e context)
    (raw_term_eval M e bound)
    (raw_term_eval M e witnessTailCode)
    (raw_term_eval M e witnessTailStep)
    (raw_term_eval M e witnessHeadCode)
    (raw_term_eval M e witnessHeadStep)
    (raw_term_eval M e axiomTailCode)
    (raw_term_eval M e axiomTailStep)
    (raw_term_eval M e axiomHeadCode)
    (raw_term_eval M e axiomHeadStep).
Proof.
  intros. unfold codedPAAxiomWitnessContextWithTablesTermAt,
    restrictedPAAnd3, RawCodedPAAxiomWitnessContextWithTables.
  cbn [raw_formula_sat].
  rewrite !raw_sat_contextListTraversalTermAt_iff,
    raw_sat_codedPAAxiomWitnessContextRowsTermAt_iff.
  reflexivity.
Qed.

Definition RawCodedPAAxiomWitnessContext (M : RawPAModel)
    (witnessList context : M) : Prop :=
  exists bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep : M,
    RawCodedPAAxiomWitnessContextWithTables M witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep.

Arguments RawCodedPAAxiomWitnessContext M witnessList context
  : clear implicits.

Definition codedPAAxiomWitnessContextTermAt
    (witnessList context : term) : formula :=
  restrictedPAEx9
    (codedPAAxiomWitnessContextWithTablesTermAt
      (liftTerm 9 witnessList) (liftTerm 9 context)
      (tVar 8)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Lemma raw_sat_codedPAAxiomWitnessContextTermAt_iff : forall
    (M : RawPAModel) e witnessList context,
  raw_formula_sat M e
    (codedPAAxiomWitnessContextTermAt witnessList context) <->
  RawCodedPAAxiomWitnessContext M
    (raw_term_eval M e witnessList) (raw_term_eval M e context).
Proof.
  intros M e witnessList context.
  unfold codedPAAxiomWitnessContextTermAt, restrictedPAEx9,
    RawCodedPAAxiomWitnessContext.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_codedPAAxiomWitnessContextWithTablesTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_nine.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    The complete restricted-PA proof wrapper. *)

(** A common assignment bound is existential certificate data.  Keeping it
    hidden in the represented predicate avoids changing the public three-
    field executable proof code while still making the bound available to
    nonstandard soundness. *)
Definition RawProofHasFormulaCoverage (M : RawPAModel)
    (proof : M) : Prop :=
  exists coverageBound : M,
    RawProofFormulaCoverage M proof coverageBound.

Arguments RawProofHasFormulaCoverage M proof : clear implicits.

Definition proofHasFormulaCoverageTermAt (proof : term) : formula :=
  pEx
    (proofFormulaCoverageTermAt
      (liftTerm 1 proof) (tVar 0)).

Lemma raw_sat_proofHasFormulaCoverageTermAt_iff : forall
    (M : RawPAModel) e proof,
  raw_formula_sat M e (proofHasFormulaCoverageTermAt proof) <->
  RawProofHasFormulaCoverage M (raw_term_eval M e proof).
Proof.
  intros M e proof.
  unfold proofHasFormulaCoverageTermAt, RawProofHasFormulaCoverage.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofFormulaCoverageTermAt_iff.
  setoid_rewrite raw_restrictedPA_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedRestrictedPAProof (M : RawPAModel)
    (level : nat) (certificate : M) : Prop :=
  exists witnessList proof context : M,
    certificate = rawCodeList3 M
      (rawNumeralValue M 0) witnessList proof /\
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawRestrictedProof M level proof /\
    RawProofAtomicallyAdequate M proof /\
    RawProofHasFormulaCoverage M proof /\
    RawProofRuleCoverage M proof /\
    RawProofRuleValid M proof context (rawFormulaBotCode M).

Arguments RawCodedRestrictedPAProof M level certificate : clear implicits.

Definition codedRestrictedPAProofTermAt
    (level : nat) (certificate : term) : formula :=
  restrictedPAEx3
    (restrictedPAAnd7
      (codeList3TermAt (liftTerm 3 certificate)
        (Term.numeral 0) (tVar 2) (tVar 1))
      (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0))
      (restrictedProofTermAt level (tVar 1))
      (proofAtomicallyAdequateTermAt (tVar 1))
      (proofHasFormulaCoverageTermAt (tVar 1))
      (proofRuleCoverageTermAt (tVar 1))
      (proofRuleValidTermAt (tVar 1) (tVar 0)
        rawFormulaBotCodeTerm)).

Lemma raw_sat_codedRestrictedPAProofTermAt_iff : forall
    (M : RawPAModel) e level certificate,
  raw_formula_sat M e
    (codedRestrictedPAProofTermAt level certificate) <->
  RawCodedRestrictedPAProof M level
    (raw_term_eval M e certificate).
Proof.
  intros M e level certificate.
  unfold codedRestrictedPAProofTermAt, restrictedPAEx3,
    restrictedPAAnd7, RawCodedRestrictedPAProof.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codeList3TermAt_iff.
  setoid_rewrite raw_sat_codedPAAxiomWitnessContextTermAt_iff.
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_proofHasFormulaCoverageTermAt_iff.
  setoid_rewrite raw_sat_proofRuleCoverageTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_three.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_eval_rawFormulaBotCodeTerm.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Finite standard list traversals.

    The public nonstandard predicate above does not use these definitions.
    They are only the quotation witnesses for an ordinary Rocq list. *)

Definition rawStandardListTailAt (M : RawPAModel)
    (xs : list M) (index : nat) : M :=
  rawListCode M (skipn index xs).

Definition rawStandardListHeadAt (M : RawPAModel)
    (xs : list M) (index : nat) : M :=
  match nth_error xs index with
  | Some value => value
  | None => raw_zero M
  end.

Lemma skipn_length_exact : forall (A : Type) (xs : list A),
  skipn (length xs) xs = [].
Proof.
  intros A xs. induction xs as [|head tail IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Lemma skipn_nth_error_cons : forall (A : Type) (xs : list A)
    index value,
  nth_error xs index = Some value ->
  skipn index xs = value :: skipn (S index) xs.
Proof.
  intros A xs. induction xs as [|head tail IH]; intros [|index] value h.
  - discriminate.
  - discriminate.
  - cbn in h. inversion h. reflexivity.
  - cbn in h |- *. exact (IH index value h).
Qed.

Lemma rawStandardListTailAt_zero : forall M xs,
  rawStandardListTailAt M xs 0 = rawListCode M xs.
Proof. reflexivity. Qed.

Lemma rawStandardListTailAt_length : forall M xs,
  rawStandardListTailAt M xs (length xs) = raw_zero M.
Proof.
  intros M xs. unfold rawStandardListTailAt.
  rewrite skipn_length_exact. reflexivity.
Qed.

Lemma rawStandardListTailAt_step : forall M xs index value,
  nth_error xs index = Some value ->
  rawStandardListTailAt M xs index =
    rawListNode M value (rawStandardListTailAt M xs (S index)).
Proof.
  intros M xs index value hnth.
  unfold rawStandardListTailAt.
  rewrite (skipn_nth_error_cons _ _ _ _ hnth). reflexivity.
Qed.

Theorem raw_standardListTraversal_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall xs : list M,
  exists tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      (rawListCode M xs) (rawNumeralValue M (length xs))
      tailCode tailStep headCode headStep /\
    forall index,
      index < length xs ->
      RawCodedAssignmentLookup M headCode headStep
        (rawNumeralValue M index)
        (rawStandardListHeadAt M xs index).
Proof.
  intros M hPA xs.
  destruct (finite_vector_beta_code M hPA (S (length xs))
    (rawStandardListTailAt M xs)) as
    [tailCode [tailStep htail]].
  destruct (finite_vector_beta_code M hPA (length xs)
    (rawStandardListHeadAt M xs)) as
    [headCode [headStep hhead]].
  exists tailCode, tailStep, headCode, headStep. split.
  - unfold RawContextListTraversal. split.
    + rewrite <- (rawStandardListTailAt_zero M xs).
      apply htail. lia.
    + split.
      * rewrite <- (rawStandardListTailAt_length M xs).
        apply htail. lia.
      * split.
        -- intros index hindex.
           destruct (raw_lt_numeralValue_cases
             M hPA index (length xs) hindex) as [k [hk ->]].
           exists (rawStandardListHeadAt M xs k).
           apply hhead. exact hk.
        -- intros index hindex.
           destruct (raw_lt_numeralValue_cases
             M hPA index (length xs) hindex) as [k [hk ->]].
           destruct (nth_error xs k) as [value |] eqn:hnth.
           ++ exists (rawStandardListTailAt M xs k),
                (rawStandardListTailAt M xs (S k)), value.
              split.
              ** apply htail. lia.
              ** split.
                 --- apply htail. lia.
                 --- split.
                     +++ replace value with
                           (rawStandardListHeadAt M xs k).
                         *** apply hhead. exact hk.
                         *** unfold rawStandardListHeadAt.
                             rewrite hnth. reflexivity.
                     +++ apply rawStandardListTailAt_step. exact hnth.
           ++ apply nth_error_None in hnth. lia.
  - intros index hindex. apply hhead. exact hindex.
Qed.

Definition rawQuotedPAAxiomWitnessList
    (M : RawPAModel) (witnesses : list PAAxiomWitness) : M :=
  rawListCode M
    (map (fun witness =>
      rawNumeralValue M (axiomWitnessCode witness)) witnesses).

Arguments rawQuotedPAAxiomWitnessList M witnesses : clear implicits.

Lemma rawQuotedPAAxiomWitnessList_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall witnesses,
  rawQuotedPAAxiomWitnessList M witnesses =
  rawNumeralValue M (axiomWitnessListCode witnesses).
Proof.
  intros M hPA witnesses.
  unfold rawQuotedPAAxiomWitnessList, axiomWitnessListCode.
  rewrite <- map_map.
  apply rawListCode_standard. exact hPA.
Qed.

(** Standard witness lists and their witnessed-axiom contexts have one
    synchronized traversal.  The row condition is universal, so beta lookup
    functionality is used to reduce arbitrary matching lookup values to the
    canonical standard heads before applying witness adequacy. *)
Theorem raw_codedPAAxiomWitnessContext_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawQuotedPAAxiomWitnessList M witnesses)
    (rawQuotedContextCode M (map witnessedAxiom witnesses)).
Proof.
  intros M hPA witnesses.
  set (witnessValues := map
    (fun witness => rawNumeralValue M (axiomWitnessCode witness))
    witnesses).
  set (axiomValues := map
    (fun witness => rawQuotedFormulaCode M (witnessedAxiom witness))
    witnesses).
  destruct (raw_standardListTraversal_exists M hPA witnessValues) as
    (witnessTailCode & witnessTailStep & witnessHeadCode &
      witnessHeadStep & hwitnessTraversal & hwitnessHead).
  destruct (raw_standardListTraversal_exists M hPA axiomValues) as
    (axiomTailCode & axiomTailStep & axiomHeadCode & axiomHeadStep &
      haxiomTraversal & haxiomHead).
  assert (hwitnessLength : length witnessValues = length witnesses).
  { unfold witnessValues. apply length_map. }
  assert (haxiomLength : length axiomValues = length witnesses).
  { unfold axiomValues. apply length_map. }
  assert (hcontext : rawQuotedContextCode M
      (map witnessedAxiom witnesses) = rawListCode M axiomValues).
  {
    rewrite rawQuotedContextCode_as_list.
    unfold axiomValues. rewrite map_map. reflexivity.
  }
  unfold rawQuotedPAAxiomWitnessList.
  change (RawCodedPAAxiomWitnessContext M
    (rawListCode M witnessValues)
    (rawQuotedContextCode M (map witnessedAxiom witnesses))).
  rewrite hcontext.
  exists (rawNumeralValue M (length witnesses)),
    witnessTailCode, witnessTailStep, witnessHeadCode, witnessHeadStep,
    axiomTailCode, axiomTailStep, axiomHeadCode, axiomHeadStep.
  unfold RawCodedPAAxiomWitnessContextWithTables.
  split.
  - rewrite <- hwitnessLength. exact hwitnessTraversal.
  - split.
    + rewrite <- haxiomLength. exact haxiomTraversal.
    + intros index witnessCode axiomCode hindex
        hwitnessLookup haxiomLookup.
      destruct (raw_lt_numeralValue_cases
        M hPA index (length witnesses) hindex) as [k [hk ->]].
      destruct (nth_error witnesses k) as [witness |] eqn:hnth.
      * assert (hwitnessCanonicalLookup :
          RawCodedAssignmentLookup M witnessHeadCode witnessHeadStep
            (rawNumeralValue M k)
            (rawNumeralValue M (axiomWitnessCode witness))).
        {
          pose proof (hwitnessHead k) as hcanonical.
          specialize (hcanonical ltac:(rewrite hwitnessLength; exact hk)).
          unfold rawStandardListHeadAt in hcanonical.
          unfold witnessValues in hcanonical.
          rewrite nth_error_map, hnth in hcanonical.
          exact hcanonical.
        }
        assert (haxiomCanonicalLookup :
          RawCodedAssignmentLookup M axiomHeadCode axiomHeadStep
            (rawNumeralValue M k)
            (rawQuotedFormulaCode M (witnessedAxiom witness))).
        {
          pose proof (haxiomHead k) as hcanonical.
          specialize (hcanonical ltac:(rewrite haxiomLength; exact hk)).
          unfold rawStandardListHeadAt in hcanonical.
          unfold axiomValues in hcanonical.
          rewrite nth_error_map, hnth in hcanonical.
          exact hcanonical.
        }
        assert (hwitnessCode : witnessCode =
            rawNumeralValue M (axiomWitnessCode witness)).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            witnessHeadCode witnessHeadStep (rawNumeralValue M k)
            witnessCode (rawNumeralValue M (axiomWitnessCode witness))
            hwitnessLookup hwitnessCanonicalLookup).
        }
        assert (haxiomCode : axiomCode =
            rawQuotedFormulaCode M (witnessedAxiom witness)).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            axiomHeadCode axiomHeadStep (rawNumeralValue M k)
            axiomCode (rawQuotedFormulaCode M (witnessedAxiom witness))
            haxiomLookup haxiomCanonicalLookup).
        }
        subst witnessCode. subst axiomCode.
        apply raw_codedPAAxiomWitness_standard. exact hPA.
      * apply nth_error_None in hnth. lia.
Qed.

(** ------------------------------------------------------------------
    Agreement with the executable standard wrappers. *)

Theorem raw_codedRestrictedPAProof_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level witnesses derivation,
    RawProofValid derivation ->
    rawContext derivation = map witnessedAxiom witnesses ->
    rawConclusion derivation = pBot ->
    rawProofOccurrenceRank derivation <= level ->
    RawCodedRestrictedPAProof M level
      (rawNumeralValue M
        (restrictedPAProofCode witnesses derivation)).
Proof.
  intros M hPA level witnesses derivation
    hvalid hcontext hconclusion hbounded.
  exists (rawQuotedPAAxiomWitnessList M witnesses),
    (rawQuotedProofCode M derivation),
    (rawQuotedContextCode M (map witnessedAxiom witnesses)).
  split.
  - unfold restrictedPAProofCode.
    rewrite rawQuotedPAAxiomWitnessList_standard by exact hPA.
    rewrite rawQuotedProofCode_standard by exact hPA.
    unfold rawCodeList3. symmetry.
    change (rawListCode M
      (map (rawNumeralValue M)
        [0; axiomWitnessListCode witnesses; rawProofCode derivation]) =
      rawNumeralValue M
        (listCode
          [0; axiomWitnessListCode witnesses; rawProofCode derivation])).
    apply rawListCode_standard. exact hPA.
  - repeat split.
    + apply raw_codedPAAxiomWitnessContext_standard. exact hPA.
    + apply (raw_restrictedProof_of_quoted_rawProof M hPA
        level derivation hvalid hbounded).
    + exact (raw_proofAtomicallyAdequate_quoted M hPA
        derivation hvalid).
    + exists (rawNumeralValue M
        (rawProofFormulaCoverageNatBound derivation)).
      exact (raw_quotedProof_formula_coverage M hPA derivation).
    + exact (raw_quotedValidProof_rule_coverage M hPA
        derivation hvalid).
    + pose proof (raw_quotedProof_rule_valid M hPA derivation hvalid)
        as hrule.
      rewrite hcontext, hconclusion in hrule.
      exact hrule.
Qed.

Corollary raw_sat_codedRestrictedPAProofTermAt_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level e witnesses derivation,
    RawProofValid derivation ->
    rawContext derivation = map witnessedAxiom witnesses ->
    rawConclusion derivation = pBot ->
    rawProofOccurrenceRank derivation <= level ->
    raw_formula_sat M e
      (codedRestrictedPAProofTermAt level
        (Term.numeral (restrictedPAProofCode witnesses derivation))).
Proof.
  intros M hPA level e witnesses derivation
    hvalid hcontext hconclusion hbounded.
  apply (proj2
    (raw_sat_codedRestrictedPAProofTermAt_iff M e level _)).
  rewrite raw_term_eval_numeral.
  exact (raw_codedRestrictedPAProof_standard M hPA
    level witnesses derivation hvalid hcontext hconclusion hbounded).
Qed.

Theorem raw_codedRestrictedPAProvTree_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level witnesses
    (derivation : ProvTree (map witnessedAxiom witnesses) pBot),
    ProofAllBounded level derivation ->
    RawCodedRestrictedPAProof M level
      (rawNumeralValue M
        (restrictedPAProvTreeCode witnesses derivation)).
Proof.
  intros M hPA level witnesses derivation hbounded.
  unfold restrictedPAProvTreeCode.
  apply (raw_codedRestrictedPAProof_standard
    M hPA level witnesses (rawOfProvTree derivation)).
  - apply RawProofValid_rawOfProvTree.
  - apply rawOfProvTree_context.
  - apply rawOfProvTree_conclusion.
  - rewrite rawProofOccurrenceRank_rawOfProvTree. exact hbounded.
Qed.

Corollary raw_sat_codedRestrictedPAProvTreeTermAt_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level e witnesses
    (derivation : ProvTree (map witnessedAxiom witnesses) pBot),
    ProofAllBounded level derivation ->
    raw_formula_sat M e
      (codedRestrictedPAProofTermAt level
        (Term.numeral (restrictedPAProvTreeCode witnesses derivation))).
Proof.
  intros M hPA level e witnesses derivation hbounded.
  apply (proj2
    (raw_sat_codedRestrictedPAProofTermAt_iff M e level _)).
  rewrite raw_term_eval_numeral.
  exact (raw_codedRestrictedPAProvTree_standard
    M hPA level witnesses derivation hbounded).
Qed.

End PABoundedRawCodedRestrictedPAProof.
