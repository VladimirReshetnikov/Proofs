(**
  Diagonal substitution for standard syntax scoped below a raw cutoff.

  The operation used to unseal universal closures must fix its input formula.
  For a quoted formula this is true whenever every free variable lies strictly
  below the substitution depth: opening then always selects the low-variable
  branch.  The depth may be nonstandard; only the syntactic free-variable
  bound is metatheoretic.

  Two public corollaries are the intended clients:

  - a formula scoped below one is fixed at every positive raw depth;
  - a closed formula (scoped below zero) is fixed at every raw depth.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedNumeralTermCode RawCodedNumeralTermShift
  RawCodedTermOperationTreeRealization
  RawCodedFormulaDiagonalOperation
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedFormulaDiagonalOperationComposition.

Module PABoundedRawCodedScopedFormulaDiagonalSubstitution.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.

Definition StandardTermScoped (scope : nat) (input : term) : Prop :=
  forall index, Term.Free index input -> index < scope.

Definition StandardFormulaScoped (scope : nat) (input : formula) : Prop :=
  forall index, Formula.Free index input -> index < scope.

Arguments StandardTermScoped scope input : clear implicits.
Arguments StandardFormulaScoped scope input : clear implicits.

(** Identity term tree; validity below an arbitrary carrier cutoff is the
    only nontrivial field. *)
Fixpoint rawStandardTermOpeningIdentityTree (M : RawPAModel)
    (input : term) : RawTermOperationTree M :=
  match input with
  | tVar index =>
      RTOTVar M (rawNumeralValue M index)
        (rawTermVarCode M (rawNumeralValue M index))
  | tZero => RTOTZero M
  | tSucc child =>
      RTOTSucc M (rawStandardTermOpeningIdentityTree M child)
  | tAdd lhs rhs =>
      RTOTBinary M RTOBAdd
        (rawStandardTermOpeningIdentityTree M lhs)
        (rawStandardTermOpeningIdentityTree M rhs)
  | tMul lhs rhs =>
      RTOTBinary M RTOBMul
        (rawStandardTermOpeningIdentityTree M lhs)
        (rawStandardTermOpeningIdentityTree M rhs)
  end.

Lemma rawStandardTermOpeningIdentityTree_source : forall M input,
  rawTermOperationTreeSource M
    (rawStandardTermOpeningIdentityTree M input) =
  rawQuotedTermCode M input.
Proof.
  intros M input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [rawStandardTermOpeningIdentityTree rawTermOperationTreeSource
      rawTermOperationBinaryCode rawQuotedTermCode];
    now rewrite ?IH, ?IHlhs, ?IHrhs.
Qed.

Lemma rawStandardTermOpeningIdentityTree_target : forall M input,
  rawTermOperationTreeTarget M
    (rawStandardTermOpeningIdentityTree M input) =
  rawQuotedTermCode M input.
Proof.
  intros M input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [rawStandardTermOpeningIdentityTree rawTermOperationTreeTarget
      rawTermOperationBinaryCode rawQuotedTermCode];
    now rewrite ?IH, ?IHlhs, ?IHrhs.
Qed.

Theorem rawStandardTermOpeningIdentityTree_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff liftedReplacement input,
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawTermOperationTreeValid M
    (RawCodedTermOpeningVariableRow M cutoff liftedReplacement)
    (rawStandardTermOpeningIdentityTree M input).
Proof.
  intros M hPA scope cutoff liftedReplacement input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs]; intros hscope hcutoff;
    cbn [rawStandardTermOpeningIdentityTree RawTermOperationTreeValid].
  - assert (hindexMeta : index < scope).
    { apply hscope. reflexivity. }
    assert (hindexRaw : rawLt M (rawNumeralValue M index) cutoff).
    {
      exact (raw_lt_le_trans_pair M hPA
        (rawNumeralValue M index) (rawNumeralValue M scope) cutoff
        (raw_lt_numeralValue_of_lt M hPA index scope hindexMeta)
        hcutoff).
    }
    exists (rawNumeralValue M index). split; [reflexivity |].
    left. split; [exact hindexRaw | reflexivity].
  - exact I.
  - apply IH; [exact hscope | exact hcutoff].
  - split.
    + apply IHlhs; [|exact hcutoff].
      intros index hfree. apply hscope. now left.
    + apply IHrhs; [|exact hcutoff].
      intros index hfree. apply hscope. now right.
  - split.
    + apply IHlhs; [|exact hcutoff].
      intros index hfree. apply hscope. now left.
    + apply IHrhs; [|exact hcutoff].
      intros index hfree. apply hscope. now right.
Qed.

Theorem raw_codedTermOpening_standard_identity_below : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    scope cutoff liftedReplacement input,
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) cutoff ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA scope cutoff liftedReplacement input hscope hcutoff.
  pose proof (raw_codedTermOpening_of_valid_tree M hPA
    cutoff liftedReplacement
    (rawStandardTermOpeningIdentityTree M input)
    (rawStandardTermOpeningIdentityTree_valid M hPA
      scope cutoff liftedReplacement input hscope hcutoff)) as hopening.
  rewrite rawStandardTermOpeningIdentityTree_source in hopening.
  rewrite rawStandardTermOpeningIdentityTree_target in hopening.
  exact hopening.
Qed.

Lemma raw_codedFormulaSubstitutionAtom_standard_identity_below : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement scope depth input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA replacementBound replacement scope depth input
    hreplacement hscope hdepth.
  exists replacement. split.
  - exact (raw_codedTermShift_numeral_identity M hPA
      replacementBound replacement (raw_zero M) depth hreplacement).
  - exact (raw_codedTermOpening_standard_identity_below M hPA
      scope depth replacement input hscope hdepth).
Qed.

(** Entering a binder grows the allowed syntactic scope and the represented
    substitution cutoff in lockstep. *)
Lemma StandardFormulaScoped_binder : forall scope input,
  StandardFormulaScoped scope (pAll input) ->
  StandardFormulaScoped (S scope) input.
Proof.
  intros scope input hscope [|index] hfree; [lia |].
  cbn [StandardFormulaScoped] in hscope.
  specialize (hscope index hfree). lia.
Qed.

Lemma StandardFormulaScoped_ex_binder : forall scope input,
  StandardFormulaScoped scope (pEx input) ->
  StandardFormulaScoped (S scope) input.
Proof.
  intros scope input hscope [|index] hfree; [lia |].
  cbn [StandardFormulaScoped] in hscope.
  specialize (hscope index hfree). lia.
Qed.

(** Structural diagonal realization for a standard formula. *)
Theorem raw_codedFormulaDiagonalSubstitution_standard_scoped : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement scope depth input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  StandardFormulaScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA replacementBound replacement scope depth input hreplacement.
  revert scope depth.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros scope depth hscope hdepth;
    cbn [rawQuotedFormulaCode].
  - apply (raw_codedFormulaDiagonalSubstitution_eq M hPA
      replacement depth (rawQuotedTermCode M lhs)
      (rawQuotedTermCode M rhs)).
    + apply (raw_codedFormulaSubstitutionAtom_standard_identity_below
        M hPA replacementBound replacement scope depth lhs hreplacement).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (raw_codedFormulaSubstitutionAtom_standard_identity_below
        M hPA replacementBound replacement scope depth rhs hreplacement).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
      replacement depth).
  - apply (raw_codedFormulaDiagonalSubstitution_imp M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_and M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_or M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_all M hPA
      replacement depth (rawQuotedFormulaCode M child)).
    apply (IHchild (S scope) (raw_succ M depth)).
    + exact (StandardFormulaScoped_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M depth)).
      exact (raw_rank_succ_le M hPA _ _ hdepth).
  - apply (raw_codedFormulaDiagonalSubstitution_ex M hPA
      replacement depth (rawQuotedFormulaCode M child)).
    apply (IHchild (S scope) (raw_succ M depth)).
    + exact (StandardFormulaScoped_ex_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M depth)).
      exact (raw_rank_succ_le M hPA _ _ hdepth).
Qed.

Corollary raw_codedFormulaDiagonalSubstitution_standard_positive : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  StandardFormulaScoped 1 input ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA replacementBound replacement input hreplacement hscope depth.
  apply (raw_codedFormulaDiagonalSubstitution_standard_scoped M hPA
    replacementBound replacement 1 (raw_succ M depth) input
    hreplacement hscope).
  apply raw_rank_one_le_succ. exact hPA.
Qed.

Corollary raw_codedFormulaDiagonalSubstitution_standard_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementBound replacement input,
  RawNumeralTermCodeAt M replacementBound replacement ->
  StandardFormulaScoped 0 input ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA replacementBound replacement input hreplacement hscope depth.
  apply (raw_codedFormulaDiagonalSubstitution_standard_scoped M hPA
    replacementBound replacement 0 depth input hreplacement hscope).
  change (rawLe M (raw_zero M) depth).
  apply raw_rank_zero_le. exact hPA.
Qed.

End PABoundedRawCodedScopedFormulaDiagonalSubstitution.
