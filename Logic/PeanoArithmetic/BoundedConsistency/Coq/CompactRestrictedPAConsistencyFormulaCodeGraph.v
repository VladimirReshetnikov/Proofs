(**
  A compact, fully internal graph of the restricted-consistency target code.

  The target formula [restrictedPAConsistencyFormula level] is large, but
  its syntax depends on [level] only through the code of the numeral term.
  The preceding raw development records that dependence as a finite syntax
  context.  This file compiles that context to an ordinary PA term: every
  syntax-code constructor is polynomial, so no recursion inside the model is
  needed once the (possibly nonstandard) numeral-term code has been produced.

  Consequently the graph below is an actual PA formula, not a selected
  standard-model Diophantine representative.  Its adequacy theorem holds in
  every law-free raw arithmetic structure.  PA is needed only to guarantee
  existence of the numeral-code trace at every, including nonstandard,
  carrier element.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedNumeralTermCode RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyFormulaCode.

Import ListNotations.

Module PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.

(** Quotation of each fixed syntax subtree can itself be written as a PA
    term, because the chosen Godel constructors are explicit polynomials. *)
Fixpoint compactQuotedTermCodeTerm (source : term) : term :=
  match source with
  | tVar index =>
      codeList2Term (Term.numeral 0) (Term.numeral index)
  | tZero => codeList1Term (Term.numeral 1)
  | tSucc child =>
      codeList2Term (Term.numeral 2)
        (compactQuotedTermCodeTerm child)
  | tAdd lhs rhs =>
      codeList3Term (Term.numeral 3)
        (compactQuotedTermCodeTerm lhs)
        (compactQuotedTermCodeTerm rhs)
  | tMul lhs rhs =>
      codeList3Term (Term.numeral 4)
        (compactQuotedTermCodeTerm lhs)
        (compactQuotedTermCodeTerm rhs)
  end.

Fixpoint compactQuotedFormulaCodeTerm (source : formula) : term :=
  match source with
  | pEq lhs rhs =>
      codeList3Term (Term.numeral 0)
        (compactQuotedTermCodeTerm lhs)
        (compactQuotedTermCodeTerm rhs)
  | pBot => codeList1Term (Term.numeral 1)
  | pImp lhs rhs =>
      codeList3Term (Term.numeral 2)
        (compactQuotedFormulaCodeTerm lhs)
        (compactQuotedFormulaCodeTerm rhs)
  | pAnd lhs rhs =>
      codeList3Term (Term.numeral 3)
        (compactQuotedFormulaCodeTerm lhs)
        (compactQuotedFormulaCodeTerm rhs)
  | pOr lhs rhs =>
      codeList3Term (Term.numeral 4)
        (compactQuotedFormulaCodeTerm lhs)
        (compactQuotedFormulaCodeTerm rhs)
  | pAll child =>
      codeList2Term (Term.numeral 5)
        (compactQuotedFormulaCodeTerm child)
  | pEx child =>
      codeList2Term (Term.numeral 6)
        (compactQuotedFormulaCodeTerm child)
  end.

Lemma raw_eval_compactQuotedTermCodeTerm : forall
    (M : RawPAModel) e source,
  raw_term_eval M e (compactQuotedTermCodeTerm source) =
  rawQuotedTermCode M source.
Proof.
  intros M e source.
  induction source as
      [index | | child IH | lhs IHl rhs IHr | lhs IHl rhs IHr];
    cbn [compactQuotedTermCodeTerm rawQuotedTermCode];
    rewrite ?raw_eval_codeList1Term, ?raw_eval_codeList2Term,
      ?raw_eval_codeList3Term, ?IH, ?IHl, ?IHr;
    try rewrite !raw_term_eval_numeral;
    reflexivity.
Qed.

Lemma raw_eval_compactQuotedFormulaCodeTerm : forall
    (M : RawPAModel) e source,
  raw_term_eval M e (compactQuotedFormulaCodeTerm source) =
  rawQuotedFormulaCode M source.
Proof.
  intros M e source.
  induction source as
      [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
       lhs IHl rhs IHr | child IH | child IH];
    cbn [compactQuotedFormulaCodeTerm rawQuotedFormulaCode];
    rewrite ?raw_eval_codeList1Term, ?raw_eval_codeList2Term,
      ?raw_eval_codeList3Term,
      ?raw_eval_compactQuotedTermCodeTerm, ?IH, ?IHl, ?IHr;
    try rewrite !raw_term_eval_numeral;
    reflexivity.
Qed.

(** Compile the shared target context.  A hole is represented by the input
    term [replacementCode]; all other nodes are direct polynomial folds. *)
Fixpoint compactRestrictedTargetTermContextCodeTerm
    (replacementCode : term) (context : RestrictedTargetTermContext)
    : term :=
  match context with
  | RTTCFixed fixed => compactQuotedTermCodeTerm fixed
  | RTTCHole => replacementCode
  | RTTCSucc child =>
      codeList2Term (Term.numeral 2)
        (compactRestrictedTargetTermContextCodeTerm
          replacementCode child)
  | RTTCAdd lhs rhs =>
      codeList3Term (Term.numeral 3)
        (compactRestrictedTargetTermContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetTermContextCodeTerm replacementCode rhs)
  | RTTCMul lhs rhs =>
      codeList3Term (Term.numeral 4)
        (compactRestrictedTargetTermContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetTermContextCodeTerm replacementCode rhs)
  end.

Fixpoint compactRestrictedTargetCloseNFormulaCodeTerm
    (count : nat) (code : term) : term :=
  match count with
  | 0 => code
  | S count' =>
      compactRestrictedTargetCloseNFormulaCodeTerm count'
        (codeList2Term (Term.numeral 5) code)
  end.

Fixpoint compactRestrictedTargetFormulaContextCodeTerm
    (replacementCode : term) (context : RestrictedTargetFormulaContext)
    : term :=
  match context with
  | RTFCFixed fixed => compactQuotedFormulaCodeTerm fixed
  | RTFCBot => codeList1Term (Term.numeral 1)
  | RTFCEq lhs rhs =>
      codeList3Term (Term.numeral 0)
        (compactRestrictedTargetTermContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetTermContextCodeTerm replacementCode rhs)
  | RTFCImp lhs rhs =>
      codeList3Term (Term.numeral 2)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode rhs)
  | RTFCAnd lhs rhs =>
      codeList3Term (Term.numeral 3)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode rhs)
  | RTFCOr lhs rhs =>
      codeList3Term (Term.numeral 4)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode lhs)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode rhs)
  | RTFCAll child =>
      codeList2Term (Term.numeral 5)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode child)
  | RTFCEx child =>
      codeList2Term (Term.numeral 6)
        (compactRestrictedTargetFormulaContextCodeTerm replacementCode child)
  | RTFCSeal child =>
      compactRestrictedTargetCloseNFormulaCodeTerm
        (restrictedTargetFormulaContextBound child)
        (compactRestrictedTargetFormulaContextCodeTerm
          replacementCode child)
  end.

Lemma raw_eval_compactRestrictedTargetTermContextCodeTerm : forall
    (M : RawPAModel) e replacementCode context,
  raw_term_eval M e
    (compactRestrictedTargetTermContextCodeTerm replacementCode context) =
  rawRestrictedTargetTermContextCode M
    (raw_term_eval M e replacementCode) context.
Proof.
  intros M e replacementCode context.
  induction context; cbn
    [compactRestrictedTargetTermContextCodeTerm
      rawRestrictedTargetTermContextCode];
    rewrite ?raw_eval_compactQuotedTermCodeTerm,
      ?raw_eval_codeList2Term, ?raw_eval_codeList3Term,
      ?IHcontext, ?IHcontext1, ?IHcontext2;
    try rewrite !raw_term_eval_numeral;
    reflexivity.
Qed.

Lemma raw_eval_compactRestrictedTargetCloseNFormulaCodeTerm : forall
    count (M : RawPAModel) e code,
  raw_term_eval M e
    (compactRestrictedTargetCloseNFormulaCodeTerm count code) =
  rawRestrictedTargetCloseNFormulaCode M count
    (raw_term_eval M e code).
Proof.
  intro count. induction count as [|count IH]; intros M e code.
  - reflexivity.
  - cbn [compactRestrictedTargetCloseNFormulaCodeTerm
      rawRestrictedTargetCloseNFormulaCode].
    rewrite IH, raw_eval_codeList2Term, raw_term_eval_numeral.
    reflexivity.
Qed.

Lemma raw_eval_compactRestrictedTargetFormulaContextCodeTerm : forall
    (M : RawPAModel) e replacementCode context,
  raw_term_eval M e
    (compactRestrictedTargetFormulaContextCodeTerm
      replacementCode context) =
  rawRestrictedTargetFormulaContextCode M
    (raw_term_eval M e replacementCode) context.
Proof.
  intros M e replacementCode context.
  induction context; cbn
    [compactRestrictedTargetFormulaContextCodeTerm
      rawRestrictedTargetFormulaContextCode];
    rewrite ?raw_eval_compactQuotedFormulaCodeTerm,
      ?raw_eval_compactRestrictedTargetTermContextCodeTerm,
      ?raw_eval_codeList1Term, ?raw_eval_codeList2Term,
      ?raw_eval_codeList3Term,
      ?raw_eval_compactRestrictedTargetCloseNFormulaCodeTerm,
      ?IHcontext, ?IHcontext1, ?IHcontext2;
    repeat rewrite raw_eval_compactRestrictedTargetTermContextCodeTerm;
    try rewrite !raw_term_eval_numeral;
    reflexivity.
Qed.

(** Output-first graph.  Beneath the existential binder, variable 0 is the
    numeral-term code, variable 1 is the requested output, and variable 2 is
    the input level. *)
Definition compactRestrictedPAConsistencyFormulaCodeGraph : formula :=
  pEx
    (pAnd
      (numeralTermCodeAtTermAt (tVar 2) (tVar 0))
      (pEq (tVar 1)
        (compactRestrictedTargetFormulaContextCodeTerm
          (tVar 0) restrictedPAConsistencyFormulaContext))).

Theorem compactRestrictedPAConsistencyFormulaCodeGraph_representation :
  RestrictedPAConsistencyFormulaCodeGraphRepresentation
    compactRestrictedPAConsistencyFormulaCodeGraph.
Proof.
  intros M tail level output.
  unfold compactRestrictedPAConsistencyFormulaCodeGraph,
    RawRestrictedPAConsistencyFormulaCodeAt.
  cbn [raw_formula_sat].
  split.
  - intros [numeralCode [hnumeral houtput]].
    exists numeralCode. split.
    + apply (proj1
        (raw_sat_numeralTermCodeAtTermAt_iff M
          (scons M numeralCode
            (scons M output (scons M level tail)))
          (tVar 2) (tVar 0))).
      exact hnumeral.
    + rewrite raw_eval_compactRestrictedTargetFormulaContextCodeTerm
        in houtput.
      cbn [raw_term_eval scons] in houtput.
      exact houtput.
  - intros [numeralCode [hnumeral houtput]].
    exists numeralCode. split.
    + apply (proj2
        (raw_sat_numeralTermCodeAtTermAt_iff M
          (scons M numeralCode
            (scons M output (scons M level tail)))
          (tVar 2) (tVar 0))).
      cbn [raw_term_eval scons].
      exact hnumeral.
    + rewrite raw_eval_compactRestrictedTargetFormulaContextCodeTerm.
      cbn [raw_term_eval scons].
      exact houtput.
Qed.

(** The graph is total at every element of every PA model, including the
    nonstandard elements that cannot be reached by Rocq recursion. *)
Theorem compactRestrictedPAConsistencyFormulaCodeGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  exists output,
    raw_formula_sat M
      (scons M output (scons M level tail))
      compactRestrictedPAConsistencyFormulaCodeGraph.
Proof.
  intros M hPA tail level.
  destruct (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA level)
    as [output houtput].
  exists output.
  exact (proj2
    (compactRestrictedPAConsistencyFormulaCodeGraph_representation
      M tail level output) houtput).
Qed.

Theorem PA_proves_compactRestrictedPAConsistencyFormulaCodeGraph_totality :
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyFormulaCodeGraphTotalityFormula
      compactRestrictedPAConsistencyFormulaCodeGraph).
Proof.
  apply
    PA_proves_restrictedPAConsistencyFormulaCodeGraphTotality_of_representation.
  exact compactRestrictedPAConsistencyFormulaCodeGraph_representation.
Qed.

(** On every standard numeral the compact graph returns exactly the legacy
    Godel code of [restrictedPAConsistencyFormula level]. *)
Theorem compactRestrictedPAConsistencyFormulaCodeGraph_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  raw_formula_sat M
    (scons M
      (rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula level)))
      (scons M (rawNumeralValue M level) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph.
Proof.
  intros M hPA tail level.
  apply (proj2
    (compactRestrictedPAConsistencyFormulaCodeGraph_representation M tail
      (rawNumeralValue M level)
      (rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula level))))).
  exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA level).
Qed.

End PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
