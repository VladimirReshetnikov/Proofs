(**
  A transparent raw graph for restricted-PA consistency target codes.

  The earlier uniform-provability module selected the graph of the external
  function [fun n => formulaCode (restrictedPAConsistencyFormula n)] through
  a generic Diophantine-representation interface.  That is adequate in the
  standard model, but it hides how a nonstandard model builds the target
  syntax.  Here the carrier-level construction is explicit; its compact
  object-formula representation is isolated as a separate interface below.

  The syntax of the target is constant except for occurrences of the numeral
  term carrying the restriction level.  We reserve the closed numeral 17 as
  a compile-time marker (the proof-constructor tags stop at 16), quote the
  marked target by transparent polynomial syntax constructors, and replace
  every marked term-code leaf with the output of [RawNumeralTermCodeAt].
  Exact agreement with the legacy concrete target family is stated as the
  finite marker-context equation below.  It is not discharged by a giant
  normalization, because expanding that formula defeats Rocq's sharing and
  is not a maintainable proof method.

  This module constructs target codes only.  It does not construct a PA proof
  certificate for the target and hence does not discharge the uniform proof
  compiler on its own.
*)

From Stdlib Require Import List Arith Lia Bool.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedRestrictedPAConsistency RawCodedNumeralTermCode.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAConsistencyFormulaCode.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedNumeralTermCode.

(** ------------------------------------------------------------------
    A decidable, transparent marker replacement on concrete PA syntax. *)

Fixpoint rawTargetTermEqb (left right : term) : bool :=
  match left, right with
  | tVar i, tVar j => Nat.eqb i j
  | tZero, tZero => true
  | tSucc a, tSucc b => rawTargetTermEqb a b
  | tAdd a b, tAdd c d
  | tMul a b, tMul c d =>
      rawTargetTermEqb a c && rawTargetTermEqb b d
  | _, _ => false
  end.

(** Seventeen is deliberately the first number beyond the constructor tags
    in [proofOccurrenceCasesTerms].  The exact replacement theorem below is
    the kernel-checked guarantee that it is not also used by fixed target
    syntax in a way that would be changed accidentally. *)
Definition restrictedPAConsistencyLevelMarker : nat := 17.

Definition restrictedPAConsistencyLevelMarkerTerm : term :=
  Term.numeral restrictedPAConsistencyLevelMarker.

Definition isRestrictedPAConsistencyLevelMarker (t : term) : bool :=
  rawTargetTermEqb t restrictedPAConsistencyLevelMarkerTerm.

Fixpoint replaceRestrictedPAConsistencyLevelTerm
    (replacement source : term) : term :=
  if isRestrictedPAConsistencyLevelMarker source then replacement
  else
    match source with
    | tVar index => tVar index
    | tZero => tZero
    | tSucc child =>
        tSucc (replaceRestrictedPAConsistencyLevelTerm replacement child)
    | tAdd lhs rhs =>
        tAdd
          (replaceRestrictedPAConsistencyLevelTerm replacement lhs)
          (replaceRestrictedPAConsistencyLevelTerm replacement rhs)
    | tMul lhs rhs =>
        tMul
          (replaceRestrictedPAConsistencyLevelTerm replacement lhs)
          (replaceRestrictedPAConsistencyLevelTerm replacement rhs)
    end.

Fixpoint replaceRestrictedPAConsistencyLevelFormula
    (replacement : term) (source : formula) : formula :=
  match source with
  | pEq lhs rhs =>
      pEq
        (replaceRestrictedPAConsistencyLevelTerm replacement lhs)
        (replaceRestrictedPAConsistencyLevelTerm replacement rhs)
  | pBot => pBot
  | pImp lhs rhs =>
      pImp
        (replaceRestrictedPAConsistencyLevelFormula replacement lhs)
        (replaceRestrictedPAConsistencyLevelFormula replacement rhs)
  | pAnd lhs rhs =>
      pAnd
        (replaceRestrictedPAConsistencyLevelFormula replacement lhs)
        (replaceRestrictedPAConsistencyLevelFormula replacement rhs)
  | pOr lhs rhs =>
      pOr
        (replaceRestrictedPAConsistencyLevelFormula replacement lhs)
        (replaceRestrictedPAConsistencyLevelFormula replacement rhs)
  | pAll child =>
      pAll (replaceRestrictedPAConsistencyLevelFormula replacement child)
  | pEx child =>
      pEx (replaceRestrictedPAConsistencyLevelFormula replacement child)
  end.

Definition markedRestrictedPAConsistencyFormula : formula :=
  restrictedPAConsistencyFormula restrictedPAConsistencyLevelMarker.

(** Exactness of the finite marked syntax context.  This proposition is kept
    explicit because blindly normalizing the already-large concrete target
    duplicates its syntax exponentially in Rocq.  A later compositional audit
    can discharge it one shared definition at a time; none of the arbitrary-
    model totality results below assumes it. *)
Definition RestrictedPAConsistencyLevelMarkerExact : Prop := forall level,
  replaceRestrictedPAConsistencyLevelFormula (Term.numeral level)
    markedRestrictedPAConsistencyFormula =
  restrictedPAConsistencyFormula level.

(** ------------------------------------------------------------------
    The same replacement while quoting into a raw model. *)

Fixpoint rawMarkedTermCode (M : RawPAModel)
    (replacementCode : M) (source : term) : M :=
  if isRestrictedPAConsistencyLevelMarker source then replacementCode
  else
    match source with
    | tVar index => rawTermVarCode M (rawNumeralValue M index)
    | tZero => rawTermZeroCode M
    | tSucc child =>
        rawTermSuccCode M (rawMarkedTermCode M replacementCode child)
    | tAdd lhs rhs =>
        rawTermAddCode M
          (rawMarkedTermCode M replacementCode lhs)
          (rawMarkedTermCode M replacementCode rhs)
    | tMul lhs rhs =>
        rawTermMulCode M
          (rawMarkedTermCode M replacementCode lhs)
          (rawMarkedTermCode M replacementCode rhs)
    end.

Fixpoint rawMarkedFormulaCode (M : RawPAModel)
    (replacementCode : M) (source : formula) : M :=
  match source with
  | pEq lhs rhs =>
      rawFormulaEqCode M
        (rawMarkedTermCode M replacementCode lhs)
        (rawMarkedTermCode M replacementCode rhs)
  | pBot => rawFormulaBotCode M
  | pImp lhs rhs =>
      rawFormulaImpCode M
        (rawMarkedFormulaCode M replacementCode lhs)
        (rawMarkedFormulaCode M replacementCode rhs)
  | pAnd lhs rhs =>
      rawFormulaAndCode M
        (rawMarkedFormulaCode M replacementCode lhs)
        (rawMarkedFormulaCode M replacementCode rhs)
  | pOr lhs rhs =>
      rawFormulaOrCode M
        (rawMarkedFormulaCode M replacementCode lhs)
        (rawMarkedFormulaCode M replacementCode rhs)
  | pAll child =>
      rawFormulaAllCode M (rawMarkedFormulaCode M replacementCode child)
  | pEx child =>
      rawFormulaExCode M (rawMarkedFormulaCode M replacementCode child)
  end.

Arguments rawMarkedTermCode M replacementCode source : clear implicits.
Arguments rawMarkedFormulaCode M replacementCode source : clear implicits.

Lemma rawMarkedTermCode_of_quoted_replacement : forall
    (M : RawPAModel) replacement source,
  rawMarkedTermCode M (rawQuotedTermCode M replacement) source =
  rawQuotedTermCode M
    (replaceRestrictedPAConsistencyLevelTerm replacement source).
Proof.
  intros M replacement source.
  induction source as
      [index | | child IH | lhs IHl rhs IHr | lhs IHl rhs IHr];
    cbn [rawMarkedTermCode
      replaceRestrictedPAConsistencyLevelTerm];
    destruct (isRestrictedPAConsistencyLevelMarker _) eqn:hmarker;
    cbn [rawQuotedTermCode]; try reflexivity.
  - now rewrite IH.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
Qed.

Lemma rawMarkedFormulaCode_of_quoted_replacement : forall
    (M : RawPAModel) replacement source,
  rawMarkedFormulaCode M (rawQuotedTermCode M replacement) source =
  rawQuotedFormulaCode M
    (replaceRestrictedPAConsistencyLevelFormula replacement source).
Proof.
  intros M replacement source.
  induction source as
      [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
       lhs IHl rhs IHr | child IH | child IH];
    cbn [rawMarkedFormulaCode
      replaceRestrictedPAConsistencyLevelFormula rawQuotedFormulaCode].
  - now rewrite !rawMarkedTermCode_of_quoted_replacement.
  - reflexivity.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - now rewrite IHl, IHr.
  - now rewrite IH.
  - now rewrite IH.
Qed.

(** ------------------------------------------------------------------
    Raw graph and arbitrary-model totality. *)

Definition RawMarkedFormulaCodeAt (source : formula)
    (M : RawPAModel) (level output : M) : Prop :=
  exists numeralCode : M,
    RawNumeralTermCodeAt M level numeralCode /\
    output = rawMarkedFormulaCode M numeralCode source.

Arguments RawMarkedFormulaCodeAt source M level output
  : clear implicits.

Definition RawRestrictedPAConsistencyFormulaCodeAt
    (M : RawPAModel) (level output : M) : Prop :=
  RawMarkedFormulaCodeAt
    markedRestrictedPAConsistencyFormula M level output.

Arguments RawRestrictedPAConsistencyFormulaCodeAt M level output
  : clear implicits.

Theorem raw_markedFormulaCodeAt_total : forall source
    (M : RawPAModel), RawPASatisfies M -> forall level,
  exists output,
    RawMarkedFormulaCodeAt source M level output.
Proof.
  intros source M hPA level.
  destruct (raw_numeralTermCodeExists_all M hPA level)
    as [numeralCode hnumeral].
  exists (rawMarkedFormulaCode M numeralCode source), numeralCode.
  split; [exact hnumeral | reflexivity].
Qed.

Corollary raw_restrictedPAConsistencyFormulaCodeAt_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  exists output,
    RawRestrictedPAConsistencyFormulaCodeAt M level output.
Proof.
  intros M hPA level.
  exact (raw_markedFormulaCodeAt_total
    markedRestrictedPAConsistencyFormula M hPA level).
Qed.

(** A formula represents the raw graph in output-first order when variable 0
    is [output] and variable 1 is [level].  This interface is deliberately
    explicit: constructing such a formula without expanding the enormous
    marked target is the remaining compositional syntax-operation trace. *)
Definition RestrictedPAConsistencyFormulaCodeGraphRepresentation
    (graph : formula) : Prop :=
  forall (M : RawPAModel) (tail : nat -> M) level output,
    raw_formula_sat M
      (scons M output (scons M level tail)) graph <->
    RawRestrictedPAConsistencyFormulaCodeAt M level output.

Arguments RestrictedPAConsistencyFormulaCodeGraphRepresentation graph
  : clear implicits.

Definition restrictedPAConsistencyFormulaCodeGraphTotalityBody
    (graph : formula) : formula :=
  pAll (pEx graph).

Definition restrictedPAConsistencyFormulaCodeGraphTotalityFormula
    (graph : formula) : formula :=
  Formula.sealPA
    (restrictedPAConsistencyFormulaCodeGraphTotalityBody graph).

Theorem restrictedPAConsistencyFormulaCodeGraphTotalityFormula_sentence :
  forall graph,
  Formula.Sentence
    (restrictedPAConsistencyFormulaCodeGraphTotalityFormula graph).
Proof.
  intro graph.
  unfold restrictedPAConsistencyFormulaCodeGraphTotalityFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem PA_proves_restrictedPAConsistencyFormulaCodeGraphTotality_of_representation :
  forall graph,
  RestrictedPAConsistencyFormulaCodeGraphRepresentation graph ->
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyFormulaCodeGraphTotalityFormula graph).
Proof.
  intros graph hgraph.
  apply PA_BProv_of_raw_valid.
  - apply restrictedPAConsistencyFormulaCodeGraphTotalityFormula_sentence.
  - intros M hPA e.
    unfold restrictedPAConsistencyFormulaCodeGraphTotalityFormula.
    apply raw_formula_sat_sealPA_of_valid.
    intro tail.
    unfold restrictedPAConsistencyFormulaCodeGraphTotalityBody.
    cbn [raw_formula_sat].
    intro level.
    destruct (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA level)
      as [output houtput].
    exists output.
    exact (proj2 (hgraph M tail level output) houtput).
Qed.

(** The graph's only possible source of non-functionality is the numeral
    trace.  This conditional theorem makes that dependency explicit and is
    usable immediately once arbitrary-model numeral-trace functionality is
    established. *)
Definition RawNumeralTermCodeAtFunctional (M : RawPAModel) : Prop :=
  forall level first second,
    RawNumeralTermCodeAt M level first ->
    RawNumeralTermCodeAt M level second ->
    first = second.

Theorem raw_restrictedPAConsistencyFormulaCodeAt_functional_of_numeral :
  forall (M : RawPAModel), RawNumeralTermCodeAtFunctional M ->
  forall level first second,
    RawRestrictedPAConsistencyFormulaCodeAt M level first ->
    RawRestrictedPAConsistencyFormulaCodeAt M level second ->
    first = second.
Proof.
  intros M hfunctional level first second
    [firstNumeral [hfirstNumeral ->]]
    [secondNumeral [hsecondNumeral ->]].
  now rewrite (hfunctional level firstNumeral secondNumeral
    hfirstNumeral hsecondNumeral).
Qed.

(** ------------------------------------------------------------------
    Agreement with the exact standard target family. *)

Lemma raw_numeralTermCodeAt_standard_output : forall
    (M : RawPAModel), RawPASatisfies M -> forall level output,
  RawNumeralTermCodeAt M (rawNumeralValue M level) output ->
  output = rawQuotedTermCode M (Term.numeral level).
Proof.
  intros M hPA level.
  induction level as [|level IH]; intros output
      (code & step & [hdefined [hzero hrows]] & houtput).
  - change (rawNumeralValue M 0) with (raw_zero M) in houtput.
    change (rawQuotedTermCode M (Term.numeral 0)) with
      (rawTermZeroCode M).
    exact (raw_codedAssignmentLookup_functional M hPA
      code step (raw_zero M) output (rawTermZeroCode M)
      houtput hzero).
  - assert (hlt : rawLt M (rawNumeralValue M level)
        (rawNumeralValue M (S level))).
    {
      apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
    }
    assert (hnextIndex : raw_succ M (rawNumeralValue M level) =
        rawNumeralValue M (S level)).
    { reflexivity. }
    unfold RawNumeralTermCodeRows in hrows.
    assert (hcurrentDefinedIndex :
        rawLt M (rawNumeralValue M level)
          (raw_succ M (rawNumeralValue M (S level)))).
    {
      eapply raw_assignment_lt_trans; [exact hPA | exact hlt |].
      exact (raw_assignment_lt_self_succ M hPA _).
    }
    destruct (hdefined (rawNumeralValue M level) hcurrentDefinedIndex)
      as [current hcurrent].
    assert (hcurrentStandard :
        current = rawQuotedTermCode M (Term.numeral level)).
    {
      apply IH.
      exists code, step. split; [| exact hcurrent].
      repeat split.
      - intros index hindex. apply hdefined.
        eapply raw_assignment_lt_trans; [exact hPA | exact hindex |].
        exact (raw_assignment_lt_self_succ M hPA
          (raw_succ M (rawNumeralValue M level))).
      - exact hzero.
      - intros index previous next hindex hprevious hnext.
        apply (hrows index previous next); [| exact hprevious | exact hnext].
        eapply raw_assignment_lt_trans; [exact hPA | exact hindex |].
        exact hlt.
    }
    specialize (hrows (rawNumeralValue M level) current output
      hlt hcurrent).
    rewrite hnextIndex in hrows.
    specialize (hrows houtput).
    rewrite hrows, hcurrentStandard.
    reflexivity.
Qed.

Corollary raw_numeralTermCodeAt_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawNumeralTermCodeAt M
    (rawNumeralValue M level)
    (rawQuotedTermCode M (Term.numeral level)).
Proof.
  intros M hPA level.
  destruct (raw_numeralTermCodeExists_all M hPA
    (rawNumeralValue M level)) as [output houtput].
  rewrite <- (raw_numeralTermCodeAt_standard_output M hPA
    level output houtput).
  exact houtput.
Qed.

Theorem raw_markedFormulaCodeAt_standard : forall source
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawMarkedFormulaCodeAt source M
    (rawNumeralValue M level)
    (rawNumeralValue M
      (formulaCode
        (replaceRestrictedPAConsistencyLevelFormula
          (Term.numeral level) source))).
Proof.
  intros source M hPA level.
  exists (rawQuotedTermCode M (Term.numeral level)). split.
  - exact (raw_numeralTermCodeAt_standard M hPA level).
  - rewrite rawMarkedFormulaCode_of_quoted_replacement.
    symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Theorem raw_restrictedPAConsistencyFormulaCodeAt_standard_of_marker_exact :
  RestrictedPAConsistencyLevelMarkerExact -> forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedPAConsistencyFormulaCodeAt M
    (rawNumeralValue M level)
    (rawNumeralValue M
      (formulaCode (restrictedPAConsistencyFormula level))).
Proof.
  intros hmarker M hPA level.
  unfold RawRestrictedPAConsistencyFormulaCodeAt.
  rewrite <- hmarker.
  apply raw_markedFormulaCodeAt_standard. exact hPA.
Qed.

End PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
