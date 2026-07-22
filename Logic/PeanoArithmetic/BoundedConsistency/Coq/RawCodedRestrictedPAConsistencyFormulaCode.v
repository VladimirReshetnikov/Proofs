(**
  A transparent raw graph for restricted-PA consistency target codes.

  The earlier uniform-provability module selected the graph of the external
  function [fun n => formulaCode (restrictedPAConsistencyFormula n)] through
  a generic Diophantine-representation interface.  That is adequate in the
  standard model, but it hides how a nonstandard model builds the target
  syntax.  Here the carrier-level construction is explicit; its compact
  object-formula representation is isolated as a separate interface below.

  The syntax of the target is constant except for occurrences of the numeral
  term carrying the restriction level.  A generic marker-replacement
  construction is retained for reuse, while the exact target family is built
  from an explicit syntax context whose holes are precisely those numerals.
  Fixed subformulae remain shared, so agreement with the legacy target is
  proved compositionally without normalizing the enormous expanded formula.

  This module constructs target codes only.  It does not construct a PA proof
  certificate for the target and hence does not discharge the uniform proof
  compiler on its own.
*)

From Stdlib Require Import List Arith Lia Bool.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality RawCodedTermEvaluationTraversal
  RawCodedContextLists
  RawCodedFormulaOperations
  RawCodedProofTraversal RawCodedProofEndpoints RawCodedProofRules
  RawCodedProofAtomicAdequacy RawCodedProofRuleCoverage
  RawCodedFixedLevelTruth RawCodedContextBounds
  RawCodedRestrictedProofTraversal RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistency RawCodedNumeralTermCode.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAConsistencyFormulaCode.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAProof.
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
    in [proofOccurrenceCasesTerms].  Marker replacement remains a useful
    generic quoting operation, but exact target agreement below uses explicit
    contexts and therefore does not depend on a global freshness claim. *)
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
    A shared syntax context for the exact target family.

    The marker construction above is useful generically, but proving that a
    concrete marker is fresh by reducing the fully expanded target destroys
    sharing.  The context datatype below records the level holes explicitly.
    [RTFCFixed] is the key sharing constructor: a level-independent formula is
    retained as one opaque subtree instead of being traversed and copied. *)

Inductive RestrictedTargetTermContext : Type :=
| RTTCFixed : term -> RestrictedTargetTermContext
| RTTCHole : RestrictedTargetTermContext
| RTTCSucc : RestrictedTargetTermContext -> RestrictedTargetTermContext
| RTTCAdd : RestrictedTargetTermContext -> RestrictedTargetTermContext ->
    RestrictedTargetTermContext
| RTTCMul : RestrictedTargetTermContext -> RestrictedTargetTermContext ->
    RestrictedTargetTermContext.

Inductive RestrictedTargetFormulaContext : Type :=
| RTFCFixed : formula -> RestrictedTargetFormulaContext
| RTFCBot : RestrictedTargetFormulaContext
| RTFCEq : RestrictedTargetTermContext -> RestrictedTargetTermContext ->
    RestrictedTargetFormulaContext
| RTFCImp : RestrictedTargetFormulaContext ->
    RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext
| RTFCAnd : RestrictedTargetFormulaContext ->
    RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext
| RTFCOr : RestrictedTargetFormulaContext ->
    RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext
| RTFCAll : RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext
| RTFCEx : RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext
| RTFCSeal : RestrictedTargetFormulaContext -> RestrictedTargetFormulaContext.

Fixpoint instantiateRestrictedTargetTermContext
    (replacement : term) (context : RestrictedTargetTermContext) : term :=
  match context with
  | RTTCFixed fixed => fixed
  | RTTCHole => replacement
  | RTTCSucc child =>
      tSucc (instantiateRestrictedTargetTermContext replacement child)
  | RTTCAdd lhs rhs =>
      tAdd
        (instantiateRestrictedTargetTermContext replacement lhs)
        (instantiateRestrictedTargetTermContext replacement rhs)
  | RTTCMul lhs rhs =>
      tMul
        (instantiateRestrictedTargetTermContext replacement lhs)
        (instantiateRestrictedTargetTermContext replacement rhs)
  end.

Fixpoint instantiateRestrictedTargetFormulaContext
    (replacement : term) (context : RestrictedTargetFormulaContext)
    : formula :=
  match context with
  | RTFCFixed fixed => fixed
  | RTFCBot => pBot
  | RTFCEq lhs rhs =>
      pEq
        (instantiateRestrictedTargetTermContext replacement lhs)
        (instantiateRestrictedTargetTermContext replacement rhs)
  | RTFCImp lhs rhs =>
      pImp
        (instantiateRestrictedTargetFormulaContext replacement lhs)
        (instantiateRestrictedTargetFormulaContext replacement rhs)
  | RTFCAnd lhs rhs =>
      pAnd
        (instantiateRestrictedTargetFormulaContext replacement lhs)
        (instantiateRestrictedTargetFormulaContext replacement rhs)
  | RTFCOr lhs rhs =>
      pOr
        (instantiateRestrictedTargetFormulaContext replacement lhs)
        (instantiateRestrictedTargetFormulaContext replacement rhs)
  | RTFCAll child =>
      pAll (instantiateRestrictedTargetFormulaContext replacement child)
  | RTFCEx child =>
      pEx (instantiateRestrictedTargetFormulaContext replacement child)
  | RTFCSeal child =>
      Formula.sealPA
        (instantiateRestrictedTargetFormulaContext replacement child)
  end.

Fixpoint restrictedTargetTermContextBound
    (context : RestrictedTargetTermContext) : nat :=
  match context with
  | RTTCFixed fixed => Term.bound fixed
  | RTTCHole => 0
  | RTTCSucc child => restrictedTargetTermContextBound child
  | RTTCAdd lhs rhs
  | RTTCMul lhs rhs =>
      restrictedTargetTermContextBound lhs +
      restrictedTargetTermContextBound rhs
  end.

Fixpoint restrictedTargetFormulaContextBound
    (context : RestrictedTargetFormulaContext) : nat :=
  match context with
  | RTFCFixed fixed => Formula.bound fixed
  | RTFCBot => 0
  | RTFCEq lhs rhs =>
      restrictedTargetTermContextBound lhs +
      restrictedTargetTermContextBound rhs
  | RTFCImp lhs rhs
  | RTFCAnd lhs rhs
  | RTFCOr lhs rhs =>
      restrictedTargetFormulaContextBound lhs +
      restrictedTargetFormulaContextBound rhs
  | RTFCAll child
  | RTFCEx child
  | RTFCSeal child => restrictedTargetFormulaContextBound child
  end.

Lemma restrictedTargetTermContextBound_instance : forall replacement,
  Term.bound replacement = 0 -> forall context,
  Term.bound (instantiateRestrictedTargetTermContext replacement context) =
  restrictedTargetTermContextBound context.
Proof.
  intros replacement hclosed context.
  induction context; cbn
    [instantiateRestrictedTargetTermContext
      restrictedTargetTermContextBound Term.bound];
    try rewrite ?IHcontext, ?IHcontext1, ?IHcontext2;
    try reflexivity.
  exact hclosed.
Qed.

Lemma restrictedTarget_formula_bound_closeN : forall count phi,
  Formula.bound (Formula.closeN count phi) = Formula.bound phi.
Proof.
  induction count as [|count IH]; intro phi; cbn [Formula.closeN].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma restrictedTargetFormulaContextBound_instance : forall replacement,
  Term.bound replacement = 0 -> forall context,
  Formula.bound
    (instantiateRestrictedTargetFormulaContext replacement context) =
  restrictedTargetFormulaContextBound context.
Proof.
  intros replacement hclosed context.
  induction context; cbn
    [instantiateRestrictedTargetFormulaContext
      restrictedTargetFormulaContextBound Formula.bound];
    try rewrite ?IHcontext, ?IHcontext1, ?IHcontext2;
    try reflexivity.
  - now rewrite !restrictedTargetTermContextBound_instance.
  - unfold Formula.sealPA.
    rewrite restrictedTarget_formula_bound_closeN, IHcontext.
    reflexivity.
Qed.

Fixpoint rawRestrictedTargetCloseNFormulaCode (M : RawPAModel)
    (count : nat) (code : M) : M :=
  match count with
  | 0 => code
  | S count' =>
      rawRestrictedTargetCloseNFormulaCode M count'
        (rawFormulaAllCode M code)
  end.

Fixpoint rawRestrictedTargetTermContextCode (M : RawPAModel)
    (replacementCode : M) (context : RestrictedTargetTermContext) : M :=
  match context with
  | RTTCFixed fixed => rawQuotedTermCode M fixed
  | RTTCHole => replacementCode
  | RTTCSucc child =>
      rawTermSuccCode M
        (rawRestrictedTargetTermContextCode M replacementCode child)
  | RTTCAdd lhs rhs =>
      rawTermAddCode M
        (rawRestrictedTargetTermContextCode M replacementCode lhs)
        (rawRestrictedTargetTermContextCode M replacementCode rhs)
  | RTTCMul lhs rhs =>
      rawTermMulCode M
        (rawRestrictedTargetTermContextCode M replacementCode lhs)
        (rawRestrictedTargetTermContextCode M replacementCode rhs)
  end.

Fixpoint rawRestrictedTargetFormulaContextCode (M : RawPAModel)
    (replacementCode : M) (context : RestrictedTargetFormulaContext) : M :=
  match context with
  | RTFCFixed fixed => rawQuotedFormulaCode M fixed
  | RTFCBot => rawFormulaBotCode M
  | RTFCEq lhs rhs =>
      rawFormulaEqCode M
        (rawRestrictedTargetTermContextCode M replacementCode lhs)
        (rawRestrictedTargetTermContextCode M replacementCode rhs)
  | RTFCImp lhs rhs =>
      rawFormulaImpCode M
        (rawRestrictedTargetFormulaContextCode M replacementCode lhs)
        (rawRestrictedTargetFormulaContextCode M replacementCode rhs)
  | RTFCAnd lhs rhs =>
      rawFormulaAndCode M
        (rawRestrictedTargetFormulaContextCode M replacementCode lhs)
        (rawRestrictedTargetFormulaContextCode M replacementCode rhs)
  | RTFCOr lhs rhs =>
      rawFormulaOrCode M
        (rawRestrictedTargetFormulaContextCode M replacementCode lhs)
        (rawRestrictedTargetFormulaContextCode M replacementCode rhs)
  | RTFCAll child =>
      rawFormulaAllCode M
        (rawRestrictedTargetFormulaContextCode M replacementCode child)
  | RTFCEx child =>
      rawFormulaExCode M
        (rawRestrictedTargetFormulaContextCode M replacementCode child)
  | RTFCSeal child =>
      rawRestrictedTargetCloseNFormulaCode M
        (restrictedTargetFormulaContextBound child)
        (rawRestrictedTargetFormulaContextCode M replacementCode child)
  end.

Arguments rawRestrictedTargetTermContextCode
  M replacementCode context : clear implicits.
Arguments rawRestrictedTargetFormulaContextCode
  M replacementCode context : clear implicits.

Lemma rawRestrictedTargetCloseNFormulaCode_quoted : forall
    (M : RawPAModel) count phi,
  rawRestrictedTargetCloseNFormulaCode M count
    (rawQuotedFormulaCode M phi) =
  rawQuotedFormulaCode M (Formula.closeN count phi).
Proof.
  intros M count. induction count as [|count IH]; intro phi.
  - reflexivity.
  - cbn [rawRestrictedTargetCloseNFormulaCode Formula.closeN].
    change (rawRestrictedTargetCloseNFormulaCode M count
      (rawQuotedFormulaCode M (pAll phi)) =
      rawQuotedFormulaCode M (Formula.closeN count (pAll phi))).
    apply IH.
Qed.

Lemma rawRestrictedTargetTermContextCode_quoted : forall
    (M : RawPAModel) replacement context,
  rawRestrictedTargetTermContextCode M
    (rawQuotedTermCode M replacement) context =
  rawQuotedTermCode M
    (instantiateRestrictedTargetTermContext replacement context).
Proof.
  intros M replacement context. induction context; cbn
    [rawRestrictedTargetTermContextCode
      instantiateRestrictedTargetTermContext rawQuotedTermCode];
    now rewrite ?IHcontext, ?IHcontext1, ?IHcontext2.
Qed.

Lemma rawRestrictedTargetFormulaContextCode_quoted : forall
    (M : RawPAModel) replacement,
  Term.bound replacement = 0 -> forall context,
  rawRestrictedTargetFormulaContextCode M
    (rawQuotedTermCode M replacement) context =
  rawQuotedFormulaCode M
    (instantiateRestrictedTargetFormulaContext replacement context).
Proof.
  intros M replacement hclosed context. induction context; cbn
    [rawRestrictedTargetFormulaContextCode
      instantiateRestrictedTargetFormulaContext rawQuotedFormulaCode].
  - reflexivity.
  - reflexivity.
  - now rewrite !rawRestrictedTargetTermContextCode_quoted.
  - now rewrite IHcontext1, IHcontext2.
  - now rewrite IHcontext1, IHcontext2.
  - now rewrite IHcontext1, IHcontext2.
  - now rewrite IHcontext.
  - now rewrite IHcontext.
  - rewrite IHcontext.
    unfold Formula.sealPA.
    rewrite (restrictedTargetFormulaContextBound_instance
      replacement hclosed context).
    apply rawRestrictedTargetCloseNFormulaCode_quoted.
Qed.

Fixpoint restrictedTargetAllN
    (count : nat) (context : RestrictedTargetFormulaContext)
    : RestrictedTargetFormulaContext :=
  match count with
  | 0 => context
  | S count' => restrictedTargetAllN count' (RTFCAll context)
  end.

Fixpoint restrictedTargetExN
    (count : nat) (context : RestrictedTargetFormulaContext)
    : RestrictedTargetFormulaContext :=
  match count with
  | 0 => context
  | S count' => restrictedTargetExN count' (RTFCEx context)
  end.

Definition restrictedTargetLeContext (lhs : term)
    : RestrictedTargetFormulaContext :=
  RTFCEx
    (RTFCEq
      (RTTCFixed (tAdd (Term.rename S lhs) (tVar 0)))
      RTTCHole).

Lemma restrictedTargetLeContext_instance : forall level lhs,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetLeContext lhs) =
  Formula.leTermAt lhs (Term.numeral level).
Proof.
  intros level lhs.
  unfold restrictedTargetLeContext, Formula.leTermAt.
  cbn [instantiateRestrictedTargetFormulaContext
    instantiateRestrictedTargetTermContext].
  now rewrite Term.rename_numeral.
Qed.

Definition restrictedTargetSigmaDomainContext
    (code : term) : RestrictedTargetFormulaContext :=
  restrictedTargetExN 2
    (RTFCAnd
      (RTFCFixed
        (codedFormulaRankTermAt (liftTerm 2 code) (tVar 1) (tVar 0)))
      (restrictedTargetLeContext (tVar 1))).

Definition restrictedTargetPiDomainContext
    (code : term) : RestrictedTargetFormulaContext :=
  restrictedTargetExN 2
    (RTFCAnd
      (RTFCFixed
        (codedFormulaRankTermAt (liftTerm 2 code) (tVar 1) (tVar 0)))
      (restrictedTargetLeContext (tVar 0))).

Lemma restrictedTargetSigmaDomainContext_instance : forall level code,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetSigmaDomainContext code) =
  fixedLevelSigmaDomainTermAt level code.
Proof.
  intros level code.
  unfold restrictedTargetSigmaDomainContext,
    fixedLevelSigmaDomainTermAt, fixedLevelEx2.
  cbn [restrictedTargetExN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetLeContext_instance.
Qed.

Lemma restrictedTargetPiDomainContext_instance : forall level code,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetPiDomainContext code) =
  fixedLevelPiDomainTermAt level code.
Proof.
  intros level code.
  unfold restrictedTargetPiDomainContext,
    fixedLevelPiDomainTermAt, fixedLevelEx2.
  cbn [restrictedTargetExN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetLeContext_instance.
Qed.

Definition restrictedTargetFormulaQuantifierBoundedContext
    (code : term) : RestrictedTargetFormulaContext :=
  RTFCOr
    (restrictedTargetSigmaDomainContext code)
    (restrictedTargetPiDomainContext code).

Lemma restrictedTargetFormulaQuantifierBoundedContext_instance : forall
    level code,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetFormulaQuantifierBoundedContext code) =
  formulaQuantifierBoundedTermAt level code.
Proof.
  intros level code.
  unfold restrictedTargetFormulaQuantifierBoundedContext,
    formulaQuantifierBoundedTermAt.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetSigmaDomainContext_instance,
    restrictedTargetPiDomainContext_instance.
Qed.

Definition restrictedTargetContextAllBoundedWithTablesContext
    (bound headCode headStep : term) : RestrictedTargetFormulaContext :=
  RTFCAll
    (RTFCImp
      (RTFCFixed
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound)))
      (RTFCAll
        (RTFCImp
          (RTFCFixed
            (codedAssignmentLookupTermAt
              (liftTerm 2 headCode) (liftTerm 2 headStep)
              (tVar 1) (tVar 0)))
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 0))))).

Lemma restrictedTargetContextAllBoundedWithTablesContext_instance : forall
    level bound headCode headStep,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetContextAllBoundedWithTablesContext
      bound headCode headStep) =
  contextAllBoundedWithTablesTermAt level bound headCode headStep.
Proof.
  intros level bound headCode headStep.
  unfold restrictedTargetContextAllBoundedWithTablesContext,
    contextAllBoundedWithTablesTermAt.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetFormulaQuantifierBoundedContext_instance.
Qed.

Definition restrictedTargetContextAllBoundedContext
    (root : term) : RestrictedTargetFormulaContext :=
  restrictedTargetExN 5
    (RTFCAnd
      (RTFCFixed
        (contextListTraversalTermAt
          (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0)))
      (restrictedTargetContextAllBoundedWithTablesContext
        (tVar 4) (tVar 1) (tVar 0))).

Lemma restrictedTargetContextAllBoundedContext_instance : forall level root,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetContextAllBoundedContext root) =
  contextAllBoundedTermAt level root.
Proof.
  intros level root.
  unfold restrictedTargetContextAllBoundedContext,
    contextAllBoundedTermAt, contextListEx5.
  cbn [restrictedTargetExN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetContextAllBoundedWithTablesContext_instance.
Qed.

Fixpoint restrictedTargetProofFormulaFieldsBoundedContext
    (fields : list term) : RestrictedTargetFormulaContext :=
  match fields with
  | [] => RTFCFixed (pEq tZero tZero)
  | field :: tail =>
      RTFCAnd
        (restrictedTargetFormulaQuantifierBoundedContext field)
        (restrictedTargetProofFormulaFieldsBoundedContext tail)
  end.

Lemma restrictedTargetProofFormulaFieldsBoundedContext_instance : forall
    level fields,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofFormulaFieldsBoundedContext fields) =
  proofFormulaFieldsBoundedTermAt level fields.
Proof.
  intros level fields. induction fields as [|field tail IH].
  - reflexivity.
  - cbn [restrictedTargetProofFormulaFieldsBoundedContext
      proofFormulaFieldsBoundedTermAt
      instantiateRestrictedTargetFormulaContext].
    now rewrite restrictedTargetFormulaQuantifierBoundedContext_instance, IH.
Qed.

Fixpoint restrictedTargetProofOccurrenceCasesBoundedContext
    (code context : term) (cases : list (term * list term))
    : RestrictedTargetFormulaContext :=
  match cases with
  | [] => RTFCFixed (pEq tZero tZero)
  | (constructorCode, formulaFields) :: tail =>
      RTFCAnd
        (RTFCImp
          (RTFCFixed (pEq code constructorCode))
          (RTFCAnd
            (restrictedTargetContextAllBoundedContext context)
            (restrictedTargetProofFormulaFieldsBoundedContext
              formulaFields)))
        (restrictedTargetProofOccurrenceCasesBoundedContext
          code context tail)
  end.

Lemma restrictedTargetProofOccurrenceCasesBoundedContext_instance : forall
    level code context cases,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofOccurrenceCasesBoundedContext
      code context cases) =
  proofOccurrenceCasesBoundedTermAt level code context cases.
Proof.
  intros level code context cases.
  induction cases as [|[constructorCode formulaFields] tail IH].
  - reflexivity.
  - cbn [restrictedTargetProofOccurrenceCasesBoundedContext
      proofOccurrenceCasesBoundedTermAt
      instantiateRestrictedTargetFormulaContext].
    now rewrite restrictedTargetContextAllBoundedContext_instance,
      restrictedTargetProofFormulaFieldsBoundedContext_instance, IH.
Qed.

Definition restrictedTargetProofConstructorOccurrencesBoundedContext
    (code : term) : RestrictedTargetFormulaContext :=
  restrictedTargetAllN 8
    (restrictedTargetProofOccurrenceCasesBoundedContext
      (liftTerm 8 code) (tVar 7)
      (proofOccurrenceCasesTerms
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))).

Lemma restrictedTargetProofConstructorOccurrencesBoundedContext_instance :
  forall level code,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofConstructorOccurrencesBoundedContext code) =
  proofConstructorOccurrencesBoundedTermAt level code.
Proof.
  intros level code.
  unfold restrictedTargetProofConstructorOccurrencesBoundedContext,
    proofConstructorOccurrencesBoundedTermAt, restrictedProofAll8.
  cbn [restrictedTargetAllN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetProofOccurrenceCasesBoundedContext_instance.
Qed.

Definition restrictedTargetProofEndpointOccurrencesBoundedContext
    (code : term) : RestrictedTargetFormulaContext :=
  restrictedTargetAllN 2
    (RTFCImp
      (RTFCFixed
        (proofEndpointTermAt
          (liftTerm 2 code) (tVar 1) (tVar 0)))
      (RTFCAnd
        (restrictedTargetContextAllBoundedContext (tVar 1))
        (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)))).

Lemma restrictedTargetProofEndpointOccurrencesBoundedContext_instance :
  forall level code,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofEndpointOccurrencesBoundedContext code) =
  proofEndpointOccurrencesBoundedTermAt level code.
Proof.
  intros level code.
  unfold restrictedTargetProofEndpointOccurrencesBoundedContext,
    proofEndpointOccurrencesBoundedTermAt, restrictedProofAll2.
  cbn [restrictedTargetAllN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetContextAllBoundedContext_instance,
    restrictedTargetFormulaQuantifierBoundedContext_instance.
Qed.

Definition restrictedTargetProofNodeContext
    (code supportCode supportStep : term) : RestrictedTargetFormulaContext :=
  RTFCAnd
    (RTFCFixed (proofSyntaxStepTermAt code supportCode supportStep))
    (RTFCAnd
      (RTFCFixed (proofRuleEndpointExistsTermAt code))
      (RTFCAnd
        (restrictedTargetProofConstructorOccurrencesBoundedContext code)
        (restrictedTargetProofEndpointOccurrencesBoundedContext code))).

Lemma restrictedTargetProofNodeContext_instance : forall
    level code supportCode supportStep,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofNodeContext code supportCode supportStep) =
  restrictedProofNodeTermAt level code supportCode supportStep.
Proof.
  intros level code supportCode supportStep.
  unfold restrictedTargetProofNodeContext,
    restrictedProofNodeTermAt, restrictedProofAnd4.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite
    restrictedTargetProofConstructorOccurrencesBoundedContext_instance,
    restrictedTargetProofEndpointOccurrencesBoundedContext_instance.
Qed.

Definition restrictedTargetProofTraversalContext
    (bound supportCode supportStep : term) : RestrictedTargetFormulaContext :=
  RTFCAnd
    (RTFCFixed
      (codedAssignmentDefinedThroughTermAt supportCode supportStep bound))
    (RTFCAll
      (RTFCImp
        (RTFCFixed
          (Formula.ltTermAt (tVar 0) (liftTerm 1 bound)))
        (RTFCImp
          (RTFCFixed
            (proofCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0)))
          (restrictedTargetProofNodeContext
            (tVar 0) (liftTerm 1 supportCode) (liftTerm 1 supportStep))))).

Lemma restrictedTargetProofTraversalContext_instance : forall
    level bound supportCode supportStep,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofTraversalContext bound supportCode supportStep) =
  restrictedProofTraversalTermAt level bound supportCode supportStep.
Proof.
  intros level bound supportCode supportStep.
  unfold restrictedTargetProofTraversalContext,
    restrictedProofTraversalTermAt.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetProofNodeContext_instance.
Qed.

Definition restrictedTargetProofCertificateWithSupportContext
    (root supportCode supportStep : term) : RestrictedTargetFormulaContext :=
  RTFCAnd
    (restrictedTargetProofTraversalContext
      (tSucc root) supportCode supportStep)
    (RTFCFixed (proofCodeSupportedTermAt supportCode supportStep root)).

Lemma restrictedTargetProofCertificateWithSupportContext_instance : forall
    level root supportCode supportStep,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofCertificateWithSupportContext
      root supportCode supportStep) =
  restrictedProofCertificateWithSupportTermAt
    level root supportCode supportStep.
Proof.
  intros level root supportCode supportStep.
  unfold restrictedTargetProofCertificateWithSupportContext,
    restrictedProofCertificateWithSupportTermAt.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetProofTraversalContext_instance.
Qed.

Definition restrictedTargetProofContext
    (root : term) : RestrictedTargetFormulaContext :=
  restrictedTargetExN 2
    (restrictedTargetProofCertificateWithSupportContext
      (liftTerm 2 root) (tVar 1) (tVar 0)).

Lemma restrictedTargetProofContext_instance : forall level root,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetProofContext root) =
  restrictedProofTermAt level root.
Proof.
  intros level root.
  unfold restrictedTargetProofContext,
    restrictedProofTermAt, restrictedProofEx2.
  cbn [restrictedTargetExN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetProofCertificateWithSupportContext_instance.
Qed.

Definition restrictedTargetCodedRestrictedPAProofContext
    (certificate : term) : RestrictedTargetFormulaContext :=
  restrictedTargetExN 3
    (RTFCAnd
      (RTFCFixed
        (codeList3TermAt (liftTerm 3 certificate)
          (Term.numeral 0) (tVar 2) (tVar 1)))
      (RTFCAnd
        (RTFCFixed
          (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0)))
        (RTFCAnd
          (restrictedTargetProofContext (tVar 1))
          (RTFCAnd
            (RTFCFixed (proofAtomicallyAdequateTermAt (tVar 1)))
            (RTFCAnd
              (RTFCFixed (proofHasFormulaCoverageTermAt (tVar 1)))
              (RTFCAnd
                (RTFCFixed (proofRuleCoverageTermAt (tVar 1)))
                (RTFCFixed
                  (proofRuleValidTermAt (tVar 1) (tVar 0)
                    rawFormulaBotCodeTerm)))))))).

Lemma restrictedTargetCodedRestrictedPAProofContext_instance : forall
    level certificate,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    (restrictedTargetCodedRestrictedPAProofContext certificate) =
  codedRestrictedPAProofTermAt level certificate.
Proof.
  intros level certificate.
  unfold restrictedTargetCodedRestrictedPAProofContext,
    codedRestrictedPAProofTermAt, restrictedPAEx3, restrictedPAAnd7.
  cbn [restrictedTargetExN instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetProofContext_instance.
Qed.

Definition restrictedPAConsistencyBodyFormulaContext
    : RestrictedTargetFormulaContext :=
  RTFCAll
    (RTFCImp
      (restrictedTargetCodedRestrictedPAProofContext (tVar 0))
      RTFCBot).

Definition restrictedPAConsistencyFormulaContext
    : RestrictedTargetFormulaContext :=
  RTFCSeal restrictedPAConsistencyBodyFormulaContext.

Theorem restrictedPAConsistencyFormulaContext_instance_exact : forall level,
  instantiateRestrictedTargetFormulaContext (Term.numeral level)
    restrictedPAConsistencyFormulaContext =
  restrictedPAConsistencyFormula level.
Proof.
  intro level.
  unfold restrictedPAConsistencyFormulaContext,
    restrictedPAConsistencyBodyFormulaContext,
    restrictedPAConsistencyFormula,
    restrictedPAConsistencyBodyFormula.
  cbn [instantiateRestrictedTargetFormulaContext].
  now rewrite restrictedTargetCodedRestrictedPAProofContext_instance.
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
  exists numeralCode : M,
    RawNumeralTermCodeAt M level numeralCode /\
    output =
      rawRestrictedTargetFormulaContextCode M numeralCode
        restrictedPAConsistencyFormulaContext.

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
  destruct (raw_numeralTermCodeExists_all M hPA level)
    as [numeralCode hnumeral].
  exists (rawRestrictedTargetFormulaContextCode M numeralCode
    restrictedPAConsistencyFormulaContext), numeralCode.
  split; [exact hnumeral | reflexivity].
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

(** Agreement of two numeral-code traces at one carrier index.  The bound
    guard is part of the formula, rather than a meta-level side condition,
    so PA's own induction axiom can propagate the assertion across every
    (possibly nonstandard) index of an arbitrary model. *)
Definition RawNumeralTermCodeTablesAgreeAt (M : RawPAModel)
    (bound leftCode leftStep rightCode rightStep current : M) : Prop :=
  rawLe M current bound ->
  forall leftValue,
    RawCodedAssignmentLookup M
      leftCode leftStep current leftValue ->
  forall rightValue,
    RawCodedAssignmentLookup M
      rightCode rightStep current rightValue ->
    leftValue = rightValue.

Arguments RawNumeralTermCodeTablesAgreeAt
  M bound leftCode leftStep rightCode rightStep current : clear implicits.

(** Formula-level version of [RawNumeralTermCodeTablesAgreeAt].  Under the
    first universal binder [leftValue] is variable 0.  Under the second,
    [rightValue] is variable 0 and [leftValue] has shifted to variable 1;
    all six surrounding parameters are lifted past the new binders. *)
Definition numeralTermCodeTablesAgreeAtTermAt
    (bound leftCode leftStep rightCode rightStep current : term) : formula :=
  pImp
    (Formula.leTermAt current bound)
    (pAll
      (pImp
        (codedAssignmentLookupTermAt
          (numeralCodeLiftTerm 1 leftCode)
          (numeralCodeLiftTerm 1 leftStep)
          (numeralCodeLiftTerm 1 current) (tVar 0))
        (pAll
          (pImp
            (codedAssignmentLookupTermAt
              (numeralCodeLiftTerm 2 rightCode)
              (numeralCodeLiftTerm 2 rightStep)
              (numeralCodeLiftTerm 2 current) (tVar 0))
            (pEq (tVar 1) (tVar 0)))))).

Lemma raw_sat_numeralTermCodeTablesAgreeAtTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    bound leftCode leftStep rightCode rightStep current,
  raw_formula_sat M e
    (numeralTermCodeTablesAgreeAtTermAt
      bound leftCode leftStep rightCode rightStep current) <->
  RawNumeralTermCodeTablesAgreeAt M
    (raw_term_eval M e bound)
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep)
    (raw_term_eval M e current).
Proof.
  intros M e bound leftCode leftStep rightCode rightStep current.
  unfold numeralTermCodeTablesAgreeAtTermAt,
    RawNumeralTermCodeTablesAgreeAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_numeralCode_eval_liftTerm_one.
  repeat setoid_rewrite raw_numeralCode_eval_liftTerm_two.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_numeralTermCodeTablesAgreeAt_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound leftCode leftStep rightCode rightStep,
  RawNumeralTermCodeTrace M bound leftCode leftStep ->
  RawNumeralTermCodeTrace M bound rightCode rightStep ->
  RawNumeralTermCodeTablesAgreeAt M bound
    leftCode leftStep rightCode rightStep (raw_zero M).
Proof.
  intros M hPA bound leftCode leftStep rightCode rightStep
    [_ [hleftZero _]] [_ [hrightZero _]] _
    leftValue hleft rightValue hright.
  transitivity (rawTermZeroCode M).
  - exact (raw_codedAssignmentLookup_functional M hPA
      leftCode leftStep (raw_zero M)
      leftValue (rawTermZeroCode M) hleft hleftZero).
  - symmetry. exact (raw_codedAssignmentLookup_functional M hPA
      rightCode rightStep (raw_zero M)
      rightValue (rawTermZeroCode M) hright hrightZero).
Qed.

(** The successor argument reads the predecessor entries from both total
    traces, uses the induction hypothesis there, and transports equality
    through the common [tSucc]-code constructor. *)
Lemma raw_numeralTermCodeTablesAgreeAt_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound leftCode leftStep rightCode rightStep current,
  RawNumeralTermCodeTrace M bound leftCode leftStep ->
  RawNumeralTermCodeTrace M bound rightCode rightStep ->
  RawNumeralTermCodeTablesAgreeAt M bound
    leftCode leftStep rightCode rightStep current ->
  RawNumeralTermCodeTablesAgreeAt M bound
    leftCode leftStep rightCode rightStep (raw_succ M current).
Proof.
  intros M hPA bound leftCode leftStep rightCode rightStep current
    [hleftDefined [_ hleftRows]]
    [hrightDefined [_ hrightRows]] hcurrent
    hsuccBound leftNext hleftNext rightNext hrightNext.
  assert (hcurrentBound : rawLt M current bound).
  { exact (raw_rank_lt_of_succ_le M hPA current bound hsuccBound). }
  assert (hcurrentDefined :
      rawLt M current (raw_succ M bound)).
  {
    apply (raw_lt_succ_of_le M hPA current bound).
    exact (raw_lt_to_le M current bound hcurrentBound).
  }
  destruct (hleftDefined current hcurrentDefined)
    as [leftCurrent hleftCurrent].
  destruct (hrightDefined current hcurrentDefined)
    as [rightCurrent hrightCurrent].
  specialize (hleftRows current leftCurrent leftNext
    hcurrentBound hleftCurrent hleftNext).
  specialize (hrightRows current rightCurrent rightNext
    hcurrentBound hrightCurrent hrightNext).
  specialize (hcurrent
    (raw_lt_to_le M current bound hcurrentBound)
    leftCurrent hleftCurrent rightCurrent hrightCurrent).
  rewrite hleftRows, hrightRows, hcurrent.
  reflexivity.
Qed.

(** Functionality at nonstandard levels cannot be obtained by Rocq's
    induction on [nat].  We instantiate the induction axiom available in
    every raw PA model with the formula above, keeping the two beta tables
    and the common bound as parameters. *)
Theorem raw_numeralTermCodeAt_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawNumeralTermCodeAtFunctional M.
Proof.
  intros M hPA level first second
    (leftCode & leftStep & hleftTrace & hleftOutput)
    (rightCode & rightStep & hrightTrace & hrightOutput).
  set (parameterEnv :=
    scons M level
      (scons M leftCode (scons M leftStep
        (scons M rightCode (scons M rightStep
          (fun _ : nat => raw_zero M)))))).
  set (phi := numeralTermCodeTablesAgreeAtTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_numeralTermCodeTablesAgreeAtTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_numeralTermCodeTablesAgreeAt_zero M hPA
        level leftCode leftStep rightCode rightStep
        hleftTrace hrightTrace).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_numeralTermCodeTablesAgreeAtTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_numeralTermCodeTablesAgreeAtTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_numeralTermCodeTablesAgreeAt_succ M hPA
        level leftCode leftStep rightCode rightStep current
        hleftTrace hrightTrace hcurrent).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_numeralTermCodeTablesAgreeAtTermAt_iff M
      (scons M level parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
    (hall level)) as hagree.
  unfold parameterEnv in hagree.
  cbn [raw_term_eval scons] in hagree.
  exact (hagree (raw_le_refl_traversal M hPA level)
    first hleftOutput second hrightOutput).
Qed.

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

Theorem raw_restrictedPAConsistencyFormulaCodeAt_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level first second,
    RawRestrictedPAConsistencyFormulaCodeAt M level first ->
    RawRestrictedPAConsistencyFormulaCodeAt M level second ->
    first = second.
Proof.
  intros M hPA.
  apply raw_restrictedPAConsistencyFormulaCodeAt_functional_of_numeral.
  exact (raw_numeralTermCodeAt_functional M hPA).
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

Theorem raw_restrictedPAConsistencyFormulaCodeAt_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedPAConsistencyFormulaCodeAt M
    (rawNumeralValue M level)
    (rawNumeralValue M
      (formulaCode (restrictedPAConsistencyFormula level))).
Proof.
  intros M hPA level.
  unfold RawRestrictedPAConsistencyFormulaCodeAt.
  exists (rawQuotedTermCode M (Term.numeral level)). split.
  - exact (raw_numeralTermCodeAt_standard M hPA level).
  - assert (hbound : Term.bound (Term.numeral level) = 0).
    { induction level; cbn [Term.numeral Term.bound];
        [reflexivity | exact IHlevel]. }
    rewrite rawRestrictedTargetFormulaContextCode_quoted by exact hbound.
    rewrite restrictedPAConsistencyFormulaContext_instance_exact.
    symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

End PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
