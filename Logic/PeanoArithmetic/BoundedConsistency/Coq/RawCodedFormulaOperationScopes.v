(**
  Scope preservation for represented term and formula operations.

  The operation graphs are intentionally split into small opaque lemmas.
  This mirrors their beta-trace architecture and prevents kernel reduction
  from expanding the complete graph whenever a client only needs its free
  variable interface.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes.

Module PABoundedRawCodedFormulaOperationScopes.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.

Ltac operation_scope_term :=
  lazymatch goal with
  | |- StandardTermScoped _ (Term.numeral _) =>
      apply standardTermScoped_numeral
  | |- StandardTermScoped _ (tVar _) =>
      apply standardTermScoped_var; lia
  | |- StandardTermScoped _ tZero =>
      apply standardTermScoped_zero
  | |- StandardTermScoped _ (tSucc _) =>
      apply standardTermScoped_succ; operation_scope_term
  | |- StandardTermScoped _ (tAdd _ _) =>
      apply standardTermScoped_add; operation_scope_term
  | |- StandardTermScoped _ (tMul _ _) =>
      apply standardTermScoped_mul; operation_scope_term
  | H : StandardTermScoped ?sourceScope ?input |-
      StandardTermScoped ?targetScope (liftTerm ?binderCount ?input) =>
      eapply standardTermScoped_weaken;
        [exact (standardTermScoped_lift sourceScope binderCount input H)
        | lia]
  | |- StandardTermScoped _ (liftTerm _ _) =>
      eapply standardTermScoped_weaken;
        [apply standardTermScoped_lift; operation_scope_term | lia]
  | |- StandardTermScoped _ (nodeTerm _ _) =>
      apply standardTermScoped_nodeTerm; operation_scope_term
  | |- StandardTermScoped _ (codeList1Term _) =>
      apply standardTermScoped_codeList1Term; operation_scope_term
  | |- StandardTermScoped _ (codeList2Term _ _) =>
      apply standardTermScoped_codeList2Term; operation_scope_term
  | |- StandardTermScoped _ (codeList3Term _ _ _) =>
      apply standardTermScoped_codeList3Term; operation_scope_term
  | |- _ => assumption
  end.

Ltac operation_scope_formula :=
  lazymatch goal with
  | |- StandardFormulaScoped _ pBot =>
      apply standardFormulaScoped_bot
  | |- StandardFormulaScoped _ (pEq _ _) =>
      apply standardFormulaScoped_eq; operation_scope_term
  | |- StandardFormulaScoped _ (pImp _ _) =>
      apply standardFormulaScoped_imp; operation_scope_formula
  | |- StandardFormulaScoped _ (pAnd _ _) =>
      apply standardFormulaScoped_and; operation_scope_formula
  | |- StandardFormulaScoped _ (pOr _ _) =>
      apply standardFormulaScoped_or; operation_scope_formula
  | |- StandardFormulaScoped _ (pAll _) =>
      apply standardFormulaScoped_all; operation_scope_formula
  | |- StandardFormulaScoped _ (pEx _) =>
      apply standardFormulaScoped_ex; operation_scope_formula
  | |- StandardFormulaScoped _ (Formula.ltTermAt _ _) =>
      apply standardFormulaScoped_ltTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (Formula.leTermAt _ _) =>
      apply standardFormulaScoped_leTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (codedAssignmentLookupTermAt _ _ _ _) =>
      apply standardFormulaScoped_codedAssignmentLookupTermAt;
        operation_scope_term
  | |- StandardFormulaScoped _
        (codedAssignmentDefinedThroughTermAt _ _ _) =>
      apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
        operation_scope_term
  | |- StandardFormulaScoped _ (termVarCodeTermAt _ _) =>
      apply standardFormulaScoped_termVarCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (termZeroCodeTermAt _) =>
      apply standardFormulaScoped_termZeroCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (termSuccCodeTermAt _ _) =>
      apply standardFormulaScoped_termSuccCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (termAddCodeTermAt _ _ _) =>
      apply standardFormulaScoped_termAddCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (termMulCodeTermAt _ _ _) =>
      apply standardFormulaScoped_termMulCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaBotCodeTermAt _) =>
      apply standardFormulaScoped_formulaBotCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaEqCodeTermAt _ _ _) =>
      apply standardFormulaScoped_formulaEqCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaImpCodeTermAt _ _ _) =>
      apply standardFormulaScoped_formulaImpCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaAndCodeTermAt _ _ _) =>
      apply standardFormulaScoped_formulaAndCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaOrCodeTermAt _ _ _) =>
      apply standardFormulaScoped_formulaOrCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaAllCodeTermAt _ _) =>
      apply standardFormulaScoped_formulaAllCodeTermAt; operation_scope_term
  | |- StandardFormulaScoped _ (formulaExCodeTermAt _ _) =>
      apply standardFormulaScoped_formulaExCodeTermAt; operation_scope_term
  | |- _ => assumption
  end.

Lemma standardFormulaScoped_codedFormulaNegationTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaNegationTermAt input output).
Proof.
  intros. unfold codedFormulaNegationTermAt, rawFormulaBotCodeTerm.
  operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedUniversalClosureRowsTermAt : forall scope
    code step count,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope count ->
  StandardFormulaScoped scope
    (codedUniversalClosureRowsTermAt code step count).
Proof.
  intros scope code step count hcode hstep hcount.
  unfold codedUniversalClosureRowsTermAt.
  repeat apply standardFormulaScoped_all.
  repeat apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 count hcount).
  - apply standardFormulaScoped_codedAssignmentLookupTermAt.
    + exact (standardTermScoped_lift scope 3 code hcode).
    + exact (standardTermScoped_lift scope 3 step hstep).
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedAssignmentLookupTermAt.
    + exact (standardTermScoped_lift scope 3 code hcode).
    + exact (standardTermScoped_lift scope 3 step hstep).
    + apply standardTermScoped_succ.
      apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_formulaAllCodeTermAt;
      apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedUniversalClosureTraceTermAt : forall scope
    code step count input output,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope count ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedUniversalClosureTraceTermAt code step count input output).
Proof.
  intros. unfold codedUniversalClosureTraceTermAt, operationAnd5.
  repeat apply standardFormulaScoped_and.
  - operation_scope_formula.
  - operation_scope_formula.
  - operation_scope_formula.
  - apply standardFormulaScoped_codedUniversalClosureRowsTermAt;
      assumption.
  - operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedUniversalClosureTermAt : forall scope
    count input output,
  StandardTermScoped scope count ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedUniversalClosureTermAt count input output).
Proof.
  intros scope count input output hcount hinput houtput.
  unfold codedUniversalClosureTermAt, operationEx2.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedUniversalClosureTraceTermAt.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 2 count hcount).
  - exact (standardTermScoped_lift scope 2 input hinput).
  - exact (standardTermScoped_lift scope 2 output houtput).
Qed.

Lemma standardFormulaScoped_codedTermOperationPairLookupTermAt : forall scope
    sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOperationPairLookupTermAt sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros. unfold codedTermOperationPairLookupTermAt.
  operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedShiftedIndexTermAt : forall scope
    cutoff amount inputIndex outputIndex,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope inputIndex ->
  StandardTermScoped scope outputIndex ->
  StandardFormulaScoped scope
    (codedShiftedIndexTermAt cutoff amount inputIndex outputIndex).
Proof.
  intros. unfold codedShiftedIndexTermAt.
  operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedTermShiftVariableRowTermAt : forall scope
    cutoff amount input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermShiftVariableRowTermAt cutoff amount input output).
Proof.
  intros scope cutoff amount input output
    hcutoff hamount hinput houtput.
  unfold codedTermShiftVariableRowTermAt,
    operationEx2, operationAnd3.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_termVarCodeTermAt.
    + exact (standardTermScoped_lift scope 2 input hinput).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_termVarCodeTermAt.
      * exact (standardTermScoped_lift scope 2 output houtput).
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedShiftedIndexTermAt.
      * exact (standardTermScoped_lift scope 2 cutoff hcutoff).
      * exact (standardTermScoped_lift scope 2 amount hamount).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermOpeningVariableRowTermAt : forall scope
    cutoff liftedReplacement input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope liftedReplacement ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOpeningVariableRowTermAt
      cutoff liftedReplacement input output).
Proof.
  intros scope cutoff liftedReplacement input output
    hcutoff hreplacement hinput houtput.
  unfold codedTermOpeningVariableRowTermAt,
    operationAnd3.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_termVarCodeTermAt.
    + exact (standardTermScoped_lift scope 1 input hinput).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_or.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_ltTermAt.
        -- apply standardTermScoped_var; lia.
        -- exact (standardTermScoped_lift scope 1 cutoff hcutoff).
      * apply standardFormulaScoped_termVarCodeTermAt.
        -- exact (standardTermScoped_lift scope 1 output houtput).
        -- apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_or.
      * apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_eq.
           ++ apply standardTermScoped_var; lia.
           ++ exact (standardTermScoped_lift scope 1 cutoff hcutoff).
        -- apply standardFormulaScoped_eq.
           ++ exact (standardTermScoped_lift scope 1 output houtput).
           ++ exact (standardTermScoped_lift
                scope 1 liftedReplacement hreplacement).
      * apply standardFormulaScoped_ex.
        apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_eq.
           ++ apply standardTermScoped_lift.
              apply standardTermScoped_var; lia.
           ++ apply standardTermScoped_succ.
              apply standardTermScoped_var; lia.
        -- apply standardFormulaScoped_and.
           ++ apply standardFormulaScoped_ltTermAt.
              ** exact (standardTermScoped_lift (1 + scope) 1
                   (liftTerm 1 cutoff)
                   (standardTermScoped_lift scope 1 cutoff hcutoff)).
              ** apply standardTermScoped_lift.
                 apply standardTermScoped_var; lia.
           ++ apply standardFormulaScoped_termVarCodeTermAt.
              ** exact (standardTermScoped_lift (1 + scope) 1
                   (liftTerm 1 output)
                   (standardTermScoped_lift scope 1 output houtput)).
              ** apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermZeroOperationRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermZeroOperationRowTermAt input output).
Proof.
  intros. unfold codedTermZeroOperationRowTermAt.
  operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedTermSuccOperationRowTermAt : forall scope
    sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermSuccOperationRowTermAt sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep index input output
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermSuccOperationRowTermAt,
    operationEx3, operationAnd4.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 index hindex).
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_termSuccCodeTermAt.
        -- exact (standardTermScoped_lift scope 3 input hinput).
        -- apply standardTermScoped_var; lia.
      * apply standardFormulaScoped_termSuccCodeTermAt.
        -- exact (standardTermScoped_lift scope 3 output houtput).
        -- apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermBinaryOperationRowTermAt : forall
    (constructor : term -> term -> term -> formula),
  (forall scope code lhs rhs,
    StandardTermScoped scope code ->
    StandardTermScoped scope lhs ->
    StandardTermScoped scope rhs ->
    StandardFormulaScoped scope (constructor code lhs rhs)) ->
  forall scope sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermBinaryOperationRowTermAt constructor sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep index input output
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermBinaryOperationRowTermAt,
    operationEx6, operationAnd6.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 6 index hindex).
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 6 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 6 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 6 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 6 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_ltTermAt.
        -- apply standardTermScoped_var; lia.
        -- exact (standardTermScoped_lift scope 6 index hindex).
      * apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
           ++ exact (standardTermScoped_lift
                scope 6 sourceCode hsourceCode).
           ++ exact (standardTermScoped_lift
                scope 6 sourceStep hsourceStep).
           ++ exact (standardTermScoped_lift
                scope 6 targetCode htargetCode).
           ++ exact (standardTermScoped_lift
                scope 6 targetStep htargetStep).
           ++ apply standardTermScoped_var; lia.
           ++ apply standardTermScoped_var; lia.
           ++ apply standardTermScoped_var; lia.
        -- apply standardFormulaScoped_and.
           ++ apply hconstructor.
              ** exact (standardTermScoped_lift scope 6 input hinput).
              ** apply standardTermScoped_var; lia.
              ** apply standardTermScoped_var; lia.
           ++ apply hconstructor.
              ** exact (standardTermScoped_lift scope 6 output houtput).
              ** apply standardTermScoped_var; lia.
              ** apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermOperationTraversalRowTermAt : forall
    (variableRow : term -> term -> formula)
    scope sourceCode sourceStep targetCode targetStep index input output,
  StandardFormulaScoped scope (variableRow input output) ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOperationTraversalRowTermAt variableRow sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros variableRow scope sourceCode sourceStep targetCode targetStep
    index input output hvariable
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermOperationTraversalRowTermAt.
  apply standardFormulaScoped_or.
  - exact hvariable.
  - apply standardFormulaScoped_or.
    + exact (standardFormulaScoped_codedTermZeroOperationRowTermAt
        scope input output hinput houtput).
    + apply standardFormulaScoped_or.
      * apply standardFormulaScoped_codedTermSuccOperationRowTermAt;
          assumption.
      * apply standardFormulaScoped_or.
        -- exact (standardFormulaScoped_codedTermBinaryOperationRowTermAt
             termAddCodeTermAt standardFormulaScoped_termAddCodeTermAt
             scope sourceCode sourceStep targetCode targetStep index
             input output hsourceCode hsourceStep htargetCode htargetStep
             hindex hinput houtput).
        -- exact (standardFormulaScoped_codedTermBinaryOperationRowTermAt
             termMulCodeTermAt standardFormulaScoped_termMulCodeTermAt
             scope sourceCode sourceStep targetCode targetStep index
             input output hsourceCode hsourceStep htargetCode htargetStep
             hindex hinput houtput).
Qed.

Lemma standardFormulaScoped_codedTermShiftTraversalRowTermAt : forall scope
    cutoff amount sourceCode sourceStep targetCode targetStep
    index input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermShiftTraversalRowTermAt cutoff amount sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros scope cutoff amount sourceCode sourceStep targetCode targetStep
    index input output hcutoff hamount hsourceCode hsourceStep
    htargetCode htargetStep hindex hinput houtput.
  unfold codedTermShiftTraversalRowTermAt.
  apply standardFormulaScoped_codedTermOperationTraversalRowTermAt.
  - exact (standardFormulaScoped_codedTermShiftVariableRowTermAt
      scope cutoff amount input output hcutoff hamount hinput houtput).
  - exact hsourceCode.
  - exact hsourceStep.
  - exact htargetCode.
  - exact htargetStep.
  - exact hindex.
  - exact hinput.
  - exact houtput.
Qed.

Lemma standardFormulaScoped_codedTermOpeningTraversalRowTermAt : forall scope
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    index input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope liftedReplacement ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOpeningTraversalRowTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep index input output).
Proof.
  intros scope cutoff liftedReplacement sourceCode sourceStep targetCode
    targetStep index input output hcutoff hreplacement hsourceCode
    hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermOpeningTraversalRowTermAt.
  apply standardFormulaScoped_codedTermOperationTraversalRowTermAt.
  - exact (standardFormulaScoped_codedTermOpeningVariableRowTermAt
      scope cutoff liftedReplacement input output
      hcutoff hreplacement hinput houtput).
  - exact hsourceCode.
  - exact hsourceStep.
  - exact htargetCode.
  - exact htargetStep.
  - exact hindex.
  - exact hinput.
  - exact houtput.
Qed.

Lemma standardFormulaScoped_codedTermOperationRowsTermAt : forall
    (row : term -> term -> term -> formula),
  (forall scope index input output,
    StandardTermScoped scope index ->
    StandardTermScoped scope input ->
    StandardTermScoped scope output ->
    StandardFormulaScoped scope (row index input output)) ->
  forall scope sourceCode sourceStep targetCode targetStep bound,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (codedTermOperationRowsTermAt row
      sourceCode sourceStep targetCode targetStep bound).
Proof.
  intros row hrow scope sourceCode sourceStep targetCode targetStep bound
    hsourceCode hsourceStep htargetCode htargetStep hbound.
  unfold codedTermOperationRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply hrow;
        apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermShiftRowsTermAt : forall scope
    cutoff amount sourceCode sourceStep targetCode targetStep bound,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (codedTermShiftRowsTermAt cutoff amount sourceCode sourceStep
      targetCode targetStep bound).
Proof.
  intros scope cutoff amount sourceCode sourceStep targetCode targetStep
    bound hcutoff hamount hsourceCode hsourceStep htargetCode htargetStep
    hbound.
  unfold codedTermShiftRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedTermShiftTraversalRowTermAt.
      * exact (standardTermScoped_lift scope 3 cutoff hcutoff).
      * exact (standardTermScoped_lift scope 3 amount hamount).
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermOpeningRowsTermAt : forall scope
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep bound,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope liftedReplacement ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (codedTermOpeningRowsTermAt cutoff liftedReplacement sourceCode
      sourceStep targetCode targetStep bound).
Proof.
  intros scope cutoff liftedReplacement sourceCode sourceStep targetCode
    targetStep bound hcutoff hreplacement hsourceCode hsourceStep
    htargetCode htargetStep hbound.
  unfold codedTermOpeningRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedTermOpeningTraversalRowTermAt.
      * exact (standardTermScoped_lift scope 3 cutoff hcutoff).
      * exact (standardTermScoped_lift
          scope 3 liftedReplacement hreplacement).
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermShiftTraceTermAt : forall scope
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope rootIndex ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermShiftTraceTermAt cutoff amount sourceCode sourceStep
      targetCode targetStep bound rootIndex input output).
Proof.
  intros scope cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output hcutoff hamount hsourceCode hsourceStep
    htargetCode htargetStep hbound hrootIndex hinput houtput.
  unfold codedTermShiftTraceTermAt, operationAnd6.
  apply standardFormulaScoped_and.
  - operation_scope_formula.
  - apply standardFormulaScoped_and.
    + operation_scope_formula.
    + apply standardFormulaScoped_and.
      * operation_scope_formula.
      * apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_codedTermOperationPairLookupTermAt;
             assumption.
        -- apply standardFormulaScoped_and.
           ++ apply standardFormulaScoped_codedTermShiftRowsTermAt;
                assumption.
           ++ operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedTermOpeningTraceTermAt : forall scope
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope liftedReplacement ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope rootIndex ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOpeningTraceTermAt cutoff liftedReplacement sourceCode
      sourceStep targetCode targetStep bound rootIndex input output).
Proof.
  intros scope cutoff liftedReplacement sourceCode sourceStep targetCode
    targetStep bound rootIndex input output hcutoff hreplacement
    hsourceCode hsourceStep htargetCode htargetStep hbound hrootIndex
    hinput houtput.
  unfold codedTermOpeningTraceTermAt, operationAnd5.
  apply standardFormulaScoped_and.
  - operation_scope_formula.
  - apply standardFormulaScoped_and.
    + operation_scope_formula.
    + apply standardFormulaScoped_and.
      * operation_scope_formula.
      * apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_codedTermOperationPairLookupTermAt;
             assumption.
        -- apply standardFormulaScoped_codedTermOpeningRowsTermAt;
             assumption.
Qed.

Lemma standardFormulaScoped_codedTermShiftTermAt : forall scope
    cutoff amount input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermShiftTermAt cutoff amount input output).
Proof.
  intros scope cutoff amount input output hcutoff hamount hinput houtput.
  unfold codedTermShiftTermAt, operationEx6.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedTermShiftTraceTermAt.
  - exact (standardTermScoped_lift scope 6 cutoff hcutoff).
  - exact (standardTermScoped_lift scope 6 amount hamount).
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 6 input hinput).
  - exact (standardTermScoped_lift scope 6 output houtput).
Qed.

Lemma standardFormulaScoped_codedTermOpeningTermAt : forall scope
    cutoff liftedReplacement input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope liftedReplacement ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermOpeningTermAt cutoff liftedReplacement input output).
Proof.
  intros scope cutoff liftedReplacement input output
    hcutoff hreplacement hinput houtput.
  unfold codedTermOpeningTermAt, operationEx6.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedTermOpeningTraceTermAt.
  - exact (standardTermScoped_lift scope 6 cutoff hcutoff).
  - exact (standardTermScoped_lift
      scope 6 liftedReplacement hreplacement).
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 6 input hinput).
  - exact (standardTermScoped_lift scope 6 output houtput).
Qed.

(** The atomic equality operation is the only higher-order argument in a
    represented formula traversal. *)
Definition StandardFormulaOperationAtomScoped
    (atom : term -> term -> term -> term -> formula) : Prop :=
  forall scope parameter depth input output,
    StandardTermScoped scope parameter ->
    StandardTermScoped scope depth ->
    StandardTermScoped scope input ->
    StandardTermScoped scope output ->
    StandardFormulaScoped scope (atom parameter depth input output).

Lemma standardFormulaScoped_codedFormulaOperationTripleLookupTermAt :
    forall scope sourceCode sourceStep targetCode targetStep
      depthCode depthStep index input output depth,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardTermScoped scope depth ->
  StandardFormulaScoped scope
    (codedFormulaOperationTripleLookupTermAt sourceCode sourceStep
      targetCode targetStep depthCode depthStep index input output depth).
Proof.
  intros. unfold codedFormulaOperationTripleLookupTermAt.
  apply standardFormulaScoped_and.
  - operation_scope_formula.
  - apply standardFormulaScoped_and; operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedFormulaEqOperationRowTermAt : forall atom,
  StandardFormulaOperationAtomScoped atom ->
  forall scope parameter depth input output,
  StandardTermScoped scope parameter ->
  StandardTermScoped scope depth ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaEqOperationRowTermAt atom parameter depth input output).
Proof.
  intros atom hatom scope parameter depth input output
    hparameter hdepth hinput houtput.
  unfold codedFormulaEqOperationRowTermAt, operationEx4, operationAnd4.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_formulaEqCodeTermAt.
    + exact (standardTermScoped_lift scope 4 input hinput).
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_formulaEqCodeTermAt.
      * exact (standardTermScoped_lift scope 4 output houtput).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply hatom.
        -- exact (standardTermScoped_lift scope 4 parameter hparameter).
        -- exact (standardTermScoped_lift scope 4 depth hdepth).
        -- apply standardTermScoped_var; lia.
        -- apply standardTermScoped_var; lia.
      * apply hatom.
        -- exact (standardTermScoped_lift scope 4 parameter hparameter).
        -- exact (standardTermScoped_lift scope 4 depth hdepth).
        -- apply standardTermScoped_var; lia.
        -- apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaBotOperationRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaBotOperationRowTermAt input output).
Proof.
  intros. unfold codedFormulaBotOperationRowTermAt.
  operation_scope_formula.
Qed.

Lemma standardFormulaScoped_codedFormulaBinaryOperationRowTermAt : forall
    (constructor : term -> term -> term -> formula),
  (forall scope code lhs rhs,
    StandardTermScoped scope code ->
    StandardTermScoped scope lhs ->
    StandardTermScoped scope rhs ->
    StandardFormulaScoped scope (constructor code lhs rhs)) ->
  forall scope sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardTermScoped scope depth ->
  StandardFormulaScoped scope
    (codedFormulaBinaryOperationRowTermAt constructor sourceCode sourceStep
      targetCode targetStep depthCode depthStep index input output depth).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep depthCode depthStep index input output depth
    hsourceCode hsourceStep htargetCode htargetStep hdepthCode hdepthStep
    hindex hinput houtput hdepth.
  unfold codedFormulaBinaryOperationRowTermAt, operationAnd8.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 8 index hindex).
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedFormulaOperationTripleLookupTermAt.
      * exact (standardTermScoped_lift scope 8 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 8 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 8 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 8 targetStep htargetStep).
      * exact (standardTermScoped_lift scope 8 depthCode hdepthCode).
      * exact (standardTermScoped_lift scope 8 depthStep hdepthStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_eq.
        -- apply standardTermScoped_var; lia.
        -- exact (standardTermScoped_lift scope 8 depth hdepth).
      * apply standardFormulaScoped_and.
        -- apply standardFormulaScoped_ltTermAt.
           ++ apply standardTermScoped_var; lia.
           ++ exact (standardTermScoped_lift scope 8 index hindex).
        -- apply standardFormulaScoped_and.
           ++ apply standardFormulaScoped_codedFormulaOperationTripleLookupTermAt.
              ** exact (standardTermScoped_lift
                   scope 8 sourceCode hsourceCode).
              ** exact (standardTermScoped_lift
                   scope 8 sourceStep hsourceStep).
              ** exact (standardTermScoped_lift
                   scope 8 targetCode htargetCode).
              ** exact (standardTermScoped_lift
                   scope 8 targetStep htargetStep).
              ** exact (standardTermScoped_lift
                   scope 8 depthCode hdepthCode).
              ** exact (standardTermScoped_lift
                   scope 8 depthStep hdepthStep).
              ** apply standardTermScoped_var; lia.
              ** apply standardTermScoped_var; lia.
              ** apply standardTermScoped_var; lia.
              ** apply standardTermScoped_var; lia.
           ++ apply standardFormulaScoped_and.
              ** apply standardFormulaScoped_eq.
                 --- apply standardTermScoped_var; lia.
                 --- exact (standardTermScoped_lift scope 8 depth hdepth).
              ** apply standardFormulaScoped_and.
                 --- apply hconstructor.
                     +++ exact (standardTermScoped_lift
                          scope 8 input hinput).
                     +++ apply standardTermScoped_var; lia.
                     +++ apply standardTermScoped_var; lia.
                 --- apply hconstructor.
                     +++ exact (standardTermScoped_lift
                          scope 8 output houtput).
                     +++ apply standardTermScoped_var; lia.
                     +++ apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaUnaryOperationRowTermAt : forall
    (constructor : term -> term -> formula),
  (forall scope code child,
    StandardTermScoped scope code ->
    StandardTermScoped scope child ->
    StandardFormulaScoped scope (constructor code child)) ->
  forall scope sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardTermScoped scope depth ->
  StandardFormulaScoped scope
    (codedFormulaUnaryOperationRowTermAt constructor sourceCode sourceStep
      targetCode targetStep depthCode depthStep index input output depth).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep depthCode depthStep index input output depth
    hsourceCode hsourceStep htargetCode htargetStep hdepthCode hdepthStep
    hindex hinput houtput hdepth.
  unfold codedFormulaUnaryOperationRowTermAt, operationEx4, operationAnd5.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 4 index hindex).
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedFormulaOperationTripleLookupTermAt.
      * exact (standardTermScoped_lift scope 4 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 4 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 4 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 4 targetStep htargetStep).
      * exact (standardTermScoped_lift scope 4 depthCode hdepthCode).
      * exact (standardTermScoped_lift scope 4 depthStep hdepthStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_eq.
        -- apply standardTermScoped_var; lia.
        -- apply standardTermScoped_succ.
           exact (standardTermScoped_lift scope 4 depth hdepth).
      * apply standardFormulaScoped_and.
        -- apply hconstructor.
           ++ exact (standardTermScoped_lift scope 4 input hinput).
           ++ apply standardTermScoped_var; lia.
        -- apply hconstructor.
           ++ exact (standardTermScoped_lift scope 4 output houtput).
           ++ apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaOperationTraversalRowTermAt :
    forall atom,
  StandardFormulaOperationAtomScoped atom ->
  forall scope parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth,
  StandardTermScoped scope parameter ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardTermScoped scope depth ->
  StandardFormulaScoped scope
    (codedFormulaOperationTraversalRowTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth).
Proof.
  intros atom hatom scope parameter sourceCode sourceStep targetCode
    targetStep depthCode depthStep index input output depth hparameter
    hsourceCode hsourceStep htargetCode htargetStep hdepthCode hdepthStep
    hindex hinput houtput hdepth.
  unfold codedFormulaOperationTraversalRowTermAt.
  apply standardFormulaScoped_or.
  - exact (standardFormulaScoped_codedFormulaEqOperationRowTermAt
      atom hatom scope parameter depth input output
      hparameter hdepth hinput houtput).
  - apply standardFormulaScoped_or.
    + exact (standardFormulaScoped_codedFormulaBotOperationRowTermAt
        scope input output hinput houtput).
    + apply standardFormulaScoped_or.
      * exact (standardFormulaScoped_codedFormulaBinaryOperationRowTermAt
          formulaImpCodeTermAt standardFormulaScoped_formulaImpCodeTermAt
          scope sourceCode sourceStep targetCode targetStep depthCode
          depthStep index input output depth hsourceCode hsourceStep
          htargetCode htargetStep hdepthCode hdepthStep hindex hinput
          houtput hdepth).
      * apply standardFormulaScoped_or.
        -- exact (standardFormulaScoped_codedFormulaBinaryOperationRowTermAt
             formulaAndCodeTermAt
             standardFormulaScoped_formulaAndCodeTermAt
             scope sourceCode sourceStep targetCode targetStep depthCode
             depthStep index input output depth hsourceCode hsourceStep
             htargetCode htargetStep hdepthCode hdepthStep hindex hinput
             houtput hdepth).
        -- apply standardFormulaScoped_or.
           ++ exact (standardFormulaScoped_codedFormulaBinaryOperationRowTermAt
                formulaOrCodeTermAt
                standardFormulaScoped_formulaOrCodeTermAt
                scope sourceCode sourceStep targetCode targetStep depthCode
                depthStep index input output depth hsourceCode hsourceStep
                htargetCode htargetStep hdepthCode hdepthStep hindex hinput
                houtput hdepth).
           ++ apply standardFormulaScoped_or.
              ** exact (standardFormulaScoped_codedFormulaUnaryOperationRowTermAt
                   formulaAllCodeTermAt
                   standardFormulaScoped_formulaAllCodeTermAt
                   scope sourceCode sourceStep targetCode targetStep
                   depthCode depthStep index input output depth
                   hsourceCode hsourceStep htargetCode htargetStep
                   hdepthCode hdepthStep hindex hinput houtput hdepth).
              ** exact (standardFormulaScoped_codedFormulaUnaryOperationRowTermAt
                   formulaExCodeTermAt
                   standardFormulaScoped_formulaExCodeTermAt
                   scope sourceCode sourceStep targetCode targetStep
                   depthCode depthStep index input output depth
                   hsourceCode hsourceStep htargetCode htargetStep
                   hdepthCode hdepthStep hindex hinput houtput hdepth).
Qed.

Lemma standardFormulaScoped_codedFormulaShiftAtomTermAt :
  StandardFormulaOperationAtomScoped codedFormulaShiftAtomTermAt.
Proof.
  intros scope amount depth input output
    hamount hdepth hinput houtput.
  unfold codedFormulaShiftAtomTermAt.
  exact (standardFormulaScoped_codedTermShiftTermAt
    scope depth amount input output hdepth hamount hinput houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaSubstitutionAtomTermAt :
  StandardFormulaOperationAtomScoped codedFormulaSubstitutionAtomTermAt.
Proof.
  intros scope replacement depth input output
    hreplacement hdepth hinput houtput.
  unfold codedFormulaSubstitutionAtomTermAt.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedTermShiftTermAt.
    + apply standardTermScoped_zero.
    + exact (standardTermScoped_lift scope 1 depth hdepth).
    + exact (standardTermScoped_lift scope 1 replacement hreplacement).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_codedTermOpeningTermAt.
    + exact (standardTermScoped_lift scope 1 depth hdepth).
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 1 input hinput).
    + exact (standardTermScoped_lift scope 1 output houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaOperationRowsTermAt : forall atom,
  StandardFormulaOperationAtomScoped atom ->
  forall scope parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound,
  StandardTermScoped scope parameter ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (codedFormulaOperationRowsTermAt atom parameter sourceCode sourceStep
      targetCode targetStep depthCode depthStep bound).
Proof.
  intros atom hatom scope parameter sourceCode sourceStep targetCode
    targetStep depthCode depthStep bound hparameter hsourceCode hsourceStep
    htargetCode htargetStep hdepthCode hdepthStep hbound.
  unfold codedFormulaOperationRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 4 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedFormulaOperationTripleLookupTermAt.
      * exact (standardTermScoped_lift scope 4 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 4 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 4 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 4 targetStep htargetStep).
      * exact (standardTermScoped_lift scope 4 depthCode hdepthCode).
      * exact (standardTermScoped_lift scope 4 depthStep hdepthStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedFormulaOperationTraversalRowTermAt
        with (atom := atom).
      * exact hatom.
      * exact (standardTermScoped_lift scope 4 parameter hparameter).
      * exact (standardTermScoped_lift scope 4 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 4 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 4 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 4 targetStep htargetStep).
      * exact (standardTermScoped_lift scope 4 depthCode hdepthCode).
      * exact (standardTermScoped_lift scope 4 depthStep hdepthStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaOperationTraceTermAt : forall atom,
  StandardFormulaOperationAtomScoped atom ->
  forall scope parameter rootDepth sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex input output,
  StandardTermScoped scope parameter ->
  StandardTermScoped scope rootDepth ->
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope depthCode ->
  StandardTermScoped scope depthStep ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope rootIndex ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaOperationTraceTermAt atom parameter rootDepth sourceCode
      sourceStep targetCode targetStep depthCode depthStep bound rootIndex
      input output).
Proof.
  intros atom hatom scope parameter rootDepth sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound rootIndex input output
    hparameter hrootDepth hsourceCode hsourceStep htargetCode htargetStep
    hdepthCode hdepthStep hbound hrootIndex hinput houtput.
  unfold codedFormulaOperationTraceTermAt, operationAnd6.
  apply standardFormulaScoped_and.
  - operation_scope_formula.
  - apply standardFormulaScoped_and.
    + operation_scope_formula.
    + apply standardFormulaScoped_and.
      * operation_scope_formula.
      * apply standardFormulaScoped_and.
        -- operation_scope_formula.
        -- apply standardFormulaScoped_and.
           ++ apply standardFormulaScoped_codedFormulaOperationTripleLookupTermAt;
                assumption.
           ++ apply standardFormulaScoped_codedFormulaOperationRowsTermAt
                with (atom := atom); assumption.
Qed.

Lemma standardFormulaScoped_codedFormulaOperationTermAt : forall atom,
  StandardFormulaOperationAtomScoped atom ->
  forall scope parameter rootDepth input output,
  StandardTermScoped scope parameter ->
  StandardTermScoped scope rootDepth ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaOperationTermAt atom parameter rootDepth input output).
Proof.
  intros atom hatom scope parameter rootDepth input output
    hparameter hrootDepth hinput houtput.
  unfold codedFormulaOperationTermAt, operationEx8.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedFormulaOperationTraceTermAt
    with (atom := atom).
  - exact hatom.
  - exact (standardTermScoped_lift scope 8 parameter hparameter).
  - exact (standardTermScoped_lift scope 8 rootDepth hrootDepth).
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 8 input hinput).
  - exact (standardTermScoped_lift scope 8 output houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaShiftTermAt : forall scope
    cutoff amount input output,
  StandardTermScoped scope cutoff ->
  StandardTermScoped scope amount ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaShiftTermAt cutoff amount input output).
Proof.
  intros scope cutoff amount input output hcutoff hamount hinput houtput.
  unfold codedFormulaShiftTermAt.
  exact (standardFormulaScoped_codedFormulaOperationTermAt
    codedFormulaShiftAtomTermAt
    standardFormulaScoped_codedFormulaShiftAtomTermAt
    scope amount cutoff input output hamount hcutoff hinput houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaSingleSubstitutionTermAt :
    forall scope replacement input output,
  StandardTermScoped scope replacement ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaSingleSubstitutionTermAt replacement input output).
Proof.
  intros scope replacement input output hreplacement hinput houtput.
  unfold codedFormulaSingleSubstitutionTermAt.
  exact (standardFormulaScoped_codedFormulaOperationTermAt
    codedFormulaSubstitutionAtomTermAt
    standardFormulaScoped_codedFormulaSubstitutionAtomTermAt
    scope replacement tZero input output hreplacement
    (standardTermScoped_zero scope) hinput houtput).
Qed.

End PABoundedRawCodedFormulaOperationScopes.
