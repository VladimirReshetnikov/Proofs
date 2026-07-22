(** Scope preservation for the represented [Term.bound] and [Formula.bound]
    graphs used by induction-axiom witnesses. *)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedPAAxiomWitness
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes
  RawCodedFormulaOperationScopes.

Module PABoundedRawCodedPAAxiomWitnessBoundScopes.

Import PA.
Import PAListRepresentability.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedFormulaOperationScopes.

Lemma standardFormulaScoped_codedTermBoundVariableRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermBoundVariableRowTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedTermBoundVariableRowTermAt.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_termVarCodeTermAt.
    + exact (standardTermScoped_lift scope 1 input hinput).
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_eq.
    + exact (standardTermScoped_lift scope 1 output houtput).
    + apply standardTermScoped_succ.
      apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermBoundZeroRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope (codedTermBoundZeroRowTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedTermBoundZeroRowTermAt.
  apply standardFormulaScoped_and.
  - exact (standardFormulaScoped_termZeroCodeTermAt scope input hinput).
  - apply standardFormulaScoped_eq;
      [exact houtput | apply standardTermScoped_zero].
Qed.

Lemma standardFormulaScoped_codedTermBoundSuccRowTermAt : forall scope
    sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermBoundSuccRowTermAt sourceCode sourceStep targetCode targetStep
      index input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep index input output
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermBoundSuccRowTermAt, operationEx3, operationAnd4.
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
      * apply standardFormulaScoped_eq.
        -- exact (standardTermScoped_lift scope 3 output houtput).
        -- apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermBoundBinaryRowTermAt : forall
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
    (codedTermBoundBinaryRowTermAt constructor sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep index input output hsourceCode hsourceStep htargetCode
    htargetStep hindex hinput houtput.
  unfold codedTermBoundBinaryRowTermAt, operationEx6, operationAnd6.
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
           ++ apply standardFormulaScoped_eq.
              ** exact (standardTermScoped_lift scope 6 output houtput).
              ** apply standardTermScoped_add;
                   apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermBoundTraversalRowTermAt : forall scope
    sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermBoundTraversalRowTermAt sourceCode sourceStep targetCode
      targetStep index input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep index input output
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedTermBoundTraversalRowTermAt.
  apply standardFormulaScoped_or.
  - exact (standardFormulaScoped_codedTermBoundVariableRowTermAt
      scope input output hinput houtput).
  - apply standardFormulaScoped_or.
    + exact (standardFormulaScoped_codedTermBoundZeroRowTermAt
        scope input output hinput houtput).
    + apply standardFormulaScoped_or.
      * apply standardFormulaScoped_codedTermBoundSuccRowTermAt;
          assumption.
      * apply standardFormulaScoped_or.
        -- exact (standardFormulaScoped_codedTermBoundBinaryRowTermAt
             termAddCodeTermAt standardFormulaScoped_termAddCodeTermAt
             scope sourceCode sourceStep targetCode targetStep index input
             output hsourceCode hsourceStep htargetCode htargetStep hindex
             hinput houtput).
        -- exact (standardFormulaScoped_codedTermBoundBinaryRowTermAt
             termMulCodeTermAt standardFormulaScoped_termMulCodeTermAt
             scope sourceCode sourceStep targetCode targetStep index input
             output hsourceCode hsourceStep htargetCode htargetStep hindex
             hinput houtput).
Qed.

Lemma standardFormulaScoped_codedTermBoundRowsTermAt : forall scope
    sourceCode sourceStep targetCode targetStep root,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope root ->
  StandardFormulaScoped scope
    (codedTermBoundRowsTermAt sourceCode sourceStep targetCode targetStep root).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep root
    hsourceCode hsourceStep htargetCode htargetStep hroot.
  unfold codedTermBoundRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 (tSucc root)
        (standardTermScoped_succ scope root hroot)).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedTermBoundTraversalRowTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedTermBoundTraceTermAt : forall scope
    sourceCode sourceStep targetCode targetStep input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedTermBoundTraceTermAt sourceCode sourceStep targetCode targetStep
      input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep input output
    hsourceCode hsourceStep htargetCode htargetStep hinput houtput.
  unfold codedTermBoundTraceTermAt, operationAnd4.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      try assumption.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
        try assumption.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_codedTermOperationPairLookupTermAt;
          assumption.
      * apply standardFormulaScoped_codedTermBoundRowsTermAt;
          assumption.
Qed.

Lemma standardFormulaScoped_codedTermBoundTermAt : forall scope input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope (codedTermBoundTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedTermBoundTermAt, operationEx4.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedTermBoundTraceTermAt.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 4 input hinput).
  - exact (standardTermScoped_lift scope 4 output houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaBoundEqRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope (codedFormulaBoundEqRowTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedFormulaBoundEqRowTermAt, operationEx4, operationAnd4.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_formulaEqCodeTermAt.
    + exact (standardTermScoped_lift scope 4 input hinput).
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedTermBoundTermAt;
        apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_codedTermBoundTermAt;
          apply standardTermScoped_var; lia.
      * apply standardFormulaScoped_eq.
        -- exact (standardTermScoped_lift scope 4 output houtput).
        -- apply standardTermScoped_add;
             apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaBoundBotRowTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope (codedFormulaBoundBotRowTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedFormulaBoundBotRowTermAt.
  apply standardFormulaScoped_and.
  - exact (standardFormulaScoped_formulaBotCodeTermAt scope input hinput).
  - apply standardFormulaScoped_eq;
      [exact houtput | apply standardTermScoped_zero].
Qed.

Lemma standardFormulaScoped_codedFormulaBoundBinaryRowTermAt : forall
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
    (codedFormulaBoundBinaryRowTermAt constructor sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep index input output hsourceCode hsourceStep htargetCode
    htargetStep hindex hinput houtput.
  exact (standardFormulaScoped_codedTermBoundBinaryRowTermAt
    constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep index input output hsourceCode hsourceStep htargetCode
    htargetStep hindex hinput houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaBoundUnaryRowTermAt : forall
    (constructor : term -> term -> formula),
  (forall scope code child,
    StandardTermScoped scope code ->
    StandardTermScoped scope child ->
    StandardFormulaScoped scope (constructor code child)) ->
  forall scope sourceCode sourceStep targetCode targetStep index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaBoundUnaryRowTermAt constructor sourceCode sourceStep
      targetCode targetStep index input output).
Proof.
  intros constructor hconstructor scope sourceCode sourceStep targetCode
    targetStep index input output hsourceCode hsourceStep htargetCode
    htargetStep hindex hinput houtput.
  unfold codedFormulaBoundUnaryRowTermAt, operationEx3, operationAnd4.
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
      * apply hconstructor.
        -- exact (standardTermScoped_lift scope 3 input hinput).
        -- apply standardTermScoped_var; lia.
      * apply standardFormulaScoped_eq.
        -- exact (standardTermScoped_lift scope 3 output houtput).
        -- apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaBoundTraversalRowTermAt :
    forall scope sourceCode sourceStep targetCode targetStep
      index input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaBoundTraversalRowTermAt sourceCode sourceStep targetCode
      targetStep index input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep index input output
    hsourceCode hsourceStep htargetCode htargetStep hindex hinput houtput.
  unfold codedFormulaBoundTraversalRowTermAt.
  apply standardFormulaScoped_or.
  - exact (standardFormulaScoped_codedFormulaBoundEqRowTermAt
      scope input output hinput houtput).
  - apply standardFormulaScoped_or.
    + exact (standardFormulaScoped_codedFormulaBoundBotRowTermAt
        scope input output hinput houtput).
    + apply standardFormulaScoped_or.
      * exact (standardFormulaScoped_codedFormulaBoundBinaryRowTermAt
          formulaImpCodeTermAt standardFormulaScoped_formulaImpCodeTermAt
          scope sourceCode sourceStep targetCode targetStep index input
          output hsourceCode hsourceStep htargetCode htargetStep hindex
          hinput houtput).
      * apply standardFormulaScoped_or.
        -- exact (standardFormulaScoped_codedFormulaBoundBinaryRowTermAt
             formulaAndCodeTermAt
             standardFormulaScoped_formulaAndCodeTermAt
             scope sourceCode sourceStep targetCode targetStep index input
             output hsourceCode hsourceStep htargetCode htargetStep hindex
             hinput houtput).
        -- apply standardFormulaScoped_or.
           ++ exact (standardFormulaScoped_codedFormulaBoundBinaryRowTermAt
                formulaOrCodeTermAt
                standardFormulaScoped_formulaOrCodeTermAt
                scope sourceCode sourceStep targetCode targetStep index input
                output hsourceCode hsourceStep htargetCode htargetStep hindex
                hinput houtput).
           ++ apply standardFormulaScoped_or.
              ** exact (standardFormulaScoped_codedFormulaBoundUnaryRowTermAt
                   formulaAllCodeTermAt
                   standardFormulaScoped_formulaAllCodeTermAt
                   scope sourceCode sourceStep targetCode targetStep index
                   input output hsourceCode hsourceStep htargetCode
                   htargetStep hindex hinput houtput).
              ** exact (standardFormulaScoped_codedFormulaBoundUnaryRowTermAt
                   formulaExCodeTermAt
                   standardFormulaScoped_formulaExCodeTermAt
                   scope sourceCode sourceStep targetCode targetStep index
                   input output hsourceCode hsourceStep htargetCode
                   htargetStep hindex hinput houtput).
Qed.

Lemma standardFormulaScoped_codedFormulaBoundRowsTermAt : forall scope
    sourceCode sourceStep targetCode targetStep root,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope root ->
  StandardFormulaScoped scope
    (codedFormulaBoundRowsTermAt
      sourceCode sourceStep targetCode targetStep root).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep root
    hsourceCode hsourceStep htargetCode htargetStep hroot.
  unfold codedFormulaBoundRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 (tSucc root)
        (standardTermScoped_succ scope root hroot)).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedTermOperationPairLookupTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_codedFormulaBoundTraversalRowTermAt.
      * exact (standardTermScoped_lift scope 3 sourceCode hsourceCode).
      * exact (standardTermScoped_lift scope 3 sourceStep hsourceStep).
      * exact (standardTermScoped_lift scope 3 targetCode htargetCode).
      * exact (standardTermScoped_lift scope 3 targetStep htargetStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedFormulaBoundTraceTermAt : forall scope
    sourceCode sourceStep targetCode targetStep input output,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope
    (codedFormulaBoundTraceTermAt sourceCode sourceStep targetCode targetStep
      input output).
Proof.
  intros scope sourceCode sourceStep targetCode targetStep input output
    hsourceCode hsourceStep htargetCode htargetStep hinput houtput.
  unfold codedFormulaBoundTraceTermAt, operationAnd4.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      assumption.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
        assumption.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_codedTermOperationPairLookupTermAt;
          assumption.
      * apply standardFormulaScoped_codedFormulaBoundRowsTermAt;
          assumption.
Qed.

Lemma standardFormulaScoped_codedFormulaBoundTermAt : forall scope
    input output,
  StandardTermScoped scope input ->
  StandardTermScoped scope output ->
  StandardFormulaScoped scope (codedFormulaBoundTermAt input output).
Proof.
  intros scope input output hinput houtput.
  unfold codedFormulaBoundTermAt, operationEx4.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedFormulaBoundTraceTermAt.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - exact (standardTermScoped_lift scope 4 input hinput).
  - exact (standardTermScoped_lift scope 4 output houtput).
Qed.

End PABoundedRawCodedPAAxiomWitnessBoundScopes.
