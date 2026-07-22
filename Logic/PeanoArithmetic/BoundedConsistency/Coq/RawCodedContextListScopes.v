(** Scope preservation for beta-certified coded context lists. *)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes.

Module PABoundedRawCodedContextListScopes.

Import PA.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedContextLists.

Lemma standardFormulaScoped_contextListRowTermAt : forall scope
    tailCode tailStep headCode headStep index,
  StandardTermScoped scope tailCode ->
  StandardTermScoped scope tailStep ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  StandardTermScoped scope index ->
  StandardFormulaScoped scope
    (contextListRowTermAt tailCode tailStep headCode headStep index).
Proof.
  intros scope tailCode tailStep headCode headStep index
    htailCode htailStep hheadCode hheadStep hindex.
  unfold contextListRowTermAt, contextListEx3, contextListAnd4.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentLookupTermAt.
    + exact (standardTermScoped_lift scope 3 tailCode htailCode).
    + exact (standardTermScoped_lift scope 3 tailStep htailStep).
    + exact (standardTermScoped_lift scope 3 index hindex).
    + apply standardTermScoped_var. lia.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt.
      * exact (standardTermScoped_lift scope 3 tailCode htailCode).
      * exact (standardTermScoped_lift scope 3 tailStep htailStep).
      * exact (standardTermScoped_lift scope 3 (tSucc index)
          (standardTermScoped_succ scope index hindex)).
      * apply standardTermScoped_var. lia.
    + apply standardFormulaScoped_and.
      * apply standardFormulaScoped_codedAssignmentLookupTermAt.
        -- exact (standardTermScoped_lift scope 3 headCode hheadCode).
        -- exact (standardTermScoped_lift scope 3 headStep hheadStep).
        -- exact (standardTermScoped_lift scope 3 index hindex).
        -- apply standardTermScoped_var. lia.
      * apply standardFormulaScoped_eq.
        -- apply standardTermScoped_var. lia.
        -- apply standardTermScoped_nodeTerm;
             apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_contextListTraversalTermAt : forall scope
    root bound tailCode tailStep headCode headStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope tailCode ->
  StandardTermScoped scope tailStep ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  StandardFormulaScoped scope
    (contextListTraversalTermAt
      root bound tailCode tailStep headCode headStep).
Proof.
  intros scope root bound tailCode tailStep headCode headStep
    hroot hbound htailCode htailStep hheadCode hheadStep.
  unfold contextListTraversalTermAt, contextListAnd4.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentLookupTermAt;
      try assumption; apply standardTermScoped_zero.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt;
        try assumption; apply standardTermScoped_zero.
    + apply standardFormulaScoped_and.
      * exact (standardFormulaScoped_codedAssignmentDefinedThroughTermAt
          scope headCode headStep bound hheadCode hheadStep hbound).
      * apply standardFormulaScoped_all.
        apply standardFormulaScoped_imp.
        -- apply standardFormulaScoped_ltTermAt.
           ++ apply standardTermScoped_var. lia.
           ++ exact (standardTermScoped_lift scope 1 bound hbound).
        -- apply standardFormulaScoped_contextListRowTermAt.
           ++ exact (standardTermScoped_lift scope 1 tailCode htailCode).
           ++ exact (standardTermScoped_lift scope 1 tailStep htailStep).
           ++ exact (standardTermScoped_lift scope 1 headCode hheadCode).
           ++ exact (standardTermScoped_lift scope 1 headStep hheadStep).
           ++ apply standardTermScoped_var. lia.
Qed.

Lemma standardFormulaScoped_contextListMemberWithTablesTermAt : forall scope
    member bound headCode headStep,
  StandardTermScoped scope member ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  StandardFormulaScoped scope
    (contextListMemberWithTablesTermAt member bound headCode headStep).
Proof.
  intros scope member bound headCode headStep
    hmember hbound hheadCode hheadStep.
  unfold contextListMemberWithTablesTermAt.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var. lia.
    + exact (standardTermScoped_lift scope 1 bound hbound).
  - apply standardFormulaScoped_codedAssignmentLookupTermAt.
    + exact (standardTermScoped_lift scope 1 headCode hheadCode).
    + exact (standardTermScoped_lift scope 1 headStep hheadStep).
    + apply standardTermScoped_var. lia.
    + exact (standardTermScoped_lift scope 1 member hmember).
Qed.

Lemma standardFormulaScoped_contextListRealizableTermAt : forall scope root,
  StandardTermScoped scope root ->
  StandardFormulaScoped scope (contextListRealizableTermAt root).
Proof.
  intros scope root hroot.
  unfold contextListRealizableTermAt, contextListEx5.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_contextListTraversalTermAt.
  - exact (standardTermScoped_lift scope 5 root hroot).
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_contextListMemberTermAt : forall scope
    root member,
  StandardTermScoped scope root ->
  StandardTermScoped scope member ->
  StandardFormulaScoped scope (contextListMemberTermAt root member).
Proof.
  intros scope root member hroot hmember.
  unfold contextListMemberTermAt, contextListEx5.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_contextListTraversalTermAt.
    + exact (standardTermScoped_lift scope 5 root hroot).
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_contextListMemberWithTablesTermAt.
    + exact (standardTermScoped_lift scope 5 member hmember).
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
    + apply standardTermScoped_var; lia.
Qed.

End PABoundedRawCodedContextListScopes.
