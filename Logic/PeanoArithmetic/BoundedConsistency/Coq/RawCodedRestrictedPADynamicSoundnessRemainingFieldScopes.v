(**
  Scope certificates for the four proof-wide checker fields.

  The local tactic is syntax-directed: it stops at the opaque scope lemmas
  for arithmetic operation graphs and unfolds only the next named proof
  constructor.  In particular it recognizes [Term.numeral] before delta
  reduction, so closed quotation constants are never expanded into gigantic
  unary terms.
*)

From Stdlib Require Import Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaOperations
  RawCodedPAAxiomWitness RawCodedContextLists
  RawCodedProofConstructors RawCodedProofDescent
  RawCodedRestrictedPAProof RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage RawCodedProofRuleCoverage RawCodedProofRules
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators RawCodedBasicFormulaScopes
  RawCodedContextListScopes RawCodedFormulaOperationScopes
  RawCodedPAAxiomWitnessBoundScopes RawCodedPAAxiomWitnessScopes
  RawCodedRestrictedPADynamicSoundnessFieldScopes.

Module PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Import PA PAListRepresentability PAListFormulas.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedContextListScopes.
Import PABoundedRawCodedFormulaOperationScopes.
Import PABoundedRawCodedPAAxiomWitnessBoundScopes.
Import PABoundedRawCodedPAAxiomWitnessScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.

Ltac raw_scope_unfold_or_reduce_head head :=
  first [is_fix head; cbn | unfold head].

Ltac raw_scope_term :=
  lazymatch goal with
  | |- StandardTermScoped _ (Term.numeral _) =>
      apply standardTermScoped_numeral
  | |- StandardTermScoped _ (tVar _) =>
      apply standardTermScoped_var; lia
  | |- StandardTermScoped _ tZero => apply standardTermScoped_zero
  | |- StandardTermScoped _ (tSucc _) =>
      apply standardTermScoped_succ; raw_scope_term
  | |- StandardTermScoped _ (tAdd _ _) =>
      apply standardTermScoped_add; raw_scope_term
  | |- StandardTermScoped _ (tMul _ _) =>
      apply standardTermScoped_mul; raw_scope_term
  | H : StandardTermScoped ?sourceScope ?input |-
      StandardTermScoped ?targetScope (liftTerm ?binderCount ?input) =>
      eapply standardTermScoped_weaken;
        [exact (standardTermScoped_lift
          sourceScope binderCount input H) | lia]
  | |- StandardTermScoped ?targetScope (liftTerm ?binderCount ?input) =>
      eapply standardTermScoped_weaken with
        (sourceScope := binderCount + (targetScope - binderCount));
        [apply standardTermScoped_lift; raw_scope_term | lia]
  | |- StandardTermScoped _ (nodeTerm _ _) =>
      apply standardTermScoped_nodeTerm; raw_scope_term
  | |- StandardTermScoped _ (codeList1Term _) =>
      apply standardTermScoped_codeList1Term; raw_scope_term
  | |- StandardTermScoped _ (codeList2Term _ _) =>
      apply standardTermScoped_codeList2Term; raw_scope_term
  | |- StandardTermScoped _ (codeList3Term _ _ _) =>
      apply standardTermScoped_codeList3Term; raw_scope_term
  | |- StandardTermScoped _ rawFormulaBotCodeTerm =>
      unfold rawFormulaBotCodeTerm; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- StandardTermScoped _ (?f _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_term
  | |- _ => assumption
  end.

Ltac raw_scope_formula :=
  lazymatch goal with
  | |- StandardFormulaScoped _ pBot => apply standardFormulaScoped_bot
  | |- StandardFormulaScoped _ (pEq _ _) =>
      apply standardFormulaScoped_eq; raw_scope_term
  | |- StandardFormulaScoped _ (pImp _ _) =>
      apply standardFormulaScoped_imp; raw_scope_formula
  | |- StandardFormulaScoped _ (pAnd _ _) =>
      apply standardFormulaScoped_and; raw_scope_formula
  | |- StandardFormulaScoped _ (pOr _ _) =>
      apply standardFormulaScoped_or; raw_scope_formula
  | |- StandardFormulaScoped _ (pAll _) =>
      apply standardFormulaScoped_all; raw_scope_formula
  | |- StandardFormulaScoped _ (pEx _) =>
      apply standardFormulaScoped_ex; raw_scope_formula
  | |- StandardFormulaScoped _ (Formula.ltTermAt _ _) =>
      apply standardFormulaScoped_ltTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (Formula.leTermAt _ _) =>
      apply standardFormulaScoped_leTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (codedAssignmentLookupTermAt _ _ _ _) =>
      apply standardFormulaScoped_codedAssignmentLookupTermAt;
        raw_scope_term
  | |- StandardFormulaScoped _
        (codedAssignmentDefinedThroughTermAt _ _ _) =>
      apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
        raw_scope_term
  | |- StandardFormulaScoped _ (codedTermShiftTermAt _ _ _ _) =>
      apply standardFormulaScoped_codedTermShiftTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (codedTermOpeningTermAt _ _ _ _) =>
      apply standardFormulaScoped_codedTermOpeningTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (codedFormulaShiftTermAt _ _ _ _) =>
      apply standardFormulaScoped_codedFormulaShiftTermAt; raw_scope_term
  | |- StandardFormulaScoped _
        (codedFormulaSingleSubstitutionTermAt _ _ _) =>
      apply standardFormulaScoped_codedFormulaSingleSubstitutionTermAt;
        raw_scope_term
  | |- StandardFormulaScoped _ (codedFormulaBoundTermAt _ _) =>
      apply standardFormulaScoped_codedFormulaBoundTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (codedUniversalClosureTermAt _ _ _) =>
      apply standardFormulaScoped_codedUniversalClosureTermAt; raw_scope_term
  | |- StandardFormulaScoped _
        (contextListTraversalTermAt _ _ _ _ _ _) =>
      apply standardFormulaScoped_contextListTraversalTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (contextListMemberTermAt _ _) =>
      apply standardFormulaScoped_contextListMemberTermAt; raw_scope_term
  | |- StandardFormulaScoped _ (codedPAAxiomWitnessTermAt _ _) =>
      apply standardFormulaScoped_codedPAAxiomWitnessTermAt; raw_scope_term
  | |- StandardFormulaScoped _
        (codedPAAxiomWitnessContextTermAt _ _) =>
      apply standardFormulaScoped_codedPAAxiomWitnessContextTermAt;
        raw_scope_term
  | |- StandardFormulaScoped _ (proofFormulaConjunction _) =>
      unfold proofFormulaConjunction; raw_scope_formula
  | |- StandardFormulaScoped _ (proofFormulaDisjunction _) =>
      unfold proofFormulaDisjunction; raw_scope_formula
  | |- StandardFormulaScoped _
        ((fix rec (cases : list formula) {struct cases} : formula := _) _) =>
      cbn; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _ _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ (?f _) =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  | |- StandardFormulaScoped _ ?f =>
      raw_scope_unfold_or_reduce_head f; raw_scope_formula
  end.

Theorem proofAtomicallyAdequateTermAt_scoped_three :
  StandardFormulaScoped 3 (proofAtomicallyAdequateTermAt (tVar 1)).
Proof.
  unfold proofAtomicallyAdequateTermAt, proofAtomicEx2.
  repeat apply standardFormulaScoped_ex.
  raw_scope_formula.
Qed.

Theorem proofHasFormulaCoverageTermAt_scoped_three :
  StandardFormulaScoped 3 (proofHasFormulaCoverageTermAt (tVar 1)).
Proof. raw_scope_formula. Qed.

Theorem proofRuleCoverageTermAt_scoped_three :
  StandardFormulaScoped 3 (proofRuleCoverageTermAt (tVar 1)).
Proof. raw_scope_formula. Qed.

Theorem proofRuleValidTermAt_scoped_three :
  StandardFormulaScoped 3
    (proofRuleValidTermAt (tVar 1) (tVar 0) rawFormulaBotCodeTerm).
Proof. raw_scope_formula. Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.
