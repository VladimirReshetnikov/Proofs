(**
  Scope certificates for the compact selector package.

  The package says that a target is the code of the restricted-consistency
  sentence at the current level and that an ordinary PA proof certificate
  proves that target.  Its one free variable is therefore a legitimate
  induction variable.  These lemmas establish that fact compositionally;
  in particular, they never normalize the large numerals occurring in
  quoted formula codes.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes
  RawCodedNumeralTermCode
  RawCodedPAProvability
  CompactRestrictedPAConsistencyFormulaCodeGraph
  CompactPAUniformProvability.

Module PABoundedRawCodedCompactSelectorScopes.

Import PA.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedPAProvability.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedCompactPAUniformProvability.

(** Quoting a fixed term produces a closed code-building term. *)
Lemma standardTermScoped_compactQuotedTermCodeTerm : forall scope source,
  StandardTermScoped scope (compactQuotedTermCodeTerm source).
Proof.
  intros scope source.
  induction source as
      [index | | child IH | lhs IHl rhs IHr | lhs IHl rhs IHr];
    cbn [compactQuotedTermCodeTerm].
  - apply standardTermScoped_codeList2Term;
      apply standardTermScoped_numeral.
  - apply standardTermScoped_codeList1Term.
    apply standardTermScoped_numeral.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
Qed.

(** Quoting a fixed formula likewise produces a closed code-building term. *)
Lemma standardTermScoped_compactQuotedFormulaCodeTerm : forall scope source,
  StandardTermScoped scope (compactQuotedFormulaCodeTerm source).
Proof.
  intros scope source.
  induction source as
      [lhs rhs | | lhs IHl rhs IHr | lhs IHl rhs IHr |
       lhs IHl rhs IHr | child IH | child IH];
    cbn [compactQuotedFormulaCodeTerm].
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + apply standardTermScoped_compactQuotedTermCodeTerm.
    + apply standardTermScoped_compactQuotedTermCodeTerm.
  - apply standardTermScoped_codeList1Term.
    apply standardTermScoped_numeral.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
Qed.

(** Replacing the distinguished hole cannot introduce variables other than
    those already occurring in the replacement-code term. *)
Lemma standardTermScoped_compactRestrictedTargetTermContextCodeTerm :
    forall scope replacement context,
  StandardTermScoped scope replacement ->
  StandardTermScoped scope
    (compactRestrictedTargetTermContextCodeTerm replacement context).
Proof.
  intros scope replacement context hreplacement.
  induction context as
      [fixed | | child IH | lhs IHl rhs IHr | lhs IHl rhs IHr];
    cbn [compactRestrictedTargetTermContextCodeTerm].
  - apply standardTermScoped_compactQuotedTermCodeTerm.
  - exact hreplacement.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
Qed.

Lemma standardTermScoped_compactRestrictedTargetCloseNFormulaCodeTerm :
    forall count scope code,
  StandardTermScoped scope code ->
  StandardTermScoped scope
    (compactRestrictedTargetCloseNFormulaCodeTerm count code).
Proof.
  intro count. induction count as [|count IH];
    intros scope code hcode;
    cbn [compactRestrictedTargetCloseNFormulaCodeTerm].
  - exact hcode.
  - apply IH.
    apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact hcode.
Qed.

Lemma standardTermScoped_compactRestrictedTargetFormulaContextCodeTerm :
    forall scope replacement context,
  StandardTermScoped scope replacement ->
  StandardTermScoped scope
    (compactRestrictedTargetFormulaContextCodeTerm replacement context).
Proof.
  intros scope replacement context hreplacement.
  induction context as
      [fixed | | lhs rhs | lhs IHl rhs IHr | lhs IHl rhs IHr |
       lhs IHl rhs IHr | child IH | child IH | child IH];
    cbn [compactRestrictedTargetFormulaContextCodeTerm].
  - apply standardTermScoped_compactQuotedFormulaCodeTerm.
  - apply standardTermScoped_codeList1Term.
    apply standardTermScoped_numeral.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + apply standardTermScoped_compactRestrictedTargetTermContextCodeTerm.
      exact hreplacement.
    + apply standardTermScoped_compactRestrictedTargetTermContextCodeTerm.
      exact hreplacement.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList3Term.
    + apply standardTermScoped_numeral.
    + exact IHl.
    + exact IHr.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
  - apply standardTermScoped_codeList2Term.
    + apply standardTermScoped_numeral.
    + exact IH.
  - apply standardTermScoped_compactRestrictedTargetCloseNFormulaCodeTerm.
    exact IH.
Qed.

(** The numeral-code graph is used independently of the compact target
    graph, so expose its parametric scope certificates as reusable lemmas.
    [numeralCodeLiftTerm] is definitionally the standard binder lift, but an
    explicit wrapper keeps the arithmetic shape stable for later proofs. *)
Lemma standardTermScoped_numeralCodeLiftTerm : forall scope count input,
  StandardTermScoped scope input ->
  StandardTermScoped (count + scope)
    (numeralCodeLiftTerm count input).
Proof.
  intros scope count input hinput index hfree.
  unfold numeralCodeLiftTerm in hfree.
  destruct (standardTermFree_rename_preimage input
    (fun sourceIndex => sourceIndex + count) index hfree)
    as [sourceIndex [hsource heq]].
  specialize (hinput sourceIndex hsource). lia.
Qed.

Lemma standardFormulaScoped_numeralTermCodeRowsTermAt : forall
    scope bound code step,
  StandardTermScoped scope bound ->
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardFormulaScoped scope
    (numeralTermCodeRowsTermAt bound code step).
Proof.
  intros scope bound code step hbound hcode hstep.
  unfold numeralTermCodeRowsTermAt.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var. lia.
    + exact (standardTermScoped_numeralCodeLiftTerm
        scope 3 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt.
      * exact (standardTermScoped_numeralCodeLiftTerm
          scope 3 code hcode).
      * exact (standardTermScoped_numeralCodeLiftTerm
          scope 3 step hstep).
      * apply standardTermScoped_var. lia.
      * apply standardTermScoped_var. lia.
    + apply standardFormulaScoped_imp.
      * apply standardFormulaScoped_codedAssignmentLookupTermAt.
        -- exact (standardTermScoped_numeralCodeLiftTerm
             scope 3 code hcode).
        -- exact (standardTermScoped_numeralCodeLiftTerm
             scope 3 step hstep).
        -- apply standardTermScoped_succ.
           apply standardTermScoped_var. lia.
        -- apply standardTermScoped_var. lia.
      * apply standardFormulaScoped_termSuccCodeTermAt;
          apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_numeralTermCodeTraceTermAt : forall
    scope bound code step,
  StandardTermScoped scope bound ->
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardFormulaScoped scope
    (numeralTermCodeTraceTermAt bound code step).
Proof.
  intros scope bound code step hbound hcode hstep.
  unfold numeralTermCodeTraceTermAt.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt.
    + exact hcode.
    + exact hstep.
    + apply standardTermScoped_succ. exact hbound.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt.
      * exact hcode.
      * exact hstep.
      * apply standardTermScoped_zero.
      * apply standardTermScoped_codeList1Term.
        apply standardTermScoped_numeral.
    + exact (standardFormulaScoped_numeralTermCodeRowsTermAt
        scope bound code step hbound hcode hstep).
Qed.

Lemma standardFormulaScoped_numeralTermCodeAtTermAt : forall scope bound code,
  StandardTermScoped scope bound ->
  StandardTermScoped scope code ->
  StandardFormulaScoped scope (numeralTermCodeAtTermAt bound code).
Proof.
  intros scope bound code hbound hcode.
  unfold numeralTermCodeAtTermAt.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_numeralTermCodeTraceTermAt.
    + exact (standardTermScoped_numeralCodeLiftTerm
        scope 2 bound hbound).
    + apply standardTermScoped_var. lia.
    + apply standardTermScoped_var. lia.
  - apply standardFormulaScoped_codedAssignmentLookupTermAt.
    + apply standardTermScoped_var. lia.
    + apply standardTermScoped_var. lia.
    + exact (standardTermScoped_numeralCodeLiftTerm
        scope 2 bound hbound).
    + exact (standardTermScoped_numeralCodeLiftTerm
        scope 2 code hcode).
Qed.

(** The compact graph has free output and input slots, in that order. *)
Theorem compactRestrictedPAConsistencyFormulaCodeGraph_scoped_two :
  StandardFormulaScoped 2
    compactRestrictedPAConsistencyFormulaCodeGraph.
Proof.
  unfold compactRestrictedPAConsistencyFormulaCodeGraph.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_numeralTermCodeAtTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_eq.
    + apply standardTermScoped_var. lia.
    + apply
        standardTermScoped_compactRestrictedTargetFormulaContextCodeTerm.
      apply standardTermScoped_var. lia.
Qed.

(** Ordinary PA proof certificates are scoped uniformly in both exposed
    terms.  The imported syntax-directed tactic stops at previously proved
    interfaces for the four large proof-wide checker fields. *)
Lemma standardFormulaScoped_codedPAProofOfTermAt : forall
    scope target certificate,
  StandardTermScoped scope target ->
  StandardTermScoped scope certificate ->
  StandardFormulaScoped scope
    (codedPAProofOfTermAt target certificate).
Proof.
  intros scope target certificate htarget hcertificate.
  raw_scope_formula.
Qed.

Lemma standardFormulaScoped_codedPAProvabilityTermAt : forall scope target,
  StandardTermScoped scope target ->
  StandardFormulaScoped scope (codedPAProvabilityTermAt target).
Proof.
  intros scope target htarget.
  unfold codedPAProvabilityTermAt.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedPAProofOfTermAt.
  - exact (standardTermScoped_lift scope 1 target htarget).
  - apply standardTermScoped_var. lia.
Qed.

(** This is the critical bookkeeping fact for the correct induction
    predicate: level is its only free variable. *)
Theorem compactSelectorPackageFormula_scoped_one :
  StandardFormulaScoped 1 compactSelectorPackageFormula.
Proof.
  unfold compactSelectorPackageFormula.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - exact compactRestrictedPAConsistencyFormulaCodeGraph_scoped_two.
  - apply standardFormulaScoped_codedPAProvabilityTermAt.
    apply standardTermScoped_var. lia.
Qed.

End PABoundedRawCodedCompactSelectorScopes.
