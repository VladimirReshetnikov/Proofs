(**
  Exact composition of model-coded proofs under one logical assumption.

  An ordinary [RawCodedPAProofOf] context consists only of witnessed PA
  axioms.  Local soundness arguments additionally work under a temporary
  assumption which must not be misclassified as a PA axiom.  The predicate
  below keeps these roles separate: [baseContext] is tied to [witnessList],
  while the proof endpoint lives at [assumption :: baseContext].

  This is deliberately not a generic weakening theorem.  Raw proof codes
  store a context at every node, and weakening an arbitrary tree would need
  a recursive constructor transformer (with special handling under binders).
  Instead, the constructors here build and compose honest trees directly in
  the extended context, then implication introduction discharges the single
  temporary assumption back into an ordinary PA certificate.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRestrictedPAProof
  RawCodedProofEndpoints RawCodedProofRuleCoverage RawCodedPAProvability
  RawCodedProofLeafConstructors RawCodedProofAssumptionLeaf
  RawCodedProofUnaryConstructors RawCodedProofBinaryConstructors
  RawCodedPAProofImpICertificates.

Module PABoundedRawCodedPAOpenProofComposition.

Import PA.
Import PAListFormulas.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofLeafConstructors.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAProofImpICertificates.

Definition RawCodedPAOpenProofOf (M : RawPAModel)
    (witnessList baseContext assumption target proof : M) : Prop :=
  RawCodedPAAxiomWitnessContext M witnessList baseContext /\
  RawProofRuleCoverage M proof /\
  RawProofEndpoint M proof
    (rawListNode M assumption baseContext) target.

Arguments RawCodedPAOpenProofOf
  M witnessList baseContext assumption target proof : clear implicits.

(** The open-proof package is itself represented by an ordinary formula,
    making the composition interface usable inside later definable
    inductions rather than only as a meta-level record. *)
Definition codedPAOpenProofOfTermAt
    (witnessList baseContext assumption target proof : term) : formula :=
  pAnd
    (codedPAAxiomWitnessContextTermAt witnessList baseContext)
    (pAnd
      (proofRuleCoverageTermAt proof)
      (proofEndpointTermAt proof
        (nodeTerm assumption baseContext) target)).

Lemma raw_sat_codedPAOpenProofOfTermAt_iff : forall
    (M : RawPAModel) e witnessList baseContext assumption target proof,
  raw_formula_sat M e
    (codedPAOpenProofOfTermAt
      witnessList baseContext assumption target proof) <->
  RawCodedPAOpenProofOf M
    (raw_term_eval M e witnessList)
    (raw_term_eval M e baseContext)
    (raw_term_eval M e assumption)
    (raw_term_eval M e target)
    (raw_term_eval M e proof).
Proof.
  intros. unfold codedPAOpenProofOfTermAt, RawCodedPAOpenProofOf.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedPAAxiomWitnessContextTermAt_iff,
    raw_sat_proofRuleCoverageTermAt_iff,
    raw_sat_proofEndpointTermAt_iff,
    raw_eval_nodeTerm.
  reflexivity.
Qed.

(** Existentially hiding the root gives the open analogue of ordinary PA
    provability.  This is the represented seam needed by a local soundness
    compiler: it may construct any covered contradiction under the temporary
    restricted-proof assumption. *)
Definition RawCodedPAOpenProvability (M : RawPAModel)
    (witnessList baseContext assumption target : M) : Prop :=
  exists proof,
    RawCodedPAOpenProofOf M
      witnessList baseContext assumption target proof.

Arguments RawCodedPAOpenProvability
  M witnessList baseContext assumption target : clear implicits.

Definition codedPAOpenProvabilityTermAt
    (witnessList baseContext assumption target : term) : formula :=
  pEx
    (codedPAOpenProofOfTermAt
      (liftTerm 1 witnessList) (liftTerm 1 baseContext)
      (liftTerm 1 assumption) (liftTerm 1 target) (tVar 0)).

Lemma raw_sat_codedPAOpenProvabilityTermAt_iff : forall
    (M : RawPAModel) e witnessList baseContext assumption target,
  raw_formula_sat M e
    (codedPAOpenProvabilityTermAt
      witnessList baseContext assumption target) <->
  RawCodedPAOpenProvability M
    (raw_term_eval M e witnessList)
    (raw_term_eval M e baseContext)
    (raw_term_eval M e assumption)
    (raw_term_eval M e target).
Proof.
  intros. unfold codedPAOpenProvabilityTermAt,
    RawCodedPAOpenProvability.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAOpenProofOfTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The temporary assumption is available as a genuine assumption leaf.
    Context realizability is extracted from the witnessed base package and
    extended through the model-internal beta traversal. *)
Theorem raw_codedPAOpenProofOf_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption assumption
    (rawProofAssumptionRoot M
      (rawListNode M assumption baseContext) assumption).
Proof.
  intros M hPA witnessList baseContext assumption hwitness.
  split; [exact hwitness |]. split.
  - apply (raw_proofAssumption_cons_head_ruleCoverage M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  - exact (raw_proofAssumption_endpoint M
      (rawListNode M assumption baseContext) assumption).
Qed.

(** Excluded middle is premise-free and can be built directly in the open
    context, including when its body is a nonstandard formula code. *)
Theorem raw_codedPAOpenProofOf_lem : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption body,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption
    (rawProofLemConclusion M body)
    (rawProofLemRoot M
      (rawListNode M assumption baseContext) body).
Proof.
  intros M hPA witnessList baseContext assumption body hwitness.
  split; [exact hwitness |]. split.
  - exact (raw_proofLem_ruleCoverage M hPA
      (rawListNode M assumption baseContext) body).
  - exact (raw_proofLem_endpoint M
      (rawListNode M assumption baseContext) body).
Qed.

Theorem raw_codedPAOpenProofOf_botE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption child,
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption (rawFormulaBotCode M) child ->
  forall target,
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption target
    (rawProofBotERoot M
      (rawListNode M assumption baseContext) target child).
Proof.
  intros M hPA witnessList baseContext assumption child
    [hwitness [hcoverage hendpoint]] target.
  split; [exact hwitness |]. split.
  - exact (raw_proofBotE_ruleCoverage M hPA
      (rawListNode M assumption baseContext) target child
      hcoverage hendpoint).
  - exact (raw_proofBotE_endpoint M
      (rawListNode M assumption baseContext) target child).
Qed.

Theorem raw_codedPAOpenProofOf_impE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption antecedent consequent
      impChild antecedentChild,
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption
    (rawFormulaImpCode M antecedent consequent) impChild ->
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption antecedent antecedentChild ->
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption consequent
    (rawProofImpERoot M
      (rawListNode M assumption baseContext)
      antecedent consequent impChild antecedentChild).
Proof.
  intros M hPA witnessList baseContext assumption antecedent consequent
    impChild antecedentChild
    [hwitness [himpCoverage himpEndpoint]]
    [_ [hantecedentCoverage hantecedentEndpoint]].
  split; [exact hwitness |]. split.
  - exact (raw_proofImpE_ruleCoverage M hPA
      (rawListNode M assumption baseContext)
      antecedent consequent impChild antecedentChild
      himpCoverage himpEndpoint
      hantecedentCoverage hantecedentEndpoint).
  - exact (raw_proofImpE_endpoint M
      (rawListNode M assumption baseContext)
      antecedent consequent impChild antecedentChild).
Qed.

(** Exact closure theorem used by local soundness compilers: an honestly
    composed proof under one temporary assumption becomes an ordinary PA
    proof of the corresponding implication, with the original witnessed
    base context restored. *)
Theorem raw_codedPAProofOf_implication_of_open : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption target child,
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption target child ->
  RawCodedPAProofOf M (rawFormulaImpCode M assumption target)
    (rawProofImpICertificate M
      witnessList baseContext assumption target child).
Proof.
  intros M hPA witnessList baseContext assumption target child
    [hwitness [hcoverage hendpoint]].
  exact (raw_codedPAProofOf_impI_from_fields M hPA
    witnessList baseContext assumption target child
    hwitness hcoverage hendpoint).
Qed.

Corollary raw_codedPAProvability_implication_of_open : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption target,
  RawCodedPAOpenProvability M
    witnessList baseContext assumption target ->
  exists certificate,
    RawCodedPAProofOf M
      (rawFormulaImpCode M assumption target) certificate.
Proof.
  intros M hPA witnessList baseContext assumption target
    [child hopen].
  exists (rawProofImpICertificate M
    witnessList baseContext assumption target child).
  exact (raw_codedPAProofOf_implication_of_open M hPA
    witnessList baseContext assumption target child hopen).
Qed.

Corollary raw_codedPAProofOf_negation_of_open_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption child,
  RawCodedPAOpenProofOf M
    witnessList baseContext assumption (rawFormulaBotCode M) child ->
  RawCodedPAProofOf M
    (rawFormulaImpCode M assumption (rawFormulaBotCode M))
    (rawProofImpICertificate M
      witnessList baseContext assumption (rawFormulaBotCode M) child).
Proof.
  intros. eapply raw_codedPAProofOf_implication_of_open; eassumption.
Qed.

(** Exact endpoint for the future local soundness argument: a represented
    open contradiction yields a represented ordinary PA proof of the
    negated temporary assumption. *)
Corollary raw_codedPAProvability_negation_of_open_bottom : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext assumption,
  RawCodedPAOpenProvability M
    witnessList baseContext assumption (rawFormulaBotCode M) ->
  exists certificate,
    RawCodedPAProofOf M
      (rawFormulaImpCode M assumption (rawFormulaBotCode M)) certificate.
Proof.
  intros. eapply raw_codedPAProvability_implication_of_open; eassumption.
Qed.

End PABoundedRawCodedPAOpenProofComposition.
