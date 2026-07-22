(**
  A transparent ordinary PA proof predicate.

  The bounded-consistency development previously exposed only certificates
  whose conclusion is falsity and whose every formula occurrence is bounded
  by a fixed metatheoretic level.  Internalizing the statement

      PA proves Con_n(PA)

  requires a different predicate: a certificate for an arbitrary coded
  conclusion.  This module packages exactly that relation using the same
  witnessed-axiom lists, proof-syntax traversal, and proof-wide local-rule
  coverage as the restricted checker.

  The final theorem is the first Hilbert--Bernays derivability condition for
  this concrete coding.  It is deliberately stated for one metatheoretic
  formula [phi].  It does not turn a family [forall n, PA |- phi n] into the
  object-language universal [PA |- forall n, Prov_PA (code (phi n))]; that
  stronger step needs a PA-verifiable uniform compiler for the family of
  proof codes.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof RawModelCompleteness
  RawCodedSyntaxConstructors RawCodedProofConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofRuleCoverageStandard
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof RawCodedRestrictedPAConsistency.

Import ListNotations.

Module PABoundedRawCodedPAProvability.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRuleCoverageStandard.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistency.

(** A certificate uses the already public list code

      [tag 0; witnessed PA axioms; raw derivation].

    [RawProofRuleCoverage] includes a complete proof-syntax traversal and a
    valid local-rule row for every supported node.  The last conjunct fixes
    the root endpoint to the requested target code. *)
Definition RawCodedPAProofOf (M : RawPAModel)
    (target certificate : M) : Prop :=
  exists witnessList proof context : M,
    certificate = rawCodeList3 M
      (rawNumeralValue M 0) witnessList proof /\
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawProofRuleCoverage M proof /\
    RawProofEndpoint M proof context target.

Arguments RawCodedPAProofOf M target certificate : clear implicits.

(** Formula with free terms [target] and [certificate].  Under the three
    existential binders, variables 2, 1, and 0 respectively denote the
    witnessed-axiom list, proof root, and proof context. *)
Definition codedPAProofOfTermAt
    (target certificate : term) : formula :=
  restrictedPAEx3
    (restrictedPAAnd4
      (codeList3TermAt (liftTerm 3 certificate)
        (Term.numeral 0) (tVar 2) (tVar 1))
      (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0))
      (proofRuleCoverageTermAt (tVar 1))
      (proofEndpointTermAt
        (tVar 1) (tVar 0) (liftTerm 3 target))).

Lemma raw_sat_codedPAProofOfTermAt_iff : forall
    (M : RawPAModel) e target certificate,
  raw_formula_sat M e (codedPAProofOfTermAt target certificate) <->
  RawCodedPAProofOf M
    (raw_term_eval M e target) (raw_term_eval M e certificate).
Proof.
  intros M e target certificate.
  unfold codedPAProofOfTermAt, RawCodedPAProofOf,
    restrictedPAEx3, restrictedPAAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codeList3TermAt_iff.
  setoid_rewrite raw_sat_codedPAAxiomWitnessContextTermAt_iff.
  setoid_rewrite raw_sat_proofRuleCoverageTermAt_iff.
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_three.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Existential closure over the proof certificate. *)
Definition codedPAProvabilityTermAt (target : term) : formula :=
  pEx (codedPAProofOfTermAt (liftTerm 1 target) (tVar 0)).

Lemma raw_sat_codedPAProvabilityTermAt_iff : forall
    (M : RawPAModel) e target,
  raw_formula_sat M e (codedPAProvabilityTermAt target) <->
  exists certificate : M,
    RawCodedPAProofOf M
      (raw_term_eval M e target) certificate.
Proof.
  intros M e target.
  unfold codedPAProvabilityTermAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProofOfTermAt_iff.
  split.
  - intros [certificate hcertificate]. exists certificate.
    rewrite raw_restrictedPA_eval_liftTerm_one in hcertificate.
    cbn [raw_term_eval scons] in hcertificate.
    exact hcertificate.
  - intros [certificate hcertificate]. exists certificate.
    rewrite raw_restrictedPA_eval_liftTerm_one.
    cbn [raw_term_eval scons]. exact hcertificate.
Qed.

(** Quotation of a fixed metatheoretic formula produces a closed standard
    provability sentence.  [sealPA] keeps closure insensitive to future
    implementation changes in the certificate formula. *)
Definition codedPAProvabilityFormula (phi : formula) : formula :=
  Formula.sealPA
    (codedPAProvabilityTermAt (Term.numeral (formulaCode phi))).

Theorem codedPAProvabilityFormula_sentence : forall phi,
  Formula.Sentence (codedPAProvabilityFormula phi).
Proof.
  intro phi. unfold codedPAProvabilityFormula.
  apply Formula.sealPA_sentence.
Qed.

(** Every ordinary standard PA derivation has a certificate in every raw PA
    model.  This is the adequacy direction needed for necessitation. *)
Theorem raw_codedPAProofOf_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnesses derivation,
  RawProofValid derivation ->
  rawContext derivation = map witnessedAxiom witnesses ->
  RawCodedPAProofOf M
    (rawQuotedFormulaCode M (rawConclusion derivation))
    (rawNumeralValue M
      (restrictedPAProofCode witnesses derivation)).
Proof.
  intros M hPA witnesses derivation hvalid hcontext.
  exists (rawQuotedPAAxiomWitnessList M witnesses),
    (rawQuotedProofCode M derivation),
    (rawQuotedContextCode M (map witnessedAxiom witnesses)).
  split.
  - unfold restrictedPAProofCode.
    rewrite rawQuotedPAAxiomWitnessList_standard by exact hPA.
    rewrite rawQuotedProofCode_standard by exact hPA.
    unfold rawCodeList3. symmetry.
    change (rawListCode M
      (map (rawNumeralValue M)
        [0; axiomWitnessListCode witnesses; rawProofCode derivation]) =
      rawNumeralValue M
        (listCode
          [0; axiomWitnessListCode witnesses; rawProofCode derivation])).
    apply rawListCode_standard. exact hPA.
  - repeat split.
    + apply raw_codedPAAxiomWitnessContext_standard. exact hPA.
    + exact (raw_quotedValidProof_rule_coverage M hPA
        derivation hvalid).
    + rewrite <- hcontext.
      exact (raw_quotedProof_endpoint M hPA derivation).
Qed.

(** Unpack the finite list of PA axioms hidden in [BProv], replace it by its
    explicit witness list, and quote a data-carrying proof tree. *)
Theorem raw_codedPAProofOf_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  Formula.BProv Formula.Ax_s [] phi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawNumeralValue M (formulaCode phi)) certificate.
Proof.
  intros M hPA phi (axioms & haxioms & hprov).
  rewrite app_nil_r in hprov.
  destruct (Ax_s_list_has_witnesses axioms haxioms)
    as [witnesses hwitnesses].
  rewrite <- hwitnesses in hprov.
  destruct (ProvTree_complete _ _ hprov) as [derivation _].
  exists (rawNumeralValue M
    (restrictedPAProofCode witnesses (rawOfProvTree derivation))).
  rewrite <- rawQuotedFormulaCode_standard by exact hPA.
  replace (rawQuotedFormulaCode M phi) with
    (rawQuotedFormulaCode M
      (rawConclusion (rawOfProvTree derivation))).
  2:{ rewrite rawOfProvTree_conclusion. reflexivity. }
  apply raw_codedPAProofOf_standard.
  - exact hPA.
  - apply RawProofValid_rawOfProvTree.
  - rewrite rawOfProvTree_context. reflexivity.
Qed.

Theorem codedPAProvabilityFormula_raw_valid_of_BProv : forall phi,
  Formula.BProv Formula.Ax_s [] phi ->
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e (codedPAProvabilityFormula phi).
Proof.
  intros phi hphi M hPA e.
  unfold codedPAProvabilityFormula.
  apply raw_formula_sat_sealPA_of_valid.
  intro e'.
  apply (proj2 (raw_sat_codedPAProvabilityTermAt_iff M e' _)).
  rewrite raw_term_eval_numeral.
  exact (raw_codedPAProofOf_of_BProv M hPA phi hphi).
Qed.

(** Concrete first derivability condition for the proof predicate above. *)
Theorem PA_BProv_codedPAProvability_of_BProv : forall phi,
  Formula.BProv Formula.Ax_s [] phi ->
  Formula.BProv Formula.Ax_s [] (codedPAProvabilityFormula phi).
Proof.
  intros phi hphi.
  apply PA_BProv_of_raw_valid.
  - apply codedPAProvabilityFormula_sentence.
  - exact (codedPAProvabilityFormula_raw_valid_of_BProv phi hphi).
Qed.

End PABoundedRawCodedPAProvability.
