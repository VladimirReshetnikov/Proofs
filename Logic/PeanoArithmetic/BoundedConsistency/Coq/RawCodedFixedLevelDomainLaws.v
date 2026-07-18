(**
  Constructor inversion for the two fixed-level hierarchy domains.

  A domain witness contains a rank traversal whose root may be a genuinely
  nonstandard formula code.  Consequently these facts cannot be obtained by
  decoding the root into a Rocq [formula] and recursing in the metatheory.
  We instead inspect the certified root row, use the proved injectivity of
  constructor codes to identify its shape, and restrict the same traversal
  to each strictly earlier child row.

  The resulting laws are the polarity bookkeeping needed by fixed-level
  truth scheduling and coherence.  In particular implication reverses the
  antecedent polarity, while an opposite quantifier consumes exactly one
  external hierarchy level.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaRankRealization RawCodedFixedLevelTruth.

Module PABoundedRawCodedFixedLevelDomainLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFixedLevelTruth.

(** A maximum is above each of its inputs in every PA model.  Keeping these
    two projections local avoids repeatedly exposing the disjunctive
    implementation of [RawMax] in the constructor proofs below. *)
Lemma raw_fixedLevel_max_left_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall out left right,
  RawMax M out left right -> rawLe M left out.
Proof.
  intros M hPA out left right [[hle ->] | [hle ->]].
  - exact hle.
  - exact (raw_rank_le_refl M hPA left).
Qed.

Lemma raw_fixedLevel_max_right_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall out left right,
  RawMax M out left right -> rawLe M right out.
Proof.
  intros M hPA out left right [[hle ->] | [hle ->]].
  - exact (raw_rank_le_refl M hPA right).
  - exact hle.
Qed.

(** Cancellation for weak inequalities between successors.  The raw order
    is represented by an additive gap; after commuting successor past that
    gap, injectivity of successor removes the common outer constructor. *)
Lemma raw_fixedLevel_succ_le_cancel : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right,
  rawLe M (raw_succ M left) (raw_succ M right) ->
  rawLe M left right.
Proof.
  intros M hPA left right [gap hgap].
  exists gap.
  apply (raw_succ_injective_syntax M hPA).
  rewrite <- raw_succ_add_pair by exact hPA.
  exact hgap.
Qed.

(** Expose the root shape while retaining the original traversal. *)
Lemma raw_codedFormulaRank_shape_view : forall (M : RawPAModel),
  forall root sigma pi,
  RawCodedFormulaRank M root sigma pi ->
  exists formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex (shape : RawCodedFormulaShape M),
    RawCodedFormulaRankTraversal M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi /\
    root = rawCodedFormulaShapeCode M shape /\
    RawCodedFormulaShapeRankRow M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      rootIndex shape sigma pi.
Proof.
  intros M root sigma pi
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal).
  pose proof (raw_codedFormulaRankTraversal_root_row M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal) as hrow.
  apply raw_codedFormulaRankTraversalRow_shape_iff in hrow.
  destruct hrow as [shape [hcode hshape]].
  exists formulaCode, formulaStep, sigmaCode, sigmaStep,
    piCode, piStep, bound, rootIndex, shape.
  split; [exact htraversal |].
  split; assumption.
Qed.

(** If the public root is already displayed with a particular constructor,
    injectivity forces the root-row view to use that very shape. *)
Lemma raw_codedFormulaRank_shape_at : forall (M : RawPAModel),
  RawPASatisfies M -> forall (wanted : RawCodedFormulaShape M) sigma pi,
  RawCodedFormulaRank M (rawCodedFormulaShapeCode M wanted) sigma pi ->
  exists formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex,
    RawCodedFormulaRankTraversal M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawCodedFormulaShapeCode M wanted) sigma pi /\
    RawCodedFormulaShapeRankRow M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      rootIndex wanted sigma pi.
Proof.
  intros M hPA wanted sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_view M
    (rawCodedFormulaShapeCode M wanted) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & actual &
     htraversal & hcode & hshape).
  assert (hactual : actual = wanted).
  {
    apply (rawCodedFormulaShapeCode_injective
      polynomialPairInjectivityProof M hPA).
    symmetry. exact hcode.
  }
  subst actual.
  exists formulaCode, formulaStep, sigmaCode, sigmaStep,
    piCode, piStep, bound, rootIndex.
  split; assumption.
Qed.

(** Constructor views additionally promote each child lookup to a public
    rank certificate.  Later domain lemmas therefore never depend on the
    private beta tables chosen by the parent certificate. *)
Lemma raw_codedFormulaRank_imp_view : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right sigma pi,
  RawCodedFormulaRank M (rawFormulaImpCode M left right) sigma pi ->
  exists leftSigma leftPi rightSigma rightPi,
    RawCodedFormulaRank M left leftSigma leftPi /\
    RawCodedFormulaRank M right rightSigma rightPi /\
    RawFormulaRankImp M sigma pi
      leftSigma leftPi rightSigma rightPi.
Proof.
  intros M hPA left right sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeImp left right) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal & hshape).
  cbn [RawCodedFormulaShapeRankRow] in hshape.
  destruct hshape as
    (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup & hequation).
  exists leftSigma, leftPi, rightSigma, rightPi.
  split.
  - exact (raw_rank_child_certificate M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawFormulaImpCode M left right) sigma pi
      htraversal leftIndex left leftSigma leftPi
      hleftIndex hleftLookup).
  - split.
    + exact (raw_rank_child_certificate M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaImpCode M left right) sigma pi
        htraversal rightIndex right rightSigma rightPi
        hrightIndex hrightLookup).
    + exact hequation.
Qed.

Lemma raw_codedFormulaRank_and_view : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right sigma pi,
  RawCodedFormulaRank M (rawFormulaAndCode M left right) sigma pi ->
  exists leftSigma leftPi rightSigma rightPi,
    RawCodedFormulaRank M left leftSigma leftPi /\
    RawCodedFormulaRank M right rightSigma rightPi /\
    RawFormulaRankAndOr M sigma pi
      leftSigma leftPi rightSigma rightPi.
Proof.
  intros M hPA left right sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeAnd left right) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal & hshape).
  cbn [RawCodedFormulaShapeRankRow] in hshape.
  destruct hshape as
    (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup & hequation).
  exists leftSigma, leftPi, rightSigma, rightPi.
  split.
  - exact (raw_rank_child_certificate M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawFormulaAndCode M left right) sigma pi
      htraversal leftIndex left leftSigma leftPi
      hleftIndex hleftLookup).
  - split.
    + exact (raw_rank_child_certificate M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaAndCode M left right) sigma pi
        htraversal rightIndex right rightSigma rightPi
        hrightIndex hrightLookup).
    + exact hequation.
Qed.

Lemma raw_codedFormulaRank_or_view : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right sigma pi,
  RawCodedFormulaRank M (rawFormulaOrCode M left right) sigma pi ->
  exists leftSigma leftPi rightSigma rightPi,
    RawCodedFormulaRank M left leftSigma leftPi /\
    RawCodedFormulaRank M right rightSigma rightPi /\
    RawFormulaRankAndOr M sigma pi
      leftSigma leftPi rightSigma rightPi.
Proof.
  intros M hPA left right sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeOr left right) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal & hshape).
  cbn [RawCodedFormulaShapeRankRow] in hshape.
  destruct hshape as
    (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
     hleftIndex & hleftLookup & hrightIndex & hrightLookup & hequation).
  exists leftSigma, leftPi, rightSigma, rightPi.
  split.
  - exact (raw_rank_child_certificate M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawFormulaOrCode M left right) sigma pi
      htraversal leftIndex left leftSigma leftPi
      hleftIndex hleftLookup).
  - split.
    + exact (raw_rank_child_certificate M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaOrCode M left right) sigma pi
        htraversal rightIndex right rightSigma rightPi
        hrightIndex hrightLookup).
    + exact hequation.
Qed.

Lemma raw_codedFormulaRank_all_view : forall (M : RawPAModel),
  RawPASatisfies M -> forall child sigma pi,
  RawCodedFormulaRank M (rawFormulaAllCode M child) sigma pi ->
  exists childSigma childPi,
    RawCodedFormulaRank M child childSigma childPi /\
    RawFormulaRankAll M sigma pi childSigma childPi.
Proof.
  intros M hPA child sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeAll child) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal & hshape).
  cbn [RawCodedFormulaShapeRankRow] in hshape.
  destruct hshape as
    (childIndex & childSigma & childPi &
     hchildIndex & hchildLookup & hequation).
  exists childSigma, childPi. split.
  - exact (raw_rank_child_certificate M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawFormulaAllCode M child) sigma pi
      htraversal childIndex child childSigma childPi
      hchildIndex hchildLookup).
  - exact hequation.
Qed.

Lemma raw_codedFormulaRank_ex_view : forall (M : RawPAModel),
  RawPASatisfies M -> forall child sigma pi,
  RawCodedFormulaRank M (rawFormulaExCode M child) sigma pi ->
  exists childSigma childPi,
    RawCodedFormulaRank M child childSigma childPi /\
    RawFormulaRankEx M sigma pi childSigma childPi.
Proof.
  intros M hPA child sigma pi hrank.
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeEx child) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal & hshape).
  cbn [RawCodedFormulaShapeRankRow] in hshape.
  destruct hshape as
    (childIndex & childSigma & childPi &
     hchildIndex & hchildLookup & hequation).
  exists childSigma, childPi. split.
  - exact (raw_rank_child_certificate M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex (rawFormulaExCode M child) sigma pi
      htraversal childIndex child childSigma childPi
      hchildIndex hchildLookup).
  - exact hequation.
Qed.

(** ------------------------------------------------------------------
    Domain inversion for Boolean constructors. *)

Theorem raw_fixedLevelSigmaDomain_imp : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelSigmaDomain M level (rawFormulaImpCode M left right) ->
  RawFixedLevelPiDomain M level left /\
  RawFixedLevelSigmaDomain M level right.
Proof.
  intros M hPA level left right
    (sigma & pi & hrank & hsigmaBound).
  destruct (raw_codedFormulaRank_imp_view M hPA
    left right sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
     hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftPi sigma
      (rawNumeralValue M level)
      (raw_fixedLevel_max_left_le M hPA
        sigma leftPi rightSigma hsigmaMax) hsigmaBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightSigma sigma
      (rawNumeralValue M level)
      (raw_fixedLevel_max_right_le M hPA
        sigma leftPi rightSigma hsigmaMax) hsigmaBound).
Qed.

Theorem raw_fixedLevelPiDomain_imp : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelPiDomain M level (rawFormulaImpCode M left right) ->
  RawFixedLevelSigmaDomain M level left /\
  RawFixedLevelPiDomain M level right.
Proof.
  intros M hPA level left right
    (sigma & pi & hrank & hpiBound).
  destruct (raw_codedFormulaRank_imp_view M hPA
    left right sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
     hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftSigma pi
      (rawNumeralValue M level)
      (raw_fixedLevel_max_left_le M hPA
        pi leftSigma rightPi hpiMax) hpiBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightPi pi
      (rawNumeralValue M level)
      (raw_fixedLevel_max_right_le M hPA
        pi leftSigma rightPi hpiMax) hpiBound).
Qed.

Lemma raw_fixedLevelSigmaDomain_and_or_from_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code left right,
  (forall sigma pi,
    RawCodedFormulaRank M code sigma pi ->
    exists leftSigma leftPi rightSigma rightPi,
      RawCodedFormulaRank M left leftSigma leftPi /\
      RawCodedFormulaRank M right rightSigma rightPi /\
      RawFormulaRankAndOr M sigma pi
        leftSigma leftPi rightSigma rightPi) ->
  RawFixedLevelSigmaDomain M level code ->
  RawFixedLevelSigmaDomain M level left /\
  RawFixedLevelSigmaDomain M level right.
Proof.
  intros M hPA level code left right hview
    (sigma & pi & hrank & hsigmaBound).
  destruct (hview sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
     hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftSigma sigma
      (rawNumeralValue M level)
      (raw_fixedLevel_max_left_le M hPA
        sigma leftSigma rightSigma hsigmaMax) hsigmaBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightSigma sigma
      (rawNumeralValue M level)
      (raw_fixedLevel_max_right_le M hPA
        sigma leftSigma rightSigma hsigmaMax) hsigmaBound).
Qed.

Lemma raw_fixedLevelPiDomain_and_or_from_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code left right,
  (forall sigma pi,
    RawCodedFormulaRank M code sigma pi ->
    exists leftSigma leftPi rightSigma rightPi,
      RawCodedFormulaRank M left leftSigma leftPi /\
      RawCodedFormulaRank M right rightSigma rightPi /\
      RawFormulaRankAndOr M sigma pi
        leftSigma leftPi rightSigma rightPi) ->
  RawFixedLevelPiDomain M level code ->
  RawFixedLevelPiDomain M level left /\
  RawFixedLevelPiDomain M level right.
Proof.
  intros M hPA level code left right hview
    (sigma & pi & hrank & hpiBound).
  destruct (hview sigma pi hrank) as
    (leftSigma & leftPi & rightSigma & rightPi &
     hleftRank & hrightRank & [hsigmaMax hpiMax]).
  split.
  - exists leftSigma, leftPi. split; [exact hleftRank |].
    exact (raw_le_trans M hPA leftPi pi
      (rawNumeralValue M level)
      (raw_fixedLevel_max_left_le M hPA
        pi leftPi rightPi hpiMax) hpiBound).
  - exists rightSigma, rightPi. split; [exact hrightRank |].
    exact (raw_le_trans M hPA rightPi pi
      (rawNumeralValue M level)
      (raw_fixedLevel_max_right_le M hPA
        pi leftPi rightPi hpiMax) hpiBound).
Qed.

Theorem raw_fixedLevelSigmaDomain_and : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelSigmaDomain M level (rawFormulaAndCode M left right) ->
  RawFixedLevelSigmaDomain M level left /\
  RawFixedLevelSigmaDomain M level right.
Proof.
  intros M hPA level left right.
  apply (raw_fixedLevelSigmaDomain_and_or_from_view M hPA level
    (rawFormulaAndCode M left right) left right).
  exact (raw_codedFormulaRank_and_view M hPA left right).
Qed.

Theorem raw_fixedLevelPiDomain_and : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelPiDomain M level (rawFormulaAndCode M left right) ->
  RawFixedLevelPiDomain M level left /\
  RawFixedLevelPiDomain M level right.
Proof.
  intros M hPA level left right.
  apply (raw_fixedLevelPiDomain_and_or_from_view M hPA level
    (rawFormulaAndCode M left right) left right).
  exact (raw_codedFormulaRank_and_view M hPA left right).
Qed.

Theorem raw_fixedLevelSigmaDomain_or : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelSigmaDomain M level (rawFormulaOrCode M left right) ->
  RawFixedLevelSigmaDomain M level left /\
  RawFixedLevelSigmaDomain M level right.
Proof.
  intros M hPA level left right.
  apply (raw_fixedLevelSigmaDomain_and_or_from_view M hPA level
    (rawFormulaOrCode M left right) left right).
  exact (raw_codedFormulaRank_or_view M hPA left right).
Qed.

Theorem raw_fixedLevelPiDomain_or : forall (M : RawPAModel),
  RawPASatisfies M -> forall level left right,
  RawFixedLevelPiDomain M level (rawFormulaOrCode M left right) ->
  RawFixedLevelPiDomain M level left /\
  RawFixedLevelPiDomain M level right.
Proof.
  intros M hPA level left right.
  apply (raw_fixedLevelPiDomain_and_or_from_view M hPA level
    (rawFormulaOrCode M left right) left right).
  exact (raw_codedFormulaRank_or_view M hPA left right).
Qed.

(** ------------------------------------------------------------------
    Quantifier-domain inversion. *)

Theorem raw_fixedLevelSigmaDomain_all_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall level child,
  RawFixedLevelSigmaDomain M (S level) (rawFormulaAllCode M child) ->
  RawFixedLevelPiDomain M level child.
Proof.
  intros M hPA level child
    (sigma & pi & hrank & hsigmaBound).
  destruct (raw_codedFormulaRank_all_view M hPA child sigma pi hrank) as
    (childSigma & childPi & hchildRank &
     base & hbaseMax & hpi & hsigma).
  subst pi. subst sigma.
  exists childSigma, childPi. split; [exact hchildRank |].
  apply (raw_le_trans M hPA childPi base (rawNumeralValue M level)).
  - exact (raw_fixedLevel_max_right_le M hPA
      base (rawNumeralValue M 1) childPi hbaseMax).
  - apply (raw_fixedLevel_succ_le_cancel M hPA).
    change (rawLe M (raw_succ M base)
      (rawNumeralValue M (S level))) in hsigmaBound.
    exact hsigmaBound.
Qed.

Theorem raw_fixedLevelPiDomain_all : forall (M : RawPAModel),
  RawPASatisfies M -> forall level child,
  RawFixedLevelPiDomain M level (rawFormulaAllCode M child) ->
  RawFixedLevelPiDomain M level child.
Proof.
  intros M hPA level child
    (sigma & pi & hrank & hpiBound).
  destruct (raw_codedFormulaRank_all_view M hPA child sigma pi hrank) as
    (childSigma & childPi & hchildRank &
     base & hbaseMax & hpi & hsigma).
  subst pi. subst sigma.
  exists childSigma, childPi. split; [exact hchildRank |].
  exact (raw_le_trans M hPA childPi base
    (rawNumeralValue M level)
    (raw_fixedLevel_max_right_le M hPA
      base (rawNumeralValue M 1) childPi hbaseMax) hpiBound).
Qed.

Theorem raw_fixedLevelSigmaDomain_ex : forall (M : RawPAModel),
  RawPASatisfies M -> forall level child,
  RawFixedLevelSigmaDomain M level (rawFormulaExCode M child) ->
  RawFixedLevelSigmaDomain M level child.
Proof.
  intros M hPA level child
    (sigma & pi & hrank & hsigmaBound).
  destruct (raw_codedFormulaRank_ex_view M hPA child sigma pi hrank) as
    (childSigma & childPi & hchildRank &
     base & hbaseMax & hsigma & hpi).
  subst sigma. subst pi.
  exists childSigma, childPi. split; [exact hchildRank |].
  exact (raw_le_trans M hPA childSigma base
    (rawNumeralValue M level)
    (raw_fixedLevel_max_right_le M hPA
      base (rawNumeralValue M 1) childSigma hbaseMax) hsigmaBound).
Qed.

Theorem raw_fixedLevelPiDomain_ex_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall level child,
  RawFixedLevelPiDomain M (S level) (rawFormulaExCode M child) ->
  RawFixedLevelSigmaDomain M level child.
Proof.
  intros M hPA level child
    (sigma & pi & hrank & hpiBound).
  destruct (raw_codedFormulaRank_ex_view M hPA child sigma pi hrank) as
    (childSigma & childPi & hchildRank &
     base & hbaseMax & hsigma & hpi).
  subst sigma. subst pi.
  exists childSigma, childPi. split; [exact hchildRank |].
  apply (raw_le_trans M hPA childSigma base (rawNumeralValue M level)).
  - exact (raw_fixedLevel_max_right_le M hPA
      base (rawNumeralValue M 1) childSigma hbaseMax).
  - apply (raw_fixedLevel_succ_le_cancel M hPA).
    change (rawLe M (raw_succ M base)
      (rawNumeralValue M (S level))) in hpiBound.
    exact hpiBound.
Qed.

End PABoundedRawCodedFixedLevelDomainLaws.
