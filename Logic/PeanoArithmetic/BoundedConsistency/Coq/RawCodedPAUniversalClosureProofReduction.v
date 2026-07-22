(**
  Model-internal reduction of a proof of an iterated universal closure.

  A host-language induction over [nat] cannot traverse a nonstandard closure
  count.  This file instead packages proof reducibility as a represented PA
  predicate and applies [raw_definable_induction] in the arbitrary model.

  The invariant quantifies over the context and the incoming proof root.  At
  a successor it first builds the exact [RP_allE] root supplied by
  [raw_codedPALocalProofOf_universalClosure_prefix_step], then passes that
  root directly to the induction hypothesis.  This is why no generic proof-
  tree weakening or context transformer is required.

  The only syntax-side input is a bounded family of represented
  self-substitution certificates for closure prefixes.  It is an operation
  graph, not a proof-producing callback; later formula-specific code may
  realize it by a renaming/substitution traversal.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedProofAllEConstructor RawCodedPALocalProofExistential
  RawCodedPAUniversalClosurePrefixElimination.

Module PABoundedRawCodedPAUniversalClosureProofReduction.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAUniversalClosurePrefixElimination.

(** The local-proof package already used by proof constructors, exposed as a
    formula so it may occur inside the represented induction invariant. *)
Definition codedPALocalProofOfTermAt
    (context target proof : term) : formula :=
  pAnd
    (proofRuleCoverageTermAt proof)
    (proofEndpointTermAt proof context target).

Lemma raw_sat_codedPALocalProofOfTermAt_iff : forall
    (M : RawPAModel) e context target proof,
  raw_formula_sat M e
    (codedPALocalProofOfTermAt context target proof) <->
  RawCodedPALocalProofOf M
    (raw_term_eval M e context)
    (raw_term_eval M e target)
    (raw_term_eval M e proof).
Proof.
  intros. unfold codedPALocalProofOfTermAt, RawCodedPALocalProofOf.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofRuleCoverageTermAt_iff,
    raw_sat_proofEndpointTermAt_iff.
  reflexivity.
Qed.

(** Every strict prefix below [limit] may be opened with one fixed
    replacement without changing that prefix.  This is precisely the graph
    fact consumed at the successor step [S current <= limit]. *)
Definition RawCodedUniversalClosureSelfInstantiationThrough
    (M : RawPAModel) (replacement body limit : M) : Prop :=
  forall count prefix : M,
    rawLt M count limit ->
    RawCodedUniversalClosure M count body prefix ->
    RawCodedFormulaSingleSubstitution M replacement prefix prefix.

Arguments RawCodedUniversalClosureSelfInstantiationThrough
  M replacement body limit : clear implicits.

Definition codedUniversalClosureSelfInstantiationThroughTermAt
    (replacement body limit : term) : formula :=
  pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 1) (liftTerm 2 limit))
      (pImp
        (codedUniversalClosureTermAt
          (tVar 1) (liftTerm 2 body) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          (liftTerm 2 replacement) (tVar 0) (tVar 0))))).

Lemma raw_sat_codedUniversalClosureSelfInstantiationThroughTermAt_iff :
    forall (M : RawPAModel) e replacement body limit,
  raw_formula_sat M e
    (codedUniversalClosureSelfInstantiationThroughTermAt
      replacement body limit) <->
  RawCodedUniversalClosureSelfInstantiationThrough M
    (raw_term_eval M e replacement)
    (raw_term_eval M e body)
    (raw_term_eval M e limit).
Proof.
  intros M e replacement body limit.
  unfold codedUniversalClosureSelfInstantiationThroughTermAt,
    RawCodedUniversalClosureSelfInstantiationThrough.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedUniversalClosureTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  cbn [raw_term_eval scons]. split.
  - intros h count prefix hlt hclosure.
    specialize (h count prefix).
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e limit) in h.
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e body) in h.
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e replacement) in h.
    exact (h hlt hclosure).
  - intros h count prefix hlt hclosure.
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e limit) in hlt.
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e body) in hclosure.
    rewrite (raw_rankTraversal_eval_liftTerm_two
      M prefix count e replacement).
    exact (h count prefix hlt hclosure).
Qed.

(** At one count, every local proof of the corresponding closure can be
    reduced to a local proof of the original body in exactly the same
    context. *)
Definition RawCodedUniversalClosureProofReducibleAt
    (M : RawPAModel) (body count : M) : Prop :=
  forall context closureFormula closureProof : M,
    RawCodedUniversalClosure M count body closureFormula ->
    RawCodedPALocalProofOf M context closureFormula closureProof ->
    exists reducedProof : M,
      RawCodedPALocalProofOf M context body reducedProof.

Arguments RawCodedUniversalClosureProofReducibleAt
  M body count : clear implicits.

Definition codedUniversalClosureProofReducibleAtTermAt
    (body count : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (codedUniversalClosureTermAt
        (liftTerm 3 count) (liftTerm 3 body) (tVar 1))
      (pImp
        (codedPALocalProofOfTermAt (tVar 2) (tVar 1) (tVar 0))
        (pEx
          (codedPALocalProofOfTermAt
            (liftTerm 1 (tVar 2))
            (liftTerm 1 (liftTerm 3 body))
            (tVar 0))))))).

Lemma raw_sat_codedUniversalClosureProofReducibleAtTermAt_iff : forall
    (M : RawPAModel) e body count,
  raw_formula_sat M e
    (codedUniversalClosureProofReducibleAtTermAt body count) <->
  RawCodedUniversalClosureProofReducibleAt M
    (raw_term_eval M e body) (raw_term_eval M e count).
Proof.
  intros M e body count.
  unfold codedUniversalClosureProofReducibleAtTermAt,
    RawCodedUniversalClosureProofReducibleAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedUniversalClosureTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofOfTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons].
  split; intros h context closureFormula closureProof hclosure hproof;
    destruct (h context closureFormula closureProof hclosure hproof)
      as [reducedProof hreduced];
    exists reducedProof.
  - rewrite (raw_operation_eval_liftTerm_one M reducedProof
      (scons M closureProof
        (scons M closureFormula (scons M context e)))
      (liftTerm 3 body)) in hreduced.
    rewrite (raw_operation_eval_liftTerm_three M
      closureProof closureFormula context e body) in hreduced.
    cbn [raw_term_eval scons] in hreduced.
    exact hreduced.
  - rewrite (raw_operation_eval_liftTerm_one M reducedProof
      (scons M closureProof
        (scons M closureFormula (scons M context e)))
      (liftTerm 3 body)).
    rewrite (raw_operation_eval_liftTerm_three M
      closureProof closureFormula context e body).
    cbn [raw_term_eval scons].
    exact hreduced.
Qed.

(** Guarding reducibility by [current <= limit] lets definable induction run
    over the entire model while consuming self-instantiation certificates
    only below the requested finite (possibly nonstandard) limit. *)
Definition RawCodedUniversalClosureProofReducibleWithin
    (M : RawPAModel) (body limit current : M) : Prop :=
  rawLe M current limit ->
  RawCodedUniversalClosureProofReducibleAt M body current.

Arguments RawCodedUniversalClosureProofReducibleWithin
  M body limit current : clear implicits.

Definition codedUniversalClosureProofReducibleWithinTermAt
    (body limit current : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (codedUniversalClosureProofReducibleAtTermAt body current).

Lemma raw_sat_codedUniversalClosureProofReducibleWithinTermAt_iff : forall
    (M : RawPAModel) e body limit current,
  raw_formula_sat M e
    (codedUniversalClosureProofReducibleWithinTermAt body limit current) <->
  RawCodedUniversalClosureProofReducibleWithin M
    (raw_term_eval M e body)
    (raw_term_eval M e limit)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedUniversalClosureProofReducibleWithinTermAt,
    RawCodedUniversalClosureProofReducibleWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedUniversalClosureProofReducibleAtTermAt_iff.
  reflexivity.
Qed.

(** The arbitrary model-coded unsealing orbit. *)
Theorem raw_codedUniversalClosureProofReducibleWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body limit,
  RawCodedUniversalClosureSelfInstantiationThrough
    M replacement body limit ->
  forall current,
    RawCodedUniversalClosureProofReducibleWithin M body limit current.
Proof.
  intros M hPA replacement body limit hself.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => body
    | _ => limit
    end).
  set (phi := codedUniversalClosureProofReducibleWithinTermAt
    (tVar 1) (tVar 2) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedUniversalClosureProofReducibleWithinTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _ context closureFormula closureProof hclosure hproof.
      pose proof (raw_codedUniversalClosure_zero M hPA
        body closureFormula hclosure) as hformula.
      subst closureFormula. exists closureProof. exact hproof.
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedUniversalClosureProofReducibleWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 0)) hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedUniversalClosureProofReducibleWithinTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intros hsuccessorLe context closureFormula closureProof
        hclosure hproof.
      assert (hcurrentLt : rawLt M current limit).
      {
        exact (raw_rank_lt_of_succ_le M hPA
          current limit hsuccessorLe).
      }
      assert (hcurrentLe : rawLe M current limit).
      { exact (raw_lt_to_le M current limit hcurrentLt). }
      destruct (raw_codedUniversalClosure_succ_inversion M hPA
        current body closureFormula hclosure) as
        [prefix [hprefix hformula]].
      assert (hsubstitution :
          RawCodedFormulaSingleSubstitution M
            replacement prefix prefix).
      { exact (hself current prefix hcurrentLt hprefix). }
      assert (hprefixProof : RawCodedPALocalProofOf M context prefix
          (rawProofAllERoot M context prefix replacement closureProof)).
      {
        exact (raw_codedPALocalProofOf_universalClosure_prefix_step
          M hPA current body closureFormula prefix replacement prefix
          context closureProof hclosure hprefix hsubstitution hproof).
      }
      exact (hcurrent hcurrentLe context prefix
        (rawProofAllERoot M context prefix replacement closureProof)
        hprefix hprefixProof).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedUniversalClosureProofReducibleWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 0)) (hall current)) as hresult.
  unfold parameterEnv in hresult.
  cbn [raw_term_eval scons] in hresult. exact hresult.
Qed.

Corollary raw_codedPALocalProofOf_universalClosure_reduce : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement body count context closureFormula closureProof,
  RawCodedUniversalClosureSelfInstantiationThrough
    M replacement body count ->
  RawCodedUniversalClosure M count body closureFormula ->
  RawCodedPALocalProofOf M context closureFormula closureProof ->
  exists reducedProof : M,
    RawCodedPALocalProofOf M context body reducedProof.
Proof.
  intros M hPA replacement body count context closureFormula closureProof
    hself hclosure hproof.
  pose proof (raw_codedUniversalClosureProofReducibleWithin_all
    M hPA replacement body count hself count) as hwithin.
  exact (hwithin (raw_rank_le_refl M hPA count)
    context closureFormula closureProof hclosure hproof).
Qed.

End PABoundedRawCodedPAUniversalClosureProofReduction.
