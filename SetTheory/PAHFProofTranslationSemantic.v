(* ===================================================================== *)
(*  PAHFProofTranslationSemantic.v                                      *)
(*                                                                       *)
(*  Semantic closure of the raw PA-to-HFFin proof translation.          *)
(*                                                                       *)
(*  A finite domain prefix supplies ordinal representatives for every    *)
(*  free variable in the conclusion and assumptions.  Raw PA soundness  *)
(*  then transports a derivation through the term-graph semantics, and   *)
(*  relative completeness returns the desired HFFin derivation.          *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFInterpretations PAHFRawSemantics PAHFRawSemanticsGraph
  PAHFTermGraphFunctional.

Import ListNotations.

(* A single prefix large enough for the free variables of every formula
   in a finite PA context. *)
Fixpoint PAContextBound (G : list PA.formula) : nat :=
  match G with
  | [] => 0
  | psi :: tail => PA.Formula.bound psi + PAContextBound tail
  end.

Lemma PAContextBound_ge : forall G psi,
  In psi G -> PA.Formula.bound psi <= PAContextBound G.
Proof.
  induction G as [|a G IH]; intros psi hpsi; simpl in *.
  - contradiction.
  - destruct hpsi as [hpsi | hpsi].
    + subst psi. lia.
    + pose proof (IH psi hpsi). lia.
Qed.

(* Functionality of translated term graphs is exactly the semantic law
   isolated by the raw-formula bridge. *)
Theorem FOFAMTermGraphFunctionalLaw_finite_model :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  FOFAMTermGraphFunctionalLaw M.
Proof.
  intros V M.
  unfold FOFAMTermGraphFunctionalLaw.
  exact (termGraphAt_outputs_eq V M).
Qed.

Theorem HFFinPAProofTranslation_raw_semantic :
  HFFinPAProofTranslation.
Proof.
  unfold HFFinPAProofTranslation.
  intros G phi hp.
  set (n := PA.Formula.bound phi + PAContextBound G).
  exists n. intro rho.
  apply completeness_inf_context.
  - exact Sentences_HFFin.
  - intros V mem e hHF hctx.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem e hHF).
    assert (hdomain : forall g,
        In g (domainContextAt rho n) -> Sat V mem e g).
    {
      intros g hg.
      apply hctx.
      apply in_app_iff. now left.
    }
    assert (hord : forall k, k < n ->
        OrdinalLike mem (e (rho k))).
    {
      exact (Sat_domainContextAt_ordinalLike V mem rho n e hdomain).
    }
    assert (hordM : forall k, k < n ->
        OrdinalLike (foam_mem V M) (e (rho k))).
    {
      intros k hk.
      change (OrdinalLike mem (e (rho k))).
      exact (hord k hk).
    }
    pose (vord := fun k =>
      match lt_dec k n with
      | left hk => exist _ (e (rho k)) (hordM k hk)
      | right _ => fofamOrdinalZero M
      end).
    assert (hvord : forall k, k < n ->
        proj1_sig (vord k) = e (rho k)).
    {
      intros k hk.
      unfold vord.
      destruct (lt_dec k n); [reflexivity | lia].
    }
    assert (hphiVars : forall k, PA.Formula.Free k phi ->
        e (rho k) = proj1_sig (vord k)).
    {
      intros k hk.
      symmetry. apply hvord.
      unfold n.
      pose proof (PA.Formula.free_lt_bound phi k hk).
      lia.
    }
    change (Sat V (foam_mem V M) e (formulaAt rho phi)).
    apply (proj2 (formulaAt_iff_fofamPAFormulaSat
      V M (FOFAMTermGraphFunctionalLaw_finite_model V M)
      phi rho e vord hphiVars)).
    apply (fofam_PA_Prov_soundness V M G phi hp vord).
    intros psi hpsi.
    assert (hpsiVars : forall k, PA.Formula.Free k psi ->
        e (rho k) = proj1_sig (vord k)).
    {
      intros k hk.
      symmetry. apply hvord.
      unfold n.
      pose proof (PA.Formula.free_lt_bound psi k hk).
      pose proof (PAContextBound_ge G psi hpsi).
      lia.
    }
    apply (proj1 (formulaAt_iff_fofamPAFormulaSat
      V M (FOFAMTermGraphFunctionalLaw_finite_model V M)
      psi rho e vord hpsiVars)).
    apply hctx.
    apply in_app_iff. right.
    unfold translateContextAt.
    apply in_map. exact hpsi.
Qed.
