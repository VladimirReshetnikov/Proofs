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
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF
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

(* Every sealed PA axiom is true in the raw ordinal algebra extracted from
   an arbitrary finite-adjunction model.  This is deliberately stated for
   [fofamPAFormulaSat], rather than by packaging the algebra as [PA.Model]:
   the latter carries a meta-level induction field which is inappropriate
   for the nonstandard models used by the compactness argument. *)
Theorem fofam_PA_Ax_s_valid :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (phi : PA.formula) (e : nat -> FOFAMOrdinal M),
  PA.Formula.Ax_s phi -> fofamPAFormulaSat M e phi.
Proof.
  intros V M phi e hphi.
  apply (proj1 (formulaAt_iff_fofamPAFormulaSat
    V M (FOFAMTermGraphFunctionalLaw_finite_model V M)
    phi (fun n => n) (fun n => proj1_sig (e n)) e
    (fun n _hn => eq_refl))).
  unfold PA.Formula.Ax_s in hphi.
  destruct hphi as
    [hphi | [hphi | [hphi | [hphi | [hphi | [hphi | [psi hphi]]]]]]];
    subst phi;
    apply formulaAt_sealPA_valid;
    intros rho env.
  - apply formulaAt_succInj_of_irrefl.
    apply foam_mem_irrefl.
  - apply formulaAt_zeroNotSucc_valid.
  - apply formulaAt_addZero_valid_model.
  - apply formulaAt_addSucc_valid_finite_model.
  - apply formulaAt_mulZero_valid_model.
  - apply formulaAt_mulSucc_valid_finite_model.
  - apply formulaAt_induction_valid_finite_model.
Qed.

(* Consequently the ordinary finite-axiom wrapper is sound directly for the
   raw semantics.  This is the reusable form needed by later arbitrary-model
   arguments: no [PA.Model] instance and no extra arithmetic hypotheses are
   introduced. *)
Theorem fofam_PA_BProv_soundness :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    G phi,
  PA.Formula.BProv PA.Formula.Ax_s G phi ->
  forall e : nat -> FOFAMOrdinal M,
    (forall psi, In psi G -> fofamPAFormulaSat M e psi) ->
    fofamPAFormulaSat M e phi.
Proof.
  intros V M G phi [L [hL hp]] e hG.
  apply (fofam_PA_Prov_soundness V M (L ++ G) phi hp e).
  intros psi hpsi.
  apply in_app_iff in hpsi.
  destruct hpsi as [hpsi | hpsi].
  - apply fofam_PA_Ax_s_valid.
    exact (hL psi hpsi).
  - exact (hG psi hpsi).
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
    assert (hordM : forall k, k < n ->
        OrdinalLike (foam_mem V M) (e (rho k))).
    {
      intros k hk.
      change (OrdinalLike mem (e (rho k))).
      exact (Sat_domainContextAt_ordinalLike
        V mem rho n e hdomain k hk).
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
