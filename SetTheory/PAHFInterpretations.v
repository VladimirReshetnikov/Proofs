(* ===================================================================== *)
(*  PAHFInterpretations.v                                                *)
(*                                                                       *)
(*  Compact assembly layer for the deductive PA -> HFFin interpretation. *)
(*  The sole residual below is the structural translation of a raw PA     *)
(*  derivation while carrying a finite prefix of ordinal-domain facts.    *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From SetTheory Require Import Fol Calculus Completeness PAHF.
Import ListNotations.

(* Instantiating the translated PA domain formula at a slot says exactly
   that the object in that slot is ordinal-like. *)
Lemma Sat_rename_inst_domainForm_ordinalLike :
  forall (V : Type) (mem : V -> V -> Prop) (e : nat -> V) k,
  Sat V mem e (rename (inst k) domainForm) <-> OrdinalLike mem (e k).
Proof.
  intros V mem e k.
  rewrite (Sat_rename V mem domainForm (inst k) e).
  change (Sat V mem (fun n => e (inst k n)) (HF_ordinalLikeAt 0) <->
    OrdinalLike mem (e k)).
  pose proof (HF_ordinalLikeAt_spec V mem (fun n => e (inst k n)) 0) as h.
  simpl in h.
  exact h.
Qed.

(* The explicit domain context supplies ordinal-like values for all selected
   PA variables below its bound. *)
Lemma Sat_domainContextAt_ordinalLike :
  forall (V : Type) (mem : V -> V -> Prop)
    (rho : nat -> nat) n (e : nat -> V),
  (forall g, In g (domainContextAt rho n) -> Sat V mem e g) ->
  forall k, k < n -> OrdinalLike mem (e (rho k)).
Proof.
  intros V mem rho n e hctx k hk.
  apply (proj1 (Sat_rename_inst_domainForm_ordinalLike
    V mem e (rho k))).
  apply hctx.
  apply mem_domainContextAt.
  exact hk.
Qed.

(* Conversely, ordinal-likeness of the selected variables validates the
   explicit domain context. *)
Lemma Sat_domainContextAt_of_ordinalLike :
  forall (V : Type) (mem : V -> V -> Prop)
    (rho : nat -> nat) n (e : nat -> V),
  (forall k, k < n -> OrdinalLike mem (e (rho k))) ->
  forall g, In g (domainContextAt rho n) -> Sat V mem e g.
Proof.
  intros V mem rho n.
  revert rho.
  induction n as [|n IH]; intros rho e hord g hg.
  - simpl in hg. contradiction.
  - simpl in hg.
    destruct hg as [hg | hg].
    + subst g.
      apply (proj2 (Sat_rename_inst_domainForm_ordinalLike
        V mem e (rho 0))).
      apply hord. lia.
    + apply (IH (fun k => rho (S k)) e).
      * intros k hk.
        apply hord. lia.
      * exact hg.
Qed.

(* Soundness for the generic bounded theory wrapper.  Completeness.v exposes
   BProv as a finite axiom list plus a raw natural-deduction derivation; this
   lemma is the corresponding semantic eliminator. *)
Lemma soundness_BProv_FOL :
  forall (V : Type) (mem : V -> V -> Prop)
    (B : form -> Prop) G phi,
  BProv B G phi ->
  forall e,
    (forall b, B b -> Sat V mem e b) ->
    (forall g, In g G -> Sat V mem e g) ->
    Sat V mem e phi.
Proof.
  intros V mem B G phi [L [hL hp]] e hB hG.
  apply (soundness V mem (L ++ G) phi hp e).
  intros x hx.
  apply in_app_iff in hx.
  destruct hx as [hx | hx].
  - apply hB. apply hL. exact hx.
  - apply hG. exact hx.
Qed.

(* This is the exact remaining proof-structural obligation before the compact
   endpoint below becomes unconditional.  Its intended inhabitant is the Coq
   port of Lean's BProv_HFFin_formulaAt_of_Prov_domainContext. *)
Definition HFFinPAProofTranslation : Prop :=
  forall (G : list PA.formula) (phi : PA.formula),
  PA.Formula.Prov G phi ->
  exists n, forall rho : nat -> nat,
    BProv HFFinAx_s
      (domainContextAt rho n ++ translateContextAt rho G)
      (formulaAt rho phi).

(* Cut the finite PA axiom list out of a domain-context translation. *)
Lemma BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation :
  HFFinPAProofTranslation ->
  forall (G : list PA.formula) (phi : PA.formula),
  PA.Formula.BProv PA.Formula.Ax_s G phi ->
  exists n, forall rho : nat -> nat,
    BProv HFFinAx_s
      (domainContextAt rho n ++ translateContextAt rho G)
      (formulaAt rho phi).
Proof.
  intros htranslate G phi [L [hL hp]].
  destruct (htranslate (L ++ G) phi hp) as [n htranslated].
  exists n. intro rho.
  apply (BProv_lift HFFinAx_s HFFinAx_s
    (domainContextAt rho n ++ translateContextAt rho (L ++ G))
    (domainContextAt rho n ++ translateContextAt rho G)
    (formulaAt rho phi) (htranslated rho)).
  - intros b hb. apply BProv_ax. exact hb.
  - intros g hg.
    apply in_app_iff in hg.
    destruct hg as [hgDomain | hgTranslated].
    + apply BProv_of_Prov.
      apply P_ass.
      apply in_app_iff. left. exact hgDomain.
    + unfold translateContextAt in hgTranslated.
      rewrite map_app in hgTranslated.
      apply in_app_iff in hgTranslated.
      destruct hgTranslated as [hgAx | hgCtx].
      * apply in_map_iff in hgAx.
        destruct hgAx as [psi [hg hpsi]].
        subst g.
        assert (hpsiAx : PA.Formula.Ax_s psi) by
          (apply hL; exact hpsi).
        pose proof (BProv_HFFin_translated_PA_axiom psi hpsiAx) as hax.
        apply (BProv_mono HFFinAx_s []
          (domainContextAt rho n ++ translateContextAt rho G)
          (formulaAt rho psi)).
        -- intros x hx. contradiction.
        -- rewrite (formulaAt_eq_translateFormula_of_PA_sentence psi rho).
           ++ exact hax.
           ++ apply PA.Formula.sentence_ax_s. exact hpsiAx.
      * apply BProv_of_Prov.
        apply P_ass.
        apply in_app_iff. right.
        unfold translateContextAt.
        exact hgCtx.
Qed.

(* Closed PA theorems need no surviving domain assumptions.  A constant-empty
   assignment satisfies the finite domain prefix in every HFFin model, and
   sentence invariance transports the result to the arbitrary assignment used
   by completeness. *)
Lemma BProv_HFFin_translateFormula_of_PA_BProv_of_translation :
  HFFinPAProofTranslation ->
  forall phi : PA.formula,
  PA.Formula.Sentence phi ->
  PA.Formula.BProv PA.Formula.Ax_s [] phi ->
  BProv HFFinAx_s [] (translateFormula phi).
Proof.
  intros htranslate phi hphi hprov.
  destruct (BProv_HFFin_formulaAt_of_PA_BProv_domainContext_of_translation
    htranslate [] phi hprov) as [n htranslated].
  apply completeness_inf.
  - exact Sentences_HFFin.
  - apply translateFormula_sentence_of_PA_sentence. exact hphi.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    pose (e0 := fun _ : nat => foam_empty V M).
    assert (hEmptyOrd : OrdinalLike mem (foam_empty V M)).
    {
      change (OrdinalLike (foam_mem V M) (foam_empty V M)).
      apply foam_OrdinalLike_empty.
    }
    assert (hdomain : forall g,
      In g (domainContextAt (fun k => k) n) -> Sat V mem e0 g).
    {
      apply Sat_domainContextAt_of_ordinalLike.
      intros k hk. exact hEmptyOrd.
    }
    assert (hcontext : forall g,
      In g (domainContextAt (fun k => k) n ++
        translateContextAt (fun k => k) []) -> Sat V mem e0 g).
    {
      intros g hg.
      unfold translateContextAt in hg.
      rewrite app_nil_r in hg.
      exact (hdomain g hg).
    }
    assert (hHF0 : forall g, HFFinAx_s g -> Sat V mem e0 g).
    {
      intros g hg.
      apply (proj1 (Sat_sentence_inv V mem g
        (Sentences_HFFin g hg) v e0)).
      exact (hHF g hg).
    }
    pose proof (soundness_BProv_FOL V mem HFFinAx_s
      (domainContextAt (fun k => k) n ++
        translateContextAt (fun k => k) [])
      (formulaAt (fun k => k) phi)
      (htranslated (fun k => k)) e0 hHF0 hcontext) as hsat.
    rewrite (formulaAt_eq_translateFormula_of_PA_sentence
      phi (fun k => k) hphi) in hsat.
    apply (proj1 (Sat_sentence_inv V mem (translateFormula phi)
      (translateFormula_sentence_of_PA_sentence phi hphi) e0 v)).
    exact hsat.
Qed.

(* The direct PA -> HFFin theory interpretation, parameterized only by the
   exact structural proof-translation residual named above. *)
Definition paInHFFinTheoryInterpretation_of_translation
    (htranslate : HFFinPAProofTranslation) :
  TheoryInterpretation PA.formula form
    PA.Formula.Sentence Sentence
    PA.Formula.Ax_s HFFinAx_s
    PA.Formula.BProv BProv.
Proof.
  refine {| ti_translate := translateFormula |}.
  - intros phi hphi.
    apply translateFormula_sentence_of_PA_sentence. exact hphi.
  - intros phi hphi.
    exact (BProv_HFFin_translated_PA_axiom phi hphi).
  - intros phi hsent hprov.
    exact (BProv_HFFin_translateFormula_of_PA_BProv_of_translation
      htranslate phi hsent hprov).
Defined.
