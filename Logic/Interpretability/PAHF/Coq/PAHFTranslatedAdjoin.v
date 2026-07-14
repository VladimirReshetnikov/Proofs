(* ===================================================================== *)
(*  PAHFTranslatedAdjoin.v                                               *)
(*                                                                       *)
(*  PA proof of the Ackermann translation of HF adjunction.              *)
(* ===================================================================== *)

From Stdlib Require Import List.
From PAHF Require Import PAHF PAHFOrdinalCode PAHFOrdinalCodeTotalInduction PAHFAdjoinTotal.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** The exact PA body obtained by translating the unsealed HF adjunction
    axiom. *)
Definition translatedHFAdjoinBody : formula :=
  pAll (pAll (pEx (pAll
    (iffForm
      (hfMemAt 0 1)
      (pOr (hfMemAt 0 3)
        (pEq (tVar 0) (tVar 2))))))).

(** Translating the syntactic sealing of the HF axiom produces the
    corresponding PA [closeN] shell around its translated body. *)
Lemma translateHFFormula_sealed_adjoin :
  translateHFFormula (Fol.seal HF_adjoin_form) =
    PA.Formula.closeN (Fol.bound HF_adjoin_form)
      translatedHFAdjoinBody.
Proof.
  unfold translateHFFormula, Fol.seal, translatedHFAdjoinBody,
    HF_adjoin_form, Fol.closeN, Fol.bound, PA.Formula.closeN.
  simpl.
  reflexivity.
Qed.

(** Syntactic outer shell: a proof of the exact translated body proves the
    translation of the sealed HF axiom. *)
Lemma BProv_Ax_s_translated_HF_adjoin_of_body :
  BProv Ax_s [] translatedHFAdjoinBody ->
  BProv Ax_s []
    (translateHFFormula (Fol.seal HF_adjoin_form)).
Proof.
  intro hbody.
  rewrite translateHFFormula_sealed_adjoin.
  exact (BProv_closeN_nil_of_sentences Ax_s sentence_ax_s
    (Fol.bound HF_adjoin_form) translatedHFAdjoinBody hbody).
Qed.

(** PA-internal adjunction totality, instantiated at the two free inputs and
    followed by universal introduction, proves the translated body. *)
Lemma BProv_Ax_s_translatedHFAdjoinBody :
  BProv Ax_s [] translatedHFAdjoinBody.
Proof.
  pose proof
    (PAHFAdjoinExistence_proof [] (tVar 1) (tVar 0)) as hex.
  assert (hinner : BProv Ax_s []
      (pEx (pAll
        (iffForm
          (hfMemAt 0 1)
          (pOr (hfMemAt 0 3)
            (pEq (tVar 0) (tVar 2))))))).
  {
    unfold hfAdjoinExistsTermAt, hfAdjoinGraphTermAt in hex.
    simpl in hex.
    exact hex.
  }
  pose proof (BProv_allI_of_sentences Ax_s [] _
    sentence_ax_s hinner) as hfirst.
  pose proof (BProv_allI_of_sentences Ax_s [] _
    sentence_ax_s hfirst) as hsecond.
  unfold translatedHFAdjoinBody.
  exact hsecond.
Qed.

Theorem BProv_Ax_s_translated_HF_adjoin :
  BProv Ax_s []
    (translateHFFormula (Fol.seal HF_adjoin_form)).
Proof.
  exact
    (BProv_Ax_s_translated_HF_adjoin_of_body
      BProv_Ax_s_translatedHFAdjoinBody).
Qed.
