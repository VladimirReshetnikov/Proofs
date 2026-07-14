(* ===================================================================== *)
(*  PAHFProofCalculus.v                                                 *)
(*                                                                       *)
(*  Reusable proof-calculus combinators for the PA/HF development.       *)
(*                                                                       *)
(*  Opening several existential witnesses creates a nontrivial context:  *)
(*  each older assumption is de Bruijn-renamed once for every witness    *)
(*  opened after it.  The definitions below make that pattern explicit,  *)
(*  explicit, and the two generic lemmas package the corresponding        *)
(*  proof lifting and nested existential elimination.                     *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Preserve the original unqualified API while the implementation lives in
    the foundational [PA.Formula] namespace. *)
Definition BProv_context_prefix := PA.Formula.BProv_context_prefix.

(** Preserve the proof-calculus module path for existing qualified clients. *)
Definition BProv_two_exE_of_sentences :=
  PA.Formula.BProv_two_exE_of_sentences.

(** [iterEx n body] adds [n] existential binders around [body]. *)
Fixpoint iterEx (n : nat) (body : formula) : formula :=
  match n with
  | 0 => body
  | S k => pEx (iterEx k body)
  end.

(** Rename a formula once for every witness binder that has been opened. *)
Fixpoint iterRenameSucc (n : nat) (phi : formula) : formula :=
  match n with
  | 0 => phi
  | S k => iterRenameSucc k (rename S phi)
  end.

(** Rename every formula in a context once per opened binder.  The
    recursive shape deliberately matches the contexts produced by repeated
    applications of [BProv_rename_of_sentences]. *)
Fixpoint iterRenameContextSucc
    (n : nat) (G : list formula) : list formula :=
  match n with
  | 0 => G
  | S k => iterRenameContextSucc k (map (rename S) G)
  end.

(** Iterated admissibility of successor renaming.  Clients that merely need
    to move a derivation under several binders should use this theorem rather
    than name a chain of one-step renamed proofs. *)
Lemma BProv_iterRenameSucc_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall n G phi,
    BProv B G phi ->
    BProv B
      (iterRenameContextSucc n G)
      (iterRenameSucc n phi).
Proof.
  intros B hB n.
  induction n as [|n IH]; intros G phi hphi.
  - exact hphi.
  - cbn [iterRenameContextSucc iterRenameSucc].
    apply IH.
    exact (BProv_rename_of_sentences B hB G phi hphi S).
Qed.

(** Add a sequence of freshly opened assumptions, in outside-in order.
    Thus [openedContext [outer; inner] G] is
    [inner :: map (rename S) (outer :: map (rename S) G)]. *)
Fixpoint openedContext
    (bodies : list formula) (G : list formula) : list formula :=
  match bodies with
  | [] => G
  | body :: rest =>
      openedContext rest (body :: map (rename S) G)
  end.

(** General context-opening lift.  Unlike [openedExContext], the successive
    bodies need not be nested instances of one formula; this is useful when
    one existential theorem is opened inside the witness of another. *)
Lemma BProv_lift_openedContext_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall bodies G phi,
    BProv B G phi ->
    BProv B
      (openedContext bodies G)
      (iterRenameSucc (length bodies) phi).
Proof.
  intros B hB bodies.
  induction bodies as [|body rest IH]; intros G phi hphi.
  - exact hphi.
  - cbn [openedContext length iterRenameSucc].
    apply IH.
    exact (BProv_rename_succ_context_cons_of_sentences
      B hB G body phi hphi).
Qed.

(** Context obtained by eliminating [iterEx n body] from a proof over [G].

    For example, two witnesses produce

    [body :: map (rename S) (pEx body :: map (rename S) G)].

    The recursive presentation follows the actual outside-in order of
    existential elimination.  It is less error-prone than manually writing
    the increasingly shifted contexts used for two, three, or more binders. *)
Fixpoint openedExContext
    (n : nat) (body : formula) (G : list formula) : list formula :=
  match n with
  | 0 => G
  | S k =>
      openedExContext k body
        (iterEx k body :: map (rename S) G)
  end.

(** Eliminate an arbitrary finite block of existential witnesses in one
    step.  The opened proof uses exactly [openedExContext n body G], so the
    theorem records all de Bruijn shifting in its type instead of leaving it
    to each client proof. *)
Lemma BProv_iterExE_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall n G body target,
    BProv B G (iterEx n body) ->
    BProv B
      (openedExContext n body G)
      (iterRenameSucc n target) ->
    BProv B G target.
Proof.
  intros B hB n.
  induction n as [|n IH]; intros G body target hex hopened.
  - exact hopened.
  - cbn [iterEx openedExContext iterRenameSucc] in hex, hopened.
    set (C := iterEx n body :: map (rename S) G).
    assert (hinner : BProv B C (iterEx n body)).
    { apply BProv_ass_head. }
    assert (htargetC : BProv B C (rename S target)).
    {
      apply (IH C body (rename S target) hinner).
      unfold C.
      exact hopened.
    }
    apply (BProv_exE_of_sentences B G (iterEx n body) target hB hex).
    unfold C in htargetC.
    exact htargetC.
Qed.

(** Convenient three-witness specialization used by multiplication graphs. *)
Lemma BProv_three_exE_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G body target,
    BProv B G (pEx (pEx (pEx body))) ->
    BProv B
      (body :: map (rename S)
        (pEx body :: map (rename S)
          (pEx (pEx body) :: map (rename S) G)))
      (rename S (rename S (rename S target))) ->
    BProv B G target.
Proof.
  intros B hB G body target hex hopened.
  exact (BProv_iterExE_of_sentences B hB 3 G body target
    hex hopened).
Qed.

(** Paired-witness specialization of the generic lifting theorem. *)
Lemma BProv_lift_two_opened_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G body phi,
    BProv B G phi ->
    BProv B
      (body :: map (rename S) (pEx body :: map (rename S) G))
      (rename S (rename S phi)).
Proof.
  intros B hB G body phi hphi.
  exact (BProv_lift_openedContext_of_sentences
    B hB [pEx body; body] G phi hphi).
Qed.

(** Two-step specialization for distinct outer and inner witness bodies. *)
Lemma BProv_lift_two_contexts_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G outer inner phi,
    BProv B G phi ->
    BProv B
      (inner :: map (rename S) (outer :: map (rename S) G))
      (rename S (rename S phi)).
Proof.
  intros B hB G outer inner phi hphi.
  exact (BProv_lift_openedContext_of_sentences
    B hB [outer; inner] G phi hphi).
Qed.

(** Three-step specialization for distinct witness bodies. *)
Lemma BProv_lift_three_contexts_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G outer middle inner phi,
    BProv B G phi ->
    BProv B
      (inner :: map (rename S)
        (middle :: map (rename S) (outer :: map (rename S) G)))
      (rename S (rename S (rename S phi))).
Proof.
  intros B hB G outer middle inner phi hphi.
  exact (BProv_lift_openedContext_of_sentences
    B hB [outer; middle; inner] G phi hphi).
Qed.

(** Substituting the three freshly opened witness variables cancels the
    three binder-aware successor renamings.  This is formula-generic; graph
    proofs should use it instead of reproving the de Bruijn calculation. *)
Lemma subst_three_witnesses_rename_three_succ : forall phi,
  subst (instTerm (tVar 0))
    (subst (Term.upSubst (instTerm (tVar 1)))
      (subst
        (Term.upSubst (Term.upSubst (instTerm (tVar 2))))
        (rename (Fol.up (Fol.up (Fol.up S)))
          (rename (Fol.up (Fol.up (Fol.up S)))
            (rename (Fol.up (Fol.up (Fol.up S))) phi))))) =
  phi.
Proof.
  intro phi.
  rewrite subst_comp, subst_comp.
  repeat rewrite subst_rename.
  transitivity (subst (fun n => tVar n) phi).
  - apply subst_ext_free.
    intros [|[|[|n]]] hn; reflexivity.
  - apply subst_id.
Qed.

(* ===================================================================== *)
(*  Provable equivalence in the PA formula calculus.                     *)
(* ===================================================================== *)

Lemma BProv_PA_iffForm_intro : forall
    (B : formula -> Prop) G a b,
  BProv B G (pImp a b) ->
  BProv B G (pImp b a) ->
  BProv B G (iffForm a b).
Proof.
  intros B G a b hab hba.
  unfold iffForm.
  exact (BProv_andI B G _ _ hab hba).
Qed.

Lemma BProv_PA_iffForm_forward : forall
    (B : formula -> Prop) G a b,
  BProv B G (iffForm a b) ->
  BProv B G (pImp a b).
Proof.
  intros B G a b h.
  unfold iffForm in h.
  exact (BProv_andE1 B G _ _ h).
Qed.

Lemma BProv_PA_iffForm_reverse : forall
    (B : formula -> Prop) G a b,
  BProv B G (iffForm a b) ->
  BProv B G (pImp b a).
Proof.
  intros B G a b h.
  unfold iffForm in h.
  exact (BProv_andE2 B G _ _ h).
Qed.

Lemma BProv_PA_imp_trans : forall
    (B : formula -> Prop) G a b c,
  BProv B G (pImp a b) ->
  BProv B G (pImp b c) ->
  BProv B G (pImp a c).
Proof.
  intros B G a b c hab hbc.
  apply BProv_impI.
  set (C := a :: G).
  assert (ha : BProv B C a).
  { apply BProv_ass_head. }
  assert (hb : BProv B C b).
  {
    exact (BProv_mp B C a b
      (BProv_context_cons B G a (pImp a b) hab) ha).
  }
  exact (BProv_mp B C b c
    (BProv_context_cons B G a (pImp b c) hbc) hb).
Qed.

Lemma BProv_PA_imp_mono : forall
    (B : formula -> Prop) G a a' b b',
  BProv B G (pImp a' a) ->
  BProv B G (pImp b b') ->
  BProv B G (pImp (pImp a b) (pImp a' b')).
Proof.
  intros B G a a' b b' ha hbb'.
  apply BProv_impI.
  apply BProv_impI.
  set (C := a' :: pImp a b :: G).
  assert (ha'C : BProv B C a').
  { apply BProv_ass_head. }
  assert (haC : BProv B C a).
  {
    exact (BProv_mp B C a' a
      (BProv_context_prefix B [a'; pImp a b] G (pImp a' a) ha) ha'C).
  }
  assert (habC : BProv B C (pImp a b)).
  { apply BProv_ass. unfold C. simpl. tauto. }
  assert (hbC : BProv B C b).
  { exact (BProv_mp B C a b habC haC). }
  exact (BProv_mp B C b b'
    (BProv_context_prefix B [a'; pImp a b] G (pImp b b') hbb') hbC).
Qed.

Lemma BProv_PA_and_mono : forall
    (B : formula -> Prop) G a a' b b',
  BProv B G (pImp a a') ->
  BProv B G (pImp b b') ->
  BProv B G (pImp (pAnd a b) (pAnd a' b')).
Proof.
  intros B G a a' b b' haa' hbb'.
  apply BProv_impI.
  set (C := pAnd a b :: G).
  assert (hp : BProv B C (pAnd a b)).
  { apply BProv_ass_head. }
  assert (haC : BProv B C a).
  { exact (BProv_andE1 B C a b hp). }
  assert (hbC : BProv B C b).
  { exact (BProv_andE2 B C a b hp). }
  assert (ha'C : BProv B C a').
  {
    exact (BProv_mp B C a a'
      (BProv_context_cons B G (pAnd a b) (pImp a a') haa') haC).
  }
  assert (hb'C : BProv B C b').
  {
    exact (BProv_mp B C b b'
      (BProv_context_cons B G (pAnd a b) (pImp b b') hbb') hbC).
  }
  exact (BProv_andI B C a' b' ha'C hb'C).
Qed.

Lemma BProv_PA_or_mono : forall
    (B : formula -> Prop) G a a' b b',
  BProv B G (pImp a a') ->
  BProv B G (pImp b b') ->
  BProv B G (pImp (pOr a b) (pOr a' b')).
Proof.
  intros B G a a' b b' haa' hbb'.
  apply BProv_impI.
  set (C := pOr a b :: G).
  assert (hor : BProv B C (pOr a b)).
  { apply BProv_ass_head. }
  assert (hleft : BProv B (a :: C) (pOr a' b')).
  {
    apply BProv_orI1.
    assert (haC : BProv B (a :: C) a).
    { apply BProv_ass_head. }
    exact (BProv_mp B (a :: C) a a'
      (BProv_context_prefix B [a; pOr a b] G (pImp a a') haa') haC).
  }
  assert (hright : BProv B (b :: C) (pOr a' b')).
  {
    apply BProv_orI2.
    assert (hbC : BProv B (b :: C) b).
    { apply BProv_ass_head. }
    exact (BProv_mp B (b :: C) b b'
      (BProv_context_prefix B [b; pOr a b] G (pImp b b') hbb') hbC).
  }
  exact (BProv_orE B C a b (pOr a' b') hor hleft hright).
Qed.

Lemma BProv_PA_iffForm_refl : forall
    (B : formula -> Prop) (G : list formula) a,
  BProv B G (iffForm a a).
Proof.
  intros B G a.
  assert (haa : BProv B G (pImp a a)).
  {
    apply BProv_impI.
    apply BProv_ass_head.
  }
  exact (BProv_PA_iffForm_intro B G a a haa haa).
Qed.

Lemma BProv_PA_iffForm_symm : forall
    (B : formula -> Prop) G a b,
  BProv B G (iffForm a b) ->
  BProv B G (iffForm b a).
Proof.
  intros B G a b h.
  exact (BProv_PA_iffForm_intro B G b a
    (BProv_PA_iffForm_reverse B G a b h)
    (BProv_PA_iffForm_forward B G a b h)).
Qed.

Lemma BProv_PA_iffForm_trans : forall
    (B : formula -> Prop) G a b c,
  BProv B G (iffForm a b) ->
  BProv B G (iffForm b c) ->
  BProv B G (iffForm a c).
Proof.
  intros B G a b c hab hbc.
  apply (BProv_PA_iffForm_intro B G a c).
  - exact (BProv_PA_imp_trans B G a b c
      (BProv_PA_iffForm_forward B G a b hab)
      (BProv_PA_iffForm_forward B G b c hbc)).
  - exact (BProv_PA_imp_trans B G c b a
      (BProv_PA_iffForm_reverse B G b c hbc)
      (BProv_PA_iffForm_reverse B G a b hab)).
Qed.

Lemma BProv_PA_iffForm_imp_congr : forall
    (B : formula -> Prop) (G : list formula) a a' b b',
  BProv B G (iffForm a a') ->
  BProv B G (iffForm b b') ->
  BProv B G (iffForm (pImp a b) (pImp a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply BProv_PA_iffForm_intro.
  - exact (BProv_PA_imp_mono B G a a' b b'
      (BProv_PA_iffForm_reverse B G a a' ha)
      (BProv_PA_iffForm_forward B G b b' hb)).
  - exact (BProv_PA_imp_mono B G a' a b' b
      (BProv_PA_iffForm_forward B G a a' ha)
      (BProv_PA_iffForm_reverse B G b b' hb)).
Qed.

Lemma BProv_PA_iffForm_and_congr : forall
    (B : formula -> Prop) (G : list formula) a a' b b',
  BProv B G (iffForm a a') ->
  BProv B G (iffForm b b') ->
  BProv B G (iffForm (pAnd a b) (pAnd a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply BProv_PA_iffForm_intro.
  - exact (BProv_PA_and_mono B G a a' b b'
      (BProv_PA_iffForm_forward B G a a' ha)
      (BProv_PA_iffForm_forward B G b b' hb)).
  - exact (BProv_PA_and_mono B G a' a b' b
      (BProv_PA_iffForm_reverse B G a a' ha)
      (BProv_PA_iffForm_reverse B G b b' hb)).
Qed.

Lemma BProv_PA_iffForm_or_congr : forall
    (B : formula -> Prop) (G : list formula) a a' b b',
  BProv B G (iffForm a a') ->
  BProv B G (iffForm b b') ->
  BProv B G (iffForm (pOr a b) (pOr a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply BProv_PA_iffForm_intro.
  - exact (BProv_PA_or_mono B G a a' b b'
      (BProv_PA_iffForm_forward B G a a' ha)
      (BProv_PA_iffForm_forward B G b b' hb)).
  - exact (BProv_PA_or_mono B G a' a b' b
      (BProv_PA_iffForm_reverse B G a a' ha)
      (BProv_PA_iffForm_reverse B G b b' hb)).
Qed.

Lemma BProv_PA_ex_mono_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G a b,
    BProv B (map (rename S) G) (pImp a b) ->
    BProv B G (pImp (pEx a) (pEx b)).
Proof.
  intros B hB G a b hab.
  apply BProv_impI.
  set (C := pEx a :: G).
  assert (hexa : BProv B C (pEx a)).
  { apply BProv_ass_head. }
  apply (BProv_exE_of_sentences B C a (pEx b) hB hexa).
  set (D := a :: map (rename S) C).
  assert (ha : BProv B D a).
  { apply BProv_ass_head. }
  assert (habD : BProv B D (pImp a b)).
  {
    unfold D, C.
    simpl.
    exact (BProv_context_two B (map (rename S) G)
      a (rename S (pEx a)) (pImp a b) hab).
  }
  assert (hb : BProv B D b).
  { exact (BProv_mp B D a b habD ha). }
  assert (hinst : BProv B D
      (subst (instTerm (tVar 0)) (rename (up S) b))).
  {
    rewrite subst_instTerm_var_zero_rename_up_succ.
    exact hb.
  }
  pose proof (BProv_exI B D (rename (up S) b) (tVar 0) hinst) as hex.
  change (BProv B D (rename S (pEx b))).
  simpl.
  exact hex.
Qed.

Lemma BProv_PA_iffForm_ex_congr_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G a b,
    BProv B (map (rename S) G) (iffForm a b) ->
    BProv B G (iffForm (pEx a) (pEx b)).
Proof.
  intros B hB G a b h.
  apply BProv_PA_iffForm_intro.
  - exact (BProv_PA_ex_mono_of_sentences B hB G a b
      (BProv_PA_iffForm_forward B (map (rename S) G) a b h)).
  - exact (BProv_PA_ex_mono_of_sentences B hB G b a
      (BProv_PA_iffForm_reverse B (map (rename S) G) a b h)).
Qed.
