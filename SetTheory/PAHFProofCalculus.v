(* ===================================================================== *)
(*  PAHFProofCalculus.v                                                 *)
(*                                                                       *)
(*  Reusable proof-calculus combinators for the PA/HF development.       *)
(*                                                                       *)
(*  Opening several existential witnesses creates a nontrivial context:  *)
(*  each older assumption is de Bruijn-renamed once for every witness    *)
(*  witness opened after it.  The definitions below make that pattern     *)
(*  explicit, and the two generic lemmas package the corresponding        *)
(*  proof lifting and nested existential elimination.                     *)
(* ===================================================================== *)

From Stdlib Require Import List.
From SetTheory Require Import Fol Calculus PAHF.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** A derivation remains valid after prepending any finite block of local
    assumptions.  This packages repeated chains of [BProv_context_cons]. *)
Lemma BProv_context_prefix : forall
    (B : formula -> Prop) prefix G phi,
  BProv B G phi ->
  BProv B (prefix ++ G) phi.
Proof.
  intros B prefix.
  induction prefix as [|head tail IH]; intros G phi hphi.
  - exact hphi.
  - simpl.
    exact (BProv_context_cons B (tail ++ G) head phi
      (IH G phi hphi)).
Qed.

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

(** Lift any relative derivation through [n] freshly opened existential
    binders.  This is the reusable form of the many local [lift2] proofs
    previously repeated in graph functionality and round-trip arguments. *)
Lemma BProv_lift_openedExContext_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall n G body phi,
    BProv B G phi ->
    BProv B (openedExContext n body G) (iterRenameSucc n phi).
Proof.
  intros B hB n.
  induction n as [|n IH]; intros G body phi hphi.
  - exact hphi.
  - cbn [openedExContext iterRenameSucc].
    apply IH.
    exact (BProv_rename_succ_context_cons_of_sentences
      B hB G (iterEx n body) phi hphi).
Qed.

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
    { apply BProv_ass. unfold C. simpl. now left. }
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

(** Convenient two-witness specialization, retained because paired graph
    witnesses are pervasive in arithmetic and finite-set encodings. *)
Lemma BProv_two_exE_of_sentences : forall
    (B : formula -> Prop), Sentences B ->
  forall G body target,
    BProv B G (pEx (pEx body)) ->
    BProv B
      (body :: map (rename S) (pEx body :: map (rename S) G))
      (rename S (rename S target)) ->
    BProv B G target.
Proof.
  intros B hB G body target hex hopened.
  exact (BProv_iterExE_of_sentences B hB 2 G body target
    hex hopened).
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
  exact (BProv_lift_openedExContext_of_sentences
    B hB 2 G body phi hphi).
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
