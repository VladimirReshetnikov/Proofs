(* ===================================================================== *)
(*  PAHFOrdinalCodeTermCompatibility.v                                  *)
(*                                                                       *)
(*  Structural reduction of the PA composite term-graph theorem.        *)
(*                                                                       *)
(*  The variable constructor follows from functionality of the          *)
(*  ordinal-code graph.  The remaining four term constructors are       *)
(*  exposed through their exact polymorphic compatibility laws, so the  *)
(*  arithmetic proofs for zero/successor/addition/multiplication can be  *)
(*  developed independently without duplicating the term induction.     *)
(* ===================================================================== *)

From Stdlib Require Import List.
From SetTheory Require Import Fol Calculus PAHF PAHFOrdinalCode
  PAHFRoundTripEquality.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Functionality in the coded output of the PA ordinal-code graph.  This
    is exactly what the variable constructor needs: an input variable's
    selected code and the graph output code must agree. *)
Definition PAOrdinalCodeGraphFunctionalProof : Prop :=
  forall (G : list formula) (raw coded1 coded2 : term),
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded1) ->
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded2) ->
    BProv Ax_s G (pEq coded1 coded2).

(** Complete graph theorem for one PA term.  The quantification over the
    context, input-slot maps, and output slot is intentionally retained:
    recursive constructor proofs instantiate it below fresh binders. *)
Definition PAOrdinalCodeTermGraphProof (t : term) : Prop :=
  forall (G : list formula) (rawMap codedMap : nat -> nat)
      (codedOut : nat),
    (forall n, Term.Free n t ->
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) ->
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap t)
        (ordinalCodeGraphTermAt
          (Term.rename rawMap t) (tVar codedOut))).

(** Exact constructor obligations after the variable case has been
    discharged from graph functionality. *)
Definition PAOrdinalCodeTermZeroCompatibility : Prop :=
  PAOrdinalCodeTermGraphProof tZero.

Definition PAOrdinalCodeTermSuccCompatibility : Prop :=
  forall t,
    PAOrdinalCodeTermGraphProof t ->
    PAOrdinalCodeTermGraphProof (tSucc t).

Definition PAOrdinalCodeTermAddCompatibility : Prop :=
  forall left right,
    PAOrdinalCodeTermGraphProof left ->
    PAOrdinalCodeTermGraphProof right ->
    PAOrdinalCodeTermGraphProof (tAdd left right).

Definition PAOrdinalCodeTermMulCompatibility : Prop :=
  forall left right,
    PAOrdinalCodeTermGraphProof left ->
    PAOrdinalCodeTermGraphProof right ->
    PAOrdinalCodeTermGraphProof (tMul left right).

(** Base constructor kit.  Addition and multiplication are kept out of
    this record because they are the two large operation-specific proof
    towers in the Lean development. *)
Record PAOrdinalCodeTermBaseCompatibilityProofs : Prop := {
  pa_term_graph_functional : PAOrdinalCodeGraphFunctionalProof;
  pa_term_graph_zero : PAOrdinalCodeTermZeroCompatibility;
  pa_term_graph_succ : PAOrdinalCodeTermSuccCompatibility
}.

(** Full operation-facing interface used by structural induction. *)
Record PAOrdinalCodeTermCompatibilityProofs : Prop := {
  pa_term_graph_base : PAOrdinalCodeTermBaseCompatibilityProofs;
  pa_term_graph_add : PAOrdinalCodeTermAddCompatibility;
  pa_term_graph_mul : PAOrdinalCodeTermMulCompatibility
}.

(** The variable graph is just equality between the selected output slot
    and the selected input-code slot.  Its forward direction transports
    the assumed input code along equality; its reverse direction is coded
    output functionality. *)
Lemma BProv_Ax_s_compositeTermGraphAt_var : forall
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (G : list formula) (n : nat)
    (rawMap codedMap : nat -> nat) (codedOut : nat),
  (forall k, Term.Free k (tVar n) ->
    BProv Ax_s G
      (ordinalCodeGraphAt (rawMap k) (codedMap k))) ->
  BProv Ax_s G
    (iffForm
      (compositeTermGraphAt codedOut codedMap (tVar n))
      (ordinalCodeGraphTermAt
        (Term.rename rawMap (tVar n)) (tVar codedOut))).
Proof.
  intros hfunctional G n rawMap codedMap codedOut hcode.
  assert (hinput : BProv Ax_s G
      (ordinalCodeGraphTermAt
        (tVar (rawMap n)) (tVar (codedMap n)))).
  {
    unfold ordinalCodeGraphAt in hcode.
    exact (hcode n eq_refl).
  }
  set (inputEq := pEq (tVar codedOut) (tVar (codedMap n))).
  set (outputGraph := ordinalCodeGraphTermAt
    (tVar (rawMap n)) (tVar codedOut)).
  assert (hforward : BProv Ax_s G (pImp inputEq outputGraph)).
  {
    set (C := inputEq :: G).
    assert (heq : BProv Ax_s C inputEq).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hinputC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (tVar (rawMap n)) (tVar (codedMap n)))).
    { exact (BProv_context_cons Ax_s G inputEq _ hinput). }
    assert (hgraph : BProv Ax_s C outputGraph).
    {
      unfold inputEq in heq.
      unfold outputGraph.
      exact (BProv_ordinalCodeGraphTermAt_congr_coded
        Ax_s C (tVar (rawMap n))
        (tVar (codedMap n)) (tVar codedOut)
        (BProv_eqSym Ax_s C _ _ heq) hinputC).
    }
    unfold C in hgraph.
    exact (BProv_impI Ax_s G inputEq outputGraph hgraph).
  }
  assert (hreverse : BProv Ax_s G (pImp outputGraph inputEq)).
  {
    set (C := outputGraph :: G).
    assert (hout : BProv Ax_s C outputGraph).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hinputC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (tVar (rawMap n)) (tVar (codedMap n)))).
    { exact (BProv_context_cons Ax_s G outputGraph _ hinput). }
    assert (heq : BProv Ax_s C inputEq).
    {
      unfold outputGraph in hout.
      unfold inputEq.
      exact (BProv_eqSym Ax_s C _ _
        (hfunctional C (tVar (rawMap n))
          (tVar (codedMap n)) (tVar codedOut)
          hinputC hout)).
    }
    unfold C in heq.
    exact (BProv_impI Ax_s G outputGraph inputEq heq).
  }
  assert (hiff : BProv Ax_s G (iffForm inputEq outputGraph)).
  {
    unfold iffForm.
    exact (BProv_andI Ax_s G _ _ hforward hreverse).
  }
  unfold inputEq, outputGraph in hiff.
  cbn [compositeTermGraphAt codedTermSlotMap termGraphAt
    hfFormulaAt Term.rename].
  exact hiff.
Qed.

(** The full term theorem follows by ordinary structural induction.  No
    constructor proof is specialized prematurely to one context or output
    slot, so the induction hypotheses remain usable under constructor
    binders. *)
Theorem PAOrdinalCodeTermGraphProof_all_of_compatibility : forall
    (C : PAOrdinalCodeTermCompatibilityProofs) t,
  PAOrdinalCodeTermGraphProof t.
Proof.
  intros C t.
  induction t as
      [n | | t IHt | left IHleft right IHright
       | left IHleft right IHright].
  - intros G rawMap codedMap codedOut hcode.
    exact (BProv_Ax_s_compositeTermGraphAt_var
      (pa_term_graph_functional (pa_term_graph_base C))
      G n rawMap codedMap codedOut hcode).
  - exact (pa_term_graph_zero (pa_term_graph_base C)).
  - exact (pa_term_graph_succ (pa_term_graph_base C) t IHt).
  - exact (pa_term_graph_add C left right IHleft IHright).
  - exact (pa_term_graph_mul C left right IHleft IHright).
Qed.

(** Public target: the constructor interface constructs exactly the graph
    field consumed by the PA composite equality proof. *)
Theorem PACompositeTermGraphProof_of_compatibility :
  PAOrdinalCodeTermCompatibilityProofs ->
  PACompositeTermGraphProof.
Proof.
  intros C G t rawMap codedMap codedOut hcode.
  exact (PAOrdinalCodeTermGraphProof_all_of_compatibility
    C t G rawMap codedMap codedOut hcode).
Qed.

(** Convenient formulation exposing only the base kit plus the two
    operation-specific residuals. *)
Theorem PACompositeTermGraphProof_of_base_add_mul :
  PAOrdinalCodeTermBaseCompatibilityProofs ->
  PAOrdinalCodeTermAddCompatibility ->
  PAOrdinalCodeTermMulCompatibility ->
  PACompositeTermGraphProof.
Proof.
  intros hbase hadd hmul.
  apply PACompositeTermGraphProof_of_compatibility.
  exact {| pa_term_graph_base := hbase;
           pa_term_graph_add := hadd;
           pa_term_graph_mul := hmul |}.
Qed.

