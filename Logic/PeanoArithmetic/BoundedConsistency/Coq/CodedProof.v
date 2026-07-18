(**
  Executable certificates for occurrence-bounded PA derivations.

  [ProvTree] in [BoundedConsistency] is indexed by its context and conclusion.
  Those indices make malformed trees unrepresentable, but they are not a
  suitable input format for an arithmetized proof checker.  This file first
  defines an unindexed [RawProof] carrying the same rule parameters.  The
  Boolean checker validates every premise endpoint explicitly.  It then
  assigns canonical natural-number codes to raw trees and supplies a total
  decoder/checker on arbitrary natural numbers.

  The central correspondence has both directions:

  - quoting any typed [ProvTree] produces an accepted raw certificate with
    exactly the same all-occurrence rank;
  - every accepted raw certificate erases to an ordinary [Formula.Prov]
    derivation with the context and conclusion computed from the certificate.

  This is still a metatheoretic executable checker.  A future internal proof
  must represent it by arithmetic formulae and prove its nonstandard-model
  correctness using fixed-level partial truth.
*)

From Stdlib Require Import List Arith Lia Bool.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From BoundedPAConsistency Require Import BoundedConsistency CodedSyntax.

Import ListNotations.

Module PABoundedCodedProof.

Import PA.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.

Lemma listCode_member_lt : forall x xs,
  In x xs -> x < PAListCode.listCode xs.
Proof.
  intros x xs. induction xs as [|a xs IH]; simpl; intro h.
  - contradiction.
  - destruct h as [h | h].
    + subst x. apply listCode_head_lt.
    + eapply Nat.lt_trans.
      * exact (IH h).
      * apply PAListCode.listCode_tail_lt.
Qed.

(** An unindexed constructor-for-constructor presentation of [ProvTree].
    The sole missing field is the proposition-valued membership witness of
    the assumption rule; the checker reconstructs that side condition. *)
Inductive RawProof : Type :=
| RP_ass : list formula -> formula -> RawProof
| RP_impI : list formula -> formula -> formula -> RawProof -> RawProof
| RP_impE : list formula -> formula -> formula ->
    RawProof -> RawProof -> RawProof
| RP_botE : list formula -> formula -> RawProof -> RawProof
| RP_lem : list formula -> formula -> RawProof
| RP_andI : list formula -> formula -> formula ->
    RawProof -> RawProof -> RawProof
| RP_andE1 : list formula -> formula -> formula -> RawProof -> RawProof
| RP_andE2 : list formula -> formula -> formula -> RawProof -> RawProof
| RP_orI1 : list formula -> formula -> formula -> RawProof -> RawProof
| RP_orI2 : list formula -> formula -> formula -> RawProof -> RawProof
| RP_orE : list formula -> formula -> formula -> formula ->
    RawProof -> RawProof -> RawProof -> RawProof
| RP_allI : list formula -> formula -> RawProof -> RawProof
| RP_allE : list formula -> formula -> term -> RawProof -> RawProof
| RP_exI : list formula -> formula -> term -> RawProof -> RawProof
| RP_exE : list formula -> formula -> formula ->
    RawProof -> RawProof -> RawProof
| RP_eqRefl : list formula -> term -> RawProof
| RP_eqElim : list formula -> term -> term -> formula ->
    RawProof -> RawProof -> RawProof.

Definition rawContext (d : RawProof) : list formula :=
  match d with
  | RP_ass G _ | RP_impI G _ _ _ | RP_impE G _ _ _ _
  | RP_botE G _ _ | RP_lem G _ | RP_andI G _ _ _ _
  | RP_andE1 G _ _ _ | RP_andE2 G _ _ _ | RP_orI1 G _ _ _
  | RP_orI2 G _ _ _ | RP_orE G _ _ _ _ _ _ | RP_allI G _ _
  | RP_allE G _ _ _ | RP_exI G _ _ _ | RP_exE G _ _ _ _
  | RP_eqRefl G _ | RP_eqElim G _ _ _ _ _ => G
  end.

Definition rawConclusion (d : RawProof) : formula :=
  match d with
  | RP_ass _ a => a
  | RP_impI _ a b _ => pImp a b
  | RP_impE _ _ b _ _ => b
  | RP_botE _ a _ => a
  | RP_lem _ a => pOr a (pImp a pBot)
  | RP_andI _ a b _ _ => pAnd a b
  | RP_andE1 _ a _ _ => a
  | RP_andE2 _ _ b _ => b
  | RP_orI1 _ a b _ => pOr a b
  | RP_orI2 _ a b _ => pOr a b
  | RP_orE _ _ _ c _ _ _ => c
  | RP_allI _ a _ => pAll a
  | RP_allE _ a t _ => Formula.subst (Formula.instTerm t) a
  | RP_exI _ a _ _ => pEx a
  | RP_exE _ _ c _ _ => c
  | RP_eqRefl _ t => pEq t t
  | RP_eqElim _ _ t a _ _ => Formula.subst (Formula.instTerm t) a
  end.

(** Structural equality is kept transparent and constructive.  The Boolean
    checker below therefore computes after extraction; it does not appeal to
    classical excluded middle. *)
Definition term_eq_dec : forall a b : term, {a = b} + {a <> b}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition formula_eq_dec : forall a b : formula, {a = b} + {a <> b}.
Proof. decide equality; apply term_eq_dec. Defined.

Definition context_eq_dec : forall G H : list formula, {G = H} + {G <> H} :=
  list_eq_dec formula_eq_dec.

Definition formulaEqb (a b : formula) : bool :=
  if formula_eq_dec a b then true else false.

Definition contextEqb (G H : list formula) : bool :=
  if context_eq_dec G H then true else false.

Definition formulaInb (a : formula) (G : list formula) : bool :=
  if in_dec formula_eq_dec a G then true else false.

Lemma formulaEqb_spec : forall a b,
  formulaEqb a b = true <-> a = b.
Proof.
  intros a b. unfold formulaEqb.
  destruct (formula_eq_dec a b) as [heq | hne].
  - split; intro h; [exact heq | reflexivity].
  - split; intro h; [discriminate | contradiction].
Qed.

Lemma contextEqb_spec : forall G H,
  contextEqb G H = true <-> G = H.
Proof.
  intros G H. unfold contextEqb.
  destruct (context_eq_dec G H) as [heq | hne].
  - split; intro h; [exact heq | reflexivity].
  - split; intro h; [discriminate | contradiction].
Qed.

Lemma formulaInb_spec : forall a G,
  formulaInb a G = true <-> In a G.
Proof.
  intros a G. unfold formulaInb.
  destruct (in_dec formula_eq_dec a G) as [hin | hnotin].
  - split; intro h; [exact hin | reflexivity].
  - split; intro h; [discriminate | contradiction].
Qed.

(** Declarative validity is convenient for proofs; [rawProofValidb] is its
    executable counterpart.  Every clause checks all recursive premises and
    verifies their complete context/conclusion endpoints. *)
Fixpoint RawProofValid (d : RawProof) : Prop :=
  match d with
  | RP_ass G a => In a G
  | RP_impI G a b h =>
      RawProofValid h /\ rawContext h = a :: G /\ rawConclusion h = b
  | RP_impE G a b hImp hA =>
      RawProofValid hImp /\ rawContext hImp = G /\
      rawConclusion hImp = pImp a b /\
      RawProofValid hA /\ rawContext hA = G /\ rawConclusion hA = a
  | RP_botE G _ hBot =>
      RawProofValid hBot /\ rawContext hBot = G /\
      rawConclusion hBot = pBot
  | RP_lem _ _ => True
  | RP_andI G a b hA hB =>
      RawProofValid hA /\ rawContext hA = G /\ rawConclusion hA = a /\
      RawProofValid hB /\ rawContext hB = G /\ rawConclusion hB = b
  | RP_andE1 G a b hAnd | RP_andE2 G a b hAnd =>
      RawProofValid hAnd /\ rawContext hAnd = G /\
      rawConclusion hAnd = pAnd a b
  | RP_orI1 G a _ hA =>
      RawProofValid hA /\ rawContext hA = G /\ rawConclusion hA = a
  | RP_orI2 G _ b hB =>
      RawProofValid hB /\ rawContext hB = G /\ rawConclusion hB = b
  | RP_orE G a b c hOr hA hB =>
      RawProofValid hOr /\ rawContext hOr = G /\
      rawConclusion hOr = pOr a b /\
      RawProofValid hA /\ rawContext hA = a :: G /\ rawConclusion hA = c /\
      RawProofValid hB /\ rawContext hB = b :: G /\ rawConclusion hB = c
  | RP_allI G a hA =>
      RawProofValid hA /\
      rawContext hA = map (Formula.rename S) G /\ rawConclusion hA = a
  | RP_allE G a _ hAll =>
      RawProofValid hAll /\ rawContext hAll = G /\
      rawConclusion hAll = pAll a
  | RP_exI G a t hA =>
      RawProofValid hA /\ rawContext hA = G /\
      rawConclusion hA = Formula.subst (Formula.instTerm t) a
  | RP_exE G a c hEx hBody =>
      RawProofValid hEx /\ rawContext hEx = G /\
      rawConclusion hEx = pEx a /\
      RawProofValid hBody /\
      rawContext hBody = a :: map (Formula.rename S) G /\
      rawConclusion hBody = Formula.rename S c
  | RP_eqRefl _ _ => True
  | RP_eqElim G s t a hEq hA =>
      RawProofValid hEq /\ rawContext hEq = G /\
      rawConclusion hEq = pEq s t /\
      RawProofValid hA /\ rawContext hA = G /\
      rawConclusion hA = Formula.subst (Formula.instTerm s) a
  end.

Fixpoint rawProofValidb (d : RawProof) : bool :=
  match d with
  | RP_ass G a => formulaInb a G
  | RP_impI G a b h =>
      rawProofValidb h && contextEqb (rawContext h) (a :: G) &&
      formulaEqb (rawConclusion h) b
  | RP_impE G a b hImp hA =>
      rawProofValidb hImp && contextEqb (rawContext hImp) G &&
      formulaEqb (rawConclusion hImp) (pImp a b) &&
      rawProofValidb hA && contextEqb (rawContext hA) G &&
      formulaEqb (rawConclusion hA) a
  | RP_botE G _ hBot =>
      rawProofValidb hBot && contextEqb (rawContext hBot) G &&
      formulaEqb (rawConclusion hBot) pBot
  | RP_lem _ _ => true
  | RP_andI G a b hA hB =>
      rawProofValidb hA && contextEqb (rawContext hA) G &&
      formulaEqb (rawConclusion hA) a &&
      rawProofValidb hB && contextEqb (rawContext hB) G &&
      formulaEqb (rawConclusion hB) b
  | RP_andE1 G a b hAnd | RP_andE2 G a b hAnd =>
      rawProofValidb hAnd && contextEqb (rawContext hAnd) G &&
      formulaEqb (rawConclusion hAnd) (pAnd a b)
  | RP_orI1 G a _ hA =>
      rawProofValidb hA && contextEqb (rawContext hA) G &&
      formulaEqb (rawConclusion hA) a
  | RP_orI2 G _ b hB =>
      rawProofValidb hB && contextEqb (rawContext hB) G &&
      formulaEqb (rawConclusion hB) b
  | RP_orE G a b c hOr hA hB =>
      rawProofValidb hOr && contextEqb (rawContext hOr) G &&
      formulaEqb (rawConclusion hOr) (pOr a b) &&
      rawProofValidb hA && contextEqb (rawContext hA) (a :: G) &&
      formulaEqb (rawConclusion hA) c &&
      rawProofValidb hB && contextEqb (rawContext hB) (b :: G) &&
      formulaEqb (rawConclusion hB) c
  | RP_allI G a hA =>
      rawProofValidb hA &&
      contextEqb (rawContext hA) (map (Formula.rename S) G) &&
      formulaEqb (rawConclusion hA) a
  | RP_allE G a _ hAll =>
      rawProofValidb hAll && contextEqb (rawContext hAll) G &&
      formulaEqb (rawConclusion hAll) (pAll a)
  | RP_exI G a t hA =>
      rawProofValidb hA && contextEqb (rawContext hA) G &&
      formulaEqb (rawConclusion hA)
        (Formula.subst (Formula.instTerm t) a)
  | RP_exE G a c hEx hBody =>
      rawProofValidb hEx && contextEqb (rawContext hEx) G &&
      formulaEqb (rawConclusion hEx) (pEx a) &&
      rawProofValidb hBody &&
      contextEqb (rawContext hBody) (a :: map (Formula.rename S) G) &&
      formulaEqb (rawConclusion hBody) (Formula.rename S c)
  | RP_eqRefl _ _ => true
  | RP_eqElim G s t a hEq hA =>
      rawProofValidb hEq && contextEqb (rawContext hEq) G &&
      formulaEqb (rawConclusion hEq) (pEq s t) &&
      rawProofValidb hA && contextEqb (rawContext hA) G &&
      formulaEqb (rawConclusion hA)
        (Formula.subst (Formula.instTerm s) a)
  end.

Theorem rawProofValidb_spec : forall d,
  rawProofValidb d = true <-> RawProofValid d.
Proof.
  induction d; cbn [rawProofValidb RawProofValid];
    repeat rewrite ?andb_true_iff, ?formulaEqb_spec,
      ?contextEqb_spec, ?formulaInb_spec,
      ?IHd, ?IHd1, ?IHd2, ?IHd3;
    tauto.
Qed.

(** An accepted raw certificate has genuine logical content.  Constructing an
    ordinary proof in [Prop] avoids any forbidden elimination from a
    proposition into the data universe. *)
Theorem RawProofValid_prov : forall d,
  RawProofValid d -> Formula.Prov (rawContext d) (rawConclusion d).
Proof.
  induction d; cbn [RawProofValid rawContext rawConclusion]; intro h.
  - exact (Formula.P_ass l f h).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_impI l f f0 IHd).
  - destruct h as [hv1 [hc1 [hf1 [hv2 [hc2 hf2]]]]].
    specialize (IHd1 hv1). specialize (IHd2 hv2).
    rewrite hc1, hf1 in IHd1. rewrite hc2, hf2 in IHd2.
    exact (Formula.P_impE l f f0 IHd1 IHd2).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_botE l f IHd).
  - exact (Formula.P_lem l f).
  - destruct h as [hv1 [hc1 [hf1 [hv2 [hc2 hf2]]]]].
    specialize (IHd1 hv1). specialize (IHd2 hv2).
    rewrite hc1, hf1 in IHd1. rewrite hc2, hf2 in IHd2.
    exact (Formula.P_andI l f f0 IHd1 IHd2).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_andE1 l f f0 IHd).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_andE2 l f f0 IHd).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_orI1 l f f0 IHd).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_orI2 l f f0 IHd).
  - destruct h as
        [hv1 [hc1 [hf1 [hv2 [hc2 [hf2 [hv3 [hc3 hf3]]]]]]]].
    specialize (IHd1 hv1). specialize (IHd2 hv2). specialize (IHd3 hv3).
    rewrite hc1, hf1 in IHd1. rewrite hc2, hf2 in IHd2.
    rewrite hc3, hf3 in IHd3.
    exact (Formula.P_orE l f f0 f1 IHd1 IHd2 IHd3).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_allI l f IHd).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_allE l f t IHd).
  - destruct h as [hv [hc hf]].
    specialize (IHd hv). rewrite hc, hf in IHd.
    exact (Formula.P_exI l f t IHd).
  - destruct h as [hv1 [hc1 [hf1 [hv2 [hc2 hf2]]]]].
    specialize (IHd1 hv1). specialize (IHd2 hv2).
    rewrite hc1, hf1 in IHd1. rewrite hc2, hf2 in IHd2.
    exact (Formula.P_exE l f f0 IHd1 IHd2).
  - exact (Formula.P_eqRefl l t).
  - destruct h as [hv1 [hc1 [hf1 [hv2 [hc2 hf2]]]]].
    specialize (IHd1 hv1). specialize (IHd2 hv2).
    rewrite hc1, hf1 in IHd1. rewrite hc2, hf2 in IHd2.
    exact (Formula.P_eqElim l t t0 f IHd1 IHd2).
Qed.

Corollary rawProofValidb_prov : forall d,
  rawProofValidb d = true ->
  Formula.Prov (rawContext d) (rawConclusion d).
Proof.
  intros d h.
  apply RawProofValid_prov.
  now apply rawProofValidb_spec.
Qed.

(** Quotation forgets only the assumption-membership proof. *)
Fixpoint rawOfProvTree {G phi} (d : ProvTree G phi) : RawProof :=
  match d with
  | PT_ass G a _ => RP_ass G a
  | PT_impI G a b h => RP_impI G a b (rawOfProvTree h)
  | PT_impE G a b hImp hA =>
      RP_impE G a b (rawOfProvTree hImp) (rawOfProvTree hA)
  | PT_botE G a hBot => RP_botE G a (rawOfProvTree hBot)
  | PT_lem G a => RP_lem G a
  | PT_andI G a b hA hB =>
      RP_andI G a b (rawOfProvTree hA) (rawOfProvTree hB)
  | PT_andE1 G a b hAnd => RP_andE1 G a b (rawOfProvTree hAnd)
  | PT_andE2 G a b hAnd => RP_andE2 G a b (rawOfProvTree hAnd)
  | PT_orI1 G a b hA => RP_orI1 G a b (rawOfProvTree hA)
  | PT_orI2 G a b hB => RP_orI2 G a b (rawOfProvTree hB)
  | PT_orE G a b c hOr hA hB =>
      RP_orE G a b c (rawOfProvTree hOr)
        (rawOfProvTree hA) (rawOfProvTree hB)
  | PT_allI G a hA => RP_allI G a (rawOfProvTree hA)
  | PT_allE G a t hAll => RP_allE G a t (rawOfProvTree hAll)
  | PT_exI G a t hA => RP_exI G a t (rawOfProvTree hA)
  | PT_exE G a c hEx hBody =>
      RP_exE G a c (rawOfProvTree hEx) (rawOfProvTree hBody)
  | PT_eqRefl G t => RP_eqRefl G t
  | PT_eqElim G s t a hEq hA =>
      RP_eqElim G s t a (rawOfProvTree hEq) (rawOfProvTree hA)
  end.

Lemma rawOfProvTree_context : forall G phi (d : ProvTree G phi),
  rawContext (rawOfProvTree d) = G.
Proof. intros G phi d. destruct d; reflexivity. Qed.

Lemma rawOfProvTree_conclusion : forall G phi (d : ProvTree G phi),
  rawConclusion (rawOfProvTree d) = phi.
Proof. intros G phi d. destruct d; reflexivity. Qed.

Theorem RawProofValid_rawOfProvTree : forall G phi (d : ProvTree G phi),
  RawProofValid (rawOfProvTree d).
Proof.
  intros G phi d. induction d; cbn [rawOfProvTree RawProofValid];
    repeat split; try assumption; try reflexivity;
    try apply rawOfProvTree_context;
    try apply rawOfProvTree_conclusion.
Qed.

Corollary rawProofValidb_rawOfProvTree : forall G phi
    (d : ProvTree G phi),
  rawProofValidb (rawOfProvTree d) = true.
Proof.
  intros G phi d. apply rawProofValidb_spec.
  apply RawProofValid_rawOfProvTree.
Qed.

(** The unindexed rank repeats the phase-one bookkeeping exactly: complete
    node contexts, conclusions, every formula-valued rule parameter, and all
    recursive premises are included. *)
Fixpoint rawProofOccurrenceRank (d : RawProof) : nat :=
  Nat.max (contextRank (rawContext d))
    (Nat.max (quantifierGroups (rawConclusion d))
      (match d with
       | RP_ass _ a => quantifierGroups a
       | RP_impI _ a b h =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (rawProofOccurrenceRank h))
       | RP_impE _ a b hImp hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (rawProofOccurrenceRank hImp)
                 (rawProofOccurrenceRank hA)))
       | RP_botE _ a hBot =>
           Nat.max (quantifierGroups a) (rawProofOccurrenceRank hBot)
       | RP_lem _ a => quantifierGroups a
       | RP_andI _ a b hA hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (rawProofOccurrenceRank hA)
                 (rawProofOccurrenceRank hB)))
       | RP_andE1 _ a b hAnd | RP_andE2 _ a b hAnd =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (rawProofOccurrenceRank hAnd))
       | RP_orI1 _ a b hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (rawProofOccurrenceRank hA))
       | RP_orI2 _ a b hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (rawProofOccurrenceRank hB))
       | RP_orE _ a b c hOr hA hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (quantifierGroups c)
                 (Nat.max (rawProofOccurrenceRank hOr)
                   (Nat.max (rawProofOccurrenceRank hA)
                     (rawProofOccurrenceRank hB)))))
       | RP_allI _ a hA =>
           Nat.max (quantifierGroups a) (rawProofOccurrenceRank hA)
       | RP_allE _ a _ hAll =>
           Nat.max (quantifierGroups a) (rawProofOccurrenceRank hAll)
       | RP_exI _ a _ hA =>
           Nat.max (quantifierGroups a) (rawProofOccurrenceRank hA)
       | RP_exE _ a c hEx hBody =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups c)
               (Nat.max (rawProofOccurrenceRank hEx)
                 (rawProofOccurrenceRank hBody)))
       | RP_eqRefl _ _ => 0
       | RP_eqElim _ _ _ a hEq hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (rawProofOccurrenceRank hEq)
               (rawProofOccurrenceRank hA))
       end)).

Theorem rawProofOccurrenceRank_rawOfProvTree : forall G phi
    (d : ProvTree G phi),
  rawProofOccurrenceRank (rawOfProvTree d) = proofOccurrenceRank d.
Proof.
  intros G phi d. induction d; cbn
    [rawOfProvTree rawProofOccurrenceRank rawContext rawConclusion
     proofOccurrenceRank]; repeat f_equal; assumption.
Qed.

Definition rawProofAllBoundedb (n : nat) (d : RawProof) : bool :=
  Nat.leb (rawProofOccurrenceRank d) n.

Lemma rawProofAllBoundedb_spec : forall n d,
  rawProofAllBoundedb n d = true <-> rawProofOccurrenceRank d <= n.
Proof.
  intros n d. unfold rawProofAllBoundedb.
  apply Nat.leb_le.
Qed.

Theorem rawProofAllBoundedb_rawOfProvTree : forall n G phi
    (d : ProvTree G phi),
  rawProofAllBoundedb n (rawOfProvTree d) = true <-> ProofAllBounded n d.
Proof.
  intros n G phi d.
  rewrite rawProofAllBoundedb_spec, rawProofOccurrenceRank_rawOfProvTree.
  reflexivity.
Qed.

(** * Natural-number quotation and total decoding *)

Definition contextCode (G : list formula) : nat :=
  PAListCode.listCode (map formulaCode G).

Fixpoint decodeFormulaCodes (codes : list nat) : option (list formula) :=
  match codes with
  | [] => Some []
  | p :: codes' =>
      match decodeFormula p, decodeFormulaCodes codes' with
      | Some phi, Some G => Some (phi :: G)
      | _, _ => None
      end
  end.

Definition decodeContext (p : nat) : option (list formula) :=
  match PAListCode.decode p with
  | Some codes => decodeFormulaCodes codes
  | None => None
  end.

Lemma decodeFormulaCodes_map_formulaCode : forall G,
  decodeFormulaCodes (map formulaCode G) = Some G.
Proof.
  induction G as [|phi G IH]; simpl.
  - reflexivity.
  - now rewrite decodeFormula_formulaCode, IH.
Qed.

Theorem decodeContext_contextCode : forall G,
  decodeContext (contextCode G) = Some G.
Proof.
  intro G. unfold decodeContext, contextCode.
  rewrite PAListCode.decode_listCode.
  apply decodeFormulaCodes_map_formulaCode.
Qed.

(** Natural tags follow the constructor order above.  Contexts and all
    formula/term parameters are quoted explicitly, so decoding loses no
    occurrence that contributes to the complexity bound. *)
Fixpoint rawProofCode (d : RawProof) : nat :=
  match d with
  | RP_ass G a =>
      PAListCode.listCode [0; contextCode G; formulaCode a]
  | RP_impI G a b h =>
      PAListCode.listCode
        [1; contextCode G; formulaCode a; formulaCode b; rawProofCode h]
  | RP_impE G a b hImp hA =>
      PAListCode.listCode
        [2; contextCode G; formulaCode a; formulaCode b;
          rawProofCode hImp; rawProofCode hA]
  | RP_botE G a hBot =>
      PAListCode.listCode
        [3; contextCode G; formulaCode a; rawProofCode hBot]
  | RP_lem G a =>
      PAListCode.listCode [4; contextCode G; formulaCode a]
  | RP_andI G a b hA hB =>
      PAListCode.listCode
        [5; contextCode G; formulaCode a; formulaCode b;
          rawProofCode hA; rawProofCode hB]
  | RP_andE1 G a b hAnd =>
      PAListCode.listCode
        [6; contextCode G; formulaCode a; formulaCode b; rawProofCode hAnd]
  | RP_andE2 G a b hAnd =>
      PAListCode.listCode
        [7; contextCode G; formulaCode a; formulaCode b; rawProofCode hAnd]
  | RP_orI1 G a b hA =>
      PAListCode.listCode
        [8; contextCode G; formulaCode a; formulaCode b; rawProofCode hA]
  | RP_orI2 G a b hB =>
      PAListCode.listCode
        [9; contextCode G; formulaCode a; formulaCode b; rawProofCode hB]
  | RP_orE G a b c hOr hA hB =>
      PAListCode.listCode
        [10; contextCode G; formulaCode a; formulaCode b; formulaCode c;
          rawProofCode hOr; rawProofCode hA; rawProofCode hB]
  | RP_allI G a hA =>
      PAListCode.listCode
        [11; contextCode G; formulaCode a; rawProofCode hA]
  | RP_allE G a t hAll =>
      PAListCode.listCode
        [12; contextCode G; formulaCode a; termCode t; rawProofCode hAll]
  | RP_exI G a t hA =>
      PAListCode.listCode
        [13; contextCode G; formulaCode a; termCode t; rawProofCode hA]
  | RP_exE G a c hEx hBody =>
      PAListCode.listCode
        [14; contextCode G; formulaCode a; formulaCode c;
          rawProofCode hEx; rawProofCode hBody]
  | RP_eqRefl G t =>
      PAListCode.listCode [15; contextCode G; termCode t]
  | RP_eqElim G s t a hEq hA =>
      PAListCode.listCode
        [16; contextCode G; termCode s; termCode t; formulaCode a;
          rawProofCode hEq; rawProofCode hA]
  end.

Definition rawChildren (d : RawProof) : list RawProof :=
  match d with
  | RP_ass _ _ | RP_lem _ _ | RP_eqRefl _ _ => []
  | RP_impI _ _ _ h | RP_botE _ _ h | RP_andE1 _ _ _ h
  | RP_andE2 _ _ _ h | RP_orI1 _ _ _ h | RP_orI2 _ _ _ h
  | RP_allI _ _ h | RP_allE _ _ _ h | RP_exI _ _ _ h => [h]
  | RP_impE _ _ _ h1 h2 | RP_andI _ _ _ h1 h2
  | RP_exE _ _ _ h1 h2 | RP_eqElim _ _ _ _ h1 h2 => [h1; h2]
  | RP_orE _ _ _ _ h1 h2 h3 => [h1; h2; h3]
  end.

(** This descent lemma is a direct consequence of the list-code dominance
    proved in [CodedSyntax].  It justifies recursive decoding with predecessor
    fuel on every genuine child. *)
Lemma rawProofCode_child_lt : forall d child,
  In child (rawChildren d) -> rawProofCode child < rawProofCode d.
Proof.
  intros d child hchild.
  destruct d; cbn [rawChildren] in hchild;
    repeat (destruct hchild as [hchild | hchild];
      [subst child |]); try contradiction;
    cbn [rawProofCode]; apply listCode_member_lt; simpl; tauto.
Qed.

Fixpoint decodeRawProofFuel (fuel p : nat) : option RawProof :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match PAListCode.decode p with
      | Some [0; g; a] =>
          match decodeContext g, decodeFormula a with
          | Some G, Some a' => Some (RP_ass G a')
          | _, _ => None
          end
      | Some [1; g; a; b; h] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' h with
          | Some G, Some a', Some b', Some h' =>
              Some (RP_impI G a' b' h')
          | _, _, _, _ => None
          end
      | Some [2; g; a; b; hImp; hA] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hImp,
              decodeRawProofFuel fuel' hA with
          | Some G, Some a', Some b', Some hImp', Some hA' =>
              Some (RP_impE G a' b' hImp' hA')
          | _, _, _, _, _ => None
          end
      | Some [3; g; a; hBot] =>
          match decodeContext g, decodeFormula a,
              decodeRawProofFuel fuel' hBot with
          | Some G, Some a', Some hBot' => Some (RP_botE G a' hBot')
          | _, _, _ => None
          end
      | Some [4; g; a] =>
          match decodeContext g, decodeFormula a with
          | Some G, Some a' => Some (RP_lem G a')
          | _, _ => None
          end
      | Some [5; g; a; b; hA; hB] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hA,
              decodeRawProofFuel fuel' hB with
          | Some G, Some a', Some b', Some hA', Some hB' =>
              Some (RP_andI G a' b' hA' hB')
          | _, _, _, _, _ => None
          end
      | Some [6; g; a; b; hAnd] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hAnd with
          | Some G, Some a', Some b', Some hAnd' =>
              Some (RP_andE1 G a' b' hAnd')
          | _, _, _, _ => None
          end
      | Some [7; g; a; b; hAnd] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hAnd with
          | Some G, Some a', Some b', Some hAnd' =>
              Some (RP_andE2 G a' b' hAnd')
          | _, _, _, _ => None
          end
      | Some [8; g; a; b; hA] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hA with
          | Some G, Some a', Some b', Some hA' =>
              Some (RP_orI1 G a' b' hA')
          | _, _, _, _ => None
          end
      | Some [9; g; a; b; hB] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeRawProofFuel fuel' hB with
          | Some G, Some a', Some b', Some hB' =>
              Some (RP_orI2 G a' b' hB')
          | _, _, _, _ => None
          end
      | Some [10; g; a; b; c; hOr; hA; hB] =>
          match decodeContext g, decodeFormula a, decodeFormula b,
              decodeFormula c, decodeRawProofFuel fuel' hOr,
              decodeRawProofFuel fuel' hA,
              decodeRawProofFuel fuel' hB with
          | Some G, Some a', Some b', Some c', Some hOr', Some hA',
              Some hB' => Some (RP_orE G a' b' c' hOr' hA' hB')
          | _, _, _, _, _, _, _ => None
          end
      | Some [11; g; a; hA] =>
          match decodeContext g, decodeFormula a,
              decodeRawProofFuel fuel' hA with
          | Some G, Some a', Some hA' => Some (RP_allI G a' hA')
          | _, _, _ => None
          end
      | Some [12; g; a; t; hAll] =>
          match decodeContext g, decodeFormula a, decodeTerm t,
              decodeRawProofFuel fuel' hAll with
          | Some G, Some a', Some t', Some hAll' =>
              Some (RP_allE G a' t' hAll')
          | _, _, _, _ => None
          end
      | Some [13; g; a; t; hA] =>
          match decodeContext g, decodeFormula a, decodeTerm t,
              decodeRawProofFuel fuel' hA with
          | Some G, Some a', Some t', Some hA' =>
              Some (RP_exI G a' t' hA')
          | _, _, _, _ => None
          end
      | Some [14; g; a; c; hEx; hBody] =>
          match decodeContext g, decodeFormula a, decodeFormula c,
              decodeRawProofFuel fuel' hEx,
              decodeRawProofFuel fuel' hBody with
          | Some G, Some a', Some c', Some hEx', Some hBody' =>
              Some (RP_exE G a' c' hEx' hBody')
          | _, _, _, _, _ => None
          end
      | Some [15; g; t] =>
          match decodeContext g, decodeTerm t with
          | Some G, Some t' => Some (RP_eqRefl G t')
          | _, _ => None
          end
      | Some [16; g; s; t; a; hEq; hA] =>
          match decodeContext g, decodeTerm s, decodeTerm t,
              decodeFormula a, decodeRawProofFuel fuel' hEq,
              decodeRawProofFuel fuel' hA with
          | Some G, Some s', Some t', Some a', Some hEq', Some hA' =>
              Some (RP_eqElim G s' t' a' hEq' hA')
          | _, _, _, _, _, _ => None
          end
      | _ => None
      end
  end.

Definition decodeRawProof (p : nat) : option RawProof :=
  decodeRawProofFuel (S p) p.

Lemma decodeRawProofFuel_rawProofCode : forall d fuel,
  rawProofCode d < fuel ->
  decodeRawProofFuel fuel (rawProofCode d) = Some d.
Proof.
  induction d; intros [|fuel] h; try lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode. reflexivity.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_impI l f f0 d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd1, IHd2.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_impE l f f0 d1 d2) d2 (or_intror (or_introl eq_refl))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_impE l f f0 d1 d2) d1 (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_botE l f d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode. reflexivity.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd1, IHd2.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_andI l f f0 d1 d2) d2 (or_intror (or_introl eq_refl))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_andI l f f0 d1 d2) d1 (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_andE1 l f f0 d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_andE2 l f f0 d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_orI1 l f f0 d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_orI2 l f f0 d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd1, IHd2, IHd3.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_orE l f f0 f1 d1 d2 d3) d3
        (or_intror (or_intror (or_introl eq_refl)))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_orE l f f0 f1 d1 d2 d3) d2
        (or_intror (or_introl eq_refl))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_orE l f f0 f1 d1 d2 d3) d1 (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_allI l f d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode, decodeTerm_termCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_allE l f t d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeFormula_formulaCode, decodeTerm_termCode, IHd.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_exI l f t d) d (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeFormula_formulaCode, IHd1, IHd2.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_exE l f f0 d1 d2) d2 (or_intror (or_introl eq_refl))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_exE l f f0 d1 d2) d1 (or_introl eq_refl)). lia.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      decodeTerm_termCode. reflexivity.
  - cbn [rawProofCode decodeRawProofFuel].
    rewrite PAListCode.decode_listCode, decodeContext_contextCode,
      !decodeTerm_termCode, decodeFormula_formulaCode, IHd1, IHd2.
    + reflexivity.
    + pose proof (rawProofCode_child_lt
        (RP_eqElim l t t0 f d1 d2) d2
        (or_intror (or_introl eq_refl))). lia.
    + pose proof (rawProofCode_child_lt
        (RP_eqElim l t t0 f d1 d2) d1 (or_introl eq_refl)). lia.
Qed.

Theorem decodeRawProof_rawProofCode : forall d,
  decodeRawProof (rawProofCode d) = Some d.
Proof.
  intro d. unfold decodeRawProof.
  apply decodeRawProofFuel_rawProofCode. lia.
Qed.

Theorem rawProofCode_injective : forall d e,
  rawProofCode d = rawProofCode e -> d = e.
Proof.
  intros d e h.
  pose proof (decodeRawProof_rawProofCode d) as hd.
  pose proof (decodeRawProof_rawProofCode e) as he.
  rewrite h in hd. rewrite hd in he. now inversion he.
Qed.

(** The public code checker accepts exactly decodable raw proofs which pass
    the rule checker and whose complete occurrence rank is at most [n]. *)
Definition checkRawProofCode (n p : nat) : bool :=
  match decodeRawProof p with
  | Some d => rawProofValidb d && rawProofAllBoundedb n d
  | None => false
  end.

Definition provTreeCode {G phi} (d : ProvTree G phi) : nat :=
  rawProofCode (rawOfProvTree d).

Theorem checkRawProofCode_provTreeCode : forall n G phi
    (d : ProvTree G phi),
  checkRawProofCode n (provTreeCode d) = true <-> ProofAllBounded n d.
Proof.
  intros n G phi d.
  unfold checkRawProofCode, provTreeCode.
  rewrite decodeRawProof_rawProofCode, andb_true_iff,
    rawProofValidb_rawOfProvTree, rawProofAllBoundedb_rawOfProvTree.
  tauto.
Qed.

Theorem checkRawProofCode_sound : forall n p,
  checkRawProofCode n p = true ->
  exists d,
    decodeRawProof p = Some d /\
    Formula.Prov (rawContext d) (rawConclusion d) /\
    rawProofOccurrenceRank d <= n.
Proof.
  intros n p. unfold checkRawProofCode.
  destruct (decodeRawProof p) as [d|] eqn:hdecode; try discriminate.
  rewrite andb_true_iff. intros [hvalid hbound].
  exists d. split; [reflexivity |]. split.
  - now apply rawProofValidb_prov.
  - now apply rawProofAllBoundedb_spec.
Qed.

(** * A coded wrapper for the PA axiom theory *)

(** An induction axiom is not recognizable merely by comparing against a
    finite table: its source formula is part of the certificate.  Making that
    witness explicit gives a simple executable checker and exactly mirrors
    the final existential clause of [Formula.Ax_s]. *)
Inductive PAAxiomWitness : Type :=
| PAW_succInj
| PAW_zeroNotSucc
| PAW_addZero
| PAW_addSucc
| PAW_mulZero
| PAW_mulSucc
| PAW_induction : formula -> PAAxiomWitness.

Definition witnessedAxiom (w : PAAxiomWitness) : formula :=
  match w with
  | PAW_succInj => Formula.sealPA Formula.succInj
  | PAW_zeroNotSucc => Formula.sealPA Formula.zeroNotSucc
  | PAW_addZero => Formula.sealPA Formula.addZero
  | PAW_addSucc => Formula.sealPA Formula.addSucc
  | PAW_mulZero => Formula.sealPA Formula.mulZero
  | PAW_mulSucc => Formula.sealPA Formula.mulSucc
  | PAW_induction phi => Formula.sealPA (Formula.inductionForm phi)
  end.

Lemma witnessedAxiom_is_Ax_s : forall w,
  Formula.Ax_s (witnessedAxiom w).
Proof.
  intro w. destruct w; cbn [witnessedAxiom].
  - apply Formula.Ax_s_succInj.
  - apply Formula.Ax_s_zeroNotSucc.
  - apply Formula.Ax_s_addZero.
  - apply Formula.Ax_s_addSucc.
  - apply Formula.Ax_s_mulZero.
  - apply Formula.Ax_s_mulSucc.
  - apply Formula.Ax_s_induction.
Qed.

Lemma Ax_s_has_witness : forall f,
  Formula.Ax_s f -> exists w, witnessedAxiom w = f.
Proof.
  intros f h. unfold Formula.Ax_s in h.
  destruct h as [h | [h | [h | [h | [h | [h | [phi h]]]]]]];
    subst f.
  - now exists PAW_succInj.
  - now exists PAW_zeroNotSucc.
  - now exists PAW_addZero.
  - now exists PAW_addSucc.
  - now exists PAW_mulZero.
  - now exists PAW_mulSucc.
  - now exists (PAW_induction phi).
Qed.

Lemma Ax_s_list_has_witnesses : forall L,
  (forall f, In f L -> Formula.Ax_s f) ->
  exists witnesses, map witnessedAxiom witnesses = L.
Proof.
  intro L. induction L as [|f L IH]; intro hL.
  - now exists [].
  - destruct (Ax_s_has_witness f (hL f (or_introl eq_refl)))
      as [w hw].
    destruct (IH (fun g hg => hL g (or_intror hg))) as [ws hws].
    exists (w :: ws). simpl. now rewrite hw, hws.
Qed.

Definition axiomWitnessCode (w : PAAxiomWitness) : nat :=
  match w with
  | PAW_succInj => PAListCode.listCode [0]
  | PAW_zeroNotSucc => PAListCode.listCode [1]
  | PAW_addZero => PAListCode.listCode [2]
  | PAW_addSucc => PAListCode.listCode [3]
  | PAW_mulZero => PAListCode.listCode [4]
  | PAW_mulSucc => PAListCode.listCode [5]
  | PAW_induction phi => PAListCode.listCode [6; formulaCode phi]
  end.

Definition decodeAxiomWitness (p : nat) : option PAAxiomWitness :=
  match PAListCode.decode p with
  | Some [0] => Some PAW_succInj
  | Some [1] => Some PAW_zeroNotSucc
  | Some [2] => Some PAW_addZero
  | Some [3] => Some PAW_addSucc
  | Some [4] => Some PAW_mulZero
  | Some [5] => Some PAW_mulSucc
  | Some [6; phi] =>
      match decodeFormula phi with
      | Some phi' => Some (PAW_induction phi')
      | None => None
      end
  | _ => None
  end.

Theorem decodeAxiomWitness_axiomWitnessCode : forall w,
  decodeAxiomWitness (axiomWitnessCode w) = Some w.
Proof.
  intro w. destruct w; unfold axiomWitnessCode, decodeAxiomWitness;
    rewrite PAListCode.decode_listCode; try reflexivity.
  now rewrite decodeFormula_formulaCode.
Qed.

Definition axiomWitnessListCode (ws : list PAAxiomWitness) : nat :=
  PAListCode.listCode (map axiomWitnessCode ws).

Fixpoint decodeAxiomWitnessCodes
    (codes : list nat) : option (list PAAxiomWitness) :=
  match codes with
  | [] => Some []
  | p :: codes' =>
      match decodeAxiomWitness p, decodeAxiomWitnessCodes codes' with
      | Some w, Some ws => Some (w :: ws)
      | _, _ => None
      end
  end.

Definition decodeAxiomWitnessList
    (p : nat) : option (list PAAxiomWitness) :=
  match PAListCode.decode p with
  | Some codes => decodeAxiomWitnessCodes codes
  | None => None
  end.

Lemma decodeAxiomWitnessCodes_map : forall ws,
  decodeAxiomWitnessCodes (map axiomWitnessCode ws) = Some ws.
Proof.
  induction ws as [|w ws IH]; simpl.
  - reflexivity.
  - now rewrite decodeAxiomWitness_axiomWitnessCode, IH.
Qed.

Theorem decodeAxiomWitnessList_axiomWitnessListCode : forall ws,
  decodeAxiomWitnessList (axiomWitnessListCode ws) = Some ws.
Proof.
  intro ws. unfold decodeAxiomWitnessList, axiomWitnessListCode.
  rewrite PAListCode.decode_listCode.
  apply decodeAxiomWitnessCodes_map.
Qed.

(** A complete restricted-PA certificate consists of an ordered list of
    axiom witnesses followed by a raw logical proof.  Its proof context must
    be precisely the witnessed-axiom list; no extra assumptions are accepted. *)
Definition restrictedPAProofCode
    (ws : list PAAxiomWitness) (d : RawProof) : nat :=
  PAListCode.listCode
    [0; axiomWitnessListCode ws; rawProofCode d].

Definition decodeRestrictedPAProof
    (p : nat) : option (list PAAxiomWitness * RawProof) :=
  match PAListCode.decode p with
  | Some [0; witnesses; proof] =>
      match decodeAxiomWitnessList witnesses, decodeRawProof proof with
      | Some ws, Some d => Some (ws, d)
      | _, _ => None
      end
  | _ => None
  end.

Theorem decodeRestrictedPAProof_restrictedPAProofCode : forall ws d,
  decodeRestrictedPAProof (restrictedPAProofCode ws d) = Some (ws, d).
Proof.
  intros ws d. unfold decodeRestrictedPAProof, restrictedPAProofCode.
  rewrite PAListCode.decode_listCode,
    decodeAxiomWitnessList_axiomWitnessListCode,
    decodeRawProof_rawProofCode.
  reflexivity.
Qed.

Definition checkRestrictedPAProofCode (n p : nat) : bool :=
  match decodeRestrictedPAProof p with
  | Some (ws, d) =>
      rawProofValidb d &&
      contextEqb (rawContext d) (map witnessedAxiom ws) &&
      formulaEqb (rawConclusion d) pBot &&
      rawProofAllBoundedb n d
  | None => false
  end.

Definition restrictedPAProvTreeCode
    (ws : list PAAxiomWitness)
    (d : ProvTree (map witnessedAxiom ws) pBot) : nat :=
  restrictedPAProofCode ws (rawOfProvTree d).

Theorem checkRestrictedPAProofCode_provTreeCode : forall n ws
    (d : ProvTree (map witnessedAxiom ws) pBot),
  checkRestrictedPAProofCode n (restrictedPAProvTreeCode ws d) = true <->
  ProofAllBounded n d.
Proof.
  intros n ws d.
  unfold checkRestrictedPAProofCode, restrictedPAProvTreeCode.
  rewrite decodeRestrictedPAProof_restrictedPAProofCode.
  repeat rewrite andb_true_iff.
  rewrite rawProofValidb_rawOfProvTree,
    rawProofAllBoundedb_rawOfProvTree,
    contextEqb_spec, formulaEqb_spec,
    rawOfProvTree_context, rawOfProvTree_conclusion.
  tauto.
Qed.

(** Every phase-one restricted PA derivation has an accepted natural-number
    certificate.  Notice that this statement is still external: the witness
    [p] is a metatheoretic natural number and the checker is a Rocq function. *)
Theorem RestrictedBProv_has_checked_code : forall n,
  RestrictedBProv n Formula.Ax_s [] pBot ->
  exists p, checkRestrictedPAProofCode n p = true.
Proof.
  intros n [L [hL hrestricted]].
  rewrite app_nil_r in hrestricted.
  destruct (Ax_s_list_has_witnesses L hL) as [ws hws].
  rewrite <- hws in hrestricted.
  destruct hrestricted as [d hd].
  exists (restrictedPAProvTreeCode ws d).
  apply checkRestrictedPAProofCode_provTreeCode.
  exact hd.
Qed.

(** Conversely, acceptance supplies an ordinary PA derivation of falsity.
    This direction deliberately states ordinary [BProv]: rebuilding a typed
    tree with exactly the raw certificate's numeric rank would be additional
    data-level work and is unnecessary for checker soundness. *)
Theorem checkRestrictedPAProofCode_BProv_sound : forall n p,
  checkRestrictedPAProofCode n p = true ->
  Formula.BProv Formula.Ax_s [] pBot.
Proof.
  intros n p. unfold checkRestrictedPAProofCode.
  destruct (decodeRestrictedPAProof p) as [[ws d]|] eqn:hdecode;
    try discriminate.
  repeat rewrite andb_true_iff.
  intros [[[hvalid hcontext] hconclusion] hbound].
  apply contextEqb_spec in hcontext.
  apply formulaEqb_spec in hconclusion.
  pose proof (rawProofValidb_prov d hvalid) as hprov.
  rewrite hcontext, hconclusion in hprov.
  exists (map witnessedAxiom ws). split.
  - intros f hf. apply in_map_iff in hf.
    destruct hf as [w [hw _]]. subst f.
    apply witnessedAxiom_is_Ax_s.
  - now rewrite app_nil_r.
Qed.

(** External consistency of the natural-code checker follows from the same
    standard-model soundness argument as phase one.  It must not be confused
    with an object-language PA proof of the formula representing this check. *)
Theorem checkedRestrictedPA_consistent_standard : forall n p,
  checkRestrictedPAProofCode n p = false.
Proof.
  intros n p.
  destruct (checkRestrictedPAProofCode n p) eqn:hcheck;
    [exfalso | reflexivity].
  pose proof (checkRestrictedPAProofCode_BProv_sound n p hcheck) as hproof.
  pose proof (Formula.soundness_BProv natModel Formula.Ax_s [] pBot
    hproof (fun _ => 0)) as hsound.
  apply (hsound
    (fun b hb => Formula.sat_axiom_s natModel (fun _ => 0) b hb)).
  intros g hg. contradiction.
Qed.

End PABoundedCodedProof.
