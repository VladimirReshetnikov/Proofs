(* ===================================================================== *)
(*  Forward.v                                                             *)
(*                                                                       *)
(*  Vladimir Reshetnikov's "Closure" axiomatization of set theory:       *)
(*  the FORWARD direction of its equivalence with ZF.                    *)
(*                                                                       *)
(*  We fix an abstract structure (V, mem) and assume only                *)
(*      Extensionality, Separation, Powerset, Closure                    *)
(*  (Regularity is part of the theory T and is stated for faithfulness   *)
(*   but plays no role below.  We work in ZF, not ZFC: the Axiom of      *)
(*   Choice plays no role in the trade and is omitted from both          *)
(*   theories.  Adding Choice back yields ZFC.                           *)
(*                                                                       *)
(*  From these we DERIVE, as theorems:                                   *)
(*      Pairing, Union, Replacement, Infinity.                           *)
(*                                                                       *)
(*  The linchpin is HOSTING: every set has a host, a in host a.  That    *)
(*  single fact makes every singleton-valued (more generally, suitably    *)
(*  bounded) class relation set-like, which turns Closure into a fully     *)
(*  general collection principle.  Hosting is ALL the trade uses of        *)
(*  Powerset (a in P(a) gives it); the four `Check`s below confirm none    *)
(*  of the derivations touches Powerset itself.  Note Hosting is far       *)
(*  weaker than Powerset and is NOT given by Powerset on finite sets,      *)
(*  since the hosted predecessors (a, b, F x, x u {x}) are arbitrary.      *)
(*                                                                       *)
(*  Shallow embedding: schemas (Separation, Closure, and the derived     *)
(*  Replacement) are rendered with the metatheory's predicates           *)
(*  (V -> Prop, V -> V -> Prop).  Every derivation instantiates a schema  *)
(*  at one concrete, definable relation, so the proof is faithful to the  *)
(*  first-order schematic argument.                                      *)
(*                                                                       *)
(*  - Created (UTC): 2026-06-30T04:48:30Z                                 *)
(*  - Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9          *)
(* ===================================================================== *)

From Stdlib Require Import ClassicalEpsilon.

Section ClosureEquivalence_Forward.

Variable V : Type.
Variable mem : V -> V -> Prop.
Infix "∈" := mem (at level 70, no associativity).

Definition Sub (a b : V) : Prop := forall x, x ∈ a -> x ∈ b.

(* First-order logic works over a nonempty domain. *)
Variable witness : V.

(* ------------------------- the surviving axioms ------------------------ *)

Hypothesis Extensionality :
  forall a b, (forall x, x ∈ a <-> x ∈ b) -> a = b.

Hypothesis Separation :
  forall (a : V) (P : V -> Prop),
    exists s, forall x, x ∈ s <-> (x ∈ a /\ P x).

Hypothesis Powerset :
  forall a, exists p, forall x, x ∈ p <-> Sub x a.

(* Hosting: every set is a member of some set.  This is the ONLY consequence  *)
(* of Powerset that the forward trade uses (via a in P(a); see               *)
(* powerset_gives_hosting below): to bound the singleton predecessor-class of *)
(* a node we only need a set CONTAINING the predecessor.  It is far weaker    *)
(* than Powerset, and is NOT supplied by Powerset restricted to finite sets,  *)
(* since the predecessors we must bound (a, b, F x, x u {x}) are arbitrary,   *)
(* possibly infinite, sets.  The four derivations below use only Hosting;     *)
(* the trailing `Check`s certify they are Powerset-free.                      *)
Hypothesis Hosting :
  forall a, exists y, a ∈ y.

Definition SetLike (R : V -> V -> Prop) : Prop :=
  forall x, exists y, forall z, R z x -> z ∈ y.

Local Definition Functional (R : V -> V -> Prop) : Prop := forall x y1 y2, R y1 x -> R y2 x -> y1 = y2.

Hypothesis Closure :
  forall R : V -> V -> Prop, SetLike R ->
    forall s, exists w, Sub s w /\ (forall u v, R u v -> v ∈ w -> u ∈ w).

(* Part of T, but unused below (shared with ZF). Stated for faithfulness. *)
Hypothesis Regularity :
  forall a, (exists x, x ∈ a) ->
            exists m, m ∈ a /\ ~ (exists z, z ∈ m /\ z ∈ a).

(* ----------- derived operators via classical description -------------- *)

Definition sep (a : V) (P : V -> Prop) : V :=
  proj1_sig (constructive_indefinite_description _ (Separation a P)).

Lemma sep_spec : forall a P x, x ∈ sep a P <-> (x ∈ a /\ P x).
Proof.
  intros a P.
  exact (proj2_sig (constructive_indefinite_description _ (Separation a P))).
Qed.

Lemma sep_intro : forall a P x, x ∈ a -> P x -> x ∈ sep a P.
Proof. intros a P x H1 H2. exact (proj2 (sep_spec a P x) (conj H1 H2)). Qed.

Lemma sep_elim1 : forall a P x, x ∈ sep a P -> x ∈ a.
Proof. intros a P x H. exact (proj1 (proj1 (sep_spec a P x) H)). Qed.

Lemma sep_elim2 : forall a P x, x ∈ sep a P -> P x.
Proof. intros a P x H. exact (proj2 (proj1 (sep_spec a P x) H)). Qed.

Local Lemma sep_spec_of_bound :
  forall a P, (forall x, P x -> x ∈ a) ->
  forall x, x ∈ sep a P <-> P x.
Proof.
  intros a P Hbound x. rewrite sep_spec. split.
  - intros [_ HP]. exact HP.
  - intro HP. exact (conj (Hbound x HP) HP).
Qed.

Lemma Sub_refl : forall a, Sub a a.
Proof. intros a x H. exact H. Qed.

(* THE LINCHPIN, in its minimal form: every set has a host, a in host a.     *)
(* This single fact is all the forward trade needs from Powerset; it makes    *)
(* every singleton-valued (suitably bounded) class relation set-like.         *)
Definition host (a : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Hosting a)).
Lemma host_spec : forall a, a ∈ host a.
Proof. intro a. exact (proj2_sig (constructive_indefinite_description _ (Hosting a))). Qed.

Local Lemma functional_setlike_of_host :
  forall (bound : V -> V),
    (forall a, a ∈ bound a) ->
    forall (fallback : V) R, Functional R -> SetLike R.
Proof.
  intros bound Hbound fallback R Hfun x.
  destruct (classic (exists y, R y x)) as [[y Hy] | Hnone].
  - exists (bound y). intros z Hz. rewrite (Hfun x z y Hz Hy). apply Hbound.
  - exists fallback. intros z Hz. exfalso. apply Hnone. now exists z.
Qed.

(* Powerset is one way to satisfy Hosting (a in P(a)); Powerset restricted to *)
(* finite sets is NOT, since it cannot host an infinite set.  This is the      *)
(* file's sole use of the Powerset hypothesis -- the four derivations use only *)
(* host, so `Check` shows them free of Powerset.                               *)
Lemma powerset_gives_hosting : forall a, exists y, a ∈ y.
Proof.
  intro a. destruct (Powerset a) as [p Hp]. exists p.
  apply (proj2 (Hp a)). apply Sub_refl.
Qed.

(* --------------------------- empty set -------------------------------- *)

Definition emptyset : V := sep witness (fun _ => False).

Lemma emptyset_spec : forall x, ~ x ∈ emptyset.
Proof. intros x H. exact (sep_elim2 witness (fun _ => False) x H). Qed.

(* --------- the singleton {empty} and the two-node seed {empty,{empty}} --- *)
(* Built from Hosting + Separation (+ a one-edge Closure for the 2-node seed),*)
(* NOT from Powerset.  host empty contains empty, so Separation carves out    *)
(* {empty}; a one-edge Closure then merges empty into the seed {{empty}} to   *)
(* yield a set holding both empty and {empty}, from which Separation extracts *)
(* {empty,{empty}}.                                                           *)

Definition single_empty : V := sep (host emptyset) (fun x => x = emptyset).

Lemma in_single_empty : forall x, x ∈ single_empty <-> x = emptyset.
Proof.
  unfold single_empty. apply sep_spec_of_bound.
  intros x H. subst x. apply host_spec.
Qed.

Lemma empty_in_single : emptyset ∈ single_empty.
Proof. apply (proj2 (in_single_empty emptyset)). reflexivity. Qed.

Lemma empty_neq_single : emptyset <> single_empty.
Proof.
  intro Heq.
  assert (H : emptyset ∈ single_empty) by exact empty_in_single.
  rewrite <- Heq in H.                          (* H : emptyset ∈ emptyset *)
  exact (emptyset_spec emptyset H).
Qed.

(* the singleton {{empty}}, the seed of the one-edge merge *)
Definition seed_single : V := sep (host single_empty) (fun x => x = single_empty).
Lemma in_seed_single : forall x, x ∈ seed_single <-> x = single_empty.
Proof.
  unfold seed_single. apply sep_spec_of_bound.
  intros x H. subst x. apply host_spec.
Qed.

(* the one-edge relation: empty is the sole predecessor of {empty} *)
Definition mergeRel : V -> V -> Prop :=
  fun z x => x = single_empty /\ z = emptyset.
Lemma mergeRel_setlike : SetLike mergeRel.
Proof.
  intro x. exists (host emptyset). intros z HR. unfold mergeRel in HR.
  destruct HR as [_ Hz]. subst z. apply host_spec.
Qed.

Definition merge_w : V :=
  proj1_sig (constructive_indefinite_description _
              (Closure mergeRel mergeRel_setlike seed_single)).
Lemma merge_w_spec :
  Sub seed_single merge_w /\
  (forall u v, mergeRel u v -> v ∈ merge_w -> u ∈ merge_w).
Proof.
  exact (proj2_sig (constructive_indefinite_description _
                     (Closure mergeRel mergeRel_setlike seed_single))).
Qed.

Lemma single_in_merge_w : single_empty ∈ merge_w.
Proof.
  apply (proj1 merge_w_spec).
  apply (proj2 (in_seed_single single_empty)). reflexivity.
Qed.

Lemma empty_in_merge_w : emptyset ∈ merge_w.
Proof.
  apply (proj2 merge_w_spec emptyset single_empty).
  - unfold mergeRel. split; reflexivity.
  - exact single_in_merge_w.
Qed.

Definition pair_empty : V := sep merge_w (fun x => x = emptyset \/ x = single_empty).

Lemma empty_in_pair : emptyset ∈ pair_empty.
Proof. apply sep_intro; [ exact empty_in_merge_w | left; reflexivity ]. Qed.

Lemma single_in_pair : single_empty ∈ pair_empty.
Proof. apply sep_intro; [ exact single_in_merge_w | right; reflexivity ]. Qed.

(* ------------------------ the four relations -------------------------- *)

Definition pairRel (a b : V) : V -> V -> Prop :=
  fun z x => (x = emptyset /\ z = a) \/ (x = single_empty /\ z = b).

Definition memRel : V -> V -> Prop := fun z x => z ∈ x.

Definition graphRel (F : V -> V) (a : V) : V -> V -> Prop :=
  fun z x => x ∈ a /\ z = F x.

Definition succRel : V -> V -> Prop :=
  fun z x => forall t, t ∈ z <-> (t ∈ x \/ t = x).

(* ============================== PAIRING ============================== *)

Theorem Pairing :
  forall a b, exists p, forall x, x ∈ p <-> (x = a \/ x = b).
Proof.
  intros a b.
  assert (Hfun : Functional (pairRel a b)).
  { unfold Functional, pairRel. intros x z1 z2 Hz1 Hz2.
    pose proof empty_neq_single as Hne.
    destruct Hz1 as [[Hx1 Hz1] | [Hx1 Hz1]];
      destruct Hz2 as [[Hx2 Hz2] | [Hx2 Hz2]]; congruence. }
  pose proof (functional_setlike_of_host host host_spec witness (pairRel a b) Hfun) as HSL.
  destruct (Closure (pairRel a b) HSL pair_empty) as [w [Hsub Hclosed]].
  assert (Ha : a ∈ w).
  { apply (Hclosed a emptyset).
    - unfold pairRel. left. split; reflexivity.
    - apply Hsub. exact empty_in_pair. }
  assert (Hb : b ∈ w).
  { apply (Hclosed b single_empty).
    - unfold pairRel. right. split; reflexivity.
    - apply Hsub. exact single_in_pair. }
  exists (sep w (fun x => x = a \/ x = b)).
  apply sep_spec_of_bound. intros x H.
  destruct H as [Hxa | Hxb]; [ subst x; exact Ha | subst x; exact Hb ].
Qed.

(* =============================== UNION =============================== *)

Theorem Union :
  forall s, exists u, forall x, x ∈ u <-> exists v, x ∈ v /\ v ∈ s.
Proof.
  intro s.
  assert (HSL : SetLike memRel).
  { intro x. exists x. intros z Hz. unfold memRel in Hz. exact Hz. }
  destruct (Closure memRel HSL s) as [w [Hsub Hclosed]].
  exists (sep w (fun x => exists v, x ∈ v /\ v ∈ s)).
  apply sep_spec_of_bound. intros x H.
  destruct H as [v [Hxv Hvs]]. apply (Hclosed x v).
  - unfold memRel. exact Hxv.
  - apply Hsub. exact Hvs.
Qed.

(* ============================ REPLACEMENT =========================== *)

Theorem Replacement :
  forall (F : V -> V) (a : V),
    exists r, forall y, y ∈ r <-> exists x, x ∈ a /\ y = F x.
Proof.
  intros F a.
  assert (HSL : SetLike (graphRel F a)).
  { intro x. exists (host (F x)). intros z HR. unfold graphRel in HR.
    destruct HR as [_ Hz]. subst z. apply host_spec. }
  destruct (Closure (graphRel F a) HSL a) as [w [Hsub Hclosed]].
  exists (sep w (fun y => exists x, x ∈ a /\ y = F x)).
  apply sep_spec_of_bound. intros y H.
  destruct H as [x [Hxa Hyf]]. apply (Hclosed y x).
  - unfold graphRel. split; [ exact Hxa | exact Hyf ].
  - apply Hsub. exact Hxa.
Qed.

(* ============================== INFINITY ============================ *)

Lemma singleton_exists : forall x, exists s, forall t, t ∈ s <-> t = x.
Proof.
  intro x. destruct (Pairing x x) as [p Hp]. exists p.
  intro t. specialize (Hp t). tauto.
Qed.

Lemma succ_exists :
  forall x, exists sx, forall t, t ∈ sx <-> (t ∈ x \/ t = x).
Proof.
  intro x.
  destruct (singleton_exists x) as [sg Hsg].
  destruct (Pairing x sg) as [pr Hpr].
  destruct (Union pr) as [u Hu].
  exists u. intro t. split.
  - intro H. destruct (proj1 (Hu t) H) as [v [Htv Hvpr]].
    destruct (proj1 (Hpr v) Hvpr) as [Hvx | Hvsg].
    + left. subst v. exact Htv.
    + right. subst v. exact (proj1 (Hsg t) Htv).
  - intro H. apply (proj2 (Hu t)). destruct H as [Htx | Htx].
    + exists x.  split; [ exact Htx | apply (proj2 (Hpr x));  left;  reflexivity ].
    + exists sg. split.
      * apply (proj2 (Hsg t)). exact Htx.
      * apply (proj2 (Hpr sg)). right. reflexivity.
Qed.

Theorem Infinity :
  exists I,
    (exists e, e ∈ I /\ forall z, ~ z ∈ e) /\
    (forall x, x ∈ I ->
       exists sx, sx ∈ I /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).
Proof.
  assert (Hfun : Functional succRel).
  { unfold Functional, succRel. intros x z1 z2 Hz1 Hz2.
    apply Extensionality. intro t. rewrite (Hz1 t), (Hz2 t). reflexivity. }
  pose proof (functional_setlike_of_host host host_spec witness succRel Hfun) as HSL.
  destruct (Closure succRel HSL single_empty) as [w [Hsub Hclosed]].
  exists w. split.
  - exists emptyset. split.
    + apply Hsub. exact empty_in_single.
    + exact emptyset_spec.
  - intros x Hx. destruct (succ_exists x) as [sx Hsx].
    exists sx. split.
    + apply (Hclosed sx x).
      * unfold succRel. exact Hsx.
      * exact Hx.
    + exact Hsx.
Qed.

End ClosureEquivalence_Forward.

(* After closing the section, each theorem is universally quantified over   *)
(* the structure (V, mem, witness) and the assumed axioms -- i.e. it is the *)
(* metatheorem: every model of {Ext, Sep, Pow, Closure} also models        *)
(* Pairing, Union, Replacement, Infinity.                                  *)

Check Pairing.
Check Union.
Check Replacement.
Check Infinity.
