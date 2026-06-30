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
(*  The linchpin is `self_in_power : a in power a`, i.e. Powerset gives   *)
(*  every set a host.  That single fact makes every singleton-valued     *)
(*  (more generally, suitably bounded) class relation set-like, which     *)
(*  turns Closure into a fully general collection principle.             *)
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

Definition SetLike (R : V -> V -> Prop) : Prop :=
  forall x, exists y, forall z, R z x -> z ∈ y.

Hypothesis Closure :
  forall R : V -> V -> Prop, SetLike R ->
    forall s, exists w, Sub s w /\ (forall u v, R u v -> v ∈ w -> u ∈ w).

(* Part of T, but unused below (shared with ZF). Stated for faithfulness. *)
Hypothesis Regularity :
  forall a, (exists x, x ∈ a) ->
            exists m, m ∈ a /\ ~ (exists z, z ∈ m /\ z ∈ a).

(* ----------- derived operators via classical description -------------- *)

Definition power (a : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Powerset a)).

Lemma power_spec : forall a x, x ∈ power a <-> Sub x a.
Proof.
  intro a.
  exact (proj2_sig (constructive_indefinite_description _ (Powerset a))).
Qed.

Definition sep (a : V) (P : V -> Prop) : V :=
  proj1_sig (constructive_indefinite_description _ (Separation a P)).

Lemma sep_spec : forall a P x, x ∈ sep a P <-> (x ∈ a /\ P x).
Proof.
  intros a P.
  exact (proj2_sig (constructive_indefinite_description _ (Separation a P))).
Qed.

(* convenient one-directional forms *)
Lemma power_intro : forall a x, Sub x a -> x ∈ power a.
Proof. intros a x H. exact (proj2 (power_spec a x) H). Qed.

Lemma power_elim : forall a x, x ∈ power a -> Sub x a.
Proof. intros a x H. exact (proj1 (power_spec a x) H). Qed.

Lemma sep_intro : forall a P x, x ∈ a -> P x -> x ∈ sep a P.
Proof. intros a P x H1 H2. exact (proj2 (sep_spec a P x) (conj H1 H2)). Qed.

Lemma sep_elim1 : forall a P x, x ∈ sep a P -> x ∈ a.
Proof. intros a P x H. exact (proj1 (proj1 (sep_spec a P x) H)). Qed.

Lemma sep_elim2 : forall a P x, x ∈ sep a P -> P x.
Proof. intros a P x H. exact (proj2 (proj1 (sep_spec a P x) H)). Qed.

Lemma Sub_refl : forall a, Sub a a.
Proof. intros a x H. exact H. Qed.

(* THE LINCHPIN: Powerset gives every set a host. *)
Lemma self_in_power : forall a, a ∈ power a.
Proof. intro a. apply power_intro. apply Sub_refl. Qed.

(* --------------------------- empty set -------------------------------- *)

Definition emptyset : V := sep witness (fun _ => False).

Lemma emptyset_spec : forall x, ~ x ∈ emptyset.
Proof. intros x H. exact (sep_elim2 witness (fun _ => False) x H). Qed.

(* ------------- the two-element seed  {empty, {empty}} ----------------- *)

Definition single_empty : V := power emptyset.   (* {empty}      *)
Definition pair_empty   : V := power single_empty. (* {empty,{empty}} *)

Lemma in_single_empty : forall x, x ∈ single_empty <-> x = emptyset.
Proof.
  intro x. unfold single_empty. split.
  - intro H. apply power_elim in H.            (* H : Sub x emptyset *)
    apply Extensionality. intro y. split.
    + intro Hy. exact (H y Hy).
    + intro Hy. exfalso. exact (emptyset_spec y Hy).
  - intro H. subst x. apply power_intro. apply Sub_refl.
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

Lemma empty_in_pair : emptyset ∈ pair_empty.
Proof.
  unfold pair_empty. apply power_intro.
  intros y Hy. exfalso. exact (emptyset_spec y Hy).
Qed.

Lemma single_in_pair : single_empty ∈ pair_empty.
Proof. unfold pair_empty. apply power_intro. apply Sub_refl. Qed.

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
  assert (HSL : SetLike (pairRel a b)).
  { intro x.
    destruct (classic (x = emptyset)) as [Hx | Hx].
    - exists (power a). intros z HR. unfold pairRel in HR.
      destruct HR as [[_ Hz] | [Hxs _]].
      + subst z. apply self_in_power.
      + exfalso. apply empty_neq_single. rewrite <- Hx. exact Hxs.
    - destruct (classic (x = single_empty)) as [Hs | Hs].
      + exists (power b). intros z HR. unfold pairRel in HR.
        destruct HR as [[Hxe _] | [_ Hz]].
        * exfalso. apply Hx. exact Hxe.
        * subst z. apply self_in_power.
      + exists emptyset. intros z HR. unfold pairRel in HR.
        destruct HR as [[Hxe _] | [Hxs _]].
        * exfalso. apply Hx. exact Hxe.
        * exfalso. apply Hs. exact Hxs. }
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
  intro x. split.
  - intro H. exact (sep_elim2 _ _ _ H).
  - intro H. apply sep_intro.
    + destruct H as [Hxa | Hxb]; [ subst x; exact Ha | subst x; exact Hb ].
    + exact H.
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
  intro x. split.
  - intro H. exact (sep_elim2 _ _ _ H).
  - intro H. apply sep_intro.
    + destruct H as [v [Hxv Hvs]]. apply (Hclosed x v).
      * unfold memRel. exact Hxv.
      * apply Hsub. exact Hvs.
    + exact H.
Qed.

(* ============================ REPLACEMENT =========================== *)

Theorem Replacement :
  forall (F : V -> V) (a : V),
    exists r, forall y, y ∈ r <-> exists x, x ∈ a /\ y = F x.
Proof.
  intros F a.
  assert (HSL : SetLike (graphRel F a)).
  { intro x. exists (power (F x)). intros z HR. unfold graphRel in HR.
    destruct HR as [_ Hz]. subst z. apply self_in_power. }
  destruct (Closure (graphRel F a) HSL a) as [w [Hsub Hclosed]].
  exists (sep w (fun y => exists x, x ∈ a /\ y = F x)).
  intro y. split.
  - intro H. exact (sep_elim2 _ _ _ H).
  - intro H. apply sep_intro.
    + destruct H as [x [Hxa Hyf]]. apply (Hclosed y x).
      * unfold graphRel. split; [ exact Hxa | exact Hyf ].
      * apply Hsub. exact Hxa.
    + exact H.
Qed.

(* ============================== INFINITY ============================ *)

Lemma singleton_exists : forall x, exists s, forall t, t ∈ s <-> t = x.
Proof.
  intro x. destruct (Pairing x x) as [p Hp]. exists p. intro t. split.
  - intro H. destruct (proj1 (Hp t) H) as [E | E]; exact E.
  - intro H. apply (proj2 (Hp t)). left. exact H.
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
  assert (HSL : SetLike succRel).
  { intro x. destruct (succ_exists x) as [sx Hsx].
    exists (power sx). intros z HR. unfold succRel in HR.
    assert (Hz : z = sx).
    { apply Extensionality. intro t. split.
      - intro Ht. apply (proj2 (Hsx t)). exact (proj1 (HR t) Ht).
      - intro Ht. apply (proj2 (HR t)).  exact (proj1 (Hsx t) Ht). }
    subst z. apply self_in_power. }
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
