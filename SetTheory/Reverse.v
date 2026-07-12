(* ===================================================================== *)
(*  Reverse.v                                                             *)
(*                                                                       *)
(*  The REVERSE direction of the equivalence: ZF proves the Closure       *)
(*  schema.  We fix an abstract structure (V, mem) and assume the         *)
(*  ordinary ZF axioms                                                    *)
(*      Extensionality, Separation, Powerset, Pairing, Union,            *)
(*      Infinity, Replacement, Regularity                                 *)
(*  and DERIVE: for every set-like class relation R and every set s,      *)
(*  there is a set w containing s and closed under R-predecessors.        *)
(*                                                                       *)
(*  The construction is the textbook one.  Let                            *)
(*      g(t) = t  ∪  { u : exists v in t, R u v }                         *)
(*  (a set: set-likeness yields a bounding function `boundf`, then        *)
(*   Replacement + Union + Separation collect the predecessors), and      *)
(*      W_n = g^n(s)        (iteration on the META-level nat).            *)
(*  To collect { W_n : n } into one object set we map the object          *)
(*  numerals `onat n` (which live in the inductive set `Inf` from         *)
(*  Infinity) to W_n via Replacement; pinning the index needs `onat`      *)
(*  injective, Foundation-free, no Regularity needed.  Then              *)
(*      w = Union (image) = Union_n W_n.                                  *)
(*                                                                       *)
(*  Together with Forward.v this gives both directions of                 *)
(*      {Ext, Reg, Sep, Pow, Closure}  ==  ZF.                            *)
(*                                                                       *)
(*  - Created (UTC): 2026-06-30T04:48:30Z                                 *)
(*  - Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9          *)
(* ===================================================================== *)

From Stdlib Require Import ClassicalEpsilon PeanoNat Lia.

Section ClosureEquivalence_Reverse.

Variable V : Type.
Variable mem : V -> V -> Prop.
Infix "∈" := mem (at level 70, no associativity).

Definition Sub (a b : V) : Prop := forall x, x ∈ a -> x ∈ b.

Lemma Sub_refl : forall a, Sub a a.
Proof. intros a x H. exact H. Qed.

Lemma Sub_trans : forall a b c, Sub a b -> Sub b c -> Sub a c.
Proof. intros a b c Hab Hbc x Hx. apply Hbc. apply Hab. exact Hx. Qed.

Lemma Sub_elim : forall a b x, Sub a b -> x ∈ a -> x ∈ b.
Proof. intros a b x H Hx. exact (H x Hx). Qed.

Variable witness : V.   (* nonempty domain (FOL convention) *)

(* ------------------------------ ZF axioms ----------------------------- *)

Hypothesis Extensionality :
  forall a b, (forall x, x ∈ a <-> x ∈ b) -> a = b.

Hypothesis Separation :
  forall (a : V) (P : V -> Prop),
    exists s, forall x, x ∈ s <-> (x ∈ a /\ P x).

Hypothesis Powerset :
  forall a, exists p, forall x, x ∈ p <-> Sub x a.

Hypothesis Pairing :
  forall a b, exists p, forall x, x ∈ p <-> (x = a \/ x = b).

Hypothesis Union :
  forall s, exists u, forall x, x ∈ u <-> exists v, x ∈ v /\ v ∈ s.

Hypothesis Infinity :
  exists I,
    (exists e, e ∈ I /\ forall z, ~ z ∈ e) /\
    (forall x, x ∈ I ->
       exists sx, sx ∈ I /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).

Hypothesis Replacement :
  forall (F : V -> V) (a : V),
    exists r, forall y, y ∈ r <-> exists x, x ∈ a /\ y = F x.

Hypothesis Regularity :
  forall a, (exists x, x ∈ a) ->
            exists m, m ∈ a /\ ~ (exists z, z ∈ m /\ z ∈ a).

Definition SetLike (R : V -> V -> Prop) : Prop :=
  forall x, exists y, forall z, R z x -> z ∈ y.

(* --------------------- ZF operators as functions ---------------------- *)

Definition sep (a : V) (P : V -> Prop) : V :=
  proj1_sig (constructive_indefinite_description _ (Separation a P)).
Lemma sep_spec : forall a P x, x ∈ sep a P <-> (x ∈ a /\ P x).
Proof. intros a P. exact (proj2_sig (constructive_indefinite_description _ (Separation a P))). Qed.
Lemma sep_intro : forall a P x, x ∈ a -> P x -> x ∈ sep a P.
Proof. intros a P x H1 H2. exact (proj2 (sep_spec a P x) (conj H1 H2)). Qed.
Lemma sep_elim2 : forall a P x, x ∈ sep a P -> P x.
Proof. intros a P x H. exact (proj2 (proj1 (sep_spec a P x) H)). Qed.

Definition emptyset : V := sep witness (fun _ => False).
Lemma emptyset_spec : forall x, ~ x ∈ emptyset.
Proof. intros x H. exact (sep_elim2 witness (fun _ => False) x H). Qed.

Definition opair2 (a b : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Pairing a b)).
Lemma opair2_spec : forall a b x, x ∈ opair2 a b <-> (x = a \/ x = b).
Proof. intros a b. exact (proj2_sig (constructive_indefinite_description _ (Pairing a b))). Qed.

Definition osingle (a : V) : V := opair2 a a.
Lemma osingle_spec : forall a x, x ∈ osingle a <-> x = a.
Proof.
  intros a x. unfold osingle. split.
  - intro H. apply (proj1 (opair2_spec a a x)) in H. destruct H as [H|H]; exact H.
  - intro H. apply (proj2 (opair2_spec a a x)). left. exact H.
Qed.

Definition ounion (s : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Union s)).
Lemma ounion_spec : forall s x, x ∈ ounion s <-> exists v, x ∈ v /\ v ∈ s.
Proof. intro s. exact (proj2_sig (constructive_indefinite_description _ (Union s))). Qed.

Definition obin (a b : V) : V := ounion (opair2 a b).
Lemma obin_spec : forall a b x, x ∈ obin a b <-> (x ∈ a \/ x ∈ b).
Proof.
  intros a b x. unfold obin. split.
  - intro H. apply (proj1 (ounion_spec (opair2 a b) x)) in H.
    destruct H as [v [Hxv Hv]]. apply (proj1 (opair2_spec a b v)) in Hv.
    destruct Hv as [Hva|Hvb]; [ left | right ]; subst v; exact Hxv.
  - intro H. apply (proj2 (ounion_spec (opair2 a b) x)). destruct H as [Ha|Hb].
    + exists a. split; [ exact Ha | apply (proj2 (opair2_spec a b a)); left; reflexivity ].
    + exists b. split; [ exact Hb | apply (proj2 (opair2_spec a b b)); right; reflexivity ].
Qed.

Definition osucc (a : V) : V := obin a (osingle a).
Lemma osucc_spec : forall a x, x ∈ osucc a <-> (x ∈ a \/ x = a).
Proof.
  intros a x. unfold osucc. split.
  - intro H. apply (proj1 (obin_spec a (osingle a) x)) in H. destruct H as [Ha|Hs].
    + left. exact Ha.
    + right. apply (proj1 (osingle_spec a x)) in Hs. exact Hs.
  - intro H. apply (proj2 (obin_spec a (osingle a) x)). destruct H as [Ha|He].
    + left. exact Ha.
    + right. apply (proj2 (osingle_spec a x)). exact He.
Qed.

Lemma osucc_super : forall a, Sub a (osucc a).
Proof. intros a x Hx. apply (proj2 (osucc_spec a x)). left. exact Hx. Qed.

Definition imageR (F : V -> V) (a : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Replacement F a)).
Lemma imageR_spec : forall F a y, y ∈ imageR F a <-> exists x, x ∈ a /\ y = F x.
Proof. intros F a. exact (proj2_sig (constructive_indefinite_description _ (Replacement F a))). Qed.

(* ----- Regularity is a CONVENIENCE here, not a necessity --------------- *)
(* The construction below needs the numerals  onat n  to be pairwise        *)
(* distinct.  The original proof got this from Regularity, via the fact      *)
(* that no set is a member of itself.  But that global fact is far more than  *)
(* we need: the finite von Neumann numerals are distinct in ZF WITHOUT       *)
(* Foundation,                                                               *)
(* because each onat n is a genuine ordinal -- a transitive set on which     *)
(* membership is irreflexive -- which we prove by induction on n             *)
(* (onat_trans, onat_no_self) using only Pairing/Union (osucc).  So          *)
(* Regularity, like Choice, is a passenger of the trade: the trailing        *)
(* `Check Closure_holds` does not list it.  (The Regularity hypothesis is    *)
(* kept above for completeness as a ZF axiom; it is simply never used.)      *)

(* --------------------- object numerals onat : nat -> V ----------------- *)

Fixpoint onat (n : nat) : V :=
  match n with
  | O   => emptyset
  | S k => osucc (onat k)
  end.

Lemma onat_self_in_succ : forall i, onat i ∈ onat (S i).
Proof.
  intro i. simpl. apply (proj2 (osucc_spec (onat i) (onat i))). right. reflexivity.
Qed.

Lemma onat_mono : forall j i, (i <= j)%nat -> Sub (onat i) (onat j).
Proof.
  induction j; intros i Hij.
  - assert (i = 0) by lia. subst i. apply Sub_refl.
  - apply Nat.le_succ_r in Hij. destruct Hij as [Hle|Heq].
    + apply Sub_trans with (onat j).
      * apply IHj. exact Hle.
      * simpl. apply osucc_super.
    + subst i. apply Sub_refl.
Qed.

Lemma onat_lt_mem : forall i j, (i < j)%nat -> onat i ∈ onat j.
Proof.
  intros i j Hij.
  apply (Sub_elim (onat (S i)) (onat j) (onat i)).
  - apply onat_mono. lia.
  - apply onat_self_in_succ.
Qed.

(* Each numeral is a transitive set -- proved by induction, Foundation-free. *)
Lemma onat_trans : forall n x, x ∈ onat n -> Sub x (onat n).
Proof.
  induction n; intros x Hx.
  - simpl in Hx. exfalso. exact (emptyset_spec x Hx).
  - simpl in Hx. apply (proj1 (osucc_spec (onat n) x)) in Hx.
    destruct Hx as [Hxin | Hxeq].
    + apply Sub_trans with (onat n).
      * apply IHn. exact Hxin.
      * apply osucc_super.
    + subst x. apply osucc_super.
Qed.

(* Hence no numeral is a member of itself -- WITHOUT Regularity.  If         *)
(* onat n in onat n then, since onat n is transitive, onat n would be a      *)
(* subset of itself containing itself, contradicting the inductive case.     *)
Lemma onat_no_self : forall n, ~ onat n ∈ onat n.
Proof.
  induction n; intro H.
  - simpl in H. exact (emptyset_spec _ H).
  - simpl in H. apply (proj1 (osucc_spec (onat n) (osucc (onat n)))) in H.
    destruct H as [Hin | Heq].
    + apply IHn. apply (onat_trans n (osucc (onat n)) Hin).
      apply (proj2 (osucc_spec (onat n) (onat n))). right. reflexivity.
    + apply IHn.
      assert (Hmem : onat n ∈ osucc (onat n)).
      { apply (proj2 (osucc_spec (onat n) (onat n))). right. reflexivity. }
      rewrite Heq in Hmem. exact Hmem.
Qed.

Lemma onat_inj : forall i j, onat i = onat j -> i = j.
Proof.
  intros i j H. destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
  - exfalso. assert (Hm : onat i ∈ onat j) by (apply onat_lt_mem; exact Hlt).
    rewrite <- H in Hm. exact (onat_no_self i Hm).
  - exact Heq.
  - exfalso. assert (Hm : onat j ∈ onat i) by (apply onat_lt_mem; exact Hgt).
    rewrite H in Hm. exact (onat_no_self j Hm).
Qed.

(* --------------------- an inductive set from Infinity ------------------ *)

Definition Inf : V := proj1_sig (constructive_indefinite_description _ Infinity).
Lemma Inf_spec :
  (exists e, e ∈ Inf /\ forall z, ~ z ∈ e) /\
  (forall x, x ∈ Inf ->
     exists sx, sx ∈ Inf /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).
Proof. exact (proj2_sig (constructive_indefinite_description _ Infinity)). Qed.

Lemma empty_in_Inf : emptyset ∈ Inf.
Proof.
  destruct Inf_spec as [[e [He Hemp]] _].
  assert (e = emptyset).
  { apply Extensionality. intro t. split; intro Ht.
    - exfalso. exact (Hemp t Ht).
    - exfalso. exact (emptyset_spec t Ht). }
  subst e. exact He.
Qed.

Lemma osucc_in_Inf : forall x, x ∈ Inf -> osucc x ∈ Inf.
Proof.
  intros x Hx. destruct Inf_spec as [_ Hsucc].
  destruct (Hsucc x Hx) as [sx [Hsx Hsxspec]].
  assert (sx = osucc x).
  { apply Extensionality. intro t. split; intro Ht.
    - apply (proj2 (osucc_spec x t)). exact (proj1 (Hsxspec t) Ht).
    - apply (proj2 (Hsxspec t)).        exact (proj1 (osucc_spec x t) Ht). }
  subst sx. exact Hsx.
Qed.

Lemma onat_in_Inf : forall n, onat n ∈ Inf.
Proof.
  induction n.
  - exact empty_in_Inf.
  - simpl. apply osucc_in_Inf. exact IHn.
Qed.

(* ------------------- the one-step closure operator g ------------------- *)

(* set-likeness yields a bounding function for the predecessors *)
Definition boundf (R : V -> V -> Prop) (HSL : SetLike R) : V -> V :=
  fun x => proj1_sig (constructive_indefinite_description _ (HSL x)).
Lemma boundf_spec :
  forall R HSL x z, R z x -> z ∈ boundf R HSL x.
Proof.
  intros R HSL x z H.
  exact (proj2_sig (constructive_indefinite_description _ (HSL x)) z H).
Qed.

Definition predsf (R : V -> V -> Prop) (HSL : SetLike R) (t : V) : V :=
  sep (ounion (imageR (boundf R HSL) t)) (fun u => exists v, v ∈ t /\ R u v).
Lemma predsf_spec :
  forall R HSL t u, u ∈ predsf R HSL t <-> (exists v, v ∈ t /\ R u v).
Proof.
  intros R HSL t u. unfold predsf. split.
  - intro H. exact (sep_elim2 _ _ _ H).
  - intro H. apply sep_intro.
    + destruct H as [v [Hvt Hruv]].
      apply (proj2 (ounion_spec (imageR (boundf R HSL) t) u)).
      exists (boundf R HSL v). split.
      * exact (boundf_spec R HSL v u Hruv).
      * apply (proj2 (imageR_spec (boundf R HSL) t (boundf R HSL v))).
        exists v. split; [ exact Hvt | reflexivity ].
    + exact H.
Qed.

Definition gstep (R : V -> V -> Prop) (HSL : SetLike R) (t : V) : V :=
  obin t (predsf R HSL t).
Lemma gstep_spec :
  forall R HSL t x, x ∈ gstep R HSL t <-> (x ∈ t \/ x ∈ predsf R HSL t).
Proof. intros R HSL t x. exact (obin_spec t (predsf R HSL t) x). Qed.

(* ------------------------- iteration on meta nat ---------------------- *)

Fixpoint iterate (g : V -> V) (s : V) (n : nat) : V :=
  match n with
  | O   => s
  | S k => g (iterate g s k)
  end.

Definition Iter (R : V -> V -> Prop) (HSL : SetLike R) (s : V) : nat -> V :=
  iterate (gstep R HSL) s.

Lemma Iter_S :
  forall R HSL s n, Iter R HSL s (S n) = gstep R HSL (Iter R HSL s n).
Proof. intros. unfold Iter. reflexivity. Qed.

(* --------------- map object numerals to their iterate ----------------- *)

(* Non-numerals map to stage 0, so every Ffun value is an iteration stage. *)
Lemma Qtot :
  forall R HSL s m,
    exists y,
      (exists n, m = onat n /\ y = Iter R HSL s n)
      \/ ((forall n, m <> onat n) /\ y = Iter R HSL s 0).
Proof.
  intros R HSL s m. destruct (classic (exists n, m = onat n)) as [[n Hn] | Hno].
  - exists (Iter R HSL s n). left. exists n. split; [ exact Hn | reflexivity ].
  - exists (Iter R HSL s 0). right. split.
    + intros n Hmn. apply Hno. exists n. exact Hmn.
    + reflexivity.
Qed.

Definition Ffun (R : V -> V -> Prop) (HSL : SetLike R) (s : V) (m : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Qtot R HSL s m)).
Lemma Ffun_spec :
  forall R HSL s m,
    (exists n, m = onat n /\ Ffun R HSL s m = Iter R HSL s n)
    \/ ((forall n, m <> onat n) /\ Ffun R HSL s m = Iter R HSL s 0).
Proof.
  intros R HSL s m.
  exact (proj2_sig (constructive_indefinite_description _ (Qtot R HSL s m))).
Qed.

Lemma F_onat : forall R HSL s k, Ffun R HSL s (onat k) = Iter R HSL s k.
Proof.
  intros R HSL s k. destruct (Ffun_spec R HSL s (onat k)) as [[n [Hn Hy]] | [Hno _]].
  - apply onat_inj in Hn. subst n. exact Hy.
  - exfalso. apply (Hno k). reflexivity.
Qed.

Lemma F_cases :
  forall R HSL s m,
    exists n, Ffun R HSL s m = Iter R HSL s n.
Proof.
  intros R HSL s m. destruct (Ffun_spec R HSL s m) as [[n [_ Hy]] | [_ Hy]].
  - exists n. exact Hy.
  - exists 0. exact Hy.
Qed.

(* ============================== CLOSURE ============================== *)

Theorem Closure_holds :
  forall R : V -> V -> Prop, SetLike R ->
    forall s, exists w, Sub s w /\ (forall u v, R u v -> v ∈ w -> u ∈ w).
Proof.
  intros R HSL s.
  exists (ounion (imageR (Ffun R HSL s) Inf)).
  split.
  - (* Sub s w *)
    intros y Hy.
    apply (proj2 (ounion_spec (imageR (Ffun R HSL s) Inf) y)).
    exists (Iter R HSL s 0). split.
    + change (y ∈ s). exact Hy.
    + apply (proj2 (imageR_spec (Ffun R HSL s) Inf (Iter R HSL s 0))).
      exists (onat 0). split.
      * exact (onat_in_Inf 0).
      * symmetry. exact (F_onat R HSL s 0).
  - (* closed under R-predecessors *)
    intros u v Hruv Hvw.
    apply (proj1 (ounion_spec (imageR (Ffun R HSL s) Inf) v)) in Hvw.
    destruct Hvw as [c [Hvc Hcr]].
    apply (proj1 (imageR_spec (Ffun R HSL s) Inf c)) in Hcr.
    destruct Hcr as [m [_ Hcm]].
    destruct (F_cases R HSL s m) as [n Hn].
    rewrite Hcm in Hvc. rewrite Hn in Hvc.       (* Hvc : v ∈ Iter .. n *)
    apply (proj2 (ounion_spec (imageR (Ffun R HSL s) Inf) u)).
    exists (Iter R HSL s (S n)). split.
    + rewrite (Iter_S R HSL s n).
      apply (proj2 (gstep_spec R HSL (Iter R HSL s n) u)).
      right.
      apply (proj2 (predsf_spec R HSL (Iter R HSL s n) u)).
      exists v. split; [ exact Hvc | exact Hruv ].
    + apply (proj2 (imageR_spec (Ffun R HSL s) Inf (Iter R HSL s (S n)))).
      exists (onat (S n)). split.
      * exact (onat_in_Inf (S n)).
      * symmetry. exact (F_onat R HSL s (S n)).
Qed.

End ClosureEquivalence_Reverse.

Check Closure_holds.
