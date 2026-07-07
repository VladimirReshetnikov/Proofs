(* ===================================================================== *)
(*  PAHF.v                                                               *)
(*                                                                       *)
(*  A Rocq/Coq semantic certificate for the standard bi-interpretability *)
(*  picture between Peano Arithmetic and Ackermann hereditary finite     *)
(*  sets.  This file deliberately mirrors the final Lean certificate at  *)
(*  the semantic/model level: standard PA, Ackermann HF over nat, the    *)
(*  finite-ordinal embedding of PA objects into HF, the Ackermann coding *)
(*  of HF objects by PA naturals, and explicit round-trip isomorphisms.  *)
(*                                                                       *)
(*  It does not smuggle proof obligations into definitions: the HF model *)
(*  properties are proved from Coq's concrete Nat.testbit API, including *)
(*  extensionality, adjunction, and set induction via x in y -> x < y.   *)
(*  The final section also states, without inhabiting, the future          *)
(*  deductive target for a genuine theory-level bi-interpretation.        *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Bool.Bool Lia PeanoNat List.
From Stdlib Require Import ClassicalEpsilon ProofIrrelevance.
From SetTheory Require Import Fol Completeness.
Import ListNotations.

Record PAModel := {
  pa_carrier :> Type;
  pa_zero : pa_carrier;
  pa_succ : pa_carrier -> pa_carrier;
  pa_add : pa_carrier -> pa_carrier -> pa_carrier;
  pa_mul : pa_carrier -> pa_carrier -> pa_carrier;
  pa_succ_injective : forall a b, pa_succ a = pa_succ b -> a = b;
  pa_zero_not_succ : forall a, pa_succ a <> pa_zero;
  pa_add_zero : forall a, pa_add a pa_zero = a;
  pa_add_succ : forall a b, pa_add a (pa_succ b) = pa_succ (pa_add a b);
  pa_mul_zero : forall a, pa_mul a pa_zero = pa_zero;
  pa_mul_succ : forall a b, pa_mul a (pa_succ b) = pa_add (pa_mul a b) a;
  pa_induction : forall P : pa_carrier -> Prop,
    P pa_zero -> (forall n, P n -> P (pa_succ n)) -> forall n, P n
}.

Definition natPAModel : PAModel.
Proof.
  refine {| pa_carrier := nat;
            pa_zero := 0;
            pa_succ := S;
            pa_add := Nat.add;
            pa_mul := Nat.mul |}.
  - intros a b H. now apply Nat.succ_inj.
  - intros a H. discriminate H.
  - exact Nat.add_0_r.
  - exact Nat.add_succ_r.
  - exact Nat.mul_0_r.
  - exact Nat.mul_succ_r.
  - intros P H0 HS n. induction n; auto.
Defined.

Record PAIso (M N : PAModel) := {
  pa_iso_to : M -> N;
  pa_iso_inv : N -> M;
  pa_iso_left_inv : forall a, pa_iso_inv (pa_iso_to a) = a;
  pa_iso_right_inv : forall b, pa_iso_to (pa_iso_inv b) = b;
  pa_iso_map_zero : pa_iso_to (pa_zero M) = pa_zero N;
  pa_iso_map_succ : forall a,
    pa_iso_to (pa_succ M a) = pa_succ N (pa_iso_to a);
  pa_iso_map_add : forall a b,
    pa_iso_to (pa_add M a b) = pa_add N (pa_iso_to a) (pa_iso_to b);
  pa_iso_map_mul : forall a b,
    pa_iso_to (pa_mul M a b) = pa_mul N (pa_iso_to a) (pa_iso_to b)
}.

Definition PA_identity_iso (M : PAModel) : PAIso M M.
Proof.
  refine {| pa_iso_to := fun x => x; pa_iso_inv := fun x => x |};
    reflexivity.
Defined.

Definition hf_mem (x y : nat) : Prop := Nat.testbit y x = true.
Definition hf_empty : nat := 0.
Definition hf_adjoin (a b : nat) : nat := Nat.lor b (2 ^ a).

Lemma hf_mem_empty : forall x, ~ hf_mem x hf_empty.
Proof.
  intros x H.
  unfold hf_mem, hf_empty in H.
  rewrite Nat.bits_0 in H.
  discriminate.
Qed.

Lemma bool_true_iff_eq_true : forall a b : bool,
  (a = true <-> b = true) -> a = b.
Proof.
  intros a b H.
  destruct a, b; try reflexivity; exfalso; destruct H as [H1 H2].
  - discriminate (H1 eq_refl).
  - discriminate (H2 eq_refl).
Qed.

Lemma hf_ext : forall a b,
  (forall x, hf_mem x a <-> hf_mem x b) -> a = b.
Proof.
  intros a b H.
  apply Nat.bits_inj.
  intros x.
  apply bool_true_iff_eq_true.
  unfold hf_mem in H.
  apply H.
Qed.

Lemma hf_mem_adjoin : forall x a b,
  hf_mem x (hf_adjoin a b) <-> hf_mem x b \/ x = a.
Proof.
  intros x a b.
  unfold hf_mem, hf_adjoin.
  rewrite Nat.lor_spec.
  rewrite Nat.pow2_bits_eqb.
  destruct (Nat.testbit b x) eqn:Hb; simpl.
  - split; intros _; auto.
  - rewrite Nat.eqb_eq.
    split.
    + intro H. right. symmetry. exact H.
    + intro H. destruct H as [H | H]; [discriminate | symmetry; exact H].
Qed.

Lemma hf_mem_lt : forall x y, hf_mem x y -> x < y.
Proof.
  intros x y H.
  destruct y as [|y].
  - exfalso.
    unfold hf_mem in H.
    rewrite Nat.bits_0 in H.
    discriminate.
  - destruct (le_gt_dec (S y) x) as [Hyx | Hlt]; [|lia].
    exfalso.
    assert (Nat.log2 (S y) < x) as Hlog by
      (pose proof (Nat.log2_lt_lin (S y) (Nat.lt_0_succ y)); lia).
    unfold hf_mem in H.
    rewrite (Nat.bits_above_log2 (S y) x Hlog) in H.
    discriminate.
Qed.

Lemma hf_nonempty_nonzero : forall a,
  (exists x, hf_mem x a) -> a <> 0.
Proof.
  intros a [x hx] ha.
  subst a.
  exact (hf_mem_empty x hx).
Qed.

Lemma hf_log2_mem : forall a,
  a <> 0 -> hf_mem (Nat.log2 a) a.
Proof.
  intros a ha.
  unfold hf_mem.
  now apply Nat.bit_log2.
Qed.

Lemma hf_mem_le_log2 : forall x a,
  hf_mem x a -> x <= Nat.log2 a.
Proof.
  intros x a hx.
  destruct (le_gt_dec x (Nat.log2 a)) as [hle | hgt].
  - exact hle.
  - exfalso.
    unfold hf_mem in hx.
    rewrite (Nat.bits_above_log2 a x hgt) in hx.
    discriminate.
Qed.

Lemma hf_mem_max_exists : forall a,
  (exists x, hf_mem x a) ->
  exists p, hf_mem p a /\ forall q, hf_mem q a -> ~ hf_mem p q.
Proof.
  intros a hne.
  pose (p := Nat.log2 a).
  assert (ha : a <> 0) by now apply hf_nonempty_nonzero.
  exists p.
  split.
  - unfold p. now apply hf_log2_mem.
  - intros q hq hpq.
    pose proof (hf_mem_le_log2 q a hq) as hqle.
    pose proof (hf_mem_lt p q hpq) as hp_lt_q.
    lia.
Qed.

Lemma hf_eq_empty_iff_no_mem : forall a,
  a = hf_empty <-> forall x, ~ hf_mem x a.
Proof.
  intros a.
  split.
  - intros -> x. apply hf_mem_empty.
  - intro h.
    apply hf_ext.
    intro x.
    split.
    + intro hx. exfalso. exact (h x hx).
    + intro hx. exfalso. exact (hf_mem_empty x hx).
Qed.

Lemma hf_exists_mem_of_ne_empty : forall a,
  a <> hf_empty -> exists x, hf_mem x a.
Proof.
  intros a ha.
  exists (Nat.log2 a).
  apply hf_log2_mem.
  exact ha.
Qed.

Lemma hf_not_mem_self : forall a, ~ hf_mem a a.
Proof.
  intros a haa.
  pose proof (hf_mem_lt a a haa).
  lia.
Qed.

Lemma hf_mem_asymm : forall a b, hf_mem a b -> ~ hf_mem b a.
Proof.
  intros a b hab hba.
  pose proof (hf_mem_lt a b hab).
  pose proof (hf_mem_lt b a hba).
  lia.
Qed.

Lemma hf_set_induction : forall P : nat -> Prop,
  (forall a, (forall x, hf_mem x a -> P x) -> P a) -> forall a, P a.
Proof.
  intros P step a.
  induction a as [a IH] using lt_wf_ind.
  apply step.
  intros x Hx.
  apply IH.
  now apply hf_mem_lt.
Qed.

Record HFModel := {
  hf_carrier :> Type;
  hf_rel : hf_carrier -> hf_carrier -> Prop;
  hf_empty_obj : hf_carrier;
  hf_adjoin_obj : hf_carrier -> hf_carrier -> hf_carrier;
  hf_extensional : forall a b,
    (forall x, hf_rel x a <-> hf_rel x b) -> a = b;
  hf_empty_spec : forall x, ~ hf_rel x hf_empty_obj;
  hf_adjoin_spec : forall x a b,
    hf_rel x (hf_adjoin_obj a b) <-> hf_rel x b \/ x = a;
  hf_set_ind : forall P : hf_carrier -> Prop,
    (forall a, (forall x, hf_rel x a -> P x) -> P a) -> forall a, P a
}.

Definition ackermannHFModel : HFModel.
Proof.
  refine {| hf_carrier := nat;
            hf_rel := hf_mem;
            hf_empty_obj := hf_empty;
            hf_adjoin_obj := hf_adjoin |}.
  - exact hf_ext.
  - exact hf_mem_empty.
  - exact hf_mem_adjoin.
  - exact hf_set_induction.
Defined.

Record HFIso (M N : HFModel) := {
  hf_iso_to : M -> N;
  hf_iso_inv : N -> M;
  hf_iso_left_inv : forall a, hf_iso_inv (hf_iso_to a) = a;
  hf_iso_right_inv : forall b, hf_iso_to (hf_iso_inv b) = b;
  hf_iso_map_mem : forall a b,
    hf_rel N (hf_iso_to a) (hf_iso_to b) <-> hf_rel M a b;
  hf_iso_map_empty : hf_iso_to (hf_empty_obj M) = hf_empty_obj N;
  hf_iso_map_adjoin : forall a b,
    hf_iso_to (hf_adjoin_obj M a b) =
    hf_adjoin_obj N (hf_iso_to a) (hf_iso_to b)
}.

Definition HF_identity_iso (M : HFModel) : HFIso M M.
Proof.
  refine {| hf_iso_to := fun x => x; hf_iso_inv := fun x => x |};
    reflexivity.
Defined.

Fixpoint ordinal_code (n : nat) : nat :=
  match n with
  | 0 => hf_empty
  | S k => hf_adjoin (ordinal_code k) (ordinal_code k)
  end.

Lemma ordinal_code_zero : ordinal_code 0 = hf_empty.
Proof. reflexivity. Qed.

Lemma ordinal_code_succ : forall n,
  ordinal_code (S n) = hf_adjoin (ordinal_code n) (ordinal_code n).
Proof. reflexivity. Qed.

Lemma hf_mem_ordinal_code_succ : forall x n,
  hf_mem x (ordinal_code (S n)) <->
    hf_mem x (ordinal_code n) \/ x = ordinal_code n.
Proof.
  intros x n.
  simpl.
  apply hf_mem_adjoin.
Qed.

Lemma ordinal_code_mem_of_lt : forall k n,
  k < n -> hf_mem (ordinal_code k) (ordinal_code n).
Proof.
  intros k n hkn.
  revert k hkn.
  induction n as [|n IH]; intros k hkn.
  - lia.
  - rewrite hf_mem_ordinal_code_succ.
    destruct (Nat.eq_dec k n) as [-> | hne].
    + right. reflexivity.
    + left. apply IH. lia.
Qed.

Lemma ordinal_code_lt_of_lt : forall k n,
  k < n -> ordinal_code k < ordinal_code n.
Proof.
  intros k n hkn.
  apply hf_mem_lt.
  now apply ordinal_code_mem_of_lt.
Qed.

Lemma hf_mem_ordinal_code_iff : forall x n,
  hf_mem x (ordinal_code n) <->
    exists k, k < n /\ x = ordinal_code k.
Proof.
  intros x n.
  induction n as [|n IH].
  - split.
    + intro hx. exfalso. exact (hf_mem_empty x hx).
    + intros [k [hk hx]]. lia.
  - rewrite hf_mem_ordinal_code_succ.
    split.
    + intros [hx | hx].
      * destruct (proj1 IH hx) as [k [hk heq]].
        exists k. split; [lia | exact heq].
      * exists n. split; [lia | exact hx].
    + intros [k [hk hx]].
      destruct (Nat.eq_dec k n) as [-> | hne].
      * right. exact hx.
      * left. apply (proj2 IH).
        exists k. split; [lia | exact hx].
Qed.

Lemma ordinal_code_transitive : forall n y x,
  hf_mem y (ordinal_code n) -> hf_mem x y ->
  hf_mem x (ordinal_code n).
Proof.
  intros n y x hy hx.
  destruct (proj1 (hf_mem_ordinal_code_iff y n) hy) as [k [hk hy_eq]].
  subst y.
  destruct (proj1 (hf_mem_ordinal_code_iff x k) hx) as [j [hj hx_eq]].
  subst x.
  apply ordinal_code_mem_of_lt.
  lia.
Qed.

Lemma ordinal_code_members_transitive : forall n y,
  hf_mem y (ordinal_code n) ->
  forall x, hf_mem x y -> hf_mem x (ordinal_code n).
Proof.
  intros n y hy x hx.
  eapply ordinal_code_transitive; eauto.
Qed.

Lemma ordinal_code_mem_total : forall n y z,
  hf_mem y (ordinal_code n) -> hf_mem z (ordinal_code n) ->
  hf_mem y z \/ y = z \/ hf_mem z y.
Proof.
  intros n y z hy hz.
  destruct (proj1 (hf_mem_ordinal_code_iff y n) hy) as [i [hi hy_eq]].
  destruct (proj1 (hf_mem_ordinal_code_iff z n) hz) as [j [hj hz_eq]].
  subst y z.
  destruct (Nat.lt_trichotomy i j) as [hij | [hij | hij]].
  - left. now apply ordinal_code_mem_of_lt.
  - right. left. now subst j.
  - right. right. now apply ordinal_code_mem_of_lt.
Qed.

Lemma ordinal_code_injective : forall m n,
  ordinal_code m = ordinal_code n -> m = n.
Proof.
  intros m n h.
  destruct (Nat.lt_trichotomy m n) as [hmn | [hmn | hnm]]; [|exact hmn|].
  - pose proof (ordinal_code_lt_of_lt m n hmn) as hlt.
    lia.
  - pose proof (ordinal_code_lt_of_lt n m hnm) as hlt.
    lia.
Qed.

Definition hf_transitive_obj (a : nat) : Prop :=
  forall y, hf_mem y a -> forall x, hf_mem x y -> hf_mem x a.

Definition hf_mem_total_on (a : nat) : Prop :=
  forall y, hf_mem y a -> forall z, hf_mem z a ->
    hf_mem y z \/ y = z \/ hf_mem z y.

Definition hf_chain_like (a : nat) : Prop :=
  (forall y, hf_mem y a -> hf_transitive_obj y) /\ hf_mem_total_on a.

Definition hf_ordinal_like (a : nat) : Prop :=
  hf_transitive_obj a /\
  (forall y, hf_mem y a -> hf_transitive_obj y) /\
  hf_mem_total_on a.

Lemma hf_ordinal_like_of_mem : forall a y,
  hf_ordinal_like a -> hf_mem y a -> hf_ordinal_like y.
Proof.
  unfold hf_ordinal_like, hf_transitive_obj, hf_mem_total_on.
  intros a y [htrans [hmtrans htotal]] hy.
  split.
  - exact (hmtrans y hy).
  - split.
    + intros z hz.
      apply hmtrans.
      eapply htrans; eauto.
    + intros u hu z hz.
      apply htotal.
      * eapply htrans; eauto.
      * eapply htrans; eauto.
Qed.

Lemma hf_ordinal_like_empty : hf_ordinal_like hf_empty.
Proof.
  unfold hf_ordinal_like, hf_transitive_obj, hf_mem_total_on.
  split.
  - intros y hy. exfalso. exact (hf_mem_empty y hy).
  - split.
    + intros y hy. exfalso. exact (hf_mem_empty y hy).
    + intros y hy. exfalso. exact (hf_mem_empty y hy).
Qed.

Lemma hf_ordinal_like_adjoin_self : forall a s,
  hf_ordinal_like a -> s = hf_adjoin a a -> hf_ordinal_like s.
Proof.
  unfold hf_ordinal_like, hf_transitive_obj, hf_mem_total_on.
  intros a s [htrans [hmtrans htotal]] hs.
  subst s.
  split.
  - intros y hy x hx.
    rewrite hf_mem_adjoin in hy.
    rewrite hf_mem_adjoin.
    destruct hy as [hyin | hyeq].
    + left. eapply htrans; eauto.
    + subst y. left. exact hx.
  - split.
    + intros y hy.
      rewrite hf_mem_adjoin in hy.
      destruct hy as [hyin | hyeq].
      * exact (hmtrans y hyin).
      * subst y. exact htrans.
    + intros y hy z hz.
      rewrite hf_mem_adjoin in hy.
      rewrite hf_mem_adjoin in hz.
      destruct hy as [hyin | hyeq];
      destruct hz as [hzin | hzeq].
      * exact (htotal y hyin z hzin).
      * left. subst z. exact hyin.
      * right. right. subst y. exact hzin.
      * right. left. congruence.
Qed.

Lemma ordinal_code_transitive_obj : forall n,
  hf_transitive_obj (ordinal_code n).
Proof.
  unfold hf_transitive_obj.
  intros n y hy x hx.
  eapply ordinal_code_transitive; eauto.
Qed.

Lemma ordinal_code_members_transitive_obj : forall n,
  forall y, hf_mem y (ordinal_code n) -> hf_transitive_obj y.
Proof.
  unfold hf_transitive_obj.
  intros n y hy z hz x hx.
  destruct (proj1 (hf_mem_ordinal_code_iff y n) hy) as [k [hk hy_eq]].
  subst y.
  eapply ordinal_code_transitive; eauto.
Qed.

Lemma ordinal_code_mem_total_on : forall n,
  hf_mem_total_on (ordinal_code n).
Proof.
  unfold hf_mem_total_on.
  intros n y hy z hz.
  eapply ordinal_code_mem_total; eauto.
Qed.

Lemma ordinal_code_chain_like : forall n,
  hf_chain_like (ordinal_code n).
Proof.
  intros n.
  split.
  - apply ordinal_code_members_transitive_obj.
  - apply ordinal_code_mem_total_on.
Qed.

Lemma ordinal_code_ordinal_like : forall n,
  hf_ordinal_like (ordinal_code n).
Proof.
  intros n.
  split.
  - apply ordinal_code_transitive_obj.
  - split.
    + apply ordinal_code_members_transitive_obj.
    + apply ordinal_code_mem_total_on.
Qed.

Definition is_ordinal_code (a : nat) : Prop :=
  exists n, ordinal_code n = a.

Lemma ordinal_code_is_ordinal_code : forall n,
  is_ordinal_code (ordinal_code n).
Proof.
  intro n.
  exists n.
  reflexivity.
Qed.

Lemma hf_ordinal_like_is_ordinal_code : forall a,
  hf_ordinal_like a -> is_ordinal_code a.
Proof.
  intros a.
  induction a as [a IH] using lt_wf_ind.
  intro ha.
  destruct (Nat.eq_dec a hf_empty) as [hzero | hnonempty].
  - subst a.
    exists 0.
    reflexivity.
  - destruct (hf_mem_max_exists a (hf_exists_mem_of_ne_empty a hnonempty))
      as [m [hm hmax]].
    destruct (IH m (hf_mem_lt m a hm)
      (hf_ordinal_like_of_mem a m ha hm)) as [k hk].
    exists (S k).
    apply hf_ext.
    intro x.
    split.
    + intro hx.
      pose proof ha as ha_parts.
      destruct ha_parts as [htrans [_hmtrans _htotal]].
      rewrite hf_mem_ordinal_code_succ in hx.
      destruct hx as [hxk | hxk].
      * apply (htrans m hm x).
        rewrite <- hk.
        exact hxk.
      * subst x.
        rewrite hk.
        exact hm.
    + intro hx.
      destruct (IH x (hf_mem_lt x a hx)
        (hf_ordinal_like_of_mem a x ha hx)) as [j hj].
      assert (hjle : j <= k).
      {
        destruct (le_gt_dec j k) as [hle | hgt].
        - exact hle.
        - exfalso.
          assert (hkj : k < j) by lia.
          pose proof (ordinal_code_mem_of_lt k j hkj) as hlt.
          rewrite hk in hlt.
          rewrite hj in hlt.
          exact (hmax x hx hlt).
      }
      rewrite hf_mem_ordinal_code_succ.
      destruct (Nat.eq_dec j k) as [heq | hne].
      * right.
        subst j.
        symmetry.
        exact hj.
      * left.
        assert (hjlt : j < k) by lia.
        rewrite <- hj.
        now apply ordinal_code_mem_of_lt.
Qed.

Lemma hf_ordinal_like_iff_is_ordinal_code : forall a,
  hf_ordinal_like a <-> is_ordinal_code a.
Proof.
  intro a.
  split.
  - apply hf_ordinal_like_is_ordinal_code.
  - intros [n <-].
    apply ordinal_code_ordinal_like.
Qed.

Definition OrdinalHF : Type := { a : nat | is_ordinal_code a }.

Definition ordinal_of_nat (n : nat) : OrdinalHF :=
  exist _ (ordinal_code n) (ordinal_code_is_ordinal_code n).

Definition nat_of_ordinal (a : OrdinalHF) : nat :=
  @epsilon nat (inhabits 0) (fun n => ordinal_code n = proj1_sig a).

Lemma nat_of_ordinal_spec : forall a : OrdinalHF,
  ordinal_code (nat_of_ordinal a) = proj1_sig a.
Proof.
  intros [a ha].
  unfold nat_of_ordinal.
  simpl.
  apply epsilon_spec.
  exact ha.
Qed.

Lemma nat_of_ordinal_ordinal_of_nat : forall n,
  nat_of_ordinal (ordinal_of_nat n) = n.
Proof.
  intro n.
  apply ordinal_code_injective.
  apply nat_of_ordinal_spec.
Qed.

Lemma ordinal_hf_eq : forall a b : OrdinalHF,
  proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros [a ha] [b hb] h.
  simpl in h.
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma ordinal_eq_of_nat_of_ordinal_eq : forall a b : OrdinalHF,
  nat_of_ordinal a = nat_of_ordinal b -> a = b.
Proof.
  intros a b h.
  apply ordinal_hf_eq.
  rewrite <- (nat_of_ordinal_spec a).
  rewrite <- (nat_of_ordinal_spec b).
  now rewrite h.
Qed.

Lemma ordinal_of_nat_nat_of_ordinal : forall a : OrdinalHF,
  ordinal_of_nat (nat_of_ordinal a) = a.
Proof.
  intro a.
  apply ordinal_hf_eq.
  simpl.
  apply nat_of_ordinal_spec.
Qed.

Definition ordinal_succ_set (a : OrdinalHF) : OrdinalHF.
Proof.
  refine (exist _ (hf_adjoin (proj1_sig a) (proj1_sig a)) _).
  exists (S (nat_of_ordinal a)).
  rewrite ordinal_code_succ.
  rewrite nat_of_ordinal_spec.
  reflexivity.
Defined.

Lemma ordinal_succ_set_eq : forall a : OrdinalHF,
  ordinal_succ_set a = ordinal_of_nat (S (nat_of_ordinal a)).
Proof.
  intro a.
  apply ordinal_hf_eq.
  simpl.
  unfold ordinal_succ_set.
  simpl.
  rewrite nat_of_ordinal_spec.
  reflexivity.
Qed.

Lemma nat_of_ordinal_succ_set : forall a : OrdinalHF,
  nat_of_ordinal (ordinal_succ_set a) = S (nat_of_ordinal a).
Proof.
  intro a.
  rewrite ordinal_succ_set_eq.
  apply nat_of_ordinal_ordinal_of_nat.
Qed.

Fixpoint ordinal_add_iter (a : OrdinalHF) (n : nat) : OrdinalHF :=
  match n with
  | 0 => a
  | S k => ordinal_succ_set (ordinal_add_iter a k)
  end.

Definition ordinal_add_set (a b : OrdinalHF) : OrdinalHF :=
  ordinal_add_iter a (nat_of_ordinal b).

Lemma nat_of_ordinal_add_iter : forall (a : OrdinalHF) n,
  nat_of_ordinal (ordinal_add_iter a n) = nat_of_ordinal a + n.
Proof.
  intros a n.
  induction n as [|n IH].
  - simpl. lia.
  - simpl. rewrite nat_of_ordinal_succ_set, IH. lia.
Qed.

Lemma nat_of_ordinal_add_set : forall a b : OrdinalHF,
  nat_of_ordinal (ordinal_add_set a b) =
    nat_of_ordinal a + nat_of_ordinal b.
Proof.
  intros a b.
  unfold ordinal_add_set.
  apply nat_of_ordinal_add_iter.
Qed.

Lemma ordinal_add_set_eq : forall a b : OrdinalHF,
  ordinal_add_set a b =
    ordinal_of_nat (nat_of_ordinal a + nat_of_ordinal b).
Proof.
  intros a b.
  apply ordinal_eq_of_nat_of_ordinal_eq.
  rewrite nat_of_ordinal_add_set.
  rewrite nat_of_ordinal_ordinal_of_nat.
  reflexivity.
Qed.

Fixpoint ordinal_mul_iter (a : OrdinalHF) (n : nat) : OrdinalHF :=
  match n with
  | 0 => ordinal_of_nat 0
  | S k => ordinal_add_set (ordinal_mul_iter a k) a
  end.

Definition ordinal_mul_set (a b : OrdinalHF) : OrdinalHF :=
  ordinal_mul_iter a (nat_of_ordinal b).

Lemma nat_of_ordinal_mul_iter : forall (a : OrdinalHF) n,
  nat_of_ordinal (ordinal_mul_iter a n) = nat_of_ordinal a * n.
Proof.
  intros a n.
  induction n as [|n IH].
  - simpl. rewrite nat_of_ordinal_ordinal_of_nat. lia.
  - simpl. rewrite nat_of_ordinal_add_set, IH. lia.
Qed.

Lemma nat_of_ordinal_mul_set : forall a b : OrdinalHF,
  nat_of_ordinal (ordinal_mul_set a b) =
    nat_of_ordinal a * nat_of_ordinal b.
Proof.
  intros a b.
  unfold ordinal_mul_set.
  apply nat_of_ordinal_mul_iter.
Qed.

Lemma ordinal_mul_set_eq : forall a b : OrdinalHF,
  ordinal_mul_set a b =
    ordinal_of_nat (nat_of_ordinal a * nat_of_ordinal b).
Proof.
  intros a b.
  apply ordinal_eq_of_nat_of_ordinal_eq.
  rewrite nat_of_ordinal_mul_set.
  rewrite nat_of_ordinal_ordinal_of_nat.
  reflexivity.
Qed.

Definition ordinalPAModel : PAModel.
Proof.
  refine {| pa_carrier := OrdinalHF;
            pa_zero := ordinal_of_nat 0;
            pa_succ := ordinal_succ_set;
            pa_add := ordinal_add_set;
            pa_mul := ordinal_mul_set |}.
  - intros a b h.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    pose proof (f_equal nat_of_ordinal h) as hn.
    rewrite !nat_of_ordinal_succ_set in hn.
    lia.
  - intros a h.
    pose proof (f_equal nat_of_ordinal h) as hn.
    rewrite nat_of_ordinal_succ_set in hn.
    rewrite nat_of_ordinal_ordinal_of_nat in hn.
    lia.
  - intro a.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_add_set.
    rewrite nat_of_ordinal_ordinal_of_nat.
    lia.
  - intros a b.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_add_set.
    rewrite nat_of_ordinal_succ_set.
    rewrite nat_of_ordinal_succ_set.
    rewrite nat_of_ordinal_add_set.
    lia.
  - intro a.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_mul_set.
    rewrite nat_of_ordinal_ordinal_of_nat.
    lia.
  - intros a b.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_mul_set.
    rewrite nat_of_ordinal_succ_set.
    rewrite nat_of_ordinal_add_set.
    rewrite nat_of_ordinal_mul_set.
    lia.
  - intros P H0 HS a.
    assert (Hnat : forall n, P (ordinal_of_nat n)).
    {
      intro n.
      induction n as [|n IH].
      - exact H0.
      - pose proof (HS (ordinal_of_nat n) IH) as Hstep.
        rewrite ordinal_succ_set_eq in Hstep.
        rewrite nat_of_ordinal_ordinal_of_nat in Hstep.
        exact Hstep.
    }
    rewrite <- (ordinal_of_nat_nat_of_ordinal a).
    apply Hnat.
Defined.

Definition PA_ordinal_round_trip_iso : PAIso natPAModel ordinalPAModel.
Proof.
  refine {| pa_iso_to := fun n : natPAModel => (ordinal_of_nat n : ordinalPAModel);
            pa_iso_inv := fun a : ordinalPAModel => (nat_of_ordinal a : natPAModel) |}.
  - apply nat_of_ordinal_ordinal_of_nat.
  - apply ordinal_of_nat_nat_of_ordinal.
  - reflexivity.
  - intro a.
    apply ordinal_hf_eq.
    simpl.
    unfold ordinal_succ_set.
    simpl.
    reflexivity.
  - intros a b.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_ordinal_of_nat.
    rewrite nat_of_ordinal_add_set.
    rewrite !nat_of_ordinal_ordinal_of_nat.
    reflexivity.
  - intros a b.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    rewrite nat_of_ordinal_ordinal_of_nat.
    rewrite nat_of_ordinal_mul_set.
    rewrite !nat_of_ordinal_ordinal_of_nat.
    reflexivity.
Defined.

Definition ordinalHFModel : HFModel.
Proof.
  refine {| hf_carrier := OrdinalHF;
            hf_rel := fun a b => hf_mem (nat_of_ordinal a) (nat_of_ordinal b);
            hf_empty_obj := ordinal_of_nat hf_empty;
            hf_adjoin_obj := fun a b =>
              ordinal_of_nat (hf_adjoin (nat_of_ordinal a) (nat_of_ordinal b)) |}.
  - intros a b H.
    apply ordinal_eq_of_nat_of_ordinal_eq.
    apply hf_ext.
    intro x.
    pose proof (H (ordinal_of_nat x)) as Hx.
    rewrite !nat_of_ordinal_ordinal_of_nat in Hx.
    exact Hx.
  - intros x H.
    rewrite nat_of_ordinal_ordinal_of_nat in H.
    exact (hf_mem_empty (nat_of_ordinal x) H).
  - intros x a b.
    rewrite nat_of_ordinal_ordinal_of_nat.
    destruct (hf_mem_adjoin
      (nat_of_ordinal x) (nat_of_ordinal a) (nat_of_ordinal b))
      as [hforward hback].
    split.
    + intro hx.
      destruct (hforward hx) as [hxb | hxa].
      * left. exact hxb.
      * right. now apply ordinal_eq_of_nat_of_ordinal_eq.
    + intro hx.
      apply hback.
      destruct hx as [hxb | hxa].
      * left. exact hxb.
      * right. subst x. reflexivity.
  - intros P step a.
    assert (Hnat : forall n, P (ordinal_of_nat n)).
    {
      apply hf_set_induction.
      intros n IH.
      apply step.
      intros x hx.
      rewrite <- (ordinal_of_nat_nat_of_ordinal x).
      apply IH.
      rewrite nat_of_ordinal_ordinal_of_nat in hx.
      exact hx.
    }
    rewrite <- (ordinal_of_nat_nat_of_ordinal a).
    apply Hnat.
Defined.

Definition HF_ordinal_round_trip_iso : HFIso ackermannHFModel ordinalHFModel.
Proof.
  refine {| hf_iso_to := fun n : ackermannHFModel =>
              (ordinal_of_nat n : ordinalHFModel);
            hf_iso_inv := fun a : ordinalHFModel =>
              (nat_of_ordinal a : ackermannHFModel) |}.
  - apply nat_of_ordinal_ordinal_of_nat.
  - apply ordinal_of_nat_nat_of_ordinal.
  - intros a b.
    simpl.
    rewrite !nat_of_ordinal_ordinal_of_nat.
    reflexivity.
  - reflexivity.
  - intros a b.
    apply ordinal_hf_eq.
    simpl.
    rewrite !nat_of_ordinal_ordinal_of_nat.
    reflexivity.
Defined.

Record TheoryInterpretation
  (Src Tgt : Type)
  (SrcSentence : Src -> Prop) (TgtSentence : Tgt -> Prop)
  (SrcAx : Src -> Prop) (TgtAx : Tgt -> Prop)
  (SrcProv : (Src -> Prop) -> list Src -> Src -> Prop)
  (TgtProv : (Tgt -> Prop) -> list Tgt -> Tgt -> Prop) := {
  ti_translate : Src -> Tgt;
  ti_maps_sentence : forall phi,
    SrcSentence phi -> TgtSentence (ti_translate phi);
  ti_maps_axiom : forall phi,
    SrcAx phi -> TgtProv TgtAx [] (ti_translate phi);
  ti_maps_theorem : forall phi,
    SrcSentence phi ->
    SrcProv SrcAx [] phi -> TgtProv TgtAx [] (ti_translate phi)
}.

Record DeductiveBiInterpretationTarget
  (PAForm : Type)
  (PASentence : PAForm -> Prop)
  (PAAx : PAForm -> Prop)
  (PAIff : PAForm -> PAForm -> PAForm)
  (PAProv : (PAForm -> Prop) -> list PAForm -> PAForm -> Prop)
  (HFAx : form -> Prop) := {
  dbi_pa_in_hf : TheoryInterpretation
    PAForm form PASentence Sentence PAAx HFAx PAProv BProv;
  dbi_hf_in_pa : TheoryInterpretation
    form PAForm Sentence PASentence HFAx PAAx BProv PAProv;
  dbi_pa_round_trip : forall phi,
    PASentence phi ->
    PAProv PAAx []
      (PAIff phi
        (ti_translate _ _ _ _ _ _ _ _ dbi_hf_in_pa
          (ti_translate _ _ _ _ _ _ _ _ dbi_pa_in_hf phi)));
  dbi_hf_round_trip : forall phi,
    Sentence phi ->
    BProv HFAx []
      (fIff phi
        (ti_translate _ _ _ _ _ _ _ _ dbi_pa_in_hf
          (ti_translate _ _ _ _ _ _ _ _ dbi_hf_in_pa phi)))
}.

Record StandardModelInterpretationCertificate := {
  certificate_pa : PAModel;
  certificate_hf : HFModel;
  pa_in_hf : PAModel;
  hf_in_pa_in_hf : HFModel;
  pa_round_trip : PAIso certificate_pa pa_in_hf;
  hf_round_trip : HFIso certificate_hf hf_in_pa_in_hf;
  pa_object : pa_in_hf -> certificate_hf;
  pa_object_zero : pa_object (pa_zero pa_in_hf) = hf_empty_obj certificate_hf;
  pa_object_succ : forall n,
    pa_object (pa_succ pa_in_hf n) =
    hf_adjoin_obj certificate_hf (pa_object n) (pa_object n);
  hf_code : certificate_hf -> certificate_pa;
  hf_decode : certificate_pa -> certificate_hf;
  hf_code_left_inv : forall x, hf_decode (hf_code x) = x
}.

Definition standardModelInterpretation : StandardModelInterpretationCertificate.
Proof.
  refine {| certificate_pa := natPAModel;
            certificate_hf := ackermannHFModel;
            pa_in_hf := ordinalPAModel;
            hf_in_pa_in_hf := ordinalHFModel;
            pa_round_trip := PA_ordinal_round_trip_iso;
            hf_round_trip := HF_ordinal_round_trip_iso;
            pa_object := fun x => proj1_sig x;
            hf_code := fun x => x;
            hf_decode := fun x => x |};
    reflexivity.
Defined.

Theorem PA_standard_model_interpretable_with_HF :
  StandardModelInterpretationCertificate.
Proof.
  exact standardModelInterpretation.
Defined.

Check natPAModel.
Check ackermannHFModel.
Check ordinal_code.
Check TheoryInterpretation.
Check DeductiveBiInterpretationTarget.
Check standardModelInterpretation.
Check PA_standard_model_interpretable_with_HF.
