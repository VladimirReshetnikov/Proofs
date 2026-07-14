From Stdlib Require Import ZArith Lia List Bool.
Import ListNotations.
Open Scope Z_scope.

Module Cooper.

(** The finite-residue core of Cooper elimination.  This file is constructive:
    all searches below range over [seq 0 m]. *)

Fixpoint max_from (x : Z) (xs : list Z) : Z :=
  match xs with
  | [] => x
  | y :: ys => max_from (Z.max x y) ys
  end.

Fixpoint min_from (x : Z) (xs : list Z) : Z :=
  match xs with
  | [] => x
  | y :: ys => min_from (Z.min x y) ys
  end.

Lemma le_max_from_left x xs : x <= max_from x xs.
Proof.
  revert x; induction xs as [|y ys IH]; intros x; simpl; [lia|].
  eapply Z.le_trans; [apply Z.le_max_l|apply IH].
Qed.

Lemma le_max_from_of_mem x y xs : In y xs -> y <= max_from x xs.
Proof.
  revert x; induction xs as [|z zs IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H].
  - eapply Z.le_trans; [apply Z.le_max_r|apply le_max_from_left].
  - apply IH, H.
Qed.

Lemma max_from_mem x xs : In (max_from x xs) (x :: xs).
Proof.
  revert x; induction xs as [|y ys IH]; intros x; simpl; [auto|].
  specialize (IH (Z.max x y)).
  destruct IH as [H|H].
  - destruct (Z_le_dec x y) as [Hxy|Hxy].
    + right; left. transitivity (Z.max x y); [symmetry; apply Z.max_r; exact Hxy|exact H].
    + left. transitivity (Z.max x y); [symmetry; apply Z.max_l; lia|exact H].
  - right; right; exact H.
Qed.

Lemma min_from_le_left x xs : min_from x xs <= x.
Proof.
  revert x; induction xs as [|y ys IH]; intros x; simpl; [lia|].
  eapply Z.le_trans; [apply IH|apply Z.le_min_l].
Qed.

Lemma min_from_le_of_mem x y xs : In y xs -> min_from x xs <= y.
Proof.
  revert x; induction xs as [|z zs IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H].
  - eapply Z.le_trans; [apply min_from_le_left|apply Z.le_min_r].
  - apply IH, H.
Qed.

Lemma min_from_mem x xs : In (min_from x xs) (x :: xs).
Proof.
  revert x; induction xs as [|y ys IH]; intros x; simpl; [auto|].
  specialize (IH (Z.min x y)).
  destruct IH as [H|H].
  - destruct (Z_le_dec x y) as [Hxy|Hxy].
    + left. transitivity (Z.min x y); [symmetry; apply Z.min_l; exact Hxy|exact H].
    + right; left. transitivity (Z.min x y); [symmetry; apply Z.min_r; lia|exact H].
  - right; right; exact H.
Qed.

Definition periodic (m : positive) (P : Z -> Prop) : Prop :=
  forall x, P (x + Z.pos m) <-> P x.

Lemma periodic_shift m P (HP : periodic m P) :
  forall x k, P (x + k * Z.pos m) <-> P x.
Proof.
  unfold periodic in HP.
  assert (Hplus : forall n x,
      P (x + Z.of_nat n * Z.pos m) <-> P x).
  { induction n as [|n IH]; intros x.
    - replace (x + Z.of_nat 0 * Z.pos m) with x by ring. tauto.
    - rewrite Nat2Z.inj_succ.
      replace (x + Z.succ (Z.of_nat n) * Z.pos m)
        with ((x + Z.of_nat n * Z.pos m) + Z.pos m) by ring.
      exact (iff_trans (HP (x + Z.of_nat n * Z.pos m)) (IH x)). }
  assert (Hminus : forall n x,
      P (x - Z.of_nat n * Z.pos m) <-> P x).
  { induction n as [|n IH]; intros x.
    - replace (x - Z.of_nat 0 * Z.pos m) with x by ring. tauto.
    - rewrite Nat2Z.inj_succ.
      replace (x - Z.succ (Z.of_nat n) * Z.pos m)
        with ((x - Z.of_nat n * Z.pos m) - Z.pos m) by ring.
      specialize (HP ((x - Z.of_nat n * Z.pos m) - Z.pos m)).
      replace ((x - Z.of_nat n * Z.pos m) - Z.pos m + Z.pos m)
        with (x - Z.of_nat n * Z.pos m) in HP by ring.
      exact (iff_trans (iff_sym HP) (IH x)). }
  intros x k; destruct k as [|p|p].
  - replace (x + 0 * Z.pos m) with x by ring. tauto.
  - replace (Z.pos p) with (Z.of_nat (Pos.to_nat p)) by apply positive_nat_Z.
    apply Hplus.
  - replace (Z.neg p) with (- Z.of_nat (Pos.to_nat p)).
    2:{ rewrite positive_nat_Z. symmetry. apply Pos2Z.opp_pos. }
    replace (x + - Z.of_nat (Pos.to_nat p) * Z.pos m)
      with (x - Z.of_nat (Pos.to_nat p) * Z.pos m) by ring.
    apply Hminus.
Qed.

Lemma mod_representative m (x : Z) :
  exists k : nat,
    (k < Pos.to_nat m)%nat /\
    Z.of_nat k = x mod Z.pos m /\
    (Z.pos m | x - Z.of_nat k).
Proof.
  exists (Z.to_nat (x mod Z.pos m)).
  assert (Hm : 0 < Z.pos m) by lia.
  pose proof (Z.mod_pos_bound x (Z.pos m) Hm) as [Hr0 Hrm].
  split.
  - rewrite <- (Z2Nat.id (x mod Z.pos m)) by lia.
    rewrite <- positive_nat_Z. lia.
  - split.
    + rewrite Z2Nat.id by exact Hr0. reflexivity.
    + rewrite Z2Nat.id by exact Hr0.
      exists (x / Z.pos m).
      pose proof (Z.div_mod x (Z.pos m)) as H.
      lia.
Qed.

Lemma periodic_has_residue m P (HP : periodic m P) :
  (exists x, P x) <->
  exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k).
Proof.
  split.
  - intros [x Hx].
    destruct (mod_representative m x) as [k [Hk [_ [q Hq]]]].
    exists k; split; [exact Hk|].
    specialize (periodic_shift m P HP (Z.of_nat k) q) as H.
    replace (Z.of_nat k + q * Z.pos m) with x in H by lia.
    tauto.
  - intros [k [_ Hk]]. exists (Z.of_nat k); exact Hk.
Qed.

Lemma periodic_interval m P (HP : periodic m P) lo hi :
  (exists x, lo <= x /\ x <= hi /\ P x) <->
  exists k : nat,
    (k < Pos.to_nat m)%nat /\
    lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k).
Proof.
  split.
  - intros [x [Hlo [Hhi Hx]]].
    destruct (mod_representative m (x - lo)) as [k [Hk [Hmod [q Hq]]]].
    exists k; repeat split; try exact Hk.
    + rewrite Hmod.
      assert ((x - lo) mod Z.pos m <= x - lo).
      { rewrite (Z.div_mod (x - lo) (Z.pos m)) at 2 by lia.
        assert (Hdiv : 0 <= (x - lo) / Z.pos m).
        { apply Z.div_pos; lia. }
        nia. }
      lia.
    + specialize (periodic_shift m P HP (lo + Z.of_nat k) q) as H.
      replace (lo + Z.of_nat k + q * Z.pos m) with x in H by lia.
      tauto.
  - intros [k [_ [Hhi HPk]]].
    exists (lo + Z.of_nat k); repeat split; try assumption; lia.
Qed.

Definition all_lower (los : list Z) (x : Z) : Prop :=
  forall lo, In lo los -> lo <= x.

Definition all_upper (his : list Z) (x : Z) : Prop :=
  forall hi, In hi his -> x <= hi.

Lemma periodic_unbounded_above m P (HP : periodic m P) los :
  (exists x, all_lower los x /\ P x) <->
  exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k).
Proof.
  split.
  - intros [x [_ Hx]]. apply (proj1 (periodic_has_residue m P HP)).
    now exists x.
  - intros [k [Hk HPk]]. destruct los as [|lo los].
    + exists (Z.of_nat k); split; [intros z H; contradiction|exact HPk].
    + set (q := Z.abs (max_from lo los - Z.of_nat k) + 1).
      set (x := Z.of_nat k + q * Z.pos m).
      assert (Hq : 0 <= q) by (unfold q; pose proof (Z.abs_nonneg
        (max_from lo los - Z.of_nat k)); lia).
      assert (Hm : 1 <= Z.pos m) by lia.
      assert (Hqm : q <= q * Z.pos m) by nia.
      assert (Hmax : max_from lo los <= x).
      { unfold x, q.
        destruct (Z.abs_spec (max_from lo los - Z.of_nat k)); lia. }
      exists x; split.
      * intros z Hz. destruct Hz as [->|Hz].
        -- eapply Z.le_trans; [apply le_max_from_left|exact Hmax].
        -- eapply Z.le_trans; [eapply le_max_from_of_mem; exact Hz|exact Hmax].
      * unfold x. apply (proj2 (periodic_shift m P HP (Z.of_nat k) q)).
        exact HPk.
Qed.

Lemma periodic_unbounded_below m P (HP : periodic m P) his :
  (exists x, all_upper his x /\ P x) <->
  exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k).
Proof.
  split.
  - intros [x [_ Hx]]. apply (proj1 (periodic_has_residue m P HP)).
    now exists x.
  - intros [k [Hk HPk]]. destruct his as [|hi his].
    + exists (Z.of_nat k); split; [intros z H; contradiction|exact HPk].
    + set (q := Z.abs (Z.of_nat k - min_from hi his) + 1).
      set (x := Z.of_nat k - q * Z.pos m).
      assert (Hq : 0 <= q) by (unfold q; pose proof (Z.abs_nonneg
        (Z.of_nat k - min_from hi his)); lia).
      assert (Hm : 1 <= Z.pos m) by lia.
      assert (Hqm : q <= q * Z.pos m) by nia.
      assert (Hmin : x <= min_from hi his).
      { unfold x, q.
        destruct (Z.abs_spec (Z.of_nat k - min_from hi his)); lia. }
      exists x; split.
      * intros z Hz. destruct Hz as [->|Hz].
        -- eapply Z.le_trans; [exact Hmin|apply min_from_le_left].
        -- eapply Z.le_trans; [exact Hmin|eapply min_from_le_of_mem; exact Hz].
      * unfold x. replace (Z.of_nat k - q * Z.pos m)
          with (Z.of_nat k + (-q) * Z.pos m) by ring.
        apply (proj2 (periodic_shift m P HP (Z.of_nat k) (-q))).
        exact HPk.
Qed.

Definition finite_criterion (m : positive) (P : Z -> Prop)
    (los his : list Z) : Prop :=
  match los, his with
  | [], _ | _, [] =>
      exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k)
  | _, _ =>
      forall lo, In lo los -> forall hi, In hi his ->
        exists k : nat, (k < Pos.to_nat m)%nat /\
          lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k)
  end.

Theorem cooper_finite_criterion m P (HP : periodic m P) los his :
  (exists x, all_lower los x /\ all_upper his x /\ P x) <->
  finite_criterion m P los his.
Proof.
  destruct los as [|lo los], his as [|hi his]; simpl.
  - split.
    + intros [x [_ [_ Hx]]]. apply (proj1 (periodic_has_residue m P HP)).
      now exists x.
    + intro H. destruct (proj2 (periodic_has_residue m P HP) H) as [x Hx].
      exists x; unfold all_lower, all_upper; firstorder.
  - split.
    + intros [x [_ [Hhi Hx]]].
      apply (proj1 (periodic_unbounded_below m P HP (hi :: his))).
      now exists x.
    + intro H. destruct (proj2 (periodic_unbounded_below m P HP (hi :: his)) H)
        as [x [Hhi Hx]].
      exists x; split; [unfold all_lower; firstorder|tauto].
  - split.
    + intros [x [Hlo [_ Hx]]].
      apply (proj1 (periodic_unbounded_above m P HP (lo :: los))).
      now exists x.
    + intro H. destruct (proj2 (periodic_unbounded_above m P HP (lo :: los)) H)
        as [x [Hlo Hx]].
      exists x; split; [exact Hlo|]. split; [unfold all_upper; firstorder|exact Hx].
  - split.
    + intros [x [Hlo [Hhi Hx]]] l Hl h Hh.
      apply (proj1 (periodic_interval m P HP l h)).
      exists x; repeat split; auto.
    + intro Hall.
      set (l := max_from lo los).
      set (h := min_from hi his).
      assert (Hl : In l (lo :: los)) by (unfold l; apply max_from_mem).
      assert (Hh : In h (hi :: his)) by (unfold h; apply min_from_mem).
      destruct (Hall l Hl h Hh) as [k [Hk [Hbound HPk]]].
      exists (l + Z.of_nat k); repeat split; try exact HPk.
      * intros z Hz.
        assert (Hzl : z <= l).
        { unfold l. destruct Hz as [Hz|Hz].
          - subst z; apply le_max_from_left.
          - exact (le_max_from_of_mem lo z los Hz). }
        eapply Z.le_trans; [exact Hzl|].
        pose proof (Nat2Z.is_nonneg k); lia.
      * intros z Hz.
        assert (Hhz : h <= z).
        { unfold h. destruct Hz as [Hz|Hz].
          - subst z; apply min_from_le_left.
          - exact (min_from_le_of_mem hi z his Hz). }
        eapply Z.le_trans; [exact Hbound|exact Hhz].
Qed.

Fixpoint exists_list_dec {A : Type} (Q : A -> Prop)
    (DQ : forall a, {Q a} + {~ Q a}) (xs : list A) :
    {exists a, In a xs /\ Q a} + {~ exists a, In a xs /\ Q a}.
Proof.
  destruct xs as [|x xs].
  - right; firstorder.
  - destruct (DQ x) as [Hx|Hx].
    + left; exists x; split; [left; reflexivity|exact Hx].
    + destruct (@exists_list_dec A Q DQ xs) as [H|H].
      * left. destruct H as [a [Ha HQ]]. exists a; split; [right; exact Ha|exact HQ].
      * right. intros [a [Ha HQ]]. destruct Ha as [Ha|Ha].
        -- subst a; contradiction.
        -- apply H. exists a; auto.
Defined.

Fixpoint forall_list_dec {A : Type} (Q : A -> Prop)
    (DQ : forall a, {Q a} + {~ Q a}) (xs : list A) :
    {forall a, In a xs -> Q a} + {~ forall a, In a xs -> Q a}.
Proof.
  destruct xs as [|x xs].
  - left; firstorder.
  - destruct (DQ x) as [Hx|Hx].
    + destruct (@forall_list_dec A Q DQ xs) as [H|H].
      * left. intros a Ha. destruct Ha as [Ha|Ha].
        -- subst a; exact Hx.
        -- exact (H a Ha).
      * right. intro Hall. apply H. intros a Ha. apply Hall. right; exact Ha.
    + right. intro Hall. apply Hx. apply Hall. left; reflexivity.
Defined.

Definition transport_decidable (A B : Prop) (H : A <-> B)
    (DB : {B} + {~ B}) : {A} + {~ A}.
Proof.
  destruct DB as [HB|HB].
  - left; exact (proj2 H HB).
  - right; intro HA; apply HB, (proj1 H), HA.
Defined.

Definition residue_dec m (P : Z -> Prop)
    (DP : forall x, {P x} + {~ P x}) :
    {exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k)} +
    {~ exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k)}.
Proof.
  apply (transport_decidable
    (exists k : nat, (k < Pos.to_nat m)%nat /\ P (Z.of_nat k))
    (exists k : nat, In k (seq 0 (Pos.to_nat m)) /\ P (Z.of_nat k))).
  - split; intros [k [Hk HPk]]; exists k; split; try exact HPk.
    + apply in_seq; lia.
    + apply in_seq in Hk; lia.
  - apply exists_list_dec. exact (fun k => DP (Z.of_nat k)).
Defined.

Definition bounded_pair_dec m (P : Z -> Prop)
    (DP : forall x, {P x} + {~ P x}) (lo hi : Z) :
    {exists k : nat, (k < Pos.to_nat m)%nat /\
      lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k)} +
    {~ exists k : nat, (k < Pos.to_nat m)%nat /\
      lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k)}.
Proof.
  apply (transport_decidable
    (exists k : nat, (k < Pos.to_nat m)%nat /\
      lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k))
    (exists k : nat, In k (seq 0 (Pos.to_nat m)) /\
      (lo + Z.of_nat k <= hi /\ P (lo + Z.of_nat k)))).
  - split; intros [k [Hk HK]]; exists k; split; try exact HK.
    + apply in_seq; lia.
    + apply in_seq in Hk; lia.
  - apply exists_list_dec. intro k.
    destruct (Z_le_dec (lo + Z.of_nat k) hi) as [Hle|Hle];
      destruct (DP (lo + Z.of_nat k)) as [Hp|Hp].
    + left; auto.
    + right; tauto.
    + right; tauto.
    + right; tauto.
Defined.

Definition finite_criterion_dec m P
    (DP : forall x, {P x} + {~ P x}) los his :
    {finite_criterion m P los his} + {~ finite_criterion m P los his}.
Proof.
  destruct los as [|lo los], his as [|hi his]; simpl.
  - exact (residue_dec m P DP).
  - exact (residue_dec m P DP).
  - exact (residue_dec m P DP).
  - exact (@forall_list_dec Z
      (fun l => forall h, In h (hi :: his) ->
        exists k : nat, (k < Pos.to_nat m)%nat /\
          l + Z.of_nat k <= h /\ P (l + Z.of_nat k))
      (fun l => @forall_list_dec Z
        (fun h => exists k : nat, (k < Pos.to_nat m)%nat /\
          l + Z.of_nat k <= h /\ P (l + Z.of_nat k))
        (fun h => bounded_pair_dec m P DP l h) (hi :: his))
      (lo :: los)).
Defined.

(** An executable, constructive decision theorem for one normalized Cooper
    step.  Repeated quantifier elimination uses precisely this operation. *)
Theorem cooper_step_decidable m P (HP : periodic m P)
    (DP : forall x, {P x} + {~ P x}) los his :
    {exists x, all_lower los x /\ all_upper his x /\ P x} +
    {~ exists x, all_lower los x /\ all_upper his x /\ P x}.
Proof.
  exact (transport_decidable _ _ (cooper_finite_criterion m P HP los his)
    (finite_criterion_dec m P DP los his)).
Defined.

End Cooper.
