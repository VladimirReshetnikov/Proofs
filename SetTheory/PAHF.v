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

Definition HF_empty_form : form :=
  fEx (fAll (fImp (fMem 0 1) fBot)).

Definition HF_extensionality_form : form :=
  fAll (fAll
    (fImp
      (fAll (fIff (fMem 0 2) (fMem 0 1)))
      (fEq 1 0))).

Definition HF_adjoin_form : form :=
  fAll (fAll (fEx (fAll
    (fIff (fMem 0 1) (fOr (fMem 0 3) (fEq 0 2)))))).

Definition HF_emptyAt (i : nat) : form :=
  fAll (fImp (fMem 0 (S i)) fBot).

Lemma HF_emptyAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (i : nat),
  Sat V mem e (HF_emptyAt i) <-> forall x, ~ mem x (e i).
Proof.
  reflexivity.
Qed.

Lemma HF_emptyAt_empty : forall (M : HFModel) (e : nat -> M) i,
  Sat M (hf_rel M) e (HF_emptyAt i) <-> e i = hf_empty_obj M.
Proof.
  intros M e i.
  split.
  - intro h.
    apply hf_extensional.
    intro x.
    split.
    + intro hx. exfalso. exact (h x hx).
    + intro hx. exfalso. exact (hf_empty_spec M x hx).
  - intros h x hx.
    change (hf_rel M x (e i)) in hx.
    rewrite h in hx.
    exact (hf_empty_spec M x hx).
Qed.

Definition HF_adjoinAt (c a b : nat) : form :=
  fAll (fIff (fMem 0 (S c)) (fOr (fMem 0 (S a)) (fEq 0 (S b)))).

Lemma HF_adjoinAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (c a b : nat),
  Sat V mem e (HF_adjoinAt c a b) <->
    forall x, mem x (e c) <-> mem x (e a) \/ x = e b.
Proof.
  intros V mem e c a b.
  split.
  - intros h x.
    unfold HF_adjoinAt, fIff in h.
    simpl in h.
    exact (conj (fun hx => proj1 (h x) hx) (fun hx => proj2 (h x) hx)).
  - intros h x.
    unfold fIff.
    simpl.
    exact (h x).
Qed.

Lemma HF_adjoinAt_adjoin : forall (M : HFModel) (e : nat -> M) c a b,
  Sat M (hf_rel M) e (HF_adjoinAt c a b) <->
    e c = hf_adjoin_obj M (e b) (e a).
Proof.
  intros M e c a b.
  split.
  - intro h.
    apply hf_extensional.
    intro x.
    rewrite (proj1 (HF_adjoinAt_spec M (hf_rel M) e c a b) h x).
    symmetry.
    apply hf_adjoin_spec.
  - intro h.
    apply (proj2 (HF_adjoinAt_spec M (hf_rel M) e c a b)).
    intro x.
    rewrite h.
    apply hf_adjoin_spec.
Qed.

Definition HF_succAt (s a : nat) : form := HF_adjoinAt s a a.

Lemma HF_succAt_spec : forall (M : HFModel) (e : nat -> M) s a,
  Sat M (hf_rel M) e (HF_succAt s a) <->
    e s = hf_adjoin_obj M (e a) (e a).
Proof.
  intros M e s a.
  apply HF_adjoinAt_adjoin.
Qed.

Definition hf_single_obj (M : HFModel) (a : M) : M :=
  hf_adjoin_obj M a (hf_empty_obj M).

Lemma hf_single_spec : forall (M : HFModel) (a x : M),
  hf_rel M x (hf_single_obj M a) <-> x = a.
Proof.
  intros M a x.
  unfold hf_single_obj.
  rewrite hf_adjoin_spec.
  split.
  - intros [hx | hx].
    + exfalso. exact (hf_empty_spec M x hx).
    + exact hx.
  - intro hx. now right.
Qed.

Definition hf_upair_obj (M : HFModel) (a b : M) : M :=
  hf_adjoin_obj M b (hf_single_obj M a).

Lemma hf_upair_spec : forall (M : HFModel) (a b x : M),
  hf_rel M x (hf_upair_obj M a b) <-> x = a \/ x = b.
Proof.
  intros M a b x.
  unfold hf_upair_obj.
  rewrite hf_adjoin_spec.
  rewrite hf_single_spec.
  tauto.
Qed.

Definition hf_kpair_obj (M : HFModel) (a b : M) : M :=
  hf_upair_obj M (hf_single_obj M a) (hf_upair_obj M a b).

Lemma hf_kpair_mem : forall (M : HFModel) (a b q : M),
  hf_rel M q (hf_kpair_obj M a b) <->
    q = hf_single_obj M a \/ q = hf_upair_obj M a b.
Proof.
  intros M a b q.
  unfold hf_kpair_obj.
  apply hf_upair_spec.
Qed.

Lemma hf_single_injective : forall (M : HFModel) (a b : M),
  hf_single_obj M a = hf_single_obj M b -> a = b.
Proof.
  intros M a b h.
  assert (ha : hf_rel M a (hf_single_obj M a)).
  { apply (proj2 (hf_single_spec M a a)). reflexivity. }
  rewrite h in ha.
  exact (proj1 (hf_single_spec M b a) ha).
Qed.

Lemma hf_upair_eq_single : forall (M : HFModel) (a b c : M),
  hf_upair_obj M a b = hf_single_obj M c -> a = c /\ b = c.
Proof.
  intros M a b c h.
  split.
  - assert (ha : hf_rel M a (hf_upair_obj M a b)).
    { apply (proj2 (hf_upair_spec M a b a)). now left. }
    rewrite h in ha.
    exact (proj1 (hf_single_spec M c a) ha).
  - assert (hb : hf_rel M b (hf_upair_obj M a b)).
    { apply (proj2 (hf_upair_spec M a b b)). now right. }
    rewrite h in hb.
    exact (proj1 (hf_single_spec M c b) hb).
Qed.

Lemma hf_kpair_injective : forall (M : HFModel) (a b c d : M),
  hf_kpair_obj M a b = hf_kpair_obj M c d -> a = c /\ b = d.
Proof.
  intros M a b c d h.
  assert (hac : a = c).
  {
    assert (hs : hf_rel M (hf_single_obj M a) (hf_kpair_obj M a b)).
    { apply (proj2 (hf_kpair_mem M a b (hf_single_obj M a))). now left. }
    rewrite h in hs.
    destruct (proj1 (hf_kpair_mem M c d (hf_single_obj M a)) hs) as [hsc | hsu].
    - exact (hf_single_injective M a c hsc).
    - symmetry. exact (proj1 (hf_upair_eq_single M c d a (eq_sym hsu))).
  }
  subst c.
  split.
  - reflexivity.
  - assert (h1 : hf_rel M (hf_upair_obj M a b) (hf_kpair_obj M a b)).
    { apply (proj2 (hf_kpair_mem M a b (hf_upair_obj M a b))). now right. }
    rewrite h in h1.
    destruct (proj1 (hf_kpair_mem M a d (hf_upair_obj M a b)) h1) as [h1_single | h1_upair].
    + pose proof (proj2 (hf_upair_eq_single M a b a h1_single)) as hba.
      assert (h2 : hf_rel M (hf_upair_obj M a d) (hf_kpair_obj M a d)).
      { apply (proj2 (hf_kpair_mem M a d (hf_upair_obj M a d))). now right. }
      rewrite <- h in h2.
      destruct (proj1 (hf_kpair_mem M a b (hf_upair_obj M a d)) h2) as [h2_single | h2_upair].
      * pose proof (proj2 (hf_upair_eq_single M a d a h2_single)) as hda.
        rewrite hba, hda. reflexivity.
      * assert (hd : hf_rel M d (hf_upair_obj M a d)).
        { apply (proj2 (hf_upair_spec M a d d)). now right. }
        rewrite h2_upair in hd.
        destruct (proj1 (hf_upair_spec M a b d) hd) as [hd_eq_a | hd_eq_b].
        -- rewrite hba, hd_eq_a. reflexivity.
        -- symmetry. exact hd_eq_b.
    + assert (hb : hf_rel M b (hf_upair_obj M a b)).
      { apply (proj2 (hf_upair_spec M a b b)). now right. }
      rewrite h1_upair in hb.
      destruct (proj1 (hf_upair_spec M a d b) hb) as [hb_eq_a | hb_eq_d].
      * assert (hd : hf_rel M d (hf_upair_obj M a d)).
        { apply (proj2 (hf_upair_spec M a d d)). now right. }
        rewrite <- h1_upair in hd.
        destruct (proj1 (hf_upair_spec M a b d) hd) as [hd_eq_a | hd_eq_b].
        -- rewrite hb_eq_a, hd_eq_a. reflexivity.
        -- symmetry. exact hd_eq_b.
      * exact hb_eq_d.
Qed.

Definition HF_singleAt (i j : nat) : form :=
  fAll (fIff (fMem 0 (S i)) (fEq 0 (S j))).

Lemma HF_singleAt_spec : forall (M : HFModel) (e : nat -> M) i j,
  Sat M (hf_rel M) e (HF_singleAt i j) <->
    e i = hf_single_obj M (e j).
Proof.
  intros M e i j.
  split.
  - intro h.
    apply hf_extensional.
    intro x.
    rewrite hf_single_spec.
    unfold HF_singleAt, fIff in h.
    simpl in h.
    exact (conj (fun hx => proj1 (h x) hx) (fun hx => proj2 (h x) hx)).
  - intros h x.
    unfold HF_singleAt, fIff.
    simpl.
    rewrite h.
    apply hf_single_spec.
Qed.

Definition HF_upairAt (i j k : nat) : form :=
  fAll (fIff (fMem 0 (S i)) (fOr (fEq 0 (S j)) (fEq 0 (S k)))).

Lemma HF_upairAt_spec : forall (M : HFModel) (e : nat -> M) i j k,
  Sat M (hf_rel M) e (HF_upairAt i j k) <->
    e i = hf_upair_obj M (e j) (e k).
Proof.
  intros M e i j k.
  split.
  - intro h.
    apply hf_extensional.
    intro x.
    rewrite hf_upair_spec.
    unfold HF_upairAt, fIff in h.
    simpl in h.
    exact (conj (fun hx => proj1 (h x) hx) (fun hx => proj2 (h x) hx)).
  - intros h x.
    unfold HF_upairAt, fIff.
    simpl.
    rewrite h.
    apply hf_upair_spec.
Qed.

Definition HF_kpairAt (p a b : nat) : form :=
  fAll (fIff (fMem 0 (S p))
    (fOr (HF_singleAt 0 (S a)) (HF_upairAt 0 (S a) (S b)))).

Lemma HF_kpairAt_spec : forall (M : HFModel) (e : nat -> M) p a b,
  Sat M (hf_rel M) e (HF_kpairAt p a b) <->
    e p = hf_kpair_obj M (e a) (e b).
Proof.
  intros M e p a b.
  split.
  - intro h.
    apply hf_extensional.
    intro q.
    unfold HF_kpairAt, fIff in h.
    simpl in h.
    rewrite hf_kpair_mem.
    split.
    + intro hq.
      destruct (proj1 (h q) hq) as [hs | hu].
      * left.
        exact (proj1 (HF_singleAt_spec M (scons M q e) 0 (S a)) hs).
      * right.
        exact (proj1 (HF_upairAt_spec M (scons M q e) 0 (S a) (S b)) hu).
    + intros [hs | hu].
      * apply (proj2 (h q)).
        left.
        exact (proj2 (HF_singleAt_spec M (scons M q e) 0 (S a)) hs).
      * apply (proj2 (h q)).
        right.
        exact (proj2 (HF_upairAt_spec M (scons M q e) 0 (S a) (S b)) hu).
  - intros h q.
    unfold HF_kpairAt, fIff.
    simpl.
    rewrite h.
    split.
    + intro hq.
      destruct (proj1 (hf_kpair_mem M (e a) (e b) q) hq) as [hs | hu].
      * left.
        exact (proj2 (HF_singleAt_spec M (scons M q e) 0 (S a)) hs).
      * right.
        exact (proj2 (HF_upairAt_spec M (scons M q e) 0 (S a) (S b)) hu).
    + intros [hs | hu].
      * apply (proj2 (hf_kpair_mem M (e a) (e b) q)).
        left.
        exact (proj1 (HF_singleAt_spec M (scons M q e) 0 (S a)) hs).
      * apply (proj2 (hf_kpair_mem M (e a) (e b) q)).
        right.
        exact (proj1 (HF_upairAt_spec M (scons M q e) 0 (S a) (S b)) hu).
Qed.

Definition HF_pairMemAt (a b r : nat) : form :=
  fEx (fAnd (HF_kpairAt 0 (S a) (S b)) (fMem 0 (S r))).

Lemma HF_pairMemAt_spec : forall (M : HFModel) (e : nat -> M) a b r,
  Sat M (hf_rel M) e (HF_pairMemAt a b r) <->
    hf_rel M (hf_kpair_obj M (e a) (e b)) (e r).
Proof.
  intros M e a b r.
  split.
  - intros [p [hp hmem]].
    pose proof (proj1 (HF_kpairAt_spec M (scons M p e) 0 (S a) (S b)) hp) as hp'.
    simpl in hp'.
    change (hf_rel M p (e r)) in hmem.
    rewrite hp' in hmem.
    exact hmem.
  - intro h.
    exists (hf_kpair_obj M (e a) (e b)).
    split.
    + apply (proj2 (HF_kpairAt_spec M
        (scons M (hf_kpair_obj M (e a) (e b)) e) 0 (S a) (S b))).
      reflexivity.
    + exact h.
Qed.

Definition hf_pair_functional (M : HFModel) (f : M) : Prop :=
  forall k y y',
    hf_rel M (hf_kpair_obj M k y) f ->
    hf_rel M (hf_kpair_obj M k y') f ->
    y = y'.

Definition hf_pair_keys_below_succ (M : HFModel) (f m : M) : Prop :=
  forall k y,
    hf_rel M (hf_kpair_obj M k y) f ->
    hf_rel M k m \/ k = m.

Definition hf_pair_total_below_succ (M : HFModel) (f m : M) : Prop :=
  forall k,
    hf_rel M k m \/ k = m ->
    exists y, hf_rel M (hf_kpair_obj M k y) f.

Definition hf_pair_succ_step (M : HFModel) (f m : M) : Prop :=
  forall k t y,
    hf_rel M k m ->
    hf_rel M (hf_kpair_obj M k t) f ->
    hf_rel M (hf_kpair_obj M (hf_adjoin_obj M k k) y) f ->
    y = hf_adjoin_obj M t t.

Definition HF_pairFunctionalAt (f : nat) : form :=
  fAll (fAll (fAll
    (fImp
      (fAnd
        (HF_pairMemAt 2 1 (S (S (S f))))
        (HF_pairMemAt 2 0 (S (S (S f)))))
      (fEq 1 0)))).

Lemma HF_pairFunctionalAt_spec : forall (M : HFModel) (e : nat -> M) f,
  Sat M (hf_rel M) e (HF_pairFunctionalAt f) <->
    hf_pair_functional M (e f).
Proof.
  intros M e f.
  split.
  - intros h k y y' hky hky'.
    apply (h k y y').
    split.
    + apply (proj2 (HF_pairMemAt_spec M
        (scons M y' (scons M y (scons M k e))) 2 1 (S (S (S f))))).
      exact hky.
    + apply (proj2 (HF_pairMemAt_spec M
        (scons M y' (scons M y (scons M k e))) 2 0 (S (S (S f))))).
      exact hky'.
  - intros h k y y' hpairs.
    unfold hf_pair_functional in h.
    change (y = y').
    exact (h k y y'
      (proj1 (HF_pairMemAt_spec M
        (scons M y' (scons M y (scons M k e))) 2 1 (S (S (S f))))
        (proj1 hpairs))
      (proj1 (HF_pairMemAt_spec M
        (scons M y' (scons M y (scons M k e))) 2 0 (S (S (S f))))
        (proj2 hpairs))).
Qed.

Definition HF_pairKeysBelowSuccAt (f m : nat) : form :=
  fAll (fAll
    (fImp
      (HF_pairMemAt 1 0 (S (S f)))
      (fOr (fMem 1 (S (S m))) (fEq 1 (S (S m)))))).

Lemma HF_pairKeysBelowSuccAt_spec : forall (M : HFModel) (e : nat -> M) f m,
  Sat M (hf_rel M) e (HF_pairKeysBelowSuccAt f m) <->
    hf_pair_keys_below_succ M (e f) (e m).
Proof.
  intros M e f m.
  split.
  - intros h k y hky.
    apply (h k y).
    apply (proj2 (HF_pairMemAt_spec M
      (scons M y (scons M k e)) 1 0 (S (S f)))).
    exact hky.
  - intros h k y hpair.
    unfold hf_pair_keys_below_succ in h.
    change (hf_rel M k (e m) \/ k = e m).
    exact (h k y
      (proj1 (HF_pairMemAt_spec M
        (scons M y (scons M k e)) 1 0 (S (S f))) hpair)).
Qed.

Definition HF_pairTotalBelowSuccAt (f m : nat) : form :=
  fAll
    (fImp
      (fOr (fMem 0 (S m)) (fEq 0 (S m)))
      (fEx (HF_pairMemAt 1 0 (S (S f))))).

Lemma HF_pairTotalBelowSuccAt_spec : forall (M : HFModel) (e : nat -> M) f m,
  Sat M (hf_rel M) e (HF_pairTotalBelowSuccAt f m) <->
    hf_pair_total_below_succ M (e f) (e m).
Proof.
  intros M e f m.
  split.
  - intros h k hk.
    destruct (h k hk) as [y hy].
    exists y.
    apply (proj1 (HF_pairMemAt_spec M
      (scons M y (scons M k e)) 1 0 (S (S f)))).
    exact hy.
  - intros h k hk.
    unfold hf_pair_total_below_succ in h.
    destruct (h k hk) as [y hy].
    exists y.
    apply (proj2 (HF_pairMemAt_spec M
      (scons M y (scons M k e)) 1 0 (S (S f)))).
    exact hy.
Qed.

Definition HF_pairSuccStepAt (f m : nat) : form :=
  fAll (fAll (fAll
    (fImp
      (fMem 2 (S (S (S m))))
      (fImp
        (HF_pairMemAt 2 1 (S (S (S f))))
        (fAll
          (fImp
            (HF_succAt 0 3)
            (fImp
              (HF_pairMemAt 0 1 (S (S (S (S f)))))
              (HF_succAt 1 2)))))))).

Lemma HF_pairSuccStepAt_spec : forall (M : HFModel) (e : nat -> M) f m,
  Sat M (hf_rel M) e (HF_pairSuccStepAt f m) <->
    hf_pair_succ_step M (e f) (e m).
Proof.
  intros M e f m.
  split.
  - intros h k t y hkm hkt hsy.
    pose (sk := hf_adjoin_obj M k k).
    pose proof (h k t y hkm) as h1.
    pose proof (h1
      (proj2 (HF_pairMemAt_spec M
        (scons M y (scons M t (scons M k e))) 2 1 (S (S (S f)))) hkt))
      as h2.
    pose proof (h2 sk
      (proj2 (HF_succAt_spec M
        (scons M sk (scons M y (scons M t (scons M k e)))) 0 3) eq_refl))
      as h3.
    pose proof (h3
      (proj2 (HF_pairMemAt_spec M
        (scons M sk (scons M y (scons M t (scons M k e)))) 0 1
        (S (S (S (S f))))) hsy)) as h4.
    exact (proj1 (HF_succAt_spec M
      (scons M sk (scons M y (scons M t (scons M k e)))) 1 2) h4).
  - intros h k t y hkm hkt sk hsk hsky.
    pose proof (proj1 (HF_succAt_spec M
      (scons M sk (scons M y (scons M t (scons M k e)))) 0 3) hsk)
      as hsk'.
    simpl in hsk'.
    assert (hsky' : hf_rel M
        (hf_kpair_obj M (hf_adjoin_obj M k k) y) (e f)).
    {
      pose proof (proj1 (HF_pairMemAt_spec M
        (scons M sk (scons M y (scons M t (scons M k e)))) 0 1
        (S (S (S (S f))))) hsky) as hpair.
      simpl in hpair.
      rewrite hsk' in hpair.
      exact hpair.
    }
    apply (proj2 (HF_succAt_spec M
      (scons M sk (scons M y (scons M t (scons M k e)))) 1 2)).
    change (y = hf_adjoin_obj M t t).
    unfold hf_pair_succ_step in h.
    change (hf_rel M k (e m)) in hkm.
    exact (h k t y hkm
      (proj1 (HF_pairMemAt_spec M
        (scons M y (scons M t (scons M k e))) 2 1 (S (S (S f)))) hkt)
      hsky').
Qed.

Definition HF_pairBaseAt (f s : nat) : form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 (S s) (S f))).

Lemma HF_pairBaseAt_spec : forall (M : HFModel) (e : nat -> M) f s,
  Sat M (hf_rel M) e (HF_pairBaseAt f s) <->
    hf_rel M (hf_kpair_obj M (hf_empty_obj M) (e s)) (e f).
Proof.
  intros M e f s.
  split.
  - intros [z [hz hpair]].
    pose proof (proj1 (HF_emptyAt_empty M (scons M z e) 0) hz) as hz'.
    simpl in hz'.
    pose proof (proj1 (HF_pairMemAt_spec M (scons M z e) 0 (S s) (S f)) hpair)
      as hpair'.
    simpl in hpair'.
    rewrite hz' in hpair'.
    exact hpair'.
  - intro h.
    exists (hf_empty_obj M).
    split.
    + apply (proj2 (HF_emptyAt_empty M (scons M (hf_empty_obj M) e) 0)).
      reflexivity.
    + apply (proj2 (HF_pairMemAt_spec M
        (scons M (hf_empty_obj M) e) 0 (S s) (S f))).
      simpl.
      exact h.
Qed.

Definition HF_pairZeroBaseAt (f : nat) : form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 0 (S f))).

Lemma HF_pairZeroBaseAt_spec : forall (M : HFModel) (e : nat -> M) f,
  Sat M (hf_rel M) e (HF_pairZeroBaseAt f) <->
    hf_rel M (hf_kpair_obj M (hf_empty_obj M) (hf_empty_obj M)) (e f).
Proof.
  intros M e f.
  split.
  - intros [z [hz hpair]].
    pose proof (proj1 (HF_emptyAt_empty M (scons M z e) 0) hz) as hz'.
    simpl in hz'.
    pose proof (proj1 (HF_pairMemAt_spec M (scons M z e) 0 0 (S f)) hpair)
      as hpair'.
    simpl in hpair'.
    rewrite hz' in hpair'.
    exact hpair'.
  - intro h.
    exists (hf_empty_obj M).
    split.
    + apply (proj2 (HF_emptyAt_empty M (scons M (hf_empty_obj M) e) 0)).
      reflexivity.
    + apply (proj2 (HF_pairMemAt_spec M
        (scons M (hf_empty_obj M) e) 0 0 (S f))).
      simpl.
      exact h.
Qed.

Definition hf_succ_rec_approx (M : HFModel) (s f m : M) : Prop :=
  hf_pair_functional M f /\
  hf_pair_keys_below_succ M f m /\
  hf_rel M (hf_kpair_obj M (hf_empty_obj M) s) f /\
  hf_pair_total_below_succ M f m /\
  hf_pair_succ_step M f m.

Definition HF_succRecApproxAt (f s m : nat) : form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairBaseAt f s)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (HF_pairSuccStepAt f m)))).

Lemma HF_succRecApproxAt_spec : forall (M : HFModel) (e : nat -> M) f s m,
  Sat M (hf_rel M) e (HF_succRecApproxAt f s m) <->
    hf_succ_rec_approx M (e s) (e f) (e m).
Proof.
  intros M e f s m.
  unfold HF_succRecApproxAt, hf_succ_rec_approx.
  split.
  - intros [hfun [hkeys [hbase [htotal hstep]]]].
    exact (conj
      (proj1 (HF_pairFunctionalAt_spec M e f) hfun)
      (conj
        (proj1 (HF_pairKeysBelowSuccAt_spec M e f m) hkeys)
        (conj
          (proj1 (HF_pairBaseAt_spec M e f s) hbase)
          (conj
            (proj1 (HF_pairTotalBelowSuccAt_spec M e f m) htotal)
            (proj1 (HF_pairSuccStepAt_spec M e f m) hstep))))).
  - intros [hfun [hkeys [hbase [htotal hstep]]]].
    exact (conj
      (proj2 (HF_pairFunctionalAt_spec M e f) hfun)
      (conj
        (proj2 (HF_pairKeysBelowSuccAt_spec M e f m) hkeys)
        (conj
          (proj2 (HF_pairBaseAt_spec M e f s) hbase)
          (conj
            (proj2 (HF_pairTotalBelowSuccAt_spec M e f m) htotal)
            (proj2 (HF_pairSuccStepAt_spec M e f m) hstep))))).
Qed.

Definition rSepParam (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S k)
  end.

Lemma Sat_rename_rSepParam : forall (V : Type) (mem : V -> V -> Prop)
    (psi : form) (e : nat -> V) (s x : V),
  Sat V mem (scons V x (scons V s e)) (rename rSepParam psi) <->
    Sat V mem (scons V x e) psi.
Proof.
  intros V mem psi e s x.
  rewrite Sat_rename.
  apply Sat_ext.
  intros [|n]; reflexivity.
Qed.

Definition rSkipParam (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S k)
  end.

Lemma Sat_rename_rSkipParam : forall (V : Type) (mem : V -> V -> Prop)
    (phi : form) (e : nat -> V) (x y : V),
  Sat V mem (scons V y (scons V x e)) (rename rSkipParam phi) <->
    Sat V mem (scons V y e) phi.
Proof.
  intros V mem phi e x y.
  rewrite Sat_rename.
  apply Sat_ext.
  intros [|n]; reflexivity.
Qed.

Definition rAdjStepOld (n : nat) : nat :=
  match n with
  | 0 => 2
  | S k => S (S (S k))
  end.

Definition rAdjStepNew (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S (S k))
  end.

Lemma Sat_rename_rAdjStepOld : forall (V : Type) (mem : V -> V -> Prop)
    (phi : form) (e : nat -> V) (a b c : V),
  Sat V mem (scons V c (scons V b (scons V a e)))
    (rename rAdjStepOld phi) <->
    Sat V mem (scons V a e) phi.
Proof.
  intros V mem phi e a b c.
  rewrite Sat_rename.
  apply Sat_ext.
  intros [|n]; reflexivity.
Qed.

Lemma Sat_rename_rAdjStepNew : forall (V : Type) (mem : V -> V -> Prop)
    (phi : form) (e : nat -> V) (a b c : V),
  Sat V mem (scons V c (scons V b (scons V a e)))
    (rename rAdjStepNew phi) <->
    Sat V mem (scons V c e) phi.
Proof.
  intros V mem phi e a b c.
  rewrite Sat_rename.
  apply Sat_ext.
  intros [|n]; reflexivity.
Qed.

Definition HF_subsetAt (a b : nat) : form :=
  fAll (fImp (fMem 0 (S a)) (fMem 0 (S b))).

Lemma HF_subsetAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a b : nat),
  Sat V mem e (HF_subsetAt a b) <->
    forall x, mem x (e a) -> mem x (e b).
Proof.
  reflexivity.
Qed.

Definition HF_sepByAt (psi : form) (a : nat) : form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fAnd (fMem 0 (S (S a))) (rename rSepParam psi)))).

Lemma HF_sepByAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (psi : form) (e : nat -> V) (a : nat),
  Sat V mem e (HF_sepByAt psi a) <->
    exists s, forall x,
      mem x s <-> mem x (e a) /\ Sat V mem (scons V x e) psi.
Proof.
  intros V mem psi e a.
  split.
  - intros [s hs].
    exists s.
    intro x.
    pose proof (hs x) as hx.
    unfold fIff in hx.
    simpl in hx.
    split.
    + intro hxs.
      destruct (proj1 hx hxs) as [hxa hpsi].
      split.
      * exact hxa.
      * exact (proj1 (Sat_rename_rSepParam V mem psi e s x) hpsi).
    + intros [hxa hpsi].
      apply (proj2 hx).
      split.
      * exact hxa.
      * exact (proj2 (Sat_rename_rSepParam V mem psi e s x) hpsi).
  - intros [s hs].
    exists s.
    intro x.
    unfold fIff.
    simpl.
    split.
    + intro hxs.
      destruct (proj1 (hs x) hxs) as [hxa hpsi].
      split.
      * exact hxa.
      * exact (proj2 (Sat_rename_rSepParam V mem psi e s x) hpsi).
    + intros [hxa hpsi].
      apply (proj2 (hs x)).
      split.
      * exact hxa.
      * exact (proj1 (Sat_rename_rSepParam V mem psi e s x) hpsi).
Qed.

Definition HF_binUnionAt (a b : nat) : form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fOr (fMem 0 (S (S a))) (fMem 0 (S (S b)))))).

Lemma HF_binUnionAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a b : nat),
  Sat V mem e (HF_binUnionAt a b) <->
    exists u, forall x, mem x u <-> mem x (e a) \/ mem x (e b).
Proof.
  intros V mem e a b.
  split.
  - intros [u hu].
    exists u.
    intro x.
    unfold fIff in hu.
    simpl in hu.
    exact (hu x).
  - intros [u hu].
    exists u.
    intro x.
    unfold fIff.
    simpl.
    exact (hu x).
Qed.

Definition HF_unionAt (a : nat) : form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fEx (fAnd (fMem 0 (S (S (S a)))) (fMem 1 0))))).

Lemma HF_unionAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_unionAt a) <->
    exists u, forall x, mem x u <-> exists v, mem v (e a) /\ mem x v.
Proof.
  intros V mem e a.
  split.
  - intros [u hu].
    exists u.
    intro x.
    unfold fIff in hu.
    simpl in hu.
    exact (hu x).
  - intros [u hu].
    exists u.
    intro x.
    unfold fIff.
    simpl.
    exact (hu x).
Qed.

Definition TransitiveObj {V : Type} (mem : V -> V -> Prop) (a : V) : Prop :=
  forall y, mem y a -> forall x, mem x y -> mem x a.

Definition HF_transitiveAt (a : nat) : form :=
  fAll (fImp (fMem 0 (S a))
    (fAll (fImp (fMem 0 1) (fMem 0 (S (S a)))))).

Lemma HF_transitiveAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_transitiveAt a) <-> TransitiveObj mem (e a).
Proof.
  intros V mem e a.
  split.
  - intros h y hy x hx. exact (h y hy x hx).
  - intros h y hy x hx. exact (h y hy x hx).
Qed.

Definition MemTotalOn {V : Type} (mem : V -> V -> Prop) (a : V) : Prop :=
  forall y, mem y a -> forall z, mem z a -> mem y z \/ y = z \/ mem z y.

Definition ChainLike {V : Type} (mem : V -> V -> Prop) (a : V) : Prop :=
  (forall y, mem y a -> TransitiveObj mem y) /\ MemTotalOn mem a.

Definition HF_memTotalOnAt (a : nat) : form :=
  fAll (fImp (fMem 0 (S a))
    (fAll (fImp (fMem 0 (S (S a)))
      (fOr (fMem 1 0) (fOr (fEq 1 0) (fMem 0 1)))))).

Lemma HF_memTotalOnAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_memTotalOnAt a) <-> MemTotalOn mem (e a).
Proof.
  intros V mem e a.
  split.
  - intros h y hy z hz. exact (h y hy z hz).
  - intros h y hy z hz. exact (h y hy z hz).
Qed.

Definition HF_chainLikeAt (a : nat) : form :=
  fAnd
    (fAll (fImp (fMem 0 (S a)) (HF_transitiveAt 0)))
    (HF_memTotalOnAt a).

Lemma HF_chainLikeAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_chainLikeAt a) <-> ChainLike mem (e a).
Proof.
  intros V mem e a.
  split.
  - intros [htrans htotal].
    split.
    + intros y hy.
      exact (proj1 (HF_transitiveAt_spec V mem (scons V y e) 0) (htrans y hy)).
    + exact (proj1 (HF_memTotalOnAt_spec V mem e a) htotal).
  - intros [htrans htotal].
    split.
    + intros y hy.
      exact (proj2 (HF_transitiveAt_spec V mem (scons V y e) 0) (htrans y hy)).
    + exact (proj2 (HF_memTotalOnAt_spec V mem e a) htotal).
Qed.

Definition OrdinalLike {V : Type} (mem : V -> V -> Prop) (a : V) : Prop :=
  TransitiveObj mem a /\
  (forall y, mem y a -> TransitiveObj mem y) /\
  MemTotalOn mem a.

Lemma OrdinalLike_of_mem : forall (V : Type) (mem : V -> V -> Prop)
    (a y : V),
  OrdinalLike mem a -> mem y a -> OrdinalLike mem y.
Proof.
  intros V mem a y [htrans [hmtrans htotal]] hy.
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

Lemma OrdinalLike_empty : forall (M : HFModel),
  OrdinalLike (hf_rel M) (hf_empty_obj M).
Proof.
  intros M.
  unfold OrdinalLike, TransitiveObj, MemTotalOn.
  split.
  - intros y hy. exfalso. exact (hf_empty_spec M y hy).
  - split.
    + intros y hy. exfalso. exact (hf_empty_spec M y hy).
    + intros y hy. exfalso. exact (hf_empty_spec M y hy).
Qed.

Lemma OrdinalLike_adjoin_self : forall (M : HFModel) (a s : M),
  OrdinalLike (hf_rel M) a ->
  s = hf_adjoin_obj M a a ->
  OrdinalLike (hf_rel M) s.
Proof.
  intros M a s [htrans [hmtrans htotal]] hs.
  subst s.
  unfold OrdinalLike, TransitiveObj, MemTotalOn in *.
  split.
  - intros y hy x hx.
    apply (proj2 (hf_adjoin_spec M x a a)).
    destruct (proj1 (hf_adjoin_spec M y a a) hy) as [hyin | hyeq].
    + left. eapply htrans; eauto.
    + subst y. left. exact hx.
  - split.
    + intros y hy.
      destruct (proj1 (hf_adjoin_spec M y a a) hy) as [hyin | hyeq].
      * exact (hmtrans y hyin).
      * subst y. exact htrans.
    + intros y hy z hz.
      destruct (proj1 (hf_adjoin_spec M y a a) hy) as [hyin | hyeq].
      * destruct (proj1 (hf_adjoin_spec M z a a) hz) as [hzin | hzeq].
        -- exact (htotal y hyin z hzin).
        -- subst z. left. exact hyin.
      * subst y.
        destruct (proj1 (hf_adjoin_spec M z a a) hz) as [hzin | hzeq].
        -- right. right. exact hzin.
        -- subst z. right. left. reflexivity.
Qed.

Definition HF_ordinalLikeAt (a : nat) : form :=
  fAnd (HF_transitiveAt a)
    (fAnd
      (fAll (fImp (fMem 0 (S a)) (HF_transitiveAt 0)))
      (HF_memTotalOnAt a)).

Lemma HF_ordinalLikeAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_ordinalLikeAt a) <-> OrdinalLike mem (e a).
Proof.
  intros V mem e a.
  split.
  - intros [htrans [hmtrans htotal]].
    split.
    + exact (proj1 (HF_transitiveAt_spec V mem e a) htrans).
    + split.
      * intros y hy.
        exact (proj1 (HF_transitiveAt_spec V mem (scons V y e) 0) (hmtrans y hy)).
      * exact (proj1 (HF_memTotalOnAt_spec V mem e a) htotal).
  - intros [htrans [hmtrans htotal]].
    split.
    + exact (proj2 (HF_transitiveAt_spec V mem e a) htrans).
    + split.
      * intros y hy.
        exact (proj2 (HF_transitiveAt_spec V mem (scons V y e) 0) (hmtrans y hy)).
      * exact (proj2 (HF_memTotalOnAt_spec V mem e a) htotal).
Qed.

Definition HF_memMaxAt (a : nat) : form :=
  fImp
    (fEx (fMem 0 (S a)))
    (fEx
      (fAnd
        (fMem 0 (S a))
        (fAll
          (fImp
            (fMem 0 (S (S a)))
            (fImp (fMem 1 0) fBot))))).

Lemma HF_memMaxAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_memMaxAt a) <->
    ((exists x, mem x (e a)) ->
      exists p, mem p (e a) /\ forall q, mem q (e a) -> ~ mem p q).
Proof.
  intros V mem e a.
  split.
  - intros h hne.
    destruct (h hne) as [p [hp hmax]].
    exists p. split; [exact hp | intros q hq hpq; exact (hmax q hq hpq)].
  - intros h hne.
    destruct (h hne) as [p [hp hmax]].
    exists p. split; [exact hp | intros q hq hpq; exact (hmax q hq hpq)].
Qed.

Definition HF_chainSubsetsMaxAt (a : nat) : form :=
  fAll
    (fImp
      (HF_subsetAt 0 (S a))
      (fImp (HF_chainLikeAt 0) (HF_memMaxAt 0))).

Lemma HF_chainSubsetsMaxAt_spec : forall (V : Type) (mem : V -> V -> Prop)
    (e : nat -> V) (a : nat),
  Sat V mem e (HF_chainSubsetsMaxAt a) <->
    forall s,
      (forall x, mem x s -> mem x (e a)) ->
      ChainLike mem s ->
      ((exists x, mem x s) ->
        exists p, mem p s /\ forall q, mem q s -> ~ mem p q).
Proof.
  intros V mem e a.
  split.
  - intros h s hsSub hsChain.
    apply (proj1 (HF_memMaxAt_spec V mem (scons V s e) 0)).
    apply h.
    + apply (proj2 (HF_subsetAt_spec V mem (scons V s e) 0 (S a))).
      exact hsSub.
    + apply (proj2 (HF_chainLikeAt_spec V mem (scons V s e) 0)).
      exact hsChain.
  - intros h s hsSubSat hsChainSat.
    apply (proj2 (HF_memMaxAt_spec V mem (scons V s e) 0)).
    apply h.
    + exact (proj1 (HF_subsetAt_spec V mem (scons V s e) 0 (S a)) hsSubSat).
    + exact (proj1 (HF_chainLikeAt_spec V mem (scons V s e) 0) hsChainSat).
Qed.

Definition HF_induction_form (phi : form) : form :=
  fImp
    (fAll
      (fImp
        (fAll (fImp (fMem 0 1) (rename rSkipParam phi)))
        phi))
    (fAll phi).

Definition HF_finite_induction_form (phi : form) : form :=
  fImp
    (fAnd
      (fAll (fImp (HF_emptyAt 0) phi))
      (fAll (fAll (fAll
        (fImp
          (HF_adjoinAt 0 2 1)
          (fImp (rename rAdjStepOld phi) (rename rAdjStepNew phi)))))))
    (fAll phi).

Lemma HF_finite_induction_form_spec : forall (V : Type) (mem : V -> V -> Prop)
    (phi : form) (e : nat -> V),
  Sat V mem e (HF_finite_induction_form phi) <->
    (((forall z, (forall x, ~ mem x z) -> Sat V mem (scons V z e) phi) /\
      (forall a b c, (forall x, mem x c <-> mem x a \/ x = b) ->
        Sat V mem (scons V a e) phi ->
        Sat V mem (scons V c e) phi)) ->
      forall a, Sat V mem (scons V a e) phi).
Proof.
  intros V mem phi e.
  split.
  - intros h hgen.
    apply h.
    split.
    + intros z hz.
      apply (proj1 hgen).
      exact (proj1 (HF_emptyAt_spec V mem (scons V z e) 0) hz).
    + intros a b c hc hOld.
      pose proof (proj1 (HF_adjoinAt_spec V mem
        (scons V c (scons V b (scons V a e))) 0 2 1) hc) as hc'.
      pose proof (proj1 (Sat_rename_rAdjStepOld V mem phi e a b c) hOld)
        as hOld'.
      apply (proj2 (Sat_rename_rAdjStepNew V mem phi e a b c)).
      exact (proj2 hgen a b c hc' hOld').
  - intros h hsyn.
    refine (h (conj _ _)).
    + intros z hz.
      apply (proj1 hsyn).
      apply (proj2 (HF_emptyAt_spec V mem (scons V z e) 0)).
      exact hz.
    + intros a b c hc hOld.
      pose proof (proj2 (HF_adjoinAt_spec V mem
        (scons V c (scons V b (scons V a e))) 0 2 1) hc) as hcSat.
      pose proof (proj2 (Sat_rename_rAdjStepOld V mem phi e a b c) hOld)
        as hOldSat.
      pose proof (proj2 hsyn a b c hcSat hOldSat) as hNewSat.
      exact (proj1 (Sat_rename_rAdjStepNew V mem phi e a b c) hNewSat).
Qed.

Definition HFAx (f : form) : Prop :=
  f = HF_empty_form \/
  f = HF_extensionality_form \/
  f = HF_adjoin_form \/
  exists phi, f = HF_induction_form phi.

Definition HFAx_s (f : form) : Prop :=
  f = seal HF_empty_form \/
  f = seal HF_extensionality_form \/
  f = seal HF_adjoin_form \/
  exists phi, f = seal (HF_induction_form phi).

Definition HFFinAx_s (f : form) : Prop :=
  HFAx_s f \/ exists phi, f = seal (HF_finite_induction_form phi).

Lemma Sentences_HF : Sentences HFAx_s.
Proof.
  intros f hf.
  destruct hf as [-> | [-> | [-> | [phi ->]]]];
    apply Sentence_seal.
Qed.

Lemma Sentences_HFFin : Sentences HFFinAx_s.
Proof.
  intros f [hf | [phi ->]].
  - exact (Sentences_HF f hf).
  - apply Sentence_seal.
Qed.

Lemma sat_HF_empty : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) e HF_empty_form.
Proof.
  intros M e.
  exists (hf_empty_obj M).
  intros x hx.
  exact (hf_empty_spec M x hx).
Qed.

Lemma sat_HF_extensionality : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) e HF_extensionality_form.
Proof.
  intros M e a b h.
  apply hf_extensional.
  intro x.
  unfold fIff in h.
  simpl in h.
  exact (h x).
Qed.

Lemma sat_HF_adjoin : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) e HF_adjoin_form.
Proof.
  intros M e a b.
  exists (hf_adjoin_obj M b a).
  intro x.
  unfold fIff.
  simpl.
  apply hf_adjoin_spec.
Qed.

Lemma sat_HF_induction : forall (M : HFModel) (phi : form) (e : nat -> M),
  Sat M (hf_rel M) e (HF_induction_form phi).
Proof.
  intros M phi e hstep a.
  apply (hf_set_ind M (fun x => Sat M (hf_rel M) (scons M x e) phi)).
  intros x ih.
  apply hstep.
  intros y hy.
  apply (proj2 (Sat_rename_rSkipParam M (hf_rel M) phi e x y)).
  exact (ih y hy).
Qed.

Lemma sat_HF_model : forall (M : HFModel) (v : nat -> M),
  forall g, HFAx_s g -> Sat M (hf_rel M) v g.
Proof.
  intros M v g hg.
  destruct hg as [-> | [-> | [-> | [phi ->]]]].
  - exact (proj2 (seal_valid M (hf_rel M) HF_empty_form)
      (sat_HF_empty M) v).
  - exact (proj2 (seal_valid M (hf_rel M) HF_extensionality_form)
      (sat_HF_extensionality M) v).
  - exact (proj2 (seal_valid M (hf_rel M) HF_adjoin_form)
      (sat_HF_adjoin M) v).
  - exact (proj2 (seal_valid M (hf_rel M) (HF_induction_form phi))
      (sat_HF_induction M phi) v).
Qed.

Lemma standard_sat_HF : forall v,
  forall g, HFAx_s g -> Sat nat hf_mem v g.
Proof.
  intros v.
  apply (sat_HF_model ackermannHFModel v).
Qed.

Lemma HFAx_s_empty : HFAx_s (seal HF_empty_form).
Proof. now left. Qed.

Lemma HFAx_s_extensionality : HFAx_s (seal HF_extensionality_form).
Proof. right; now left. Qed.

Lemma HFAx_s_adjoin : HFAx_s (seal HF_adjoin_form).
Proof. right; right; now left. Qed.

Lemma HFAx_s_induction : forall phi, HFAx_s (seal (HF_induction_form phi)).
Proof.
  intro phi.
  right; right; right.
  now exists phi.
Qed.

Lemma HFFinAx_s_of_HFAx_s : forall f, HFAx_s f -> HFFinAx_s f.
Proof. intros f hf. now left. Qed.

Lemma HFFinAx_s_finite_induction : forall phi,
  HFFinAx_s (seal (HF_finite_induction_form phi)).
Proof.
  intro phi.
  right. now exists phi.
Qed.

Lemma semantic_empty_of_HFAx_s : forall (V : Type) (mem : V -> V -> Prop)
    (v : nat -> V),
  (forall g, HFAx_s g -> Sat V mem v g) ->
  exists e, forall x, ~ mem x e.
Proof.
  intros V mem v hHF.
  exact (extract HFAx_s V mem v HF_empty_form hHF HFAx_s_empty v).
Qed.

Lemma semantic_extensionality_of_HFAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFAx_s g -> Sat V mem v g) ->
  forall a b, (forall x, mem x a <-> mem x b) -> a = b.
Proof.
  intros V mem v hHF a b hab.
  pose proof (extract HFAx_s V mem v HF_extensionality_form
    hHF HFAx_s_extensionality) as hExt.
  apply (hExt v a b).
  intro x.
  unfold fIff.
  simpl.
  exact (hab x).
Qed.

Lemma semantic_adjoin_of_HFAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFAx_s g -> Sat V mem v g) ->
  forall a b, exists c, forall x, mem x c <-> mem x a \/ x = b.
Proof.
  intros V mem v hHF a b.
  pose proof (extract HFAx_s V mem v HF_adjoin_form
    hHF HFAx_s_adjoin) as hAdj.
  destruct (hAdj v a b) as [c hc].
  exists c.
  intro x.
  unfold fIff in hc.
  simpl in hc.
  exact (hc x).
Qed.

Lemma semantic_induction_schema_of_HFAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFAx_s g -> Sat V mem v g) ->
  forall phi e, Sat V mem e (HF_induction_form phi).
Proof.
  intros V mem v hHF phi.
  exact (extract HFAx_s V mem v (HF_induction_form phi)
    hHF (HFAx_s_induction phi)).
Qed.

Lemma semantic_finite_induction_schema_of_HFFinAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall phi e, Sat V mem e (HF_finite_induction_form phi).
Proof.
  intros V mem v hHF phi.
  exact (extract HFFinAx_s V mem v (HF_finite_induction_form phi)
    hHF (HFFinAx_s_finite_induction phi)).
Qed.

Lemma semantic_empty_of_HFFinAx_s : forall (V : Type) (mem : V -> V -> Prop)
    (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  exists e, forall x, ~ mem x e.
Proof.
  intros V mem v hHF.
  apply (semantic_empty_of_HFAx_s V mem v).
  intros g hg.
  apply hHF.
  now apply HFFinAx_s_of_HFAx_s.
Qed.

Lemma semantic_extensionality_of_HFFinAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall a b, (forall x, mem x a <-> mem x b) -> a = b.
Proof.
  intros V mem v hHF.
  apply (semantic_extensionality_of_HFAx_s V mem v).
  intros g hg.
  apply hHF.
  now apply HFFinAx_s_of_HFAx_s.
Qed.

Lemma semantic_adjoin_of_HFFinAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall a b, exists c, forall x, mem x c <-> mem x a \/ x = b.
Proof.
  intros V mem v hHF.
  apply (semantic_adjoin_of_HFAx_s V mem v).
  intros g hg.
  apply hHF.
  now apply HFFinAx_s_of_HFAx_s.
Qed.

Lemma semantic_induction_schema_of_HFFinAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFFinAx_s g -> Sat V mem v g) ->
  forall phi e, Sat V mem e (HF_induction_form phi).
Proof.
  intros V mem v hHF.
  apply (semantic_induction_schema_of_HFAx_s V mem v).
  intros g hg.
  apply hHF.
  now apply HFFinAx_s_of_HFAx_s.
Qed.

Lemma semantic_mem_irrefl_of_HFAx_s :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
  (forall g, HFAx_s g -> Sat V mem v g) ->
  forall a, ~ mem a a.
Proof.
  intros V mem v hHF.
  pose (phi := fImp (fMem 0 0) fBot).
  pose proof (semantic_induction_schema_of_HFAx_s V mem v hHF phi v) as hind.
  assert (hall : forall a, Sat V mem (scons V a v) phi).
  {
    apply hind.
    intros a ih haa.
    exact (ih a haa haa).
  }
  intros a haa.
  exact (hall a haa).
Qed.

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
