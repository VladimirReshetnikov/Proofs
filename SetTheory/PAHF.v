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

Record FirstOrderHFModel (V : Type) := {
  fohf_mem : V -> V -> Prop;
  fohf_extensional : forall a b,
    (forall x, fohf_mem x a <-> fohf_mem x b) -> a = b;
  fohf_empty_exists : exists e, forall x, ~ fohf_mem x e;
  fohf_adjoin_exists : forall a b,
    exists c, forall x, fohf_mem x c <-> fohf_mem x a \/ x = b;
  fohf_induction_schema : forall phi e,
    Sat V fohf_mem e (HF_induction_form phi)
}.

Record FirstOrderAdjunctionModel (V : Type) := {
  foam_mem : V -> V -> Prop;
  foam_empty : V;
  foam_adjoin : V -> V -> V;
  foam_extensional : forall a b,
    (forall x, foam_mem x a <-> foam_mem x b) -> a = b;
  foam_empty_spec : forall x, ~ foam_mem x foam_empty;
  foam_adjoin_spec : forall x a b,
    foam_mem x (foam_adjoin a b) <-> foam_mem x a \/ x = b;
  foam_induction_schema : forall phi e,
    Sat V foam_mem e (HF_induction_form phi)
}.

Record FirstOrderFiniteAdjunctionModel (V : Type) := {
  fofam_base :> FirstOrderAdjunctionModel V;
  fofam_finite_induction_schema : forall phi e,
    Sat V (foam_mem V fofam_base) e (HF_finite_induction_form phi)
}.

Lemma foam_mem_irrefl : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  ~ foam_mem V M a a.
Proof.
  intros V M a.
  pose (phi := fImp (fMem 0 0) fBot).
  pose proof (foam_induction_schema V M phi (fun _ => a)) as hind.
  assert (hall : forall x, Sat V (foam_mem V M) (scons V x (fun _ => a)) phi).
  {
    apply hind.
    intros x ih hxx.
    exact (ih x hxx hxx).
  }
  exact (hall a).
Qed.

Lemma foam_mem_asymm : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b : V),
  foam_mem V M a b -> ~ foam_mem V M b a.
Proof.
  intros V M a b hab.
  pose (phi := fAll (fImp (fMem 0 1) (fImp (fMem 1 0) fBot))).
  pose (tail := fun _ : nat => a).
  pose proof (foam_induction_schema V M phi tail) as hind.
  assert (hall : forall x, Sat V (foam_mem V M) (scons V x tail) phi).
  {
    apply hind.
    intros x ih y hyx hxy.
    pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M) phi tail x y)
      (ih y hyx)) as hySat.
    exact (hySat x hxy hyx).
  }
  exact (hall b a hab).
Qed.

Lemma foam_adjoin_self_mem : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  foam_mem V M a (foam_adjoin V M a a).
Proof.
  intros V M a.
  apply (proj2 (foam_adjoin_spec V M a a a)).
  now right.
Qed.

Lemma foam_adjoin_self_ne_self : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  foam_adjoin V M a a <> a.
Proof.
  intros V M a h.
  pose proof (foam_adjoin_self_mem V M a) as ha.
  rewrite h in ha.
  exact (foam_mem_irrefl V M a ha).
Qed.

Lemma foam_adjoin_self_not_mem_of_OrdinalLike : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  OrdinalLike (foam_mem V M) a ->
  ~ foam_mem V M (foam_adjoin V M a a) a.
Proof.
  intros V M a ha hsucc.
  pose proof (foam_adjoin_self_mem V M a) as ha_in_succ.
  pose proof (proj1 ha (foam_adjoin V M a a) hsucc a ha_in_succ) as haa.
  exact (foam_mem_irrefl V M a haa).
Qed.

Lemma foam_adjoin_self_injective_on_OrdinalLike : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b : V),
  OrdinalLike (foam_mem V M) a ->
  OrdinalLike (foam_mem V M) b ->
  foam_adjoin V M a a = foam_adjoin V M b b ->
  a = b.
Proof.
  intros V M a b _ha hb h.
  assert (hasucc : foam_mem V M a (foam_adjoin V M b b)).
  {
    rewrite <- h.
    apply foam_adjoin_self_mem.
  }
  destruct (proj1 (foam_adjoin_spec V M a b b) hasucc) as [hab | hab].
  - assert (hbsucc : foam_mem V M b (foam_adjoin V M a a)).
    {
      rewrite h.
      apply foam_adjoin_self_mem.
    }
    destruct (proj1 (foam_adjoin_spec V M b a a) hbsucc) as [hba | hba].
    + pose proof (proj1 hb a hab b hba) as hbb.
      exfalso. exact (foam_mem_irrefl V M b hbb).
    + symmetry. exact hba.
  - exact hab.
Qed.

Lemma foam_OrdinalLike_empty : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  OrdinalLike (foam_mem V M) (foam_empty V M).
Proof.
  intros V M.
  unfold OrdinalLike, TransitiveObj, MemTotalOn.
  split.
  - intros y hy. exfalso. exact (foam_empty_spec V M y hy).
  - split.
    + intros y hy. exfalso. exact (foam_empty_spec V M y hy).
    + intros y hy. exfalso. exact (foam_empty_spec V M y hy).
Qed.

Lemma foam_OrdinalLike_adjoin_self : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a s : V),
  OrdinalLike (foam_mem V M) a ->
  s = foam_adjoin V M a a ->
  OrdinalLike (foam_mem V M) s.
Proof.
  intros V M a s [htrans [hmtrans htotal]] hs.
  subst s.
  unfold OrdinalLike, TransitiveObj, MemTotalOn in *.
  split.
  - intros y hy x hx.
    apply (proj2 (foam_adjoin_spec V M x a a)).
    destruct (proj1 (foam_adjoin_spec V M y a a) hy) as [hyin | hyeq].
    + left. eapply htrans; eauto.
    + subst y. left. exact hx.
  - split.
    + intros y hy.
      destruct (proj1 (foam_adjoin_spec V M y a a) hy) as [hyin | hyeq].
      * exact (hmtrans y hyin).
      * subst y. exact htrans.
    + intros y hy z hz.
      destruct (proj1 (foam_adjoin_spec V M y a a) hy) as [hyin | hyeq].
      * destruct (proj1 (foam_adjoin_spec V M z a a) hz) as [hzin | hzeq].
        -- exact (htotal y hyin z hzin).
        -- subst z. left. exact hyin.
      * subst y.
        destruct (proj1 (foam_adjoin_spec V M z a a) hz) as [hzin | hzeq].
        -- right. right. exact hzin.
        -- subst z. right. left. reflexivity.
Qed.

Lemma foam_OrdinalLike_eq_succ_of_mem_max : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a p : V),
  OrdinalLike (foam_mem V M) a ->
  foam_mem V M p a ->
  (forall q, foam_mem V M q a -> ~ foam_mem V M p q) ->
  a = foam_adjoin V M p p.
Proof.
  intros V M a p ha hp hmax.
  apply (foam_extensional V M).
  intro x.
  split.
  - intro hx.
    apply (proj2 (foam_adjoin_spec V M x p p)).
    destruct (proj2 (proj2 ha) x hx p hp) as [hxp | [hxp | hpx]].
    + now left.
    + now right.
    + exfalso. exact (hmax x hx hpx).
  - intro hx.
    destruct (proj1 (foam_adjoin_spec V M x p p) hx) as [hxp | hxp].
    + exact (proj1 ha p hp x hxp).
    + subst x. exact hp.
Qed.

Lemma foam_OrdinalLike_empty_or_succ_of_mem_max_exists : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  (forall a, (exists x, foam_mem V M x a) ->
    exists p, foam_mem V M p a /\
      forall q, foam_mem V M q a -> ~ foam_mem V M p q) ->
  forall a, OrdinalLike (foam_mem V M) a ->
    a = foam_empty V M \/
    exists p, foam_mem V M p a /\ a = foam_adjoin V M p p.
Proof.
  intros V M hMax a ha.
  destruct (classic (exists x, foam_mem V M x a)) as [hne | hne].
  - destruct (hMax a hne) as [p [hp hmax]].
    right.
    exists p.
    split; [exact hp |].
    exact (foam_OrdinalLike_eq_succ_of_mem_max V M a p ha hp hmax).
  - left.
    apply (foam_extensional V M).
    intro x.
    split.
    + intro hx. exfalso. exact (hne (ex_intro _ x hx)).
    + intro hx. exfalso. exact (foam_empty_spec V M x hx).
Qed.

Definition firstOrderHFModel_of_HFAx_s (V : Type) (mem : V -> V -> Prop)
    (v : nat -> V)
    (hHF : forall g, HFAx_s g -> Sat V mem v g) :
    FirstOrderHFModel V :=
  {| fohf_mem := mem;
     fohf_extensional := semantic_extensionality_of_HFAx_s V mem v hHF;
     fohf_empty_exists := semantic_empty_of_HFAx_s V mem v hHF;
     fohf_adjoin_exists := semantic_adjoin_of_HFAx_s V mem v hHF;
     fohf_induction_schema := semantic_induction_schema_of_HFAx_s V mem v hHF |}.

Definition firstOrderAdjunctionModel_of_HFAx_s (V : Type)
    (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFAx_s g -> Sat V mem v g) :
    FirstOrderAdjunctionModel V.
Proof.
  pose (empty_sig :=
    constructive_indefinite_description _
      (semantic_empty_of_HFAx_s V mem v hHF)).
  pose (adj_sig := fun a b =>
    constructive_indefinite_description _
      (semantic_adjoin_of_HFAx_s V mem v hHF a b)).
  refine {| foam_mem := mem;
            foam_empty := proj1_sig empty_sig;
            foam_adjoin := fun a b => proj1_sig (adj_sig a b);
            foam_extensional := semantic_extensionality_of_HFAx_s V mem v hHF;
            foam_induction_schema := semantic_induction_schema_of_HFAx_s V mem v hHF |}.
  - exact (proj2_sig empty_sig).
  - intros x a b.
    exact (proj2_sig (adj_sig a b) x).
Defined.

Definition firstOrderFiniteAdjunctionModel_of_HFFinAx_s (V : Type)
    (mem : V -> V -> Prop) (v : nat -> V)
    (hHF : forall g, HFFinAx_s g -> Sat V mem v g) :
    FirstOrderFiniteAdjunctionModel V.
Proof.
  pose (empty_sig :=
    constructive_indefinite_description _
      (semantic_empty_of_HFFinAx_s V mem v hHF)).
  pose (adj_sig := fun a b =>
    constructive_indefinite_description _
      (semantic_adjoin_of_HFFinAx_s V mem v hHF a b)).
  refine {| fofam_base :=
      {| foam_mem := mem;
         foam_empty := proj1_sig empty_sig;
         foam_adjoin := fun a b => proj1_sig (adj_sig a b);
         foam_extensional := semantic_extensionality_of_HFFinAx_s V mem v hHF;
         foam_induction_schema := semantic_induction_schema_of_HFFinAx_s V mem v hHF |};
      fofam_finite_induction_schema :=
        semantic_finite_induction_schema_of_HFFinAx_s V mem v hHF |}.
  - exact (proj2_sig empty_sig).
  - intros x a b.
    exact (proj2_sig (adj_sig a b) x).
Defined.

Definition foam_single_obj (V : Type) (M : FirstOrderAdjunctionModel V)
    (a : V) : V :=
  foam_adjoin V M (foam_empty V M) a.

Lemma foam_single_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a x : V),
  foam_mem V M x (foam_single_obj V M a) <-> x = a.
Proof.
  intros V M a x.
  unfold foam_single_obj.
  rewrite foam_adjoin_spec.
  split.
  - intros [hx | hx].
    + exfalso. exact (foam_empty_spec V M x hx).
    + exact hx.
  - intro hx. now right.
Qed.

Definition foam_upair_obj (V : Type) (M : FirstOrderAdjunctionModel V)
    (a b : V) : V :=
  foam_adjoin V M (foam_single_obj V M a) b.

Lemma foam_upair_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b x : V),
  foam_mem V M x (foam_upair_obj V M a b) <-> x = a \/ x = b.
Proof.
  intros V M a b x.
  unfold foam_upair_obj.
  rewrite foam_adjoin_spec.
  rewrite foam_single_spec.
  tauto.
Qed.

Definition foam_kpair_obj (V : Type) (M : FirstOrderAdjunctionModel V)
    (a b : V) : V :=
  foam_upair_obj V M (foam_single_obj V M a) (foam_upair_obj V M a b).

Lemma foam_kpair_mem : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b q : V),
  foam_mem V M q (foam_kpair_obj V M a b) <->
    q = foam_single_obj V M a \/ q = foam_upair_obj V M a b.
Proof.
  intros V M a b q.
  unfold foam_kpair_obj.
  apply foam_upair_spec.
Qed.

Lemma foam_single_injective : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b : V),
  foam_single_obj V M a = foam_single_obj V M b -> a = b.
Proof.
  intros V M a b h.
  assert (ha : foam_mem V M a (foam_single_obj V M a)).
  { apply (proj2 (foam_single_spec V M a a)). reflexivity. }
  rewrite h in ha.
  exact (proj1 (foam_single_spec V M b a) ha).
Qed.

Lemma foam_upair_eq_single : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b c : V),
  foam_upair_obj V M a b = foam_single_obj V M c -> a = c /\ b = c.
Proof.
  intros V M a b c h.
  split.
  - assert (ha : foam_mem V M a (foam_upair_obj V M a b)).
    { apply (proj2 (foam_upair_spec V M a b a)). now left. }
    rewrite h in ha.
    exact (proj1 (foam_single_spec V M c a) ha).
  - assert (hb : foam_mem V M b (foam_upair_obj V M a b)).
    { apply (proj2 (foam_upair_spec V M a b b)). now right. }
    rewrite h in hb.
    exact (proj1 (foam_single_spec V M c b) hb).
Qed.

Lemma foam_kpair_injective : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a b c d : V),
  foam_kpair_obj V M a b = foam_kpair_obj V M c d -> a = c /\ b = d.
Proof.
  intros V M a b c d h.
  assert (hac : a = c).
  {
    assert (hs : foam_mem V M (foam_single_obj V M a)
        (foam_kpair_obj V M a b)).
    { apply (proj2 (foam_kpair_mem V M a b (foam_single_obj V M a))). now left. }
    rewrite h in hs.
    destruct (proj1 (foam_kpair_mem V M c d (foam_single_obj V M a)) hs)
      as [hsc | hsu].
    - exact (foam_single_injective V M a c hsc).
    - symmetry. exact (proj1 (foam_upair_eq_single V M c d a (eq_sym hsu))).
  }
  subst c.
  split.
  - reflexivity.
  - assert (h1 : foam_mem V M (foam_upair_obj V M a b)
        (foam_kpair_obj V M a b)).
    { apply (proj2 (foam_kpair_mem V M a b (foam_upair_obj V M a b))). now right. }
    rewrite h in h1.
    destruct (proj1 (foam_kpair_mem V M a d (foam_upair_obj V M a b)) h1)
      as [h1_single | h1_upair].
    + pose proof (proj2 (foam_upair_eq_single V M a b a h1_single)) as hba.
      assert (h2 : foam_mem V M (foam_upair_obj V M a d)
          (foam_kpair_obj V M a d)).
      { apply (proj2 (foam_kpair_mem V M a d (foam_upair_obj V M a d))). now right. }
      rewrite <- h in h2.
      destruct (proj1 (foam_kpair_mem V M a b (foam_upair_obj V M a d)) h2)
        as [h2_single | h2_upair].
      * pose proof (proj2 (foam_upair_eq_single V M a d a h2_single)) as hda.
        rewrite hba, hda. reflexivity.
      * assert (hd : foam_mem V M d (foam_upair_obj V M a d)).
        { apply (proj2 (foam_upair_spec V M a d d)). now right. }
        rewrite h2_upair in hd.
        destruct (proj1 (foam_upair_spec V M a b d) hd) as [hd_eq_a | hd_eq_b].
        -- rewrite hba, hd_eq_a. reflexivity.
        -- symmetry. exact hd_eq_b.
    + assert (hb : foam_mem V M b (foam_upair_obj V M a b)).
      { apply (proj2 (foam_upair_spec V M a b b)). now right. }
      rewrite h1_upair in hb.
      destruct (proj1 (foam_upair_spec V M a d b) hb) as [hb_eq_a | hb_eq_d].
      * assert (hd : foam_mem V M d (foam_upair_obj V M a d)).
        { apply (proj2 (foam_upair_spec V M a d d)). now right. }
        rewrite <- h1_upair in hd.
        destruct (proj1 (foam_upair_spec V M a b d) hd) as [hd_eq_a | hd_eq_b].
        -- rewrite hb_eq_a, hd_eq_a. reflexivity.
        -- symmetry. exact hd_eq_b.
      * exact hb_eq_d.
Qed.

Lemma foam_HF_emptyAt_empty : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) i,
  Sat V (foam_mem V M) e (HF_emptyAt i) <-> e i = foam_empty V M.
Proof.
  intros V M e i.
  split.
  - intro h.
    apply (foam_extensional V M).
    intro x.
    split.
    + intro hx. exfalso. exact (h x hx).
    + intro hx. exfalso. exact (foam_empty_spec V M x hx).
  - intros h x hx.
    change (foam_mem V M x (e i)) in hx.
    rewrite h in hx.
    exact (foam_empty_spec V M x hx).
Qed.

Lemma foam_HF_adjoinAt_adjoin : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) c a b,
  Sat V (foam_mem V M) e (HF_adjoinAt c a b) <->
    e c = foam_adjoin V M (e a) (e b).
Proof.
  intros V M e c a b.
  split.
  - intro h.
    apply (foam_extensional V M).
    intro x.
    rewrite (proj1 (HF_adjoinAt_spec V (foam_mem V M) e c a b) h x).
    symmetry.
    apply foam_adjoin_spec.
  - intro h.
    apply (proj2 (HF_adjoinAt_spec V (foam_mem V M) e c a b)).
    intro x.
    rewrite h.
    apply foam_adjoin_spec.
Qed.

Lemma foam_HF_succAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) s a,
  Sat V (foam_mem V M) e (HF_succAt s a) <->
    e s = foam_adjoin V M (e a) (e a).
Proof.
  intros V M e s a.
  apply foam_HF_adjoinAt_adjoin.
Qed.

Lemma foam_HF_singleAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) i j,
  Sat V (foam_mem V M) e (HF_singleAt i j) <->
    e i = foam_single_obj V M (e j).
Proof.
  intros V M e i j.
  split.
  - intro h.
    apply (foam_extensional V M).
    intro x.
    rewrite foam_single_spec.
    unfold HF_singleAt, fIff in h.
    simpl in h.
    exact (conj (fun hx => proj1 (h x) hx) (fun hx => proj2 (h x) hx)).
  - intros h x.
    unfold HF_singleAt, fIff.
    simpl.
    rewrite h.
    apply foam_single_spec.
Qed.

Lemma foam_HF_upairAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) i j k,
  Sat V (foam_mem V M) e (HF_upairAt i j k) <->
    e i = foam_upair_obj V M (e j) (e k).
Proof.
  intros V M e i j k.
  split.
  - intro h.
    apply (foam_extensional V M).
    intro x.
    rewrite foam_upair_spec.
    unfold HF_upairAt, fIff in h.
    simpl in h.
    exact (conj (fun hx => proj1 (h x) hx) (fun hx => proj2 (h x) hx)).
  - intros h x.
    unfold HF_upairAt, fIff.
    simpl.
    rewrite h.
    apply foam_upair_spec.
Qed.

Lemma foam_HF_kpairAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) p a b,
  Sat V (foam_mem V M) e (HF_kpairAt p a b) <->
    e p = foam_kpair_obj V M (e a) (e b).
Proof.
  intros V M e p a b.
  split.
  - intro h.
    apply (foam_extensional V M).
    intro q.
    unfold HF_kpairAt, fIff in h.
    simpl in h.
    rewrite foam_kpair_mem.
    split.
    + intro hq.
      destruct (proj1 (h q) hq) as [hs | hu].
      * left.
        exact (proj1 (foam_HF_singleAt_spec V M (scons V q e) 0 (S a)) hs).
      * right.
        exact (proj1 (foam_HF_upairAt_spec V M (scons V q e) 0 (S a) (S b)) hu).
    + intros [hs | hu].
      * apply (proj2 (h q)).
        left.
        exact (proj2 (foam_HF_singleAt_spec V M (scons V q e) 0 (S a)) hs).
      * apply (proj2 (h q)).
        right.
        exact (proj2 (foam_HF_upairAt_spec V M (scons V q e) 0 (S a) (S b)) hu).
  - intros h q.
    unfold HF_kpairAt, fIff.
    simpl.
    rewrite h.
    split.
    + intro hq.
      destruct (proj1 (foam_kpair_mem V M (e a) (e b) q) hq) as [hs | hu].
      * left.
        exact (proj2 (foam_HF_singleAt_spec V M (scons V q e) 0 (S a)) hs).
      * right.
        exact (proj2 (foam_HF_upairAt_spec V M (scons V q e) 0 (S a) (S b)) hu).
    + intros [hs | hu].
      * apply (proj2 (foam_kpair_mem V M (e a) (e b) q)).
        left.
        exact (proj1 (foam_HF_singleAt_spec V M (scons V q e) 0 (S a)) hs).
      * apply (proj2 (foam_kpair_mem V M (e a) (e b) q)).
        right.
        exact (proj1 (foam_HF_upairAt_spec V M (scons V q e) 0 (S a) (S b)) hu).
Qed.

Lemma foam_HF_pairMemAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) a b r,
  Sat V (foam_mem V M) e (HF_pairMemAt a b r) <->
    foam_mem V M (foam_kpair_obj V M (e a) (e b)) (e r).
Proof.
  intros V M e a b r.
  split.
  - intros [p [hp hmem]].
    pose proof (proj1 (foam_HF_kpairAt_spec V M (scons V p e) 0 (S a) (S b)) hp)
      as hp'.
    simpl in hp'.
    change (foam_mem V M p (e r)) in hmem.
    rewrite hp' in hmem.
    exact hmem.
  - intro h.
    exists (foam_kpair_obj V M (e a) (e b)).
    split.
    + apply (proj2 (foam_HF_kpairAt_spec V M
        (scons V (foam_kpair_obj V M (e a) (e b)) e) 0 (S a) (S b))).
      reflexivity.
    + exact h.
Qed.

Definition foam_pair_functional (V : Type)
    (M : FirstOrderAdjunctionModel V) (f : V) : Prop :=
  forall k y y',
    foam_mem V M (foam_kpair_obj V M k y) f ->
    foam_mem V M (foam_kpair_obj V M k y') f ->
    y = y'.

Definition foam_pair_keys_below_succ (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m : V) : Prop :=
  forall k y,
    foam_mem V M (foam_kpair_obj V M k y) f ->
    foam_mem V M k m \/ k = m.

Definition foam_pair_total_below_succ (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m : V) : Prop :=
  forall k,
    foam_mem V M k m \/ k = m ->
    exists y, foam_mem V M (foam_kpair_obj V M k y) f.

Definition foam_pair_succ_step (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m : V) : Prop :=
  forall k t y,
    foam_mem V M k m ->
    foam_mem V M (foam_kpair_obj V M k t) f ->
    foam_mem V M (foam_kpair_obj V M (foam_adjoin V M k k) y) f ->
    y = foam_adjoin V M t t.

Lemma foam_HF_pairFunctionalAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f,
  Sat V (foam_mem V M) e (HF_pairFunctionalAt f) <->
    foam_pair_functional V M (e f).
Proof.
  intros V M e f.
  split.
  - intros h k y y' hky hky'.
    apply (h k y y').
    split.
    + apply (proj2 (foam_HF_pairMemAt_spec V M
        (scons V y' (scons V y (scons V k e))) 2 1 (S (S (S f))))).
      exact hky.
    + apply (proj2 (foam_HF_pairMemAt_spec V M
        (scons V y' (scons V y (scons V k e))) 2 0 (S (S (S f))))).
      exact hky'.
  - intros h k y y' hpairs.
    unfold foam_pair_functional in h.
    change (y = y').
    exact (h k y y'
      (proj1 (foam_HF_pairMemAt_spec V M
        (scons V y' (scons V y (scons V k e))) 2 1 (S (S (S f))))
        (proj1 hpairs))
      (proj1 (foam_HF_pairMemAt_spec V M
        (scons V y' (scons V y (scons V k e))) 2 0 (S (S (S f))))
        (proj2 hpairs))).
Qed.

Lemma foam_HF_pairKeysBelowSuccAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f m,
  Sat V (foam_mem V M) e (HF_pairKeysBelowSuccAt f m) <->
    foam_pair_keys_below_succ V M (e f) (e m).
Proof.
  intros V M e f m.
  split.
  - intros h k y hky.
    apply (h k y).
    apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V y (scons V k e)) 1 0 (S (S f)))).
    exact hky.
  - intros h k y hpair.
    unfold foam_pair_keys_below_succ in h.
    change (foam_mem V M k (e m) \/ k = e m).
    exact (h k y
      (proj1 (foam_HF_pairMemAt_spec V M
        (scons V y (scons V k e)) 1 0 (S (S f))) hpair)).
Qed.

Lemma foam_HF_pairTotalBelowSuccAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f m,
  Sat V (foam_mem V M) e (HF_pairTotalBelowSuccAt f m) <->
    foam_pair_total_below_succ V M (e f) (e m).
Proof.
  intros V M e f m.
  split.
  - intros h k hk.
    destruct (h k hk) as [y hy].
    exists y.
    apply (proj1 (foam_HF_pairMemAt_spec V M
      (scons V y (scons V k e)) 1 0 (S (S f)))).
    exact hy.
  - intros h k hk.
    unfold foam_pair_total_below_succ in h.
    destruct (h k hk) as [y hy].
    exists y.
    apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V y (scons V k e)) 1 0 (S (S f)))).
    exact hy.
Qed.

Lemma foam_HF_pairSuccStepAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f m,
  Sat V (foam_mem V M) e (HF_pairSuccStepAt f m) <->
    foam_pair_succ_step V M (e f) (e m).
Proof.
  intros V M e f m.
  split.
  - intros h k t y hkm hkt hsy.
    pose (sk := foam_adjoin V M k k).
    pose proof (h k t y hkm) as h1.
    pose proof (h1
      (proj2 (foam_HF_pairMemAt_spec V M
        (scons V y (scons V t (scons V k e))) 2 1 (S (S (S f)))) hkt))
      as h2.
    pose proof (h2 sk
      (proj2 (foam_HF_succAt_spec V M
        (scons V sk (scons V y (scons V t (scons V k e)))) 0 3) eq_refl))
      as h3.
    pose proof (h3
      (proj2 (foam_HF_pairMemAt_spec V M
        (scons V sk (scons V y (scons V t (scons V k e)))) 0 1
        (S (S (S (S f))))) hsy)) as h4.
    exact (proj1 (foam_HF_succAt_spec V M
      (scons V sk (scons V y (scons V t (scons V k e)))) 1 2) h4).
  - intros h k t y hkm hkt sk hsk hsky.
    pose proof (proj1 (foam_HF_succAt_spec V M
      (scons V sk (scons V y (scons V t (scons V k e)))) 0 3) hsk)
      as hsk'.
    simpl in hsk'.
    assert (hsky' : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M k k) y) (e f)).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M
        (scons V sk (scons V y (scons V t (scons V k e)))) 0 1
        (S (S (S (S f))))) hsky) as hpair.
      simpl in hpair.
      rewrite hsk' in hpair.
      exact hpair.
    }
    apply (proj2 (foam_HF_succAt_spec V M
      (scons V sk (scons V y (scons V t (scons V k e)))) 1 2)).
    change (y = foam_adjoin V M t t).
    unfold foam_pair_succ_step in h.
    change (foam_mem V M k (e m)) in hkm.
    exact (h k t y hkm
      (proj1 (foam_HF_pairMemAt_spec V M
        (scons V y (scons V t (scons V k e))) 2 1 (S (S (S f)))) hkt)
      hsky').
Qed.

Lemma foam_HF_pairBaseAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f s,
  Sat V (foam_mem V M) e (HF_pairBaseAt f s) <->
    foam_mem V M (foam_kpair_obj V M (foam_empty V M) (e s)) (e f).
Proof.
  intros V M e f s.
  split.
  - intros [z [hz hpair]].
    pose proof (proj1 (foam_HF_emptyAt_empty V M (scons V z e) 0) hz) as hz'.
    simpl in hz'.
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V z e) 0 (S s) (S f)) hpair) as hpair'.
    simpl in hpair'.
    rewrite hz' in hpair'.
    exact hpair'.
  - intro h.
    exists (foam_empty V M).
    split.
    + apply (proj2 (foam_HF_emptyAt_empty V M (scons V (foam_empty V M) e) 0)).
      reflexivity.
    + apply (proj2 (foam_HF_pairMemAt_spec V M
        (scons V (foam_empty V M) e) 0 (S s) (S f))).
      simpl.
      exact h.
Qed.

Lemma foam_HF_pairZeroBaseAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f,
  Sat V (foam_mem V M) e (HF_pairZeroBaseAt f) <->
    foam_mem V M (foam_kpair_obj V M (foam_empty V M) (foam_empty V M)) (e f).
Proof.
  intros V M e f.
  split.
  - intros [z [hz hpair]].
    pose proof (proj1 (foam_HF_emptyAt_empty V M (scons V z e) 0) hz) as hz'.
    simpl in hz'.
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V z e) 0 0 (S f)) hpair) as hpair'.
    simpl in hpair'.
    rewrite hz' in hpair'.
    exact hpair'.
  - intro h.
    exists (foam_empty V M).
    split.
    + apply (proj2 (foam_HF_emptyAt_empty V M (scons V (foam_empty V M) e) 0)).
      reflexivity.
    + apply (proj2 (foam_HF_pairMemAt_spec V M
        (scons V (foam_empty V M) e) 0 0 (S f))).
      simpl.
      exact h.
Qed.

Definition foam_succ_rec_approx (V : Type)
    (M : FirstOrderAdjunctionModel V) (s f m : V) : Prop :=
  foam_pair_functional V M f /\
  foam_pair_keys_below_succ V M f m /\
  foam_mem V M (foam_kpair_obj V M (foam_empty V M) s) f /\
  foam_pair_total_below_succ V M f m /\
  foam_pair_succ_step V M f m.

Definition foam_succ_rec_total (V : Type)
    (M : FirstOrderAdjunctionModel V) (s m : V) : Prop :=
  exists f z,
    foam_succ_rec_approx V M s f m /\
    foam_mem V M (foam_kpair_obj V M m z) f.

Definition HF_succRecTotalAt (s m : nat) : form :=
  fEx (fEx (fAnd
    (HF_succRecApproxAt 1 (S (S s)) (S (S m)))
    (HF_pairMemAt (S (S m)) 0 1))).

Definition HF_succRecTotalOnOrdinalAt (s m : nat) : form :=
  fImp (HF_ordinalLikeAt m) (HF_succRecTotalAt s m).

Lemma foam_HF_succRecApproxAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f s m,
  Sat V (foam_mem V M) e (HF_succRecApproxAt f s m) <->
    foam_succ_rec_approx V M (e s) (e f) (e m).
Proof.
  intros V M e f s m.
  unfold HF_succRecApproxAt, foam_succ_rec_approx.
  split.
  - intros [hfun [hkeys [hbase [htotal hstep]]]].
    exact (conj
      (proj1 (foam_HF_pairFunctionalAt_spec V M e f) hfun)
      (conj
        (proj1 (foam_HF_pairKeysBelowSuccAt_spec V M e f m) hkeys)
        (conj
          (proj1 (foam_HF_pairBaseAt_spec V M e f s) hbase)
          (conj
            (proj1 (foam_HF_pairTotalBelowSuccAt_spec V M e f m) htotal)
            (proj1 (foam_HF_pairSuccStepAt_spec V M e f m) hstep))))).
  - intros [hfun [hkeys [hbase [htotal hstep]]]].
    exact (conj
      (proj2 (foam_HF_pairFunctionalAt_spec V M e f) hfun)
      (conj
        (proj2 (foam_HF_pairKeysBelowSuccAt_spec V M e f m) hkeys)
        (conj
          (proj2 (foam_HF_pairBaseAt_spec V M e f s) hbase)
          (conj
            (proj2 (foam_HF_pairTotalBelowSuccAt_spec V M e f m) htotal)
            (proj2 (foam_HF_pairSuccStepAt_spec V M e f m) hstep))))).
Qed.

Lemma foam_HF_succRecTotalAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) s m,
  Sat V (foam_mem V M) e (HF_succRecTotalAt s m) <->
    foam_succ_rec_total V M (e s) (e m).
Proof.
  intros V M e s m.
  split.
  - intros [f [z [hf hz]]].
    exists f, z.
    split.
    + exact (proj1 (foam_HF_succRecApproxAt_spec V M
        (scons V z (scons V f e)) 1 (S (S s)) (S (S m))) hf).
    + exact (proj1 (foam_HF_pairMemAt_spec V M
        (scons V z (scons V f e)) (S (S m)) 0 1) hz).
  - intros [f [z [hf hz]]].
    exists f, z.
    split.
    + exact (proj2 (foam_HF_succRecApproxAt_spec V M
        (scons V z (scons V f e)) 1 (S (S s)) (S (S m))) hf).
    + exact (proj2 (foam_HF_pairMemAt_spec V M
        (scons V z (scons V f e)) (S (S m)) 0 1) hz).
Qed.

Lemma foam_HF_succRecTotalOnOrdinalAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) s m,
  Sat V (foam_mem V M) e (HF_succRecTotalOnOrdinalAt s m) <->
    (OrdinalLike (foam_mem V M) (e m) ->
      foam_succ_rec_total V M (e s) (e m)).
Proof.
  intros V M e s m.
  unfold HF_succRecTotalOnOrdinalAt.
  split.
  - intros h hm.
    apply (proj1 (foam_HF_succRecTotalAt_spec V M e s m)).
    apply h.
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) e m)).
    exact hm.
  - intros h hmSat.
    apply (proj2 (foam_HF_succRecTotalAt_spec V M e s m)).
    apply h.
    apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) e m)).
    exact hmSat.
Qed.

Definition foam_zero_succ_rec_graph (V : Type)
    (M : FirstOrderAdjunctionModel V) (s : V) : V :=
  foam_single_obj V M (foam_kpair_obj V M (foam_empty V M) s).

Lemma foam_zero_succ_rec_graph_base : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (s : V),
  foam_mem V M
    (foam_kpair_obj V M (foam_empty V M) s)
    (foam_zero_succ_rec_graph V M s).
Proof.
  intros V M s.
  apply (proj2 (foam_single_spec V M
    (foam_kpair_obj V M (foam_empty V M) s)
    (foam_kpair_obj V M (foam_empty V M) s))).
  reflexivity.
Qed.

Lemma foam_zero_succ_rec_graph_succRecApprox : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (s : V),
  foam_succ_rec_approx V M s
    (foam_zero_succ_rec_graph V M s)
    (foam_empty V M).
Proof.
  intros V M s.
  unfold foam_succ_rec_approx.
  repeat split.
  - intros k y y' hky hky'.
    pose proof (proj1 (foam_single_spec V M
      (foam_kpair_obj V M (foam_empty V M) s)
      (foam_kpair_obj V M k y)) hky) as hky_eq.
    pose proof (proj1 (foam_single_spec V M
      (foam_kpair_obj V M (foam_empty V M) s)
      (foam_kpair_obj V M k y')) hky') as hky'_eq.
    pose proof (proj2 (foam_kpair_injective V M k y (foam_empty V M) s hky_eq))
      as hy.
    pose proof (proj2 (foam_kpair_injective V M k y' (foam_empty V M) s hky'_eq))
      as hy'.
    rewrite hy, hy'. reflexivity.
  - intros k y hky.
    pose proof (proj1 (foam_single_spec V M
      (foam_kpair_obj V M (foam_empty V M) s)
      (foam_kpair_obj V M k y)) hky) as hk_eq.
    right.
    exact (proj1 (foam_kpair_injective V M k y (foam_empty V M) s hk_eq)).
  - apply foam_zero_succ_rec_graph_base.
  - intros k [hk | hk].
    + exfalso. exact (foam_empty_spec V M k hk).
    + subst k.
      exists s.
      apply foam_zero_succ_rec_graph_base.
  - intros k t y hkm _ _.
    exfalso. exact (foam_empty_spec V M k hkm).
Qed.

Lemma foam_succ_rec_total_empty : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (s : V),
  foam_succ_rec_total V M s (foam_empty V M).
Proof.
  intros V M s.
  exists (foam_zero_succ_rec_graph V M s), s.
  split.
  - apply foam_zero_succ_rec_graph_succRecApprox.
  - apply foam_zero_succ_rec_graph_base.
Qed.

Definition foam_succ_rec_graph_succ (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m z : V) : V :=
  foam_adjoin V M f
    (foam_kpair_obj V M
      (foam_adjoin V M m m)
      (foam_adjoin V M z z)).

Lemma foam_succ_rec_graph_succ_old : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m z p : V),
  foam_mem V M p f ->
  foam_mem V M p (foam_succ_rec_graph_succ V M f m z).
Proof.
  intros V M f m z p hp.
  apply (proj2 (foam_adjoin_spec V M p f
    (foam_kpair_obj V M
      (foam_adjoin V M m m)
      (foam_adjoin V M z z)))).
  now left.
Qed.

Lemma foam_succ_rec_graph_succ_new : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m z : V),
  foam_mem V M
    (foam_kpair_obj V M
      (foam_adjoin V M m m)
      (foam_adjoin V M z z))
    (foam_succ_rec_graph_succ V M f m z).
Proof.
  intros V M f m z.
  apply (proj2 (foam_adjoin_spec V M
    (foam_kpair_obj V M
      (foam_adjoin V M m m)
      (foam_adjoin V M z z))
    f
    (foam_kpair_obj V M
      (foam_adjoin V M m m)
      (foam_adjoin V M z z)))).
  now right.
Qed.

Lemma foam_succ_rec_graph_succ_succRecApprox : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (s f m z : V),
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_approx V M s f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  foam_succ_rec_approx V M s
    (foam_succ_rec_graph_succ V M f m z)
    (foam_adjoin V M m m).
Proof.
  intros V M s f m z hm hf hz.
  destruct hf as [hfun [hkeys [hbase [htotal hstep]]]].
  set (sm := foam_adjoin V M m m).
  set (sz := foam_adjoin V M z z).
  set (newPair := foam_kpair_obj V M sm sz).
  set (g := foam_succ_rec_graph_succ V M f m z).
  assert (hsm_not_mem : ~ foam_mem V M sm m).
  {
    unfold sm.
    exact (foam_adjoin_self_not_mem_of_OrdinalLike V M m hm).
  }
  assert (hsm_ne_m : sm <> m).
  {
    unfold sm.
    exact (foam_adjoin_self_ne_self V M m).
  }
  assert (hmem_g : forall p,
      foam_mem V M p g <-> foam_mem V M p f \/ p = newPair).
  {
    intro p.
    unfold g, newPair, sm, sz, foam_succ_rec_graph_succ.
    apply foam_adjoin_spec.
  }
  assert (old_key_ne_succ : forall k y,
      foam_mem V M (foam_kpair_obj V M k y) f -> k <> sm).
  {
    intros k y hOld hk.
    pose proof (hkeys k y hOld) as hkBound.
    rewrite hk in hkBound.
    destruct hkBound as [hmem | heq].
    - exact (hsm_not_mem hmem).
    - exact (hsm_ne_m heq).
  }
  assert (pair_old_of_mem_key : forall k y,
      foam_mem V M k m ->
      foam_mem V M (foam_kpair_obj V M k y) g ->
      foam_mem V M (foam_kpair_obj V M k y) f).
  {
    intros k y hkm hkg.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k y)) hkg)
      as [hOld | hNew].
    - exact hOld.
    - pose proof (proj1 (foam_kpair_injective V M k y sm sz hNew)) as hk.
      rewrite hk in hkm.
      exfalso. exact (hsm_not_mem hkm).
  }
  unfold foam_succ_rec_approx.
  repeat split.
  - intros k y y' hky hky'.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k y)) hky)
      as [hOld | hNew].
    + destruct (proj1 (hmem_g (foam_kpair_obj V M k y')) hky')
        as [hOld' | hNew'].
      * exact (hfun k y y' hOld hOld').
      * pose proof (proj1 (foam_kpair_injective V M k y' sm sz hNew')) as hk.
        exfalso. exact (old_key_ne_succ k y hOld hk).
    + destruct (proj1 (hmem_g (foam_kpair_obj V M k y')) hky')
        as [hOld' | hNew'].
      * pose proof (proj1 (foam_kpair_injective V M k y sm sz hNew)) as hk.
        exfalso. exact (old_key_ne_succ k y' hOld' hk).
      * pose proof (proj2 (foam_kpair_injective V M k y sm sz hNew)) as hy.
        pose proof (proj2 (foam_kpair_injective V M k y' sm sz hNew')) as hy'.
        rewrite hy, hy'. reflexivity.
  - intros k y hky.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k y)) hky)
      as [hOld | hNew].
    + destruct (hkeys k y hOld) as [hkm | hkm].
      * left. apply (proj2 (foam_adjoin_spec V M k m m)). now left.
      * left. apply (proj2 (foam_adjoin_spec V M k m m)). now right.
    + right. exact (proj1 (foam_kpair_injective V M k y sm sz hNew)).
  - exact (foam_succ_rec_graph_succ_old V M f m z
      (foam_kpair_obj V M (foam_empty V M) s) hbase).
  - intros k hk.
    destruct hk as [hksm | hksm].
    + destruct (proj1 (foam_adjoin_spec V M k m m) hksm)
        as [hkm | hkm].
      * destruct (htotal k (or_introl hkm)) as [y hy].
        exists y.
        exact (foam_succ_rec_graph_succ_old V M f m z
          (foam_kpair_obj V M k y) hy).
      * destruct (htotal k (or_intror hkm)) as [y hy].
        exists y.
        exact (foam_succ_rec_graph_succ_old V M f m z
          (foam_kpair_obj V M k y) hy).
    + subst k.
      exists sz.
      unfold sz, sm.
      apply foam_succ_rec_graph_succ_new.
  - intros k t y hksm hkt hsky.
    destruct (proj1 (foam_adjoin_spec V M k m m) hksm)
      as [hkm | hkm].
    + assert (hktOld : foam_mem V M (foam_kpair_obj V M k t) f).
      {
        exact (pair_old_of_mem_key k t hkm hkt).
      }
      assert (hskyOld :
          foam_mem V M (foam_kpair_obj V M (foam_adjoin V M k k) y) f).
      {
        destruct (proj1 (hmem_g
          (foam_kpair_obj V M (foam_adjoin V M k k) y)) hsky)
          as [hOld | hNew].
        - exact hOld.
        - pose proof (proj1 (foam_kpair_injective V M
            (foam_adjoin V M k k) y sm sz hNew)) as hsk.
          assert (hkOrd : OrdinalLike (foam_mem V M) k).
          {
            exact (OrdinalLike_of_mem V (foam_mem V M) m k hm hkm).
          }
          assert (hkm_eq : k = m).
          {
            apply (foam_adjoin_self_injective_on_OrdinalLike V M k m hkOrd hm).
            unfold sm in hsk.
            exact hsk.
          }
          rewrite hkm_eq in hkm.
          exfalso. exact (foam_mem_irrefl V M m hkm).
      }
      exact (hstep k t y hkm hktOld hskyOld).
    + subst k.
      assert (hktOld : foam_mem V M (foam_kpair_obj V M m t) f).
      {
        destruct (proj1 (hmem_g (foam_kpair_obj V M m t)) hkt)
          as [hOld | hNew].
        - exact hOld.
        - pose proof (proj1 (foam_kpair_injective V M m t sm sz hNew))
            as hm_eq_sm.
          exfalso. exact (hsm_ne_m (eq_sym hm_eq_sm)).
      }
      pose proof (hfun m t z hktOld hz) as ht.
      destruct (proj1 (hmem_g (foam_kpair_obj V M sm y)) hsky)
        as [hOld | hNew].
      * exfalso. exact (old_key_ne_succ sm y hOld eq_refl).
      * pose proof (proj2 (foam_kpair_injective V M sm y sm sz hNew)) as hy.
        rewrite hy, ht.
        unfold sz.
        reflexivity.
Qed.

Lemma foam_succ_rec_total_succ : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (s m : V),
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_total V M s m ->
  foam_succ_rec_total V M s (foam_adjoin V M m m).
Proof.
  intros V M s m hm [f [z [hf hz]]].
  exists (foam_succ_rec_graph_succ V M f m z), (foam_adjoin V M z z).
  split.
  - exact (foam_succ_rec_graph_succ_succRecApprox V M s f m z hm hf hz).
  - apply foam_succ_rec_graph_succ_new.
Qed.

Lemma foam_succ_rec_total_of_ordinalLike_of_predecessor : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  (forall a, OrdinalLike (foam_mem V M) a ->
    a = foam_empty V M \/
    exists p, foam_mem V M p a /\ a = foam_adjoin V M p p) ->
  forall s m,
    OrdinalLike (foam_mem V M) m ->
    foam_succ_rec_total V M s m.
Proof.
  intros V M hPred s m hm.
  pose (phi := HF_succRecTotalOnOrdinalAt 1 0).
  pose (tail := fun _ : nat => s).
  pose proof (foam_induction_schema V M phi (scons V s tail)) as hind.
  assert (hall : forall a,
      Sat V (foam_mem V M) (scons V a (scons V s tail)) phi).
  {
    apply hind.
    intros a ih.
    apply (proj2 (foam_HF_succRecTotalOnOrdinalAt_spec V M
      (scons V a (scons V s tail)) 1 0)).
    intro ha.
    destruct (hPred a ha) as [haEmpty | [p [hpa haSucc]]].
    - rewrite haEmpty.
      apply foam_succ_rec_total_empty.
    - assert (hpOrd : OrdinalLike (foam_mem V M) p).
      {
        exact (OrdinalLike_of_mem V (foam_mem V M) a p ha hpa).
      }
      pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
        phi (scons V s tail) a p) (ih p hpa)) as hpSat.
      assert (hpTotal : foam_succ_rec_total V M s p).
      {
        exact (proj1 (foam_HF_succRecTotalOnOrdinalAt_spec V M
          (scons V p (scons V s tail)) 1 0) hpSat hpOrd).
      }
      rewrite haSucc.
      exact (foam_succ_rec_total_succ V M s p hpOrd hpTotal).
  }
  exact (proj1 (foam_HF_succRecTotalOnOrdinalAt_spec V M
    (scons V m (scons V s tail)) 1 0) (hall m) hm).
Qed.

Lemma foam_succ_rec_total_of_ordinalLike_of_mem_max_exists : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  (forall a, (exists x, foam_mem V M x a) ->
    exists p, foam_mem V M p a /\
      forall q, foam_mem V M q a -> ~ foam_mem V M p q) ->
  forall s m,
    OrdinalLike (foam_mem V M) m ->
    foam_succ_rec_total V M s m.
Proof.
  intros V M hMax s m hm.
  apply (foam_succ_rec_total_of_ordinalLike_of_predecessor V M).
  - intros a ha.
    exact (foam_OrdinalLike_empty_or_succ_of_mem_max_exists V M hMax a ha).
  - exact hm.
Qed.

Lemma fofam_sepBy_exists : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (psi : form) (e : nat -> V)
    (a : V),
  exists s, forall x,
    foam_mem V M x s <->
      foam_mem V M x a /\ Sat V (foam_mem V M) (scons V x e) psi.
Proof.
  intros V M psi e a.
  pose (theta := rename rSepParam psi).
  pose (phi := HF_sepByAt theta 0).
  pose proof (fofam_finite_induction_schema V M phi e) as hind.
  assert (hall : forall a,
      Sat V (foam_mem V M) (scons V a e) phi).
  {
    apply (proj1 (HF_finite_induction_form_spec V (foam_mem V M)
      phi e) hind).
    split.
    - intros z hzEmpty.
      apply (proj2 (HF_sepByAt_spec V (foam_mem V M) theta
        (scons V z e) 0)).
      exists (foam_empty V M).
      intro x.
      split.
      + intro hx. exfalso. exact (foam_empty_spec V M x hx).
      + intros [hxz _].
        exfalso. exact (hzEmpty x hxz).
    - intros old y c hc hOld.
      destruct (proj1 (HF_sepByAt_spec V (foam_mem V M) theta
        (scons V old e) 0) hOld) as [s hs].
      destruct (classic (Sat V (foam_mem V M) (scons V y e) psi))
        as [hyPsi | hyNotPsi].
      + apply (proj2 (HF_sepByAt_spec V (foam_mem V M) theta
          (scons V c e) 0)).
        exists (foam_adjoin V M s y).
        intro x.
        split.
        * intro hx.
          destruct (proj1 (foam_adjoin_spec V M x s y) hx) as [hxs | hxy].
          -- destruct (proj1 (hs x) hxs) as [hxold hxThetaOld].
             pose proof (proj1 (Sat_rename_rSepParam V (foam_mem V M)
               psi e old x) hxThetaOld) as hxPsi.
             split.
             ++ exact (proj2 (hc x) (or_introl hxold)).
             ++ exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
                  psi e c x) hxPsi).
          -- subst x.
             split.
             ++ exact (proj2 (hc y) (or_intror eq_refl)).
             ++ exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
                  psi e c y) hyPsi).
        * intros [hxc hxThetaC].
          destruct (proj1 (hc x) hxc) as [hxold | hxy].
          -- apply (proj2 (foam_adjoin_spec V M x s y)).
             left.
             pose proof (proj1 (Sat_rename_rSepParam V (foam_mem V M)
               psi e c x) hxThetaC) as hxPsi.
             apply (proj2 (hs x)).
             split.
             ++ exact hxold.
             ++ exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
                  psi e old x) hxPsi).
          -- apply (proj2 (foam_adjoin_spec V M x s y)).
             now right.
      + apply (proj2 (HF_sepByAt_spec V (foam_mem V M) theta
          (scons V c e) 0)).
        exists s.
        intro x.
        split.
        * intro hxs.
          destruct (proj1 (hs x) hxs) as [hxold hxThetaOld].
          pose proof (proj1 (Sat_rename_rSepParam V (foam_mem V M)
            psi e old x) hxThetaOld) as hxPsi.
          split.
          -- exact (proj2 (hc x) (or_introl hxold)).
          -- exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
               psi e c x) hxPsi).
        * intros [hxc hxThetaC].
          destruct (proj1 (hc x) hxc) as [hxold | hxy].
          -- pose proof (proj1 (Sat_rename_rSepParam V (foam_mem V M)
               psi e c x) hxThetaC) as hxPsi.
             apply (proj2 (hs x)).
             split.
             ++ exact hxold.
             ++ exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
                  psi e old x) hxPsi).
          -- subst x.
             pose proof (proj1 (Sat_rename_rSepParam V (foam_mem V M)
               psi e c y) hxThetaC) as hyPsi.
             exfalso. exact (hyNotPsi hyPsi).
  }
  destruct (proj1 (HF_sepByAt_spec V (foam_mem V M) theta
    (scons V a e) 0) (hall a)) as [s hs].
  exists s.
  intro x.
  split.
  - intro hxs.
    destruct (proj1 (hs x) hxs) as [hxa hxTheta].
    split.
    + exact hxa.
    + exact (proj1 (Sat_rename_rSepParam V (foam_mem V M)
        psi e a x) hxTheta).
  - intros [hxa hxPsi].
    apply (proj2 (hs x)).
    split.
    + exact hxa.
    + exact (proj2 (Sat_rename_rSepParam V (foam_mem V M)
        psi e a x) hxPsi).
Qed.

Lemma fofam_binUnion_exists : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (a b : V),
  exists u, forall x,
    foam_mem V M x u <-> foam_mem V M x a \/ foam_mem V M x b.
Proof.
  intros V M a b.
  pose (phi := HF_binUnionAt 1 0).
  pose (tail := fun _ : nat => a).
  pose proof (fofam_finite_induction_schema V M phi (scons V a tail))
    as hind.
  assert (hall : forall b,
      Sat V (foam_mem V M) (scons V b (scons V a tail)) phi).
  {
    apply (proj1 (HF_finite_induction_form_spec V (foam_mem V M)
      phi (scons V a tail)) hind).
    split.
    - intros z hzEmpty.
      apply (proj2 (HF_binUnionAt_spec V (foam_mem V M)
        (scons V z (scons V a tail)) 1 0)).
      exists a.
      intro x.
      split.
      + intro hxa. now left.
      + intros [hxa | hxz].
        * exact hxa.
        * exfalso. exact (hzEmpty x hxz).
    - intros old y c hc hOld.
      destruct (proj1 (HF_binUnionAt_spec V (foam_mem V M)
        (scons V old (scons V a tail)) 1 0) hOld) as [u hu].
      apply (proj2 (HF_binUnionAt_spec V (foam_mem V M)
        (scons V c (scons V a tail)) 1 0)).
      exists (foam_adjoin V M u y).
      intro x.
      split.
      + intro hx.
        destruct (proj1 (foam_adjoin_spec V M x u y) hx) as [hxu | hxy].
        * destruct (proj1 (hu x) hxu) as [hxa | hxold].
          -- now left.
          -- right. exact (proj2 (hc x) (or_introl hxold)).
        * subst x.
          right. exact (proj2 (hc y) (or_intror eq_refl)).
      + intros [hxa | hxc].
        * apply (proj2 (foam_adjoin_spec V M x u y)).
          left. exact (proj2 (hu x) (or_introl hxa)).
        * destruct (proj1 (hc x) hxc) as [hxold | hxy].
          -- apply (proj2 (foam_adjoin_spec V M x u y)).
             left. exact (proj2 (hu x) (or_intror hxold)).
          -- apply (proj2 (foam_adjoin_spec V M x u y)).
             now right.
  }
  exact (proj1 (HF_binUnionAt_spec V (foam_mem V M)
    (scons V b (scons V a tail)) 1 0) (hall b)).
Qed.

Lemma fofam_union_exists : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (a : V),
  exists u, forall x,
    foam_mem V M x u <->
      exists v, foam_mem V M v a /\ foam_mem V M x v.
Proof.
  intros V M a.
  pose (phi := HF_unionAt 0).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (fofam_finite_induction_schema V M phi tail) as hind.
  assert (hall : forall a,
      Sat V (foam_mem V M) (scons V a tail) phi).
  {
    apply (proj1 (HF_finite_induction_form_spec V (foam_mem V M)
      phi tail) hind).
    split.
    - intros z hzEmpty.
      apply (proj2 (HF_unionAt_spec V (foam_mem V M)
        (scons V z tail) 0)).
      exists (foam_empty V M).
      intro x.
      split.
      + intro hx. exfalso. exact (foam_empty_spec V M x hx).
      + intros [v [hvz _]].
        exfalso. exact (hzEmpty v hvz).
    - intros old y c hc hOld.
      destruct (proj1 (HF_unionAt_spec V (foam_mem V M)
        (scons V old tail) 0) hOld) as [u hu].
      destruct (fofam_binUnion_exists V M u y) as [w hw].
      apply (proj2 (HF_unionAt_spec V (foam_mem V M)
        (scons V c tail) 0)).
      exists w.
      intro x.
      split.
      + intro hxw.
        destruct (proj1 (hw x) hxw) as [hxu | hxy].
        * destruct (proj1 (hu x) hxu) as [v [hvold hxv]].
          exists v.
          split.
          -- exact (proj2 (hc v) (or_introl hvold)).
          -- exact hxv.
        * exists y.
          split.
          -- exact (proj2 (hc y) (or_intror eq_refl)).
          -- exact hxy.
      + intros [v [hvc hxv]].
        destruct (proj1 (hc v) hvc) as [hvold | hvy].
        * apply (proj2 (hw x)).
          left. exact (proj2 (hu x) (ex_intro _ v (conj hvold hxv))).
        * subst v.
          apply (proj2 (hw x)).
          now right.
  }
  exact (proj1 (HF_unionAt_spec V (foam_mem V M)
    (scons V a tail) 0) (hall a)).
Qed.

Lemma fofam_chainSubsetsMax_exists : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V),
  forall a s,
    (forall x, foam_mem V M x s -> foam_mem V M x a) ->
    ChainLike (foam_mem V M) s ->
    (exists x, foam_mem V M x s) ->
    exists p, foam_mem V M p s /\
      forall q, foam_mem V M q s -> ~ foam_mem V M p q.
Proof.
  intros V M.
  pose (phi := HF_chainSubsetsMaxAt 0).
  pose (tail := fun _ : nat => foam_empty V M).
  pose proof (fofam_finite_induction_schema V M phi tail) as hind.
  assert (hall : forall a,
      Sat V (foam_mem V M) (scons V a tail) phi).
  {
    apply (proj1 (HF_finite_induction_form_spec V (foam_mem V M)
      phi tail) hind).
    split.
    - intros z hzEmpty.
      apply (proj2 (HF_chainSubsetsMaxAt_spec V (foam_mem V M)
        (scons V z tail) 0)).
      intros s hsSub _hsChain [x hxs].
      exfalso. exact (hzEmpty x (hsSub x hxs)).
    - intros old y c hc hOld.
      pose proof (proj1 (HF_chainSubsetsMaxAt_spec V (foam_mem V M)
        (scons V old tail) 0) hOld) as oldP.
      apply (proj2 (HF_chainSubsetsMaxAt_spec V (foam_mem V M)
        (scons V c tail) 0)).
      intros s hsSub hsChain hsNonempty.
      destruct (fofam_sepBy_exists V M (fMem 0 1) (scons V s tail) old)
        as [t ht].
      assert (htSubOld : forall x,
          foam_mem V M x t -> foam_mem V M x old).
      {
        intros x hxt.
        exact (proj1 (proj1 (ht x) hxt)).
      }
      assert (htSubS : forall x,
          foam_mem V M x t -> foam_mem V M x s).
      {
        intros x hxt.
        exact (proj2 (proj1 (ht x) hxt)).
      }
      assert (htChain : ChainLike (foam_mem V M) t).
      {
        split.
        - intros x hxt.
          exact (proj1 hsChain x (htSubS x hxt)).
        - intros x hxt z hzt.
          exact (proj2 hsChain x (htSubS x hxt) z (htSubS z hzt)).
      }
      destruct (classic (exists x, foam_mem V M x t)) as [htne | htne].
      + destruct (oldP t htSubOld htChain htne) as [p [hpt hpMaxT]].
        assert (hps : foam_mem V M p s) by exact (htSubS p hpt).
        destruct (classic (foam_mem V M y s)) as [hys | hys].
        * destruct (proj2 hsChain p hps y hys) as [hpy | [hpy | hyp]].
          -- exists y.
             split; [exact hys |].
             intros q hqs hyq.
             destruct (proj1 (hc q) (hsSub q hqs)) as [hqold | hqy].
             ++ assert (hqt : foam_mem V M q t).
                {
                  apply (proj2 (ht q)).
                  split; [exact hqold | exact hqs].
                }
                assert (htransq : TransitiveObj (foam_mem V M) q)
                  by exact (proj1 hsChain q hqs).
                assert (hpq : foam_mem V M p q)
                  by exact (htransq y hyq p hpy).
                exact (hpMaxT q hqt hpq).
             ++ subst q.
                exact (foam_mem_irrefl V M y hyq).
          -- subst p.
             exists y.
             split; [exact hys |].
             intros q hqs hyq.
             destruct (proj1 (hc q) (hsSub q hqs)) as [hqold | hqy].
             ++ assert (hqt : foam_mem V M q t).
                {
                  apply (proj2 (ht q)).
                  split; [exact hqold | exact hqs].
                }
                exact (hpMaxT q hqt hyq).
             ++ subst q.
                exact (foam_mem_irrefl V M y hyq).
          -- exists p.
             split; [exact hps |].
             intros q hqs hpq.
             destruct (proj1 (hc q) (hsSub q hqs)) as [hqold | hqy].
             ++ assert (hqt : foam_mem V M q t).
                {
                  apply (proj2 (ht q)).
                  split; [exact hqold | exact hqs].
                }
                exact (hpMaxT q hqt hpq).
             ++ subst q.
                exact (foam_mem_asymm V M y p hyp hpq).
        * exists p.
          split; [exact hps |].
          intros q hqs hpq.
          destruct (proj1 (hc q) (hsSub q hqs)) as [hqold | hqy].
          -- assert (hqt : foam_mem V M q t).
             {
               apply (proj2 (ht q)).
               split; [exact hqold | exact hqs].
             }
             exact (hpMaxT q hqt hpq).
          -- subst q.
             exact (hys hqs).
      + destruct hsNonempty as [p hps].
        assert (hp_eq_y : p = y).
        {
          destruct (proj1 (hc p) (hsSub p hps)) as [hpold | hpy].
          - assert (hpt : foam_mem V M p t).
            {
              apply (proj2 (ht p)).
              split; [exact hpold | exact hps].
            }
            exfalso. exact (htne (ex_intro _ p hpt)).
          - exact hpy.
        }
        exists p.
        split; [exact hps |].
        intros q hqs hpq.
        assert (hq_eq_y : q = y).
        {
          destruct (proj1 (hc q) (hsSub q hqs)) as [hqold | hqy].
          - assert (hqt : foam_mem V M q t).
            {
              apply (proj2 (ht q)).
              split; [exact hqold | exact hqs].
            }
            exfalso. exact (htne (ex_intro _ q hqt)).
          - exact hqy.
        }
        subst p.
        subst q.
        exact (foam_mem_irrefl V M y hpq).
  }
  intros a s hsSub hsChain hsNonempty.
  exact (proj1 (HF_chainSubsetsMaxAt_spec V (foam_mem V M)
    (scons V a tail) 0) (hall a) s hsSub hsChain hsNonempty).
Qed.

Lemma fofam_OrdinalLike_empty_or_succ : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (a : V),
  OrdinalLike (foam_mem V M) a ->
  a = foam_empty V M \/
  exists p, foam_mem V M p a /\ a = foam_adjoin V M p p.
Proof.
  intros V M a ha.
  destruct (classic (exists x, foam_mem V M x a)) as [hne | hne].
  - assert (hChain : ChainLike (foam_mem V M) a).
    {
      split.
      - exact (proj1 (proj2 ha)).
      - exact (proj2 (proj2 ha)).
    }
    destruct (fofam_chainSubsetsMax_exists V M a a
      (fun _ hx => hx) hChain hne) as [p [hp hmax]].
    right.
    exists p.
    split; [exact hp |].
    exact (foam_OrdinalLike_eq_succ_of_mem_max V M a p ha hp hmax).
  - left.
    apply (foam_extensional V M).
    intro x.
    split.
    + intro hx. exfalso. exact (hne (ex_intro _ x hx)).
    + intro hx. exfalso. exact (foam_empty_spec V M x hx).
Qed.

Lemma fofam_succ_rec_total_of_ordinalLike : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (s m : V),
  OrdinalLike (foam_mem V M) m ->
  foam_succ_rec_total V M s m.
Proof.
  intros V M s m hm.
  apply (foam_succ_rec_total_of_ordinalLike_of_predecessor V M).
  - intros a ha.
    exact (fofam_OrdinalLike_empty_or_succ V M a ha).
  - exact hm.
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

Fixpoint succ_iter_obj (s n : nat) : nat :=
  match n with
  | 0 => s
  | S k => hf_adjoin (succ_iter_obj s k) (succ_iter_obj s k)
  end.

Lemma succ_iter_obj_ordinal_code : forall m n,
  succ_iter_obj (ordinal_code m) n = ordinal_code (m + n).
Proof.
  intros m n.
  induction n as [|n IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.

Fixpoint succ_rec_trace (s n : nat) : nat :=
  match n with
  | 0 =>
      hf_single_obj ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty s)
  | S k =>
      hf_adjoin
        (hf_kpair_obj ackermannHFModel
          (ordinal_code (S k)) (succ_iter_obj s (S k)))
        (succ_rec_trace s k)
  end.

Lemma succ_rec_trace_mem_iff : forall s p n,
  hf_mem p (succ_rec_trace s n) <->
    exists k, k <= n /\
      p = hf_kpair_obj ackermannHFModel
        (ordinal_code k) (succ_iter_obj s k).
Proof.
  intros s p n.
  induction n as [|n IH].
  - simpl.
    split.
    + intro hp.
      pose proof (proj1 (hf_single_spec ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty s) p) hp) as hp'.
      exists 0.
      split; [lia |].
      simpl. exact hp'.
    + intros [k [hk hp]].
      assert (k = 0) by lia.
      subst k.
      apply (proj2 (hf_single_spec ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty s) p)).
      simpl in hp. exact hp.
  - simpl.
    rewrite hf_mem_adjoin.
    rewrite IH.
    split.
    + intros [[k [hk hp]] | hp].
      * exists k. split; [lia | exact hp].
      * exists (S n). split; [lia | exact hp].
    + intros [k [hk hp]].
      destruct (Nat.eq_dec k (S n)) as [heq | hne].
      * right. subst k. exact hp.
      * left. exists k. split; [lia | exact hp].
Qed.

Lemma succ_rec_trace_pair_mem : forall s k n,
  k <= n ->
  hf_mem
    (hf_kpair_obj ackermannHFModel
      (ordinal_code k) (succ_iter_obj s k))
    (succ_rec_trace s n).
Proof.
  intros s k n hk.
  apply (proj2 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel
      (ordinal_code k) (succ_iter_obj s k)) n)).
  exists k. split; [exact hk | reflexivity].
Qed.

Lemma succ_rec_trace_functional : forall s n,
  hf_pair_functional ackermannHFModel (succ_rec_trace s n).
Proof.
  unfold hf_pair_functional.
  intros s n k y y' hky hky'.
  destruct (proj1 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel k y) n) hky)
    as [i [_hi hpair_i]].
  destruct (proj1 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel k y') n) hky')
    as [j [_hj hpair_j]].
  destruct (hf_kpair_injective ackermannHFModel
    k y (ordinal_code i) (succ_iter_obj s i) hpair_i)
    as [hk_i hy_i].
  destruct (hf_kpair_injective ackermannHFModel
    k y' (ordinal_code j) (succ_iter_obj s j) hpair_j)
    as [hk_j hy_j].
  assert (hij : i = j).
  {
    apply ordinal_code_injective.
    rewrite <- hk_i.
    rewrite <- hk_j.
    reflexivity.
  }
  rewrite hy_i, hy_j, hij.
  reflexivity.
Qed.

Lemma succ_rec_trace_keys_below_succ : forall s n,
  hf_pair_keys_below_succ ackermannHFModel
    (succ_rec_trace s n) (ordinal_code n).
Proof.
  unfold hf_pair_keys_below_succ.
  intros s n k y hky.
  destruct (proj1 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel k y) n) hky)
    as [i [hi hpair_i]].
  destruct (hf_kpair_injective ackermannHFModel
    k y (ordinal_code i) (succ_iter_obj s i) hpair_i)
    as [hk_i _hy_i].
  rewrite hk_i.
  destruct (Nat.eq_dec i n) as [heq | hne].
  - right. now subst i.
  - left. apply ordinal_code_mem_of_lt. lia.
Qed.

Lemma succ_rec_trace_total_below_succ : forall s n,
  hf_pair_total_below_succ ackermannHFModel
    (succ_rec_trace s n) (ordinal_code n).
Proof.
  unfold hf_pair_total_below_succ.
  intros s n k hk.
  destruct hk as [hmem | heq].
  - destruct (proj1 (hf_mem_ordinal_code_iff k n) hmem) as [i [hi hk_eq]].
    subst k.
    exists (succ_iter_obj s i).
    apply succ_rec_trace_pair_mem.
    lia.
  - subst k.
    exists (succ_iter_obj s n).
    apply succ_rec_trace_pair_mem.
    lia.
Qed.

Lemma succ_rec_trace_succ_step : forall s n,
  hf_pair_succ_step ackermannHFModel
    (succ_rec_trace s n) (ordinal_code n).
Proof.
  unfold hf_pair_succ_step.
  intros s n k t y hkm hkt hsy.
  destruct (proj1 (hf_mem_ordinal_code_iff k n) hkm) as [i [_hi hk_eq]].
  destruct (proj1 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel k t) n) hkt)
    as [j [_hj hpair_j]].
  destruct (hf_kpair_injective ackermannHFModel
    k t (ordinal_code j) (succ_iter_obj s j) hpair_j)
    as [hk_j ht_j].
  assert (hij : i = j).
  {
    apply ordinal_code_injective.
    rewrite <- hk_eq.
    rewrite <- hk_j.
    reflexivity.
  }
  assert (hsucck : hf_adjoin k k = ordinal_code (S i)).
  {
    rewrite hk_eq.
    reflexivity.
  }
  destruct (proj1 (succ_rec_trace_mem_iff s
    (hf_kpair_obj ackermannHFModel (hf_adjoin k k) y) n) hsy)
    as [l [_hl hpair_l]].
  destruct (hf_kpair_injective ackermannHFModel
    (hf_adjoin k k) y (ordinal_code l) (succ_iter_obj s l) hpair_l)
    as [hkey_l hy_l].
  assert (hil : S i = l).
  {
    apply ordinal_code_injective.
    rewrite <- hsucck.
    exact hkey_l.
  }
  rewrite hy_l.
  rewrite <- hil.
  rewrite ht_j.
  rewrite <- hij.
  simpl.
  reflexivity.
Qed.

Lemma succ_rec_trace_succ_rec_approx : forall s n,
  hf_succ_rec_approx ackermannHFModel
    s (succ_rec_trace s n) (ordinal_code n).
Proof.
  intros s n.
  unfold hf_succ_rec_approx.
  repeat split.
  - apply succ_rec_trace_functional.
  - apply succ_rec_trace_keys_below_succ.
  - change (hf_mem
      (hf_kpair_obj ackermannHFModel (ordinal_code 0) (succ_iter_obj s 0))
      (succ_rec_trace s n)).
    apply succ_rec_trace_pair_mem.
    lia.
  - apply succ_rec_trace_total_below_succ.
  - apply succ_rec_trace_succ_step.
Qed.

Lemma succ_rec_approx_value_of_le : forall s f n N y,
  hf_succ_rec_approx ackermannHFModel s f (ordinal_code N) ->
  n <= N ->
  hf_mem (hf_kpair_obj ackermannHFModel (ordinal_code n) y) f ->
  y = succ_iter_obj s n.
Proof.
  intros s f n.
  induction n as [|n IH]; intros N y hA hn hy.
  - destruct hA as [hfun [_hkeys [hbase [_htotal _hstep]]]].
    pose proof (hfun (ordinal_code 0) y s hy hbase) as hy_eq.
    simpl in hy_eq.
    exact hy_eq.
  - pose proof hA as hA'.
    destruct hA as [_hfun [_hkeys [_hbase [htotal hstep]]]].
    assert (hnlt : n < N) by lia.
    destruct (htotal (ordinal_code n)
      (or_introl (ordinal_code_mem_of_lt n N hnlt))) as [t ht].
    assert (hnle : n <= N) by lia.
    pose proof (IH N t hA' hnle ht) as htval.
    assert (hysucc :
        hf_mem
          (hf_kpair_obj ackermannHFModel
            (hf_adjoin (ordinal_code n) (ordinal_code n)) y) f).
    {
      change (hf_mem
        (hf_kpair_obj ackermannHFModel (ordinal_code (S n)) y) f).
      exact hy.
    }
    pose proof (hstep (ordinal_code n) t y
      (ordinal_code_mem_of_lt n N hnlt) ht hysucc) as hstepval.
    rewrite hstepval, htval.
    simpl.
    reflexivity.
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
