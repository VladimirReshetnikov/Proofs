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
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import ClassicalEpsilon ProofIrrelevance.
From SetTheory Require Import Fol Calculus Completeness.
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

Ltac solve_free_vars :=
  simpl in *;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  | H : False |- _ => contradiction
  end;
  lia.

Lemma HF_emptyAt_free : forall i a,
  Free i (HF_emptyAt a) -> i = a.
Proof.
  intros i a h.
  unfold HF_emptyAt in h.
  solve_free_vars.
Qed.

Lemma HF_adjoinAt_free : forall i c a b,
  Free i (HF_adjoinAt c a b) -> i = c \/ i = a \/ i = b.
Proof.
  intros i c a b h.
  unfold HF_adjoinAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_succAt_free : forall i s a,
  Free i (HF_succAt s a) -> i = s \/ i = a.
Proof.
  intros i s a h.
  unfold HF_succAt, HF_adjoinAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_singleAt_free : forall i a b,
  Free i (HF_singleAt a b) -> i = a \/ i = b.
Proof.
  intros i a b h.
  unfold HF_singleAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_upairAt_free : forall i a b c,
  Free i (HF_upairAt a b c) -> i = a \/ i = b \/ i = c.
Proof.
  intros i a b c h.
  unfold HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_kpairAt_free : forall i p a b,
  Free i (HF_kpairAt p a b) -> i = p \/ i = a \/ i = b.
Proof.
  intros i p a b h.
  unfold HF_kpairAt, HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairMemAt_free : forall i a b r,
  Free i (HF_pairMemAt a b r) -> i = a \/ i = b \/ i = r.
Proof.
  intros i a b r h.
  unfold HF_pairMemAt, HF_kpairAt, HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairFunctionalAt_free : forall i f,
  Free i (HF_pairFunctionalAt f) -> i = f.
Proof.
  intros i f h.
  unfold HF_pairFunctionalAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairKeysBelowSuccAt_free : forall i f m,
  Free i (HF_pairKeysBelowSuccAt f m) -> i = f \/ i = m.
Proof.
  intros i f m h.
  unfold HF_pairKeysBelowSuccAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairTotalBelowSuccAt_free : forall i f m,
  Free i (HF_pairTotalBelowSuccAt f m) -> i = f \/ i = m.
Proof.
  intros i f m h.
  unfold HF_pairTotalBelowSuccAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairSuccStepAt_free : forall i f m,
  Free i (HF_pairSuccStepAt f m) -> i = f \/ i = m.
Proof.
  intros i f m h.
  unfold HF_pairSuccStepAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, HF_succAt, HF_adjoinAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairBaseAt_free : forall i f s,
  Free i (HF_pairBaseAt f s) -> i = f \/ i = s.
Proof.
  intros i f s h.
  unfold HF_pairBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_pairZeroBaseAt_free : forall i f,
  Free i (HF_pairZeroBaseAt f) -> i = f.
Proof.
  intros i f h.
  unfold HF_pairZeroBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff in h.
  solve_free_vars.
Qed.

Lemma HF_succRecApproxAt_free : forall i f s m,
  Free i (HF_succRecApproxAt f s m) -> i = f \/ i = s \/ i = m.
Proof.
  intros i f s m h.
  unfold HF_succRecApproxAt in h.
  simpl in h.
  destruct h as [h | [h | [h | [h | h]]]].
  - pose proof (HF_pairFunctionalAt_free i f h). lia.
  - destruct (HF_pairKeysBelowSuccAt_free i f m h) as [hi | hi]; lia.
  - destruct (HF_pairBaseAt_free i f s h) as [hi | hi]; lia.
  - destruct (HF_pairTotalBelowSuccAt_free i f m h) as [hi | hi]; lia.
  - destruct (HF_pairSuccStepAt_free i f m h) as [hi | hi]; lia.
Qed.

Lemma HF_subsetAt_free : forall i a b,
  Free i (HF_subsetAt a b) -> i = a \/ i = b.
Proof.
  intros i a b h.
  unfold HF_subsetAt in h.
  solve_free_vars.
Qed.

Lemma HF_transitiveAt_free : forall i a,
  Free i (HF_transitiveAt a) -> i = a.
Proof.
  intros i a h.
  unfold HF_transitiveAt in h.
  solve_free_vars.
Qed.

Lemma HF_memTotalOnAt_free : forall i a,
  Free i (HF_memTotalOnAt a) -> i = a.
Proof.
  intros i a h.
  unfold HF_memTotalOnAt in h.
  solve_free_vars.
Qed.

Lemma HF_ordinalLikeAt_free : forall i a,
  Free i (HF_ordinalLikeAt a) -> i = a.
Proof.
  intros i a h.
  unfold HF_ordinalLikeAt, HF_transitiveAt, HF_memTotalOnAt in h.
  solve_free_vars.
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

Definition foam_mul_step (V : Type)
    (M : FirstOrderAdjunctionModel V) (f a m : V) : Prop :=
  forall k t y,
    foam_mem V M k m ->
    foam_mem V M (foam_kpair_obj V M k t) f ->
    foam_mem V M (foam_kpair_obj V M (foam_adjoin V M k k) y) f ->
    exists g,
      foam_succ_rec_approx V M t g a /\
        foam_mem V M (foam_kpair_obj V M a y) g.

Definition foam_mul_rec_approx (V : Type)
    (M : FirstOrderAdjunctionModel V) (a f m : V) : Prop :=
  foam_pair_functional V M f /\
    foam_pair_keys_below_succ V M f m /\
      foam_mem V M
        (foam_kpair_obj V M (foam_empty V M) (foam_empty V M)) f /\
        foam_pair_total_below_succ V M f m /\
          foam_mul_step V M f a m.

Definition foam_mul_rec_total (V : Type)
    (M : FirstOrderAdjunctionModel V) (a m : V) : Prop :=
  exists f z,
    foam_mul_rec_approx V M a f m /\
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

Definition foam_mul_rec_graph_succ (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m y : V) : V :=
  foam_adjoin V M f
    (foam_kpair_obj V M (foam_adjoin V M m m) y).

Lemma foam_mul_rec_graph_succ_old : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m y p : V),
  foam_mem V M p f ->
  foam_mem V M p (foam_mul_rec_graph_succ V M f m y).
Proof.
  intros V M f m y p hp.
  apply (proj2 (foam_adjoin_spec V M p f
    (foam_kpair_obj V M (foam_adjoin V M m m) y))).
  now left.
Qed.

Lemma foam_mul_rec_graph_succ_new : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (f m y : V),
  foam_mem V M (foam_kpair_obj V M (foam_adjoin V M m m) y)
    (foam_mul_rec_graph_succ V M f m y).
Proof.
  intros V M f m y.
  apply (proj2 (foam_adjoin_spec V M
    (foam_kpair_obj V M (foam_adjoin V M m m) y)
    f
    (foam_kpair_obj V M (foam_adjoin V M m m) y))).
  now right.
Qed.

Lemma foam_mul_rec_graph_succ_mulRecApprox : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a f m z y : V),
  OrdinalLike (foam_mem V M) m ->
  foam_mul_rec_approx V M a f m ->
  foam_mem V M (foam_kpair_obj V M m z) f ->
  (exists g,
    foam_succ_rec_approx V M z g a /\
      foam_mem V M (foam_kpair_obj V M a y) g) ->
  foam_mul_rec_approx V M a
    (foam_mul_rec_graph_succ V M f m y)
    (foam_adjoin V M m m).
Proof.
  intros V M a f m z y hm hf hz hadd.
  destruct hf as [hfun [hkeys [hbase [htotal hstep]]]].
  set (sm := foam_adjoin V M m m).
  set (newPair := foam_kpair_obj V M sm y).
  set (g := foam_mul_rec_graph_succ V M f m y).
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
    unfold g, newPair, sm, foam_mul_rec_graph_succ.
    apply foam_adjoin_spec.
  }
  assert (old_key_ne_succ : forall k out,
      foam_mem V M (foam_kpair_obj V M k out) f -> k <> sm).
  {
    intros k out hOld hk.
    pose proof (hkeys k out hOld) as hkBound.
    rewrite hk in hkBound.
    destruct hkBound as [hmem | heq].
    - exact (hsm_not_mem hmem).
    - exact (hsm_ne_m heq).
  }
  assert (pair_old_of_mem_key : forall k out,
      foam_mem V M k m ->
      foam_mem V M (foam_kpair_obj V M k out) g ->
      foam_mem V M (foam_kpair_obj V M k out) f).
  {
    intros k out hkm hkg.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k out)) hkg)
      as [hOld | hNew].
    - exact hOld.
    - pose proof (proj1 (foam_kpair_injective V M k out sm y hNew)) as hk.
      rewrite hk in hkm.
      exfalso. exact (hsm_not_mem hkm).
  }
  unfold foam_mul_rec_approx.
  repeat split.
  - intros k u v hku hkv.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k u)) hku)
      as [hOld | hNew].
    + destruct (proj1 (hmem_g (foam_kpair_obj V M k v)) hkv)
        as [hOld' | hNew'].
      * exact (hfun k u v hOld hOld').
      * pose proof (proj1 (foam_kpair_injective V M k v sm y hNew')) as hk.
        exfalso. exact (old_key_ne_succ k u hOld hk).
    + destruct (proj1 (hmem_g (foam_kpair_obj V M k v)) hkv)
        as [hOld' | hNew'].
      * pose proof (proj1 (foam_kpair_injective V M k u sm y hNew)) as hk.
        exfalso. exact (old_key_ne_succ k v hOld' hk).
      * pose proof (proj2 (foam_kpair_injective V M k u sm y hNew)) as hu.
        pose proof (proj2 (foam_kpair_injective V M k v sm y hNew')) as hv.
        rewrite hu, hv. reflexivity.
  - intros k out hku.
    destruct (proj1 (hmem_g (foam_kpair_obj V M k out)) hku)
      as [hOld | hNew].
    + destruct (hkeys k out hOld) as [hkm | hkm].
      * left. apply (proj2 (foam_adjoin_spec V M k m m)). now left.
      * left. apply (proj2 (foam_adjoin_spec V M k m m)). now right.
    + right. exact (proj1 (foam_kpair_injective V M k out sm y hNew)).
  - exact (foam_mul_rec_graph_succ_old V M f m y
      (foam_kpair_obj V M (foam_empty V M) (foam_empty V M)) hbase).
  - intros k hk.
    destruct hk as [hksm | hksm].
    + destruct (proj1 (foam_adjoin_spec V M k m m) hksm)
        as [hkm | hkm].
      * destruct (htotal k (or_introl hkm)) as [out hout].
        exists out.
        exact (foam_mul_rec_graph_succ_old V M f m y
          (foam_kpair_obj V M k out) hout).
      * destruct (htotal k (or_intror hkm)) as [out hout].
        exists out.
        exact (foam_mul_rec_graph_succ_old V M f m y
          (foam_kpair_obj V M k out) hout).
    + subst k.
      exists y.
      unfold sm.
      apply foam_mul_rec_graph_succ_new.
  - intros k t out hksm hkt hsky.
    destruct (proj1 (foam_adjoin_spec V M k m m) hksm)
      as [hkm | hkm].
    + assert (hktOld : foam_mem V M (foam_kpair_obj V M k t) f).
      {
        exact (pair_old_of_mem_key k t hkm hkt).
      }
      assert (hskyOld :
          foam_mem V M (foam_kpair_obj V M (foam_adjoin V M k k) out) f).
      {
        destruct (proj1 (hmem_g
          (foam_kpair_obj V M (foam_adjoin V M k k) out)) hsky)
          as [hOld | hNew].
        - exact hOld.
        - pose proof (proj1 (foam_kpair_injective V M
            (foam_adjoin V M k k) out sm y hNew)) as hsk.
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
      exact (hstep k t out hkm hktOld hskyOld).
    + subst k.
      assert (hktOld : foam_mem V M (foam_kpair_obj V M m t) f).
      {
        destruct (proj1 (hmem_g (foam_kpair_obj V M m t)) hkt)
          as [hOld | hNew].
        - exact hOld.
        - pose proof (proj1 (foam_kpair_injective V M m t sm y hNew))
            as hm_eq_sm.
          exfalso. exact (hsm_ne_m (eq_sym hm_eq_sm)).
      }
      pose proof (hfun m t z hktOld hz) as ht.
      destruct (proj1 (hmem_g (foam_kpair_obj V M sm out)) hsky)
        as [hOld | hNew].
      * exfalso. exact (old_key_ne_succ sm out hOld eq_refl).
      * pose proof (proj2 (foam_kpair_injective V M sm out sm y hNew)) as hout.
        rewrite ht, hout.
        exact hadd.
Qed.

Lemma foam_zero_mul_rec_graph_mulRecApprox : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  foam_mul_rec_approx V M a
    (foam_zero_succ_rec_graph V M (foam_empty V M))
    (foam_empty V M).
Proof.
  intros V M a.
  pose proof (foam_zero_succ_rec_graph_succRecApprox V M
    (foam_empty V M)) as hf.
  destruct hf as [hfun [hkeys [hbase [htotal _hstep]]]].
  unfold foam_mul_rec_approx.
  repeat split.
  - exact hfun.
  - exact hkeys.
  - exact hbase.
  - exact htotal.
  - intros k _t _y hkm _ _.
    exfalso. exact (foam_empty_spec V M k hkm).
Qed.

Lemma foam_mul_rec_total_empty : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a : V),
  foam_mul_rec_total V M a (foam_empty V M).
Proof.
  intros V M a.
  exists (foam_zero_succ_rec_graph V M (foam_empty V M)),
    (foam_empty V M).
  split.
  - apply foam_zero_mul_rec_graph_mulRecApprox.
  - apply foam_zero_succ_rec_graph_base.
Qed.

Lemma foam_mul_rec_total_succ_of_addTotal : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (a m : V),
  OrdinalLike (foam_mem V M) m ->
  (forall s, foam_succ_rec_total V M s a) ->
  foam_mul_rec_total V M a m ->
  foam_mul_rec_total V M a (foam_adjoin V M m m).
Proof.
  intros V M a m hm hAddTotal [f [z [hf hz]]].
  destruct (hAddTotal z) as [g [y [hg hy]]].
  exists (foam_mul_rec_graph_succ V M f m y), y.
  split.
  - apply (foam_mul_rec_graph_succ_mulRecApprox V M a f m z y
      hm hf hz).
    exists g. split; assumption.
  - apply foam_mul_rec_graph_succ_new.
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

Fixpoint mul_rec_trace (m n : nat) : nat :=
  match n with
  | 0 =>
      hf_single_obj ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty hf_empty)
  | S k =>
      hf_adjoin
        (hf_kpair_obj ackermannHFModel
          (ordinal_code (S k)) (ordinal_code (m * S k)))
        (mul_rec_trace m k)
  end.

Lemma mul_rec_trace_mem_iff : forall m p n,
  hf_mem p (mul_rec_trace m n) <->
    exists k, k <= n /\
      p = hf_kpair_obj ackermannHFModel
        (ordinal_code k) (ordinal_code (m * k)).
Proof.
  intros m p n.
  induction n as [|n IH].
  - simpl.
    split.
    + intro hp.
      pose proof (proj1 (hf_single_spec ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty hf_empty) p) hp) as hp'.
      exists 0.
      split; [lia |].
      rewrite Nat.mul_0_r.
      simpl. exact hp'.
    + intros [k [hk hp]].
      assert (k = 0) by lia.
      subst k.
      apply (proj2 (hf_single_spec ackermannHFModel
        (hf_kpair_obj ackermannHFModel hf_empty hf_empty) p)).
      rewrite Nat.mul_0_r in hp.
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

Lemma mul_rec_trace_pair_mem : forall m k n,
  k <= n ->
  hf_mem
    (hf_kpair_obj ackermannHFModel
      (ordinal_code k) (ordinal_code (m * k)))
    (mul_rec_trace m n).
Proof.
  intros m k n hk.
  apply (proj2 (mul_rec_trace_mem_iff m
    (hf_kpair_obj ackermannHFModel
      (ordinal_code k) (ordinal_code (m * k))) n)).
  exists k. split; [exact hk | reflexivity].
Qed.

Lemma mul_rec_trace_functional : forall m n,
  hf_pair_functional ackermannHFModel (mul_rec_trace m n).
Proof.
  unfold hf_pair_functional.
  intros m n k y y' hky hky'.
  destruct (proj1 (mul_rec_trace_mem_iff m
    (hf_kpair_obj ackermannHFModel k y) n) hky)
    as [i [_hi hpair_i]].
  destruct (proj1 (mul_rec_trace_mem_iff m
    (hf_kpair_obj ackermannHFModel k y') n) hky')
    as [j [_hj hpair_j]].
  destruct (hf_kpair_injective ackermannHFModel
    k y (ordinal_code i) (ordinal_code (m * i)) hpair_i)
    as [hk_i hy_i].
  destruct (hf_kpair_injective ackermannHFModel
    k y' (ordinal_code j) (ordinal_code (m * j)) hpair_j)
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

Lemma mul_rec_trace_keys_below_succ : forall m n,
  hf_pair_keys_below_succ ackermannHFModel
    (mul_rec_trace m n) (ordinal_code n).
Proof.
  unfold hf_pair_keys_below_succ.
  intros m n k y hky.
  destruct (proj1 (mul_rec_trace_mem_iff m
    (hf_kpair_obj ackermannHFModel k y) n) hky)
    as [i [hi hpair_i]].
  destruct (hf_kpair_injective ackermannHFModel
    k y (ordinal_code i) (ordinal_code (m * i)) hpair_i)
    as [hk_i _hy_i].
  rewrite hk_i.
  destruct (Nat.eq_dec i n) as [heq | hne].
  - right. now subst i.
  - left. apply ordinal_code_mem_of_lt. lia.
Qed.

Lemma mul_rec_trace_total_below_succ : forall m n,
  hf_pair_total_below_succ ackermannHFModel
    (mul_rec_trace m n) (ordinal_code n).
Proof.
  unfold hf_pair_total_below_succ.
  intros m n k hk.
  destruct hk as [hmem | heq].
  - destruct (proj1 (hf_mem_ordinal_code_iff k n) hmem) as [i [hi hk_eq]].
    subst k.
    exists (ordinal_code (m * i)).
    apply mul_rec_trace_pair_mem.
    lia.
  - subst k.
    exists (ordinal_code (m * n)).
    apply mul_rec_trace_pair_mem.
    lia.
Qed.

Definition domainForm : form := HF_ordinalLikeAt 0.

Definition zeroGraph : form := HF_emptyAt 0.

Definition succGraph : form := HF_succAt 0 1.

Definition addGraphAt (out left right : nat) : form :=
  fEx (fAnd (HF_succRecApproxAt 0 (S left) (S right))
    (HF_pairMemAt (S right) (S out) 0)).

Definition addGraph : form := addGraphAt 0 1 2.

Lemma OrdinalLike_of_hf_ordinal_like : forall a,
  hf_ordinal_like a -> OrdinalLike hf_mem a.
Proof.
  unfold hf_ordinal_like, OrdinalLike,
    hf_transitive_obj, TransitiveObj,
    hf_mem_total_on, MemTotalOn.
  tauto.
Qed.

Lemma hf_ordinal_like_of_OrdinalLike : forall a,
  OrdinalLike hf_mem a -> hf_ordinal_like a.
Proof.
  unfold hf_ordinal_like, OrdinalLike,
    hf_transitive_obj, TransitiveObj,
    hf_mem_total_on, MemTotalOn.
  tauto.
Qed.

Lemma HF_ordinalLikeAt_of_ordinal_code : forall (e : nat -> nat) i n,
  e i = ordinal_code n ->
  Sat nat hf_mem e (HF_ordinalLikeAt i).
Proof.
  intros e i n h.
  apply (proj2 (HF_ordinalLikeAt_spec nat hf_mem e i)).
  rewrite h.
  apply OrdinalLike_of_hf_ordinal_like.
  apply ordinal_code_ordinal_like.
Qed.

Lemma HF_ordinalLikeAt_exact : forall (e : nat -> nat) i,
  Sat nat hf_mem e (HF_ordinalLikeAt i) <-> is_ordinal_code (e i).
Proof.
  intros e i.
  split.
  - intro h.
    apply hf_ordinal_like_is_ordinal_code.
    apply hf_ordinal_like_of_OrdinalLike.
    exact (proj1 (HF_ordinalLikeAt_spec nat hf_mem e i) h).
  - intros [n hn].
    apply (HF_ordinalLikeAt_of_ordinal_code e i n).
    symmetry. exact hn.
Qed.

Lemma domain_ordinal_code : forall n e,
  Sat nat hf_mem (scons nat (ordinal_code n) e) domainForm.
Proof.
  intros n e.
  unfold domainForm.
  apply (HF_ordinalLikeAt_of_ordinal_code
    (scons nat (ordinal_code n) e) 0 n).
  reflexivity.
Qed.

Lemma domain_exact : forall e,
  Sat nat hf_mem e domainForm <-> is_ordinal_code (e 0).
Proof.
  intro e.
  unfold domainForm.
  apply HF_ordinalLikeAt_exact.
Qed.

Lemma zeroGraph_ordinal_code : forall e,
  Sat nat hf_mem (scons nat (ordinal_code 0) e) zeroGraph.
Proof.
  intro e.
  unfold zeroGraph.
  apply (proj2 (HF_emptyAt_empty ackermannHFModel
    (scons nat (ordinal_code 0) e) 0)).
  reflexivity.
Qed.

Lemma zeroGraph_exact_on_ordinal_code : forall n e,
  Sat nat hf_mem (scons nat (ordinal_code n) e) zeroGraph <-> n = 0.
Proof.
  intros n e.
  split.
  - intro h.
    pose proof (proj1 (HF_emptyAt_empty ackermannHFModel
      (scons nat (ordinal_code n) e) 0) h) as hz.
    apply ordinal_code_injective.
    rewrite ordinal_code_zero.
    exact hz.
  - intro h.
    subst n.
    apply zeroGraph_ordinal_code.
Qed.

Lemma succGraph_ordinal_code : forall n e,
  Sat nat hf_mem
    (scons nat (ordinal_code (S n)) (scons nat (ordinal_code n) e))
    succGraph.
Proof.
  intros n e.
  unfold succGraph.
  apply (proj2 (HF_succAt_spec ackermannHFModel
    (scons nat (ordinal_code (S n)) (scons nat (ordinal_code n) e)) 0 1)).
  reflexivity.
Qed.

Lemma succGraph_exact_on_ordinal_codes : forall m n e,
  Sat nat hf_mem
    (scons nat (ordinal_code m) (scons nat (ordinal_code n) e))
    succGraph <-> m = S n.
Proof.
  intros m n e.
  split.
  - intro h.
    pose proof (proj1 (HF_succAt_spec ackermannHFModel
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)) 0 1) h)
      as hs.
    apply ordinal_code_injective.
    rewrite ordinal_code_succ.
    exact hs.
  - intro h.
    subst m.
    apply succGraph_ordinal_code.
Qed.

Lemma addGraphAt_ordinal_code : forall out left right m n e,
  e out = ordinal_code (m + n) ->
  e left = ordinal_code m ->
  e right = ordinal_code n ->
  Sat nat hf_mem e (addGraphAt out left right).
Proof.
  intros out left right m n e hout hleft hright.
  unfold addGraphAt.
  pose (f := succ_rec_trace (ordinal_code m) n).
  exists f.
  split.
  - apply (proj2 (HF_succRecApproxAt_spec ackermannHFModel
      (scons nat f e) 0 (S left) (S right))).
    change (hf_succ_rec_approx ackermannHFModel (e left) f (e right)).
    rewrite hleft, hright.
    exact (succ_rec_trace_succ_rec_approx (ordinal_code m) n).
  - apply (proj2 (HF_pairMemAt_spec ackermannHFModel
      (scons nat f e) (S right) (S out) 0)).
    change (hf_mem (hf_kpair_obj ackermannHFModel (e right) (e out)) f).
    rewrite hout, hright.
    unfold f.
    pose proof (succ_rec_trace_pair_mem (ordinal_code m) n n) as hp.
    assert (hnn : n <= n) by lia.
    specialize (hp hnn).
    rewrite succ_iter_obj_ordinal_code in hp.
    exact hp.
Qed.

Lemma addGraph_ordinal_code : forall m n e,
  Sat nat hf_mem
    (scons nat (ordinal_code (m + n))
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)))
    addGraph.
Proof.
  intros m n e.
  unfold addGraph.
  apply (addGraphAt_ordinal_code 0 1 2 m n
    (scons nat (ordinal_code (m + n))
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e))));
    reflexivity.
Qed.

Lemma addGraphAt_value_of_ordinal_inputs : forall out left right m n e,
  e left = ordinal_code m ->
  e right = ordinal_code n ->
  Sat nat hf_mem e (addGraphAt out left right) ->
  e out = ordinal_code (m + n).
Proof.
  intros out left right m n e hleft hright h.
  unfold addGraphAt in h.
  destruct h as [f [hf hpair]].
  pose proof (proj1 (HF_succRecApproxAt_spec ackermannHFModel
    (scons nat f e) 0 (S left) (S right)) hf) as hf'.
  pose proof (proj1 (HF_pairMemAt_spec ackermannHFModel
    (scons nat f e) (S right) (S out) 0) hpair) as hpair'.
  change (hf_succ_rec_approx ackermannHFModel (e left) f (e right)) in hf'.
  change (hf_mem (hf_kpair_obj ackermannHFModel (e right) (e out)) f)
    in hpair'.
  rewrite hleft, hright in hf'.
  rewrite hright in hpair'.
  assert (hnn : n <= n) by lia.
  pose proof (succ_rec_approx_value_of_le
    (ordinal_code m) f n n (e out) hf' hnn hpair') as hval.
  rewrite hval.
  apply succ_iter_obj_ordinal_code.
Qed.

Lemma addGraphAt_exact_on_ordinal_codes : forall out left right r m n e,
  e out = ordinal_code r ->
  e left = ordinal_code m ->
  e right = ordinal_code n ->
  (Sat nat hf_mem e (addGraphAt out left right) <-> r = m + n).
Proof.
  intros out left right r m n e hout hleft hright.
  split.
  - intro h.
    pose proof (addGraphAt_value_of_ordinal_inputs
      out left right m n e hleft hright h) as hval.
    apply ordinal_code_injective.
    rewrite <- hout.
    exact hval.
  - intro h.
    subst r.
    apply (addGraphAt_ordinal_code out left right m n e); assumption.
Qed.

Lemma addGraph_exact_on_ordinal_codes : forall r m n e,
  Sat nat hf_mem
    (scons nat (ordinal_code r)
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)))
    addGraph <-> r = m + n.
Proof.
  intros r m n e.
  unfold addGraph.
  apply (addGraphAt_exact_on_ordinal_codes 0 1 2 r m n
    (scons nat (ordinal_code r)
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e))));
    reflexivity.
Qed.

Definition mulStepAt (f a m : nat) : form :=
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
              (addGraphAt 1 2 (S (S (S (S a)))))))))))).

Definition mulRecApproxAt (f a m : nat) : form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairZeroBaseAt f)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (mulStepAt f a m)))).

Definition mulGraphAt (out left right : nat) : form :=
  fEx (fAnd (mulRecApproxAt 0 (S left) (S right))
    (HF_pairMemAt (S right) (S out) 0)).

Definition mulGraph : form := mulGraphAt 0 1 2.

Definition mulRecTotalAt (a m : nat) : form :=
  fEx (fEx (fAnd
    (mulRecApproxAt 1 (S (S a)) (S (S m)))
    (HF_pairMemAt (S (S m)) 0 1))).

Definition mulRecTotalOnOrdinalAt (a m : nat) : form :=
  fImp (HF_ordinalLikeAt m) (mulRecTotalAt a m).

Lemma foam_mulStepAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f a m,
  Sat V (foam_mem V M) e (mulStepAt f a m) <->
    foam_mul_step V M (e f) (e a) (e m).
Proof.
  intros V M e f a m.
  split.
  - intros h k t y hkm hkt hsky.
    simpl in h.
    pose (sk := foam_adjoin V M k k).
    pose (Ekty := scons V y (scons V t (scons V k e))).
    pose (Eskty := scons V sk Ekty).
    assert (hktSat : Sat V (foam_mem V M) Ekty
        (HF_pairMemAt 2 1 (S (S (S f))))).
    {
      apply (proj2 (foam_HF_pairMemAt_spec V M Ekty
        2 1 (S (S (S f))))).
      change (foam_mem V M (foam_kpair_obj V M k t) (e f)).
      exact hkt.
    }
    assert (hskSat : Sat V (foam_mem V M) Eskty (HF_succAt 0 3)).
    {
      apply (proj2 (foam_HF_succAt_spec V M Eskty 0 3)).
      change (sk = foam_adjoin V M k k).
      unfold sk. reflexivity.
    }
    assert (hskySat : Sat V (foam_mem V M) Eskty
        (HF_pairMemAt 0 1 (S (S (S (S f)))))).
    {
      apply (proj2 (foam_HF_pairMemAt_spec V M Eskty
        0 1 (S (S (S (S f)))))).
      change (foam_mem V M (foam_kpair_obj V M sk y) (e f)).
      unfold sk.
      exact hsky.
    }
    destruct (h k t y hkm hktSat sk hskSat hskySat)
      as [g [hg hy]].
    pose proof (proj1 (foam_HF_succRecApproxAt_spec V M
      (scons V g Eskty) 0 3 (S (S (S (S (S a)))))) hg) as hg'.
    pose proof (proj1 (foam_HF_pairMemAt_spec V M
      (scons V g Eskty) (S (S (S (S (S a))))) 2 0) hy) as hy'.
    exists g.
    split.
    + change (foam_succ_rec_approx V M t g (e a)) in hg'.
      exact hg'.
    + change (foam_mem V M (foam_kpair_obj V M (e a) y) g) in hy'.
      exact hy'.
  - intros h.
    simpl.
    intros k t y hkm hkt sk hsk hsky.
    pose proof (proj1 (foam_HF_succAt_spec V M
      (scons V sk (scons V y (scons V t (scons V k e)))) 0 3) hsk)
      as hsk'.
    assert (hkt' : foam_mem V M (foam_kpair_obj V M k t) (e f)).
    {
      exact (proj1 (foam_HF_pairMemAt_spec V M
        (scons V y (scons V t (scons V k e))) 2 1 (S (S (S f)))) hkt).
    }
    assert (hsky' : foam_mem V M
        (foam_kpair_obj V M (foam_adjoin V M k k) y) (e f)).
    {
      pose proof (proj1 (foam_HF_pairMemAt_spec V M
        (scons V sk (scons V y (scons V t (scons V k e))))
        0 1 (S (S (S (S f))))) hsky) as hp.
      rewrite hsk' in hp.
      exact hp.
    }
    destruct (h k t y hkm hkt' hsky') as [g [hg hy]].
    exists g.
    split.
    + apply (proj2 (foam_HF_succRecApproxAt_spec V M
        (scons V g (scons V sk (scons V y (scons V t (scons V k e)))))
        0 3 (S (S (S (S (S a))))))).
      change (foam_succ_rec_approx V M t g (e a)).
      exact hg.
    + apply (proj2 (foam_HF_pairMemAt_spec V M
        (scons V g (scons V sk (scons V y (scons V t (scons V k e)))))
        (S (S (S (S (S a))))) 2 0)).
      change (foam_mem V M (foam_kpair_obj V M (e a) y) g).
      exact hy.
Qed.

Lemma foam_mulRecApproxAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) f a m,
  Sat V (foam_mem V M) e (mulRecApproxAt f a m) <->
    foam_mul_rec_approx V M (e a) (e f) (e m).
Proof.
  intros V M e f a m.
  split.
  - intro h.
    unfold mulRecApproxAt in h.
    simpl in h.
    destruct h as [hfun [hkeys [hbase [htotal hstep]]]].
    unfold foam_mul_rec_approx.
    repeat split.
    + exact (proj1 (foam_HF_pairFunctionalAt_spec V M e f) hfun).
    + exact (proj1 (foam_HF_pairKeysBelowSuccAt_spec V M e f m) hkeys).
    + exact (proj1 (foam_HF_pairZeroBaseAt_spec V M e f) hbase).
    + exact (proj1 (foam_HF_pairTotalBelowSuccAt_spec V M e f m) htotal).
    + exact (proj1 (foam_mulStepAt_spec V M e f a m) hstep).
  - intro h.
    unfold foam_mul_rec_approx in h.
    destruct h as [hfun [hkeys [hbase [htotal hstep]]]].
    unfold mulRecApproxAt.
    simpl.
    repeat split.
    + exact (proj2 (foam_HF_pairFunctionalAt_spec V M e f) hfun).
    + exact (proj2 (foam_HF_pairKeysBelowSuccAt_spec V M e f m) hkeys).
    + exact (proj2 (foam_HF_pairZeroBaseAt_spec V M e f) hbase).
    + exact (proj2 (foam_HF_pairTotalBelowSuccAt_spec V M e f m) htotal).
    + exact (proj2 (foam_mulStepAt_spec V M e f a m) hstep).
Qed.

Lemma foam_mulRecTotalAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) a m,
  Sat V (foam_mem V M) e (mulRecTotalAt a m) <->
    foam_mul_rec_total V M (e a) (e m).
Proof.
  intros V M e a m.
  split.
  - intros [f [z [hf hz]]].
    exists f, z.
    split.
    + exact (proj1 (foam_mulRecApproxAt_spec V M
        (scons V z (scons V f e)) 1 (S (S a)) (S (S m))) hf).
    + exact (proj1 (foam_HF_pairMemAt_spec V M
        (scons V z (scons V f e)) (S (S m)) 0 1) hz).
  - intros [f [z [hf hz]]].
    exists f, z.
    split.
    + exact (proj2 (foam_mulRecApproxAt_spec V M
        (scons V z (scons V f e)) 1 (S (S a)) (S (S m))) hf).
    + exact (proj2 (foam_HF_pairMemAt_spec V M
        (scons V z (scons V f e)) (S (S m)) 0 1) hz).
Qed.

Lemma foam_mulRecTotalOnOrdinalAt_spec : forall (V : Type)
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) a m,
  Sat V (foam_mem V M) e (mulRecTotalOnOrdinalAt a m) <->
    (OrdinalLike (foam_mem V M) (e m) ->
      foam_mul_rec_total V M (e a) (e m)).
Proof.
  intros V M e a m.
  unfold mulRecTotalOnOrdinalAt.
  split.
  - intros h hm.
    apply (proj1 (foam_mulRecTotalAt_spec V M e a m)).
    apply h.
    apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M) e m)).
    exact hm.
  - intros h hmSat.
    apply (proj2 (foam_mulRecTotalAt_spec V M e a m)).
    apply h.
    apply (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M) e m)).
    exact hmSat.
Qed.

Lemma foam_mul_rec_total_of_ordinalLike_of_predecessor : forall (V : Type)
    (M : FirstOrderAdjunctionModel V),
  (forall a, OrdinalLike (foam_mem V M) a ->
    a = foam_empty V M \/
    exists p, foam_mem V M p a /\ a = foam_adjoin V M p p) ->
  (forall s m, OrdinalLike (foam_mem V M) m ->
    foam_succ_rec_total V M s m) ->
  forall a m,
    OrdinalLike (foam_mem V M) a ->
    OrdinalLike (foam_mem V M) m ->
    foam_mul_rec_total V M a m.
Proof.
  intros V M hPred hAddTotal a m ha hm.
  pose (phi := mulRecTotalOnOrdinalAt 1 0).
  pose (tail := fun _ : nat => a).
  pose proof (foam_induction_schema V M phi (scons V a tail)) as hind.
  assert (hall : forall b,
      Sat V (foam_mem V M) (scons V b (scons V a tail)) phi).
  {
    apply hind.
    intros b ih.
    apply (proj2 (foam_mulRecTotalOnOrdinalAt_spec V M
      (scons V b (scons V a tail)) 1 0)).
    intro hb.
    destruct (hPred b hb) as [hbEmpty | [p [hpb hbSucc]]].
    - rewrite hbEmpty.
      apply foam_mul_rec_total_empty.
    - assert (hpOrd : OrdinalLike (foam_mem V M) p).
      {
        exact (OrdinalLike_of_mem V (foam_mem V M) b p hb hpb).
      }
      pose proof (proj1 (Sat_rename_rSkipParam V (foam_mem V M)
        phi (scons V a tail) b p) (ih p hpb)) as hpSat.
      assert (hpTotal : foam_mul_rec_total V M a p).
      {
        exact (proj1 (foam_mulRecTotalOnOrdinalAt_spec V M
          (scons V p (scons V a tail)) 1 0) hpSat hpOrd).
      }
      rewrite hbSucc.
      apply (foam_mul_rec_total_succ_of_addTotal V M a p hpOrd).
      + intro s.
        exact (hAddTotal s a ha).
      + exact hpTotal.
  }
  exact (proj1 (foam_mulRecTotalOnOrdinalAt_spec V M
    (scons V m (scons V a tail)) 1 0) (hall m) hm).
Qed.

Lemma fofam_mul_rec_total_of_ordinalLike : forall (V : Type)
    (M : FirstOrderFiniteAdjunctionModel V) (a m : V),
  OrdinalLike (foam_mem V M) a ->
  OrdinalLike (foam_mem V M) m ->
  foam_mul_rec_total V M a m.
Proof.
  intros V M a m ha hm.
  apply (foam_mul_rec_total_of_ordinalLike_of_predecessor V M).
  - intros b hb.
    exact (fofam_OrdinalLike_empty_or_succ V M b hb).
  - intros s r hr.
    exact (fofam_succ_rec_total_of_ordinalLike V M s r hr).
  - exact ha.
  - exact hm.
Qed.

Lemma domainForm_free : forall i,
  Free i domainForm -> i = 0.
Proof.
  intros i h.
  unfold domainForm in h.
  apply (HF_ordinalLikeAt_free i 0 h).
Qed.

Lemma zeroGraph_free : forall i,
  Free i zeroGraph -> i = 0.
Proof.
  intros i h.
  unfold zeroGraph in h.
  apply (HF_emptyAt_free i 0 h).
Qed.

Lemma succGraph_free : forall i,
  Free i succGraph -> i = 0 \/ i = 1.
Proof.
  intros i h.
  unfold succGraph in h.
  destruct (HF_succAt_free i 0 1 h) as [hi | hi]; lia.
Qed.

Lemma addGraphAt_free : forall i out left right,
  Free i (addGraphAt out left right) ->
    i = out \/ i = left \/ i = right.
Proof.
  intros i out left right h.
  unfold addGraphAt in h.
  simpl in h.
  destruct h as [h | h].
  - destruct (HF_succRecApproxAt_free (S i) 0 (S left) (S right) h)
      as [hi | [hi | hi]]; lia.
  - destruct (HF_pairMemAt_free (S i) (S right) (S out) 0 h)
      as [hi | [hi | hi]]; lia.
Qed.

Lemma addGraph_free : forall i,
  Free i addGraph -> i = 0 \/ i = 1 \/ i = 2.
Proof.
  intros i h.
  unfold addGraph in h.
  exact (addGraphAt_free i 0 1 2 h).
Qed.

Lemma mulStepAt_free : forall i f a m,
  Free i (mulStepAt f a m) -> i = f \/ i = a \/ i = m.
Proof.
  intros i f a m h.
  unfold mulStepAt, addGraphAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, HF_succAt, HF_adjoinAt,
    HF_succRecApproxAt, HF_pairFunctionalAt, HF_pairKeysBelowSuccAt,
    HF_pairBaseAt, HF_pairZeroBaseAt, HF_pairTotalBelowSuccAt,
    HF_pairSuccStepAt, HF_emptyAt, fIff in h.
  solve_free_vars.
Qed.

Lemma mulRecApproxAt_free : forall i f a m,
  Free i (mulRecApproxAt f a m) -> i = f \/ i = a \/ i = m.
Proof.
  intros i f a m h.
  unfold mulRecApproxAt in h.
  simpl in h.
  destruct h as [h | [h | [h | [h | h]]]].
  - pose proof (HF_pairFunctionalAt_free i f h). lia.
  - destruct (HF_pairKeysBelowSuccAt_free i f m h) as [hi | hi]; lia.
  - pose proof (HF_pairZeroBaseAt_free i f h). lia.
  - destruct (HF_pairTotalBelowSuccAt_free i f m h) as [hi | hi]; lia.
  - destruct (mulStepAt_free i f a m h) as [hi | [hi | hi]]; lia.
Qed.

Lemma mulGraphAt_free : forall i out left right,
  Free i (mulGraphAt out left right) ->
    i = out \/ i = left \/ i = right.
Proof.
  intros i out left right h.
  unfold mulGraphAt in h.
  simpl in h.
  destruct h as [h | h].
  - destruct (mulRecApproxAt_free (S i) 0 (S left) (S right) h)
      as [hi | [hi | hi]]; lia.
  - destruct (HF_pairMemAt_free (S i) (S right) (S out) 0 h)
      as [hi | [hi | hi]]; lia.
Qed.

Lemma mulGraph_free : forall i,
  Free i mulGraph -> i = 0 \/ i = 1 \/ i = 2.
Proof.
  intros i h.
  unfold mulGraph in h.
  exact (mulGraphAt_free i 0 1 2 h).
Qed.

Lemma mulRecApproxAt_value_of_le : forall m N f outDummy e n y,
  Sat nat hf_mem
    (scons nat f
      (scons nat outDummy
        (scons nat (ordinal_code m) (scons nat (ordinal_code N) e))))
    (mulRecApproxAt 0 2 3) ->
  n <= N ->
  hf_mem (hf_kpair_obj ackermannHFModel (ordinal_code n) y) f ->
  y = ordinal_code (m * n).
Proof.
  intros m N f outDummy e n.
  induction n as [|n IH]; intros y hA hn hy.
  - destruct hA as [hfunSat [_hkeysSat [hzeroSat [_htotalSat _hstepSat]]]].
    pose (E := scons nat f
      (scons nat outDummy
        (scons nat (ordinal_code m) (scons nat (ordinal_code N) e)))).
    pose proof (proj1 (HF_pairFunctionalAt_spec ackermannHFModel E 0)
      hfunSat) as hfun.
    pose proof (proj1 (HF_pairZeroBaseAt_spec ackermannHFModel E 0)
      hzeroSat) as hbase.
    change (hf_pair_functional ackermannHFModel f) in hfun.
    change (hf_mem (hf_kpair_obj ackermannHFModel hf_empty hf_empty) f)
      in hbase.
    change (hf_mem
      (hf_kpair_obj ackermannHFModel (ordinal_code 0) (ordinal_code 0)) f)
      in hbase.
    pose proof (hfun (ordinal_code 0) y (ordinal_code 0) hy hbase) as hy_eq.
    rewrite Nat.mul_0_r.
    simpl.
    exact hy_eq.
  - pose proof hA as hA'.
    destruct hA as [_hfunSat [_hkeysSat [_hzeroSat [htotalSat hstepSat]]]].
    pose (E := scons nat f
      (scons nat outDummy
        (scons nat (ordinal_code m) (scons nat (ordinal_code N) e)))).
    pose proof (proj1 (HF_pairTotalBelowSuccAt_spec ackermannHFModel E 0 3)
      htotalSat) as htotal.
    change (hf_pair_total_below_succ ackermannHFModel f (ordinal_code N))
      in htotal.
    assert (hnlt : n < N) by lia.
    destruct (htotal (ordinal_code n)
      (or_introl (ordinal_code_mem_of_lt n N hnlt))) as [t ht].
    assert (hnle : n <= N) by lia.
    pose proof (IH t hA' hnle ht) as htval.
    pose (Ekty := scons nat y (scons nat t (scons nat (ordinal_code n) E))).
    pose (Eskty := scons nat (ordinal_code (S n)) Ekty).
    assert (hktSat : Sat nat hf_mem Ekty (HF_pairMemAt 2 1 3)).
    {
      apply (proj2 (HF_pairMemAt_spec ackermannHFModel Ekty 2 1 3)).
      change (hf_mem (hf_kpair_obj ackermannHFModel (ordinal_code n) t) f).
      exact ht.
    }
    assert (hskSat : Sat nat hf_mem Eskty (HF_succAt 0 3)).
    {
      apply (proj2 (HF_succAt_spec ackermannHFModel Eskty 0 3)).
      reflexivity.
    }
    assert (hskySat : Sat nat hf_mem Eskty (HF_pairMemAt 0 1 4)).
    {
      apply (proj2 (HF_pairMemAt_spec ackermannHFModel Eskty 0 1 4)).
      change (hf_mem
        (hf_kpair_obj ackermannHFModel (ordinal_code (S n)) y) f).
      exact hy.
    }
    pose proof (hstepSat (ordinal_code n) t y
      (ordinal_code_mem_of_lt n N hnlt)
      hktSat (ordinal_code (S n)) hskSat hskySat) as haddSat.
    pose proof (addGraphAt_value_of_ordinal_inputs 1 2 6 (m * n) m
      Eskty htval eq_refl haddSat) as hyval.
    change (y = ordinal_code (m * n + m)) in hyval.
    change (y = ordinal_code (m * S n)).
    rewrite hyval.
    rewrite Nat.mul_succ_r.
    reflexivity.
Qed.

Lemma mulGraph_ordinal_code : forall m n e,
  Sat nat hf_mem
    (scons nat (ordinal_code (m * n))
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)))
    mulGraph.
Proof.
  intros m n e.
  unfold mulGraph, mulGraphAt.
  pose (f := mul_rec_trace m n).
  pose (E := scons nat f
    (scons nat (ordinal_code (m * n))
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)))).
  exists f.
  split.
  - change (Sat nat hf_mem E (mulRecApproxAt 0 2 3)).
    unfold mulRecApproxAt.
    repeat split.
    + apply (proj2 (HF_pairFunctionalAt_spec ackermannHFModel E 0)).
      change (hf_pair_functional ackermannHFModel f).
      exact (mul_rec_trace_functional m n).
    + apply (proj2 (HF_pairKeysBelowSuccAt_spec ackermannHFModel E 0 3)).
      change (hf_pair_keys_below_succ ackermannHFModel f (ordinal_code n)).
      exact (mul_rec_trace_keys_below_succ m n).
    + apply (proj2 (HF_pairZeroBaseAt_spec ackermannHFModel E 0)).
      change (hf_mem (hf_kpair_obj ackermannHFModel hf_empty hf_empty) f).
      unfold f.
      pose proof (mul_rec_trace_pair_mem m 0 n) as hp.
      assert (h0n : 0 <= n) by lia.
      specialize (hp h0n).
      rewrite Nat.mul_0_r in hp.
      simpl in hp.
      exact hp.
    + apply (proj2 (HF_pairTotalBelowSuccAt_spec ackermannHFModel E 0 3)).
      change (hf_pair_total_below_succ ackermannHFModel f (ordinal_code n)).
      exact (mul_rec_trace_total_below_succ m n).
    + unfold mulStepAt.
      intros k t y hkm hkt sk hsk hsky.
      pose (Ekty := scons nat y (scons nat t (scons nat k E))).
      pose (Eskty := scons nat sk Ekty).
      pose proof (proj1 (HF_pairMemAt_spec ackermannHFModel Ekty 2 1 3)
        hkt) as hkt'.
      change (hf_mem (hf_kpair_obj ackermannHFModel k t) f) in hkt'.
      pose proof (proj1 (HF_pairMemAt_spec ackermannHFModel Eskty 0 1 4)
        hsky) as hsky'.
      change (hf_mem (hf_kpair_obj ackermannHFModel sk y) f) in hsky'.
      pose proof (proj1 (HF_succAt_spec ackermannHFModel Eskty 0 3)
        hsk) as hsk'.
      change (sk = hf_adjoin k k) in hsk'.
      destruct (proj1 (hf_mem_ordinal_code_iff k n) hkm) as [i [hi hk]].
      destruct (proj1 (mul_rec_trace_mem_iff m
        (hf_kpair_obj ackermannHFModel k t) n) hkt')
        as [j [_hj hpair_j]].
      destruct (hf_kpair_injective ackermannHFModel
        k t (ordinal_code j) (ordinal_code (m * j)) hpair_j)
        as [hk_j ht_j].
      assert (hij : i = j).
      {
        apply ordinal_code_injective.
        rewrite <- hk.
        exact hk_j.
      }
      assert (ht : t = ordinal_code (m * i)).
      {
        rewrite ht_j.
        now rewrite <- hij.
      }
      assert (hskcode : sk = ordinal_code (S i)).
      {
        rewrite hsk', hk.
        reflexivity.
      }
      destruct (proj1 (mul_rec_trace_mem_iff m
        (hf_kpair_obj ackermannHFModel sk y) n) hsky')
        as [l [_hl hpair_l]].
      destruct (hf_kpair_injective ackermannHFModel
        sk y (ordinal_code l) (ordinal_code (m * l)) hpair_l)
        as [hsk_l hy_l].
      assert (hil : S i = l).
      {
        apply ordinal_code_injective.
        rewrite <- hskcode.
        exact hsk_l.
      }
      assert (hy : y = ordinal_code (m * S i)).
      {
        rewrite hy_l.
        now rewrite <- hil.
      }
      apply (addGraphAt_ordinal_code 1 2 6 (m * i) m Eskty).
      * change (y = ordinal_code (m * i + m)).
        rewrite hy.
        rewrite Nat.mul_succ_r.
        reflexivity.
      * change (t = ordinal_code (m * i)).
        exact ht.
      * reflexivity.
  - apply (proj2 (HF_pairMemAt_spec ackermannHFModel E 3 1 0)).
    change (hf_mem
      (hf_kpair_obj ackermannHFModel (ordinal_code n) (ordinal_code (m * n)))
      f).
    unfold f.
    apply mul_rec_trace_pair_mem.
    lia.
Qed.

Lemma mulGraph_exact_on_ordinal_codes : forall r m n e,
  Sat nat hf_mem
    (scons nat (ordinal_code r)
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) e)))
    mulGraph <-> r = m * n.
Proof.
  intros r m n e.
  split.
  - intro h.
    unfold mulGraph, mulGraphAt in h.
    destruct h as [f [hf hout]].
    pose proof (proj1 (HF_pairMemAt_spec ackermannHFModel
      (scons nat f
        (scons nat (ordinal_code r)
          (scons nat (ordinal_code m) (scons nat (ordinal_code n) e))))
      3 1 0) hout) as hout'.
    change (hf_mem
      (hf_kpair_obj ackermannHFModel (ordinal_code n) (ordinal_code r)) f)
      in hout'.
    assert (hnn : n <= n) by lia.
    pose proof (mulRecApproxAt_value_of_le m n f (ordinal_code r) e
      n (ordinal_code r) hf hnn hout') as hval.
    apply ordinal_code_injective.
    exact hval.
  - intro h.
    subst r.
    apply mulGraph_ordinal_code.
Qed.

Lemma mulGraph_value_of_ordinal_inputs : forall m n e,
  e 1 = ordinal_code m ->
  e 2 = ordinal_code n ->
  Sat nat hf_mem e mulGraph ->
  e 0 = ordinal_code (m * n).
Proof.
  intros m n e hleft hright h.
  unfold mulGraph, mulGraphAt in h.
  destruct h as [f [hf hout]].
  pose (tail := fun k => e (S (S (S k)))).
  pose (eCanon := scons nat f
    (scons nat (e 0)
      (scons nat (ordinal_code m) (scons nat (ordinal_code n) tail)))).
  assert (heq : forall k, eCanon k = scons nat f e k).
  {
    intro k.
    destruct k as [|[|[|[|k]]]]; simpl.
    - reflexivity.
    - reflexivity.
    - symmetry. exact hleft.
    - symmetry. exact hright.
    - reflexivity.
  }
  assert (hfCanon : Sat nat hf_mem eCanon (mulRecApproxAt 0 2 3)).
  {
    apply (proj2 (@Sat_ext nat hf_mem (mulRecApproxAt 0 2 3)
      eCanon (scons nat f e) heq)).
    exact hf.
  }
  pose proof (proj1 (HF_pairMemAt_spec ackermannHFModel
    (scons nat f e) 3 1 0) hout) as hout'.
  change (hf_mem (hf_kpair_obj ackermannHFModel (e 2) (e 0)) f) in hout'.
  rewrite hright in hout'.
  assert (hnn : n <= n) by lia.
  exact (mulRecApproxAt_value_of_le m n f (e 0) tail
    n (e 0) hfCanon hnn hout').
Qed.

Lemma hf_model_mem_irrefl : forall (M : HFModel) (a : M),
  ~ hf_rel M a a.
Proof.
  intros M.
  apply (hf_set_ind M (fun a => ~ hf_rel M a a)).
  intros a ih haa.
  exact (ih a haa haa).
Qed.

Lemma domain_empty_model : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) (scons M (hf_empty_obj M) e) domainForm.
Proof.
  intros M e.
  unfold domainForm.
  apply (proj2 (HF_ordinalLikeAt_spec M (hf_rel M)
    (scons M (hf_empty_obj M) e) 0)).
  apply OrdinalLike_empty.
Qed.

Lemma zeroGraph_empty_model : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) (scons M (hf_empty_obj M) e) zeroGraph.
Proof.
  intros M e.
  unfold zeroGraph.
  apply (proj2 (HF_emptyAt_empty M
    (scons M (hf_empty_obj M) e) 0)).
  reflexivity.
Qed.

Lemma succGraph_adjoin_self_model : forall (M : HFModel)
    (a : M) (e : nat -> M),
  Sat M (hf_rel M)
    (scons M (hf_adjoin_obj M a a) (scons M a e)) succGraph.
Proof.
  intros M a e.
  unfold succGraph.
  apply (proj2 (HF_succAt_spec M
    (scons M (hf_adjoin_obj M a a) (scons M a e)) 0 1)).
  reflexivity.
Qed.

Lemma domain_adjoin_self_model : forall (M : HFModel)
    (a : M) (e : nat -> M),
  Sat M (hf_rel M) (scons M a e) domainForm ->
  Sat M (hf_rel M)
    (scons M (hf_adjoin_obj M a a) e) domainForm.
Proof.
  intros M a e ha.
  unfold domainForm in *.
  apply (proj2 (HF_ordinalLikeAt_spec M (hf_rel M)
    (scons M (hf_adjoin_obj M a a) e) 0)).
  pose proof (proj1 (HF_ordinalLikeAt_spec M (hf_rel M)
    (scons M a e) 0) ha) as ha'.
  exact (OrdinalLike_adjoin_self M a (hf_adjoin_obj M a a) ha' eq_refl).
Qed.

Definition Domain (M : HFModel) : Type :=
  { a : M | OrdinalLike (hf_rel M) a }.

Definition domainZero (M : HFModel) : Domain M :=
  exist _ (hf_empty_obj M) (OrdinalLike_empty M).

Definition domainSucc (M : HFModel) (a : Domain M) : Domain M :=
  exist _ (hf_adjoin_obj M (proj1_sig a) (proj1_sig a))
    (OrdinalLike_adjoin_self M (proj1_sig a)
      (hf_adjoin_obj M (proj1_sig a) (proj1_sig a))
      (proj2_sig a) eq_refl).

Lemma domainZero_val : forall (M : HFModel),
  proj1_sig (domainZero M) = hf_empty_obj M.
Proof.
  reflexivity.
Qed.

Lemma domainSucc_val : forall (M : HFModel) (a : Domain M),
  proj1_sig (domainSucc M a) =
    hf_adjoin_obj M (proj1_sig a) (proj1_sig a).
Proof.
  reflexivity.
Qed.

Lemma adjoin_self_ne_empty_model : forall (M : HFModel) (a : M),
  hf_adjoin_obj M a a <> hf_empty_obj M.
Proof.
  intros M a h.
  assert (ha : hf_rel M a (hf_adjoin_obj M a a)).
  {
    apply (proj2 (hf_adjoin_spec M a a a)).
    now right.
  }
  rewrite h in ha.
  exact (hf_empty_spec M a ha).
Qed.

Lemma adjoin_self_injective_on_ordinalLike_model :
  forall (M : HFModel) (a b : M),
  OrdinalLike (hf_rel M) a ->
  OrdinalLike (hf_rel M) b ->
  hf_adjoin_obj M a a = hf_adjoin_obj M b b ->
  a = b.
Proof.
  intros M a b _ha hb h.
  assert (hasucc : hf_rel M a (hf_adjoin_obj M b b)).
  {
    rewrite <- h.
    apply (proj2 (hf_adjoin_spec M a a a)).
    now right.
  }
  destruct (proj1 (hf_adjoin_spec M a b b) hasucc) as [hab | hab].
  - assert (hbsucc : hf_rel M b (hf_adjoin_obj M a a)).
    {
      rewrite h.
      apply (proj2 (hf_adjoin_spec M b b b)).
      now right.
    }
    destruct (proj1 (hf_adjoin_spec M b a a) hbsucc) as [hba | hba].
    + pose proof (proj1 hb a hab b hba) as hbb.
      exfalso. exact (hf_model_mem_irrefl M b hbb).
    + symmetry. exact hba.
  - exact hab.
Qed.

Lemma domainSucc_injective_model : forall (M : HFModel) (a b : Domain M),
  domainSucc M a = domainSucc M b -> a = b.
Proof.
  intros M [a ha] [b hb] h.
  assert (hval : hf_adjoin_obj M a a = hf_adjoin_obj M b b).
  {
    exact (f_equal (@proj1_sig M
      (fun x => OrdinalLike (hf_rel M) x)) h).
  }
  assert (hab : a = b).
  {
    exact (adjoin_self_injective_on_ordinalLike_model M a b ha hb hval).
  }
  subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma domainSucc_ne_zero_model : forall (M : HFModel) (a : Domain M),
  domainSucc M a <> domainZero M.
Proof.
  intros M [a ha] h.
  pose proof (f_equal (@proj1_sig M
    (fun x => OrdinalLike (hf_rel M) x)) h) as hval.
  simpl in hval.
  exact (adjoin_self_ne_empty_model M a hval).
Qed.

Lemma domainElement_domainForm_model : forall (M : HFModel)
    (a : Domain M) (e : nat -> M),
  Sat M (hf_rel M) (scons M (proj1_sig a) e) domainForm.
Proof.
  intros M [a ha] e.
  unfold domainForm.
  apply (proj2 (HF_ordinalLikeAt_spec M (hf_rel M)
    (scons M a e) 0)).
  exact ha.
Qed.

Lemma domainZero_domainForm_model : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) (scons M (proj1_sig (domainZero M)) e) domainForm.
Proof.
  intros M e.
  apply domainElement_domainForm_model.
Qed.

Lemma domainZero_zeroGraph_model : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) (scons M (proj1_sig (domainZero M)) e) zeroGraph.
Proof.
  intros M e.
  change (Sat M (hf_rel M) (scons M (hf_empty_obj M) e) zeroGraph).
  apply zeroGraph_empty_model.
Qed.

Lemma domainSucc_domainForm_model : forall (M : HFModel)
    (a : Domain M) (e : nat -> M),
  Sat M (hf_rel M) (scons M (proj1_sig (domainSucc M a)) e) domainForm.
Proof.
  intros M a e.
  apply domainElement_domainForm_model.
Qed.

Lemma domainSucc_succGraph_model : forall (M : HFModel)
    (a : Domain M) (e : nat -> M),
  Sat M (hf_rel M)
    (scons M (proj1_sig (domainSucc M a)) (scons M (proj1_sig a) e))
    succGraph.
Proof.
  intros M a e.
  change (Sat M (hf_rel M)
    (scons M (hf_adjoin_obj M (proj1_sig a) (proj1_sig a))
      (scons M (proj1_sig a) e)) succGraph).
  apply succGraph_adjoin_self_model.
Qed.

Lemma zeroGraph_domain_model : forall (M : HFModel) (e : nat -> M),
  Sat M (hf_rel M) e zeroGraph ->
  Sat M (hf_rel M) e domainForm.
Proof.
  intros M e hz.
  unfold domainForm.
  apply (proj2 (HF_ordinalLikeAt_spec M (hf_rel M) e 0)).
  pose proof (proj1 (HF_emptyAt_empty M e 0) hz) as hz'.
  rewrite hz'.
  apply OrdinalLike_empty.
Qed.

Lemma zeroGraph_domain : forall e,
  Sat nat hf_mem e zeroGraph -> Sat nat hf_mem e domainForm.
Proof.
  intros e hz.
  exact (zeroGraph_domain_model ackermannHFModel e hz).
Qed.

Lemma succGraph_preserves_domain_model : forall (M : HFModel)
    (e : nat -> M),
  Sat M (hf_rel M) e (HF_ordinalLikeAt 1) ->
  Sat M (hf_rel M) e succGraph ->
  Sat M (hf_rel M) e domainForm.
Proof.
  intros M e hin hs.
  unfold domainForm.
  apply (proj2 (HF_ordinalLikeAt_spec M (hf_rel M) e 0)).
  pose proof (proj1 (HF_ordinalLikeAt_spec M (hf_rel M) e 1) hin) as hin'.
  pose proof (proj1 (HF_succAt_spec M e 0 1) hs) as hs'.
  exact (OrdinalLike_adjoin_self M (e 1) (e 0) hin' hs').
Qed.

Lemma succGraph_preserves_domain : forall e,
  Sat nat hf_mem e (HF_ordinalLikeAt 1) ->
  Sat nat hf_mem e succGraph ->
  Sat nat hf_mem e domainForm.
Proof.
  intros e hin hs.
  exact (succGraph_preserves_domain_model ackermannHFModel e hin hs).
Qed.

Definition upVarMap (rho : nat -> nat) : nat -> nat :=
  fun n =>
    match n with
    | 0 => 0
    | S k => S (rho k)
    end.

Definition substZeroAfterMap (p k : nat) (rho : nat -> nat) : nat -> nat :=
  fun n => if n <? p then k + n else rho (n - p) + k + p.

Definition substZeroBeforeMap (p k : nat) (rho : nat -> nat) : nat -> nat :=
  fun n =>
    if n <? p then k + n
    else if n =? p then k + p
    else rho (n - p - 1) + k + p + 1.

Lemma substZeroAfterMap_lt : forall p k n rho,
  n < p -> substZeroAfterMap p k rho n = k + n.
Proof.
  intros p k n rho h.
  unfold substZeroAfterMap.
  destruct (Nat.ltb_spec n p); [reflexivity | lia].
Qed.

Lemma substZeroAfterMap_ge : forall p k n rho,
  p <= n -> substZeroAfterMap p k rho n = rho (n - p) + k + p.
Proof.
  intros p k n rho h.
  unfold substZeroAfterMap.
  destruct (Nat.ltb_spec n p); [lia | reflexivity].
Qed.

Lemma substZeroBeforeMap_lt : forall p k n rho,
  n < p -> substZeroBeforeMap p k rho n = k + n.
Proof.
  intros p k n rho h.
  unfold substZeroBeforeMap.
  destruct (Nat.ltb_spec n p); [reflexivity | lia].
Qed.

Lemma substZeroBeforeMap_eq : forall p k rho,
  substZeroBeforeMap p k rho p = k + p.
Proof.
  intros p k rho.
  unfold substZeroBeforeMap.
  destruct (Nat.ltb_spec p p); [lia |].
  destruct (Nat.eqb_spec p p); [reflexivity | congruence].
Qed.

Lemma substZeroBeforeMap_gt : forall p k n rho,
  p < n -> substZeroBeforeMap p k rho n =
    rho (n - p - 1) + k + p + 1.
Proof.
  intros p k n rho h.
  unfold substZeroBeforeMap.
  destruct (Nat.ltb_spec n p); [lia |].
  destruct (Nat.eqb_spec n p); [lia | reflexivity].
Qed.

Lemma substZeroBeforeMap_ne_replaced_slot : forall p k n rho,
  n <> p -> substZeroBeforeMap p k rho n <> k + p.
Proof.
  intros p k n rho hne hslot.
  unfold substZeroBeforeMap in hslot.
  destruct (Nat.ltb_spec n p) as [hlt | hnlt].
  - lia.
  - destruct (Nat.eqb_spec n p) as [heq | hneq].
    + contradiction.
    + lia.
Qed.

Lemma substZeroAfterMap_add : forall p k d rho n,
  substZeroAfterMap p k rho n + d =
    substZeroAfterMap p (k + d) rho n.
Proof.
  intros p k d rho n.
  unfold substZeroAfterMap.
  destruct (Nat.ltb_spec n p); lia.
Qed.

Lemma substZeroBeforeMap_add : forall p k d rho n,
  substZeroBeforeMap p k rho n + d =
    substZeroBeforeMap p (k + d) rho n.
Proof.
  intros p k d rho n.
  unfold substZeroBeforeMap.
  destruct (Nat.ltb_spec n p); [lia |].
  destruct (Nat.eqb_spec n p); lia.
Qed.

Lemma upVarMap_substZeroAfterMap_zero : forall p rho n,
  upVarMap (substZeroAfterMap p 0 rho) n =
    substZeroAfterMap (S p) 0 rho n.
Proof.
  intros p rho [|n].
  - unfold upVarMap, substZeroAfterMap.
    destruct (Nat.ltb_spec 0 (S p)); [reflexivity | lia].
  - unfold upVarMap.
    simpl.
    destruct (Nat.ltb_spec n p) as [hlt | hnlt].
    + rewrite (substZeroAfterMap_lt p 0 n rho hlt).
      rewrite (substZeroAfterMap_lt (S p) 0 (S n) rho); [lia | lia].
    + assert (hge : p <= n) by lia.
      rewrite (substZeroAfterMap_ge p 0 n rho hge).
      rewrite (substZeroAfterMap_ge (S p) 0 (S n) rho); [|lia].
      replace (S n - S p) with (n - p) by lia.
      lia.
Qed.

Lemma upVarMap_substZeroBeforeMap_zero : forall p rho n,
  upVarMap (substZeroBeforeMap p 0 rho) n =
    substZeroBeforeMap (S p) 0 rho n.
Proof.
  intros p rho [|n].
  - unfold upVarMap, substZeroBeforeMap.
    destruct (Nat.ltb_spec 0 (S p)); [reflexivity | lia].
  - unfold upVarMap.
    simpl.
    destruct (Nat.ltb_spec n p) as [hlt | hnlt].
    + rewrite (substZeroBeforeMap_lt p 0 n rho hlt).
      rewrite (substZeroBeforeMap_lt (S p) 0 (S n) rho); [lia | lia].
    + destruct (Nat.eq_dec n p) as [heq | hne].
      * subst n.
        rewrite substZeroBeforeMap_eq.
        rewrite substZeroBeforeMap_eq.
        lia.
      * assert (hgt : p < n) by lia.
        rewrite (substZeroBeforeMap_gt p 0 n rho hgt).
        rewrite (substZeroBeforeMap_gt (S p) 0 (S n) rho); [|lia].
        replace (S n - S p - 1) with (n - p - 1) by lia.
        lia.
Qed.

Lemma substZeroAfterMap_zero_zero : forall rho n,
  substZeroAfterMap 0 0 rho n = rho n.
Proof.
  intros rho n.
  unfold substZeroAfterMap.
  destruct (Nat.ltb_spec n 0); [lia |].
  replace (n - 0) with n by lia.
  lia.
Qed.

Lemma substZeroBeforeMap_zero_zero : forall rho n,
  substZeroBeforeMap 0 0 rho n = upVarMap rho n.
Proof.
  intros rho [|n].
  - apply substZeroBeforeMap_eq.
  - rewrite (substZeroBeforeMap_gt 0 0 (S n) rho); [|lia].
    unfold upVarMap.
    simpl.
    replace (S n - 0 - 1) with n by lia.
    replace (n - 0) with n by lia.
    repeat rewrite Nat.add_0_r.
    apply Nat.add_1_r.
Qed.

Definition insertAt {A : Type} (k : nat) (x : A) (e : nat -> A) :
    nat -> A :=
  fun n => if n <? k then e n else if n =? k then x else e (n - 1).

Lemma insertAt_zero : forall A (x : A) e n,
  insertAt 0 x e n = scons A x e n.
Proof.
  intros A x e [|n].
  - unfold insertAt, scons.
    destruct (Nat.ltb_spec 0 0); [lia |].
    destruct (Nat.eqb_spec 0 0); [reflexivity | congruence].
  - unfold insertAt, scons.
    destruct (Nat.ltb_spec (S n) 0); [lia |].
    destruct (Nat.eqb_spec (S n) 0); [lia |].
    replace (S n - 1) with n by lia.
    reflexivity.
Qed.

Lemma insertAt_lt : forall A k n (x : A) e,
  n < k -> insertAt k x e n = e n.
Proof.
  intros A k n x e h.
  unfold insertAt.
  destruct (Nat.ltb_spec n k); [reflexivity | lia].
Qed.

Lemma insertAt_eq : forall A k (x : A) e,
  insertAt k x e k = x.
Proof.
  intros A k x e.
  unfold insertAt.
  destruct (Nat.ltb_spec k k); [lia |].
  destruct (Nat.eqb_spec k k); [reflexivity | congruence].
Qed.

Lemma insertAt_gt : forall A k n (x : A) e,
  k < n -> insertAt k x e n = e (n - 1).
Proof.
  intros A k n x e h.
  unfold insertAt.
  destruct (Nat.ltb_spec n k); [lia |].
  destruct (Nat.eqb_spec n k); [lia | reflexivity].
Qed.

Definition replaceAt {A : Type} (k : nat) (x : A) (e : nat -> A) :
    nat -> A :=
  fun n => if n =? k then x else e n.

Lemma replaceAt_eq : forall A k (x : A) e,
  replaceAt k x e k = x.
Proof.
  intros A k x e.
  unfold replaceAt.
  destruct (Nat.eqb_spec k k); [reflexivity | congruence].
Qed.

Lemma replaceAt_ne : forall A k n (x : A) e,
  n <> k -> replaceAt k x e n = e n.
Proof.
  intros A k n x e h.
  unfold replaceAt.
  destruct (Nat.eqb_spec n k); [congruence | reflexivity].
Qed.

Lemma replaceAt_zero_scons : forall A (x d : A) e n,
  replaceAt 0 x (scons A d e) n = scons A x e n.
Proof.
  intros A x d e [|n].
  - apply replaceAt_eq.
  - rewrite replaceAt_ne; [reflexivity | lia].
Qed.

Definition succReplaceAt {A : Type} (M : FirstOrderAdjunctionModel A)
    (k : nat) (e : nat -> A) : nat -> A :=
  replaceAt k (foam_adjoin A M (e k) (e k)) e.

Lemma succReplaceAt_eq : forall A (M : FirstOrderAdjunctionModel A) k e,
  succReplaceAt M k e k = foam_adjoin A M (e k) (e k).
Proof.
  intros A M k e.
  unfold succReplaceAt.
  apply replaceAt_eq.
Qed.

Lemma succReplaceAt_ne : forall A (M : FirstOrderAdjunctionModel A) k n e,
  n <> k -> succReplaceAt M k e n = e n.
Proof.
  intros A M k n e h.
  unfold succReplaceAt.
  apply replaceAt_ne.
  exact h.
Qed.

Lemma scons_insertAt : forall A k (x d : A) e n,
  scons A d (insertAt k x e) n =
    insertAt (S k) x (scons A d e) n.
Proof.
  intros A k x d e [|n].
  - unfold scons, insertAt.
    destruct (Nat.ltb_spec 0 (S k)); [reflexivity | lia].
  - unfold scons at 1.
    simpl.
    destruct (lt_eq_lt_dec n k) as [[hlt | heq] | hgt].
    + rewrite (insertAt_lt A k n x e hlt).
      rewrite (insertAt_lt A (S k) (S n) x (scons A d e)); [reflexivity | lia].
    + subst n.
      rewrite insertAt_eq.
      rewrite insertAt_eq.
      reflexivity.
    + rewrite (insertAt_gt A k n x e hgt).
      rewrite (insertAt_gt A (S k) (S n) x (scons A d e)); [|lia].
      replace (S n - 1) with n by lia.
      destruct n as [|n]; [lia |].
      simpl.
      replace (S n - 1) with n by lia.
      replace (n - 0) with n by lia.
      reflexivity.
Qed.

Lemma scons2_insertAt : forall A k (x d1 d2 : A) e n,
  scons A d2 (scons A d1 (insertAt k x e)) n =
    insertAt (S (S k)) x (scons A d2 (scons A d1 e)) n.
Proof.
  intros A k x d1 d2 e [|n].
  - unfold scons, insertAt.
    destruct (Nat.ltb_spec 0 (S (S k))); [reflexivity | lia].
  - simpl.
    rewrite (scons_insertAt A k x d1 e n).
    exact (scons_insertAt A (S k) x d2 (scons A d1 e) (S n)).
Qed.

Lemma scons3_insertAt : forall A k (x d1 d2 d3 : A) e n,
  scons A d3 (scons A d2 (scons A d1 (insertAt k x e))) n =
    insertAt (S (S (S k))) x
      (scons A d3 (scons A d2 (scons A d1 e))) n.
Proof.
  intros A k x d1 d2 d3 e [|n].
  - unfold scons, insertAt.
    destruct (Nat.ltb_spec 0 (S (S (S k)))); [reflexivity | lia].
  - simpl.
    rewrite (scons2_insertAt A k x d1 d2 e n).
    exact (scons_insertAt A (S (S k)) x d3
      (scons A d2 (scons A d1 e)) (S n)).
Qed.

Lemma scons_insertAt_prefix : forall A p k (x d : A) e n,
  scons A d (insertAt (k + p) x e) n =
    insertAt (S k + p) x (scons A d e) n.
Proof.
  intros A p k x d e n.
  rewrite (scons_insertAt A (k + p) x d e n).
  replace (S (k + p)) with (S k + p) by lia.
  reflexivity.
Qed.

Lemma scons2_insertAt_prefix : forall A p k (x d1 d2 : A) e n,
  scons A d2 (scons A d1 (insertAt (k + p) x e)) n =
    insertAt (S (S k) + p) x (scons A d2 (scons A d1 e)) n.
Proof.
  intros A p k x d1 d2 e n.
  rewrite (scons2_insertAt A (k + p) x d1 d2 e n).
  replace (S (S (k + p))) with (S (S k) + p) by lia.
  reflexivity.
Qed.

Lemma scons3_insertAt_prefix : forall A p k (x d1 d2 d3 : A) e n,
  scons A d3 (scons A d2 (scons A d1 (insertAt (k + p) x e))) n =
    insertAt (S (S (S k)) + p) x
      (scons A d3 (scons A d2 (scons A d1 e))) n.
Proof.
  intros A p k x d1 d2 d3 e n.
  rewrite (scons3_insertAt A (k + p) x d1 d2 d3 e n).
  replace (S (S (S (k + p)))) with (S (S (S k)) + p) by lia.
  reflexivity.
Qed.

Lemma scons_replaceAt : forall A k (x d : A) e n,
  scons A d (replaceAt k x e) n =
    replaceAt (S k) x (scons A d e) n.
Proof.
  intros A k x d e [|n].
  - unfold scons, replaceAt.
    destruct (Nat.eqb_spec 0 (S k)); [lia | reflexivity].
  - simpl.
    destruct (Nat.eq_dec n k) as [heq | hne].
    + subst n.
      rewrite replaceAt_eq.
      rewrite replaceAt_eq.
      reflexivity.
    + rewrite (replaceAt_ne A k n x e hne).
      rewrite (replaceAt_ne A (S k) (S n) x (scons A d e)); [reflexivity | lia].
Qed.

Lemma scons_replaceAt_prefix : forall A p k (x d : A) e n,
  scons A d (replaceAt (k + p) x e) n =
    replaceAt (S k + p) x (scons A d e) n.
Proof.
  intros A p k x d e n.
  rewrite (scons_replaceAt A (k + p) x d e n).
  replace (S (k + p)) with (S k + p) by lia.
  reflexivity.
Qed.

Lemma scons2_replaceAt_prefix : forall A p k (x d1 d2 : A) e n,
  scons A d2 (scons A d1 (replaceAt (k + p) x e)) n =
    replaceAt (S (S k) + p) x (scons A d2 (scons A d1 e)) n.
Proof.
  intros A p k x d1 d2 e [|n].
  - unfold scons, replaceAt.
    destruct (Nat.eqb_spec 0 (S (S k) + p)); [lia | reflexivity].
  - simpl.
    rewrite (scons_replaceAt_prefix A p k x d1 e n).
    replace (S k + p) with (S (k + p)) by lia.
    pose proof (scons_replaceAt A (S (k + p)) x d2
      (scons A d1 e) (S n)) as h.
    simpl in h.
    rewrite h.
    replace (S (S (k + p))) with (S (S k) + p) by lia.
    reflexivity.
Qed.

Lemma scons3_replaceAt_prefix : forall A p k (x d1 d2 d3 : A) e n,
  scons A d3 (scons A d2 (scons A d1 (replaceAt (k + p) x e))) n =
    replaceAt (S (S (S k)) + p) x
      (scons A d3 (scons A d2 (scons A d1 e))) n.
Proof.
  intros A p k x d1 d2 d3 e [|n].
  - unfold scons, replaceAt.
    destruct (Nat.eqb_spec 0 (S (S (S k)) + p)); [lia | reflexivity].
  - simpl.
    rewrite (scons2_replaceAt_prefix A p k x d1 d2 e n).
    replace (S (S k) + p) with (S (S (k + p))) by lia.
    pose proof (scons_replaceAt A (S (S (k + p))) x d3
      (scons A d2 (scons A d1 e)) (S n)) as h.
    simpl in h.
    rewrite h.
    replace (S (S (S (k + p)))) with (S (S (S k)) + p) by lia.
    reflexivity.
Qed.

Lemma scons_succReplaceAt_prefix :
  forall A (M : FirstOrderAdjunctionModel A) p k d e n,
    scons A d (succReplaceAt M (k + p) e) n =
      succReplaceAt M (S k + p) (scons A d e) n.
Proof.
  intros A M p k d e n.
  unfold succReplaceAt.
  assert (hslot : scons A d e (S k + p) = e (k + p)).
  {
    replace (S k + p) with (S (k + p)) by lia.
    reflexivity.
  }
  rewrite hslot.
  apply scons_replaceAt_prefix.
Qed.

Lemma scons2_succReplaceAt_prefix :
  forall A (M : FirstOrderAdjunctionModel A) p k d1 d2 e n,
    scons A d2 (scons A d1 (succReplaceAt M (k + p) e)) n =
      succReplaceAt M (S (S k) + p) (scons A d2 (scons A d1 e)) n.
Proof.
  intros A M p k d1 d2 e n.
  unfold succReplaceAt.
  assert (hslot :
    scons A d2 (scons A d1 e) (S (S k) + p) = e (k + p)).
  {
    replace (S (S k) + p) with (S (S (k + p))) by lia.
    reflexivity.
  }
  rewrite hslot.
  apply scons2_replaceAt_prefix.
Qed.

Lemma scons3_succReplaceAt_prefix :
  forall A (M : FirstOrderAdjunctionModel A) p k d1 d2 d3 e n,
    scons A d3 (scons A d2 (scons A d1 (succReplaceAt M (k + p) e))) n =
      succReplaceAt M (S (S (S k)) + p)
        (scons A d3 (scons A d2 (scons A d1 e))) n.
Proof.
  intros A M p k d1 d2 d3 e n.
  unfold succReplaceAt.
  assert (hslot :
    scons A d3 (scons A d2 (scons A d1 e)) (S (S (S k)) + p) =
      e (k + p)).
  {
    replace (S (S (S k)) + p) with (S (S (S (k + p)))) by lia.
    reflexivity.
  }
  rewrite hslot.
  apply scons3_replaceAt_prefix.
Qed.

Lemma domainForm_scons_insertAt :
  forall A (mem : A -> A -> Prop) p x d e,
    Sat A mem (scons A d (insertAt p x e)) domainForm <->
      Sat A mem (scons A d e) domainForm.
Proof.
  intros A mem p x d e.
  apply (Sat_ext_free A mem domainForm
    (scons A d (insertAt p x e)) (scons A d e)).
  intros n hn.
  pose proof (domainForm_free n hn) as hn0.
  subst n.
  reflexivity.
Qed.

Lemma domainForm_scons_succReplaceAt :
  forall A (M : FirstOrderAdjunctionModel A) p d e,
    Sat A (foam_mem A M) (scons A d (succReplaceAt M p e)) domainForm <->
      Sat A (foam_mem A M) (scons A d e) domainForm.
Proof.
  intros A M p d e.
  apply (Sat_ext_free A (foam_mem A M) domainForm
    (scons A d (succReplaceAt M p e)) (scons A d e)).
  intros n hn.
  pose proof (domainForm_free n hn) as hn0.
  subst n.
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

Module PA.

Record Model := {
  carrier :> Type;
  zero : carrier;
  succ : carrier -> carrier;
  add : carrier -> carrier -> carrier;
  mul : carrier -> carrier -> carrier;
  succ_injective : forall a b, succ a = succ b -> a = b;
  zero_not_succ : forall a, succ a <> zero;
  induction_schema : forall P : carrier -> Prop,
    P zero -> (forall a, P a -> P (succ a)) -> forall a, P a;
  add_zero : forall a, add a zero = a;
  add_succ : forall a b, add a (succ b) = succ (add a b);
  mul_zero : forall a, mul a zero = zero;
  mul_succ : forall a b, mul a (succ b) = add (mul a b) a
}.

Record Iso (M N : Model) := {
  iso_to : M -> N;
  iso_inv : N -> M;
  iso_left_inv : forall a, iso_inv (iso_to a) = a;
  iso_right_inv : forall b, iso_to (iso_inv b) = b;
  iso_map_zero : iso_to (zero M) = zero N;
  iso_map_succ : forall a, iso_to (succ M a) = succ N (iso_to a);
  iso_map_add : forall a b, iso_to (add M a b) = add N (iso_to a) (iso_to b);
  iso_map_mul : forall a b, iso_to (mul M a b) = mul N (iso_to a) (iso_to b)
}.

Definition natModel : Model.
Proof.
  refine {| carrier := nat;
            zero := 0;
            succ := S;
            add := Nat.add;
            mul := Nat.mul |}.
  - intros a b h. now inversion h.
  - intros a h. discriminate h.
  - intros P h0 hs a.
    induction a as [|a ih].
    + exact h0.
    + exact (hs a ih).
  - apply Nat.add_0_r.
  - apply Nat.add_succ_r.
  - apply Nat.mul_0_r.
  - apply Nat.mul_succ_r.
Defined.

Inductive term : Type :=
| tVar : nat -> term
| tZero : term
| tSucc : term -> term
| tAdd : term -> term -> term
| tMul : term -> term -> term.

Inductive formula : Type :=
| pEq : term -> term -> formula
| pBot : formula
| pImp : formula -> formula -> formula
| pAnd : formula -> formula -> formula
| pOr : formula -> formula -> formula
| pAll : formula -> formula
| pEx : formula -> formula.

Module Term.

Fixpoint rename (r : nat -> nat) (t : term) : term :=
  match t with
  | tVar n => tVar (r n)
  | tZero => tZero
  | tSucc a => tSucc (rename r a)
  | tAdd a b => tAdd (rename r a) (rename r b)
  | tMul a b => tMul (rename r a) (rename r b)
  end.

Definition upSubst (sigma : nat -> term) : nat -> term :=
  fun n =>
    match n with
    | 0 => tVar 0
    | S k => rename S (sigma k)
    end.

Fixpoint subst (sigma : nat -> term) (t : term) : term :=
  match t with
  | tVar n => sigma n
  | tZero => tZero
  | tSucc a => tSucc (subst sigma a)
  | tAdd a b => tAdd (subst sigma a) (subst sigma b)
  | tMul a b => tMul (subst sigma a) (subst sigma b)
  end.

Fixpoint eval (M : Model) (e : nat -> M) (t : term) : M :=
  match t with
  | tVar n => e n
  | tZero => zero M
  | tSucc a => succ M (eval M e a)
  | tAdd a b => add M (eval M e a) (eval M e b)
  | tMul a b => mul M (eval M e a) (eval M e b)
  end.

Fixpoint numeral (n : nat) : term :=
  match n with
  | 0 => tZero
  | S k => tSucc (numeral k)
  end.

Fixpoint numeralValue (M : Model) (n : nat) : M :=
  match n with
  | 0 => zero M
  | S k => succ M (numeralValue M k)
  end.

Lemma eval_numeral : forall (M : Model) (e : nat -> M) n,
  eval M e (numeral n) = numeralValue M n.
Proof.
  intros M e n.
  induction n as [|n IH]; simpl; congruence.
Qed.

Lemma numeralValue_natModel : forall n,
  numeralValue natModel n = n.
Proof.
  intro n.
  induction n as [|n IH]; simpl; congruence.
Qed.

Lemma eval_numeral_natModel : forall (e : nat -> nat) n,
  eval natModel e (numeral n) = n.
Proof.
  intros e n.
  rewrite eval_numeral.
  apply numeralValue_natModel.
Qed.

Fixpoint bound (t : term) : nat :=
  match t with
  | tVar n => S n
  | tZero => 0
  | tSucc a => bound a
  | tAdd a b => bound a + bound b
  | tMul a b => bound a + bound b
  end.

Fixpoint Free (n : nat) (t : term) : Prop :=
  match t with
  | tVar k => n = k
  | tZero => False
  | tSucc a => Free n a
  | tAdd a b => Free n a \/ Free n b
  | tMul a b => Free n a \/ Free n b
  end.

Lemma free_lt_bound : forall t n, Free n t -> n < bound t.
Proof.
  induction t; simpl; intros k hk.
  - subst k. lia.
  - contradiction.
  - apply IHt. exact hk.
  - destruct hk as [hk | hk].
    + pose proof (IHt1 k hk). lia.
    + pose proof (IHt2 k hk). lia.
  - destruct hk as [hk | hk].
    + pose proof (IHt1 k hk). lia.
    + pose proof (IHt2 k hk). lia.
Qed.

Lemma eval_ext : forall (M : Model) (t : term) (e e' : nat -> M),
  (forall n, e n = e' n) -> eval M e t = eval M e' t.
Proof.
  intros M t.
  induction t; simpl; intros e e' h; try reflexivity.
  - apply h.
  - now rewrite (IHt e e' h).
  - now rewrite (IHt1 e e' h), (IHt2 e e' h).
  - now rewrite (IHt1 e e' h), (IHt2 e e' h).
Qed.

Lemma eval_ext_free : forall (M : Model) (t : term) (e e' : nat -> M),
  (forall n, Free n t -> e n = e' n) -> eval M e t = eval M e' t.
Proof.
  intros M t.
  induction t; simpl; intros e e' h; try reflexivity.
  - apply h. reflexivity.
  - now rewrite (IHt e e' h).
  - rewrite (IHt1 e e' (fun n hn => h n (or_introl hn))).
    rewrite (IHt2 e e' (fun n hn => h n (or_intror hn))).
    reflexivity.
  - rewrite (IHt1 e e' (fun n hn => h n (or_introl hn))).
    rewrite (IHt2 e e' (fun n hn => h n (or_intror hn))).
    reflexivity.
Qed.

Lemma eval_rename : forall (M : Model) (t : term)
    (r : nat -> nat) (e : nat -> M),
  eval M e (rename r t) = eval M (fun n => e (r n)) t.
Proof.
  intros M t.
  induction t; simpl; intros r e; try reflexivity.
  - now rewrite (IHt r e).
  - now rewrite (IHt1 r e), (IHt2 r e).
  - now rewrite (IHt1 r e), (IHt2 r e).
Qed.

Lemma rename_ext : forall t (r r' : nat -> nat),
  (forall n, r n = r' n) -> rename r t = rename r' t.
Proof.
  induction t; simpl; intros r r' h; try reflexivity.
  - now rewrite h.
  - now rewrite (IHt r r' h).
  - now rewrite (IHt1 r r' h), (IHt2 r r' h).
  - now rewrite (IHt1 r r' h), (IHt2 r r' h).
Qed.

Lemma rename_comp : forall t (r r' : nat -> nat),
  rename r (rename r' t) = rename (fun n => r (r' n)) t.
Proof.
  induction t; simpl; intros r r'; try reflexivity.
  - now rewrite (IHt r r').
  - now rewrite (IHt1 r r'), (IHt2 r r').
  - now rewrite (IHt1 r r'), (IHt2 r r').
Qed.

Lemma eval_upSubst : forall (M : Model) (sigma : nat -> term)
    (e : nat -> M) (d : M) n,
  eval M (scons M d e) (upSubst sigma n) =
    scons M d (fun k => eval M e (sigma k)) n.
Proof.
  intros M sigma e d [|n]; simpl.
  - reflexivity.
  - rewrite eval_rename. reflexivity.
Qed.

Lemma eval_subst : forall (M : Model) (t : term)
    (sigma : nat -> term) (e : nat -> M),
  eval M e (subst sigma t) =
    eval M (fun n => eval M e (sigma n)) t.
Proof.
  intros M t.
  induction t; simpl; intros sigma e; try reflexivity.
  - now rewrite (IHt sigma e).
  - now rewrite (IHt1 sigma e), (IHt2 sigma e).
  - now rewrite (IHt1 sigma e), (IHt2 sigma e).
Qed.

Lemma subst_ext : forall t (sigma tau : nat -> term),
  (forall n, sigma n = tau n) -> subst sigma t = subst tau t.
Proof.
  induction t; simpl; intros sigma tau h; try reflexivity.
  - apply h.
  - now rewrite (IHt sigma tau h).
  - now rewrite (IHt1 sigma tau h), (IHt2 sigma tau h).
  - now rewrite (IHt1 sigma tau h), (IHt2 sigma tau h).
Qed.

Lemma subst_rename : forall t (sigma : nat -> term) (r : nat -> nat),
  subst sigma (rename r t) = subst (fun n => sigma (r n)) t.
Proof.
  induction t; simpl; intros sigma r; try reflexivity.
  - now rewrite (IHt sigma r).
  - now rewrite (IHt1 sigma r), (IHt2 sigma r).
  - now rewrite (IHt1 sigma r), (IHt2 sigma r).
Qed.

Lemma rename_subst : forall t (r : nat -> nat) (sigma : nat -> term),
  rename r (subst sigma t) =
    subst (fun n => rename r (sigma n)) t.
Proof.
  induction t; simpl; intros r sigma; try reflexivity.
  - now rewrite (IHt r sigma).
  - now rewrite (IHt1 r sigma), (IHt2 r sigma).
  - now rewrite (IHt1 r sigma), (IHt2 r sigma).
Qed.

End Term.

Module Formula.

Definition iffForm (a b : formula) : formula :=
  pAnd (pImp a b) (pImp b a).

Fixpoint rename (r : nat -> nat) (phi : formula) : formula :=
  match phi with
  | pEq a b => pEq (Term.rename r a) (Term.rename r b)
  | pBot => pBot
  | pImp a b => pImp (rename r a) (rename r b)
  | pAnd a b => pAnd (rename r a) (rename r b)
  | pOr a b => pOr (rename r a) (rename r b)
  | pAll a => pAll (rename (up r) a)
  | pEx a => pEx (rename (up r) a)
  end.

Fixpoint subst (sigma : nat -> term) (phi : formula) : formula :=
  match phi with
  | pEq a b => pEq (Term.subst sigma a) (Term.subst sigma b)
  | pBot => pBot
  | pImp a b => pImp (subst sigma a) (subst sigma b)
  | pAnd a b => pAnd (subst sigma a) (subst sigma b)
  | pOr a b => pOr (subst sigma a) (subst sigma b)
  | pAll a => pAll (subst (Term.upSubst sigma) a)
  | pEx a => pEx (subst (Term.upSubst sigma) a)
  end.

Fixpoint Sat (M : Model) (e : nat -> M) (phi : formula) : Prop :=
  match phi with
  | pEq a b => Term.eval M e a = Term.eval M e b
  | pBot => False
  | pImp a b => Sat M e a -> Sat M e b
  | pAnd a b => Sat M e a /\ Sat M e b
  | pOr a b => Sat M e a \/ Sat M e b
  | pAll a => forall d, Sat M (scons M d e) a
  | pEx a => exists d, Sat M (scons M d e) a
  end.

Lemma Sat_iffForm : forall (M : Model) (e : nat -> M) a b,
  Sat M e (iffForm a b) <-> (Sat M e a <-> Sat M e b).
Proof.
  intros M e a b.
  unfold iffForm. simpl. tauto.
Qed.

Fixpoint bound (phi : formula) : nat :=
  match phi with
  | pEq a b => Term.bound a + Term.bound b
  | pBot => 0
  | pImp a b => bound a + bound b
  | pAnd a b => bound a + bound b
  | pOr a b => bound a + bound b
  | pAll a => bound a
  | pEx a => bound a
  end.

Fixpoint Free (n : nat) (phi : formula) : Prop :=
  match phi with
  | pEq a b => Term.Free n a \/ Term.Free n b
  | pBot => False
  | pImp a b => Free n a \/ Free n b
  | pAnd a b => Free n a \/ Free n b
  | pOr a b => Free n a \/ Free n b
  | pAll a => Free (S n) a
  | pEx a => Free (S n) a
  end.

Definition Sentence (phi : formula) : Prop := forall n, ~ Free n phi.

Lemma free_lt_bound : forall phi n, Free n phi -> n < bound phi.
Proof.
  induction phi; simpl; intros k hk.
  - destruct hk as [hk | hk].
    + pose proof (Term.free_lt_bound t k hk). lia.
    + pose proof (Term.free_lt_bound t0 k hk). lia.
  - contradiction.
  - destruct hk as [hk | hk].
    + pose proof (IHphi1 k hk). lia.
    + pose proof (IHphi2 k hk). lia.
  - destruct hk as [hk | hk].
    + pose proof (IHphi1 k hk). lia.
    + pose proof (IHphi2 k hk). lia.
  - destruct hk as [hk | hk].
    + pose proof (IHphi1 k hk). lia.
    + pose proof (IHphi2 k hk). lia.
  - pose proof (IHphi (S k) hk). lia.
  - pose proof (IHphi (S k) hk). lia.
Qed.

Fixpoint closeN (k : nat) (phi : formula) : formula :=
  match k with
  | 0 => phi
  | S n => closeN n (pAll phi)
  end.

Definition sealPA (phi : formula) : formula := closeN (bound phi) phi.

Lemma Free_closeN : forall k phi n,
  Free n (closeN k phi) -> Free (k + n) phi.
Proof.
  induction k as [|k IH]; simpl; intros phi n h.
  - exact h.
  - pose proof (IH (pAll phi) n h) as h'.
    simpl in h'.
    exact h'.
Qed.

Lemma sealPA_sentence : forall phi, Sentence (sealPA phi).
Proof.
  unfold Sentence, sealPA.
  intros phi n h.
  pose proof (Free_closeN (bound phi) phi n h) as hfree.
  pose proof (free_lt_bound phi (bound phi + n) hfree) as hlt.
  lia.
Qed.

Lemma Sat_ext : forall (M : Model) phi (e e' : nat -> M),
  (forall n, e n = e' n) -> Sat M e phi <-> Sat M e' phi.
Proof.
  intros M phi.
  induction phi; simpl; intros e e' h.
  - rewrite (Term.eval_ext M t e e' h).
    rewrite (Term.eval_ext M t0 e e' h).
    reflexivity.
  - reflexivity.
  - split; intros hp hi.
    + apply (proj1 (IHphi2 e e' h)).
      apply hp.
      apply (proj2 (IHphi1 e e' h)).
      exact hi.
    + apply (proj2 (IHphi2 e e' h)).
      apply hp.
      apply (proj1 (IHphi1 e e' h)).
      exact hi.
  - split; intros [ha hb].
    + split.
      * apply (proj1 (IHphi1 e e' h)); exact ha.
      * apply (proj1 (IHphi2 e e' h)); exact hb.
    + split.
      * apply (proj2 (IHphi1 e e' h)); exact ha.
      * apply (proj2 (IHphi2 e e' h)); exact hb.
  - split; intros hp.
    + destruct hp as [ha | hb].
      * left. apply (proj1 (IHphi1 e e' h)); exact ha.
      * right. apply (proj1 (IHphi2 e e' h)); exact hb.
    + destruct hp as [ha | hb].
      * left. apply (proj2 (IHphi1 e e' h)); exact ha.
      * right. apply (proj2 (IHphi2 e e' h)); exact hb.
  - split; intros hall d.
    + apply (proj1 (IHphi (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => h k end))).
      exact (hall d).
    + apply (proj2 (IHphi (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => h k end))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      apply (proj1 (IHphi (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => h k end))).
      exact hd.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHphi (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => h k end))).
      exact hd.
Qed.

Lemma Sat_ext_free : forall (M : Model) phi (e e' : nat -> M),
  (forall n, Free n phi -> e n = e' n) -> Sat M e phi <-> Sat M e' phi.
Proof.
  intros M phi.
  induction phi; simpl; intros e e' h.
  - rewrite (Term.eval_ext_free M t e e'
      (fun n hn => h n (or_introl hn))).
    rewrite (Term.eval_ext_free M t0 e e'
      (fun n hn => h n (or_intror hn))).
    reflexivity.
  - reflexivity.
  - split; intros hp hi.
    + apply (proj1 (IHphi2 e e' (fun n hn => h n (or_intror hn)))).
      apply hp.
      apply (proj2 (IHphi1 e e' (fun n hn => h n (or_introl hn)))).
      exact hi.
    + apply (proj2 (IHphi2 e e' (fun n hn => h n (or_intror hn)))).
      apply hp.
      apply (proj1 (IHphi1 e e' (fun n hn => h n (or_introl hn)))).
      exact hi.
  - split; intros [ha hb].
    + split.
      * apply (proj1 (IHphi1 e e' (fun n hn => h n (or_introl hn)))).
        exact ha.
      * apply (proj1 (IHphi2 e e' (fun n hn => h n (or_intror hn)))).
        exact hb.
    + split.
      * apply (proj2 (IHphi1 e e' (fun n hn => h n (or_introl hn)))).
        exact ha.
      * apply (proj2 (IHphi2 e e' (fun n hn => h n (or_intror hn)))).
        exact hb.
  - split; intros hp.
    + destruct hp as [ha | hb].
      * left. apply (proj1 (IHphi1 e e'
          (fun n hn => h n (or_introl hn)))); exact ha.
      * right. apply (proj1 (IHphi2 e e'
          (fun n hn => h n (or_intror hn)))); exact hb.
    + destruct hp as [ha | hb].
      * left. apply (proj2 (IHphi1 e e'
          (fun n hn => h n (or_introl hn)))); exact ha.
      * right. apply (proj2 (IHphi2 e e'
          (fun n hn => h n (or_intror hn)))); exact hb.
  - split; intros hall d.
    + assert (henv : forall n, Free n phi ->
        scons M d e n = scons M d e' n).
      {
        intros [|k] hk; simpl.
        - reflexivity.
        - apply h. exact hk.
      }
      apply (proj1 (IHphi (scons M d e) (scons M d e') henv)).
      exact (hall d).
    + assert (henv : forall n, Free n phi ->
        scons M d e n = scons M d e' n).
      {
        intros [|k] hk; simpl.
        - reflexivity.
        - apply h. exact hk.
      }
      apply (proj2 (IHphi (scons M d e) (scons M d e') henv)).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      assert (henv : forall n, Free n phi ->
        scons M d e n = scons M d e' n).
      {
        intros [|k] hk; simpl.
        - reflexivity.
        - apply h. exact hk.
      }
      apply (proj1 (IHphi (scons M d e) (scons M d e') henv)).
      exact hd.
    + destruct hex as [d hd].
      exists d.
      assert (henv : forall n, Free n phi ->
        scons M d e n = scons M d e' n).
      {
        intros [|k] hk; simpl.
        - reflexivity.
        - apply h. exact hk.
      }
      apply (proj2 (IHphi (scons M d e) (scons M d e') henv)).
      exact hd.
Qed.

Lemma Sat_subst : forall (M : Model) phi (sigma : nat -> term)
    (e : nat -> M),
  Sat M e (subst sigma phi) <->
    Sat M (fun n => Term.eval M e (sigma n)) phi.
Proof.
  intros M phi.
  induction phi; simpl; intros sigma e.
  - rewrite (Term.eval_subst M t sigma e).
    rewrite (Term.eval_subst M t0 sigma e).
    reflexivity.
  - reflexivity.
  - split; intros hp hi.
    + apply (proj1 (IHphi2 sigma e)).
      apply hp.
      apply (proj2 (IHphi1 sigma e)).
      exact hi.
    + apply (proj2 (IHphi2 sigma e)).
      apply hp.
      apply (proj1 (IHphi1 sigma e)).
      exact hi.
  - split; intros [ha hb].
    + split.
      * apply (proj1 (IHphi1 sigma e)); exact ha.
      * apply (proj1 (IHphi2 sigma e)); exact hb.
    + split.
      * apply (proj2 (IHphi1 sigma e)); exact ha.
      * apply (proj2 (IHphi2 sigma e)); exact hb.
  - split; intros hp.
    + destruct hp as [ha | hb].
      * left. apply (proj1 (IHphi1 sigma e)); exact ha.
      * right. apply (proj1 (IHphi2 sigma e)); exact hb.
    + destruct hp as [ha | hb].
      * left. apply (proj2 (IHphi1 sigma e)); exact ha.
      * right. apply (proj2 (IHphi2 sigma e)); exact hb.
  - split; intros hall d.
    + pose proof (proj1 (IHphi (Term.upSubst sigma) (scons M d e))
        (hall d)) as hbody.
      apply (proj1 (Sat_ext M phi
        (fun n => Term.eval M (scons M d e) (Term.upSubst sigma n))
        (scons M d (fun k => Term.eval M e (sigma k)))
        (fun n => Term.eval_upSubst M sigma e d n))).
      exact hbody.
    + pose proof (proj2 (Sat_ext M phi
        (fun n => Term.eval M (scons M d e) (Term.upSubst sigma n))
        (scons M d (fun k => Term.eval M e (sigma k)))
        (fun n => Term.eval_upSubst M sigma e d n))
        (hall d)) as hbody.
      apply (proj2 (IHphi (Term.upSubst sigma) (scons M d e))).
      exact hbody.
  - split; intros hex.
    + destruct hex as [d hd].
      pose proof (proj1 (IHphi (Term.upSubst sigma) (scons M d e))
        hd) as hbody.
      exists d.
      apply (proj1 (Sat_ext M phi
        (fun n => Term.eval M (scons M d e) (Term.upSubst sigma n))
        (scons M d (fun k => Term.eval M e (sigma k)))
        (fun n => Term.eval_upSubst M sigma e d n))).
      exact hbody.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj2 (Sat_ext M phi
        (fun n => Term.eval M (scons M d e) (Term.upSubst sigma n))
        (scons M d (fun k => Term.eval M e (sigma k)))
        (fun n => Term.eval_upSubst M sigma e d n))
        hd) as hbody.
      apply (proj2 (IHphi (Term.upSubst sigma) (scons M d e))).
      exact hbody.
Qed.

Lemma closeN_valid : forall (M : Model) k phi,
  (forall e : nat -> M, Sat M e (closeN k phi)) <->
    (forall e, Sat M e phi).
Proof.
  intros M k.
  induction k as [|k IH]; intros phi.
  - reflexivity.
  - simpl.
    rewrite (IH (pAll phi)).
    split.
    + intros h e'.
      assert (pf : forall n,
          scons M (e' 0) (fun n => e' (S n)) n = e' n).
      {
        intros [|n]; reflexivity.
      }
      apply (proj1 (Sat_ext M phi
        (scons M (e' 0) (fun n => e' (S n))) e' pf)).
      exact (h (fun n => e' (S n)) (e' 0)).
    + intros h e d.
      exact (h (scons M d e)).
Qed.

Lemma seal_valid : forall (M : Model) phi,
  (forall e : nat -> M, Sat M e (sealPA phi)) <->
    (forall e, Sat M e phi).
Proof.
  intros M phi.
  unfold sealPA.
  apply closeN_valid.
Qed.

Definition instTerm (t : term) : nat -> term :=
  fun n =>
    match n with
    | 0 => t
    | S k => tVar k
    end.

Lemma Sat_rename : forall (M : Model) phi
    (r : nat -> nat) (e : nat -> M),
  Sat M e (rename r phi) <-> Sat M (fun n => e (r n)) phi.
Proof.
  intros M phi.
  induction phi; simpl; intros r e.
  - rewrite (Term.eval_rename M t r e).
    rewrite (Term.eval_rename M t0 r e).
    reflexivity.
  - reflexivity.
  - split; intros hp hi.
    + apply (proj1 (IHphi2 r e)).
      apply hp.
      apply (proj2 (IHphi1 r e)).
      exact hi.
    + apply (proj2 (IHphi2 r e)).
      apply hp.
      apply (proj1 (IHphi1 r e)).
      exact hi.
  - split; intros [ha hb].
    + split.
      * apply (proj1 (IHphi1 r e)); exact ha.
      * apply (proj1 (IHphi2 r e)); exact hb.
    + split.
      * apply (proj2 (IHphi1 r e)); exact ha.
      * apply (proj2 (IHphi2 r e)); exact hb.
  - split; intros hp.
    + destruct hp as [ha | hb].
      * left. apply (proj1 (IHphi1 r e)); exact ha.
      * right. apply (proj1 (IHphi2 r e)); exact hb.
    + destruct hp as [ha | hb].
      * left. apply (proj2 (IHphi1 r e)); exact ha.
      * right. apply (proj2 (IHphi2 r e)); exact hb.
  - split; intros hall d.
    + pose proof (proj1 (IHphi (up r) (scons M d e))
        (hall d)) as hbody.
      apply (proj1 (Sat_ext M phi
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact hbody.
    + pose proof (proj2 (Sat_ext M phi
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))
        (hall d)) as hbody.
      apply (proj2 (IHphi (up r) (scons M d e))).
      exact hbody.
  - split; intros hex.
    + destruct hex as [d hd].
      pose proof (proj1 (IHphi (up r) (scons M d e))
        hd) as hbody.
      exists d.
      apply (proj1 (Sat_ext M phi
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact hbody.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj2 (Sat_ext M phi
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))
        hd) as hbody.
      apply (proj2 (IHphi (up r) (scons M d e))).
      exact hbody.
Qed.

Lemma Sat_rename_succ : forall (M : Model) phi
    (e : nat -> M) (d : M),
  Sat M (scons M d e) (rename S phi) <-> Sat M e phi.
Proof.
  intros M phi e d.
  eapply iff_trans.
  - apply Sat_rename.
  - apply Sat_ext.
    intro n. reflexivity.
Qed.

Lemma rename_ext : forall phi (r r' : nat -> nat),
  (forall n, r n = r' n) -> rename r phi = rename r' phi.
Proof.
  induction phi; simpl; intros r r' h; try reflexivity.
  - rewrite (Term.rename_ext t r r' h).
    rewrite (Term.rename_ext t0 r r' h).
    reflexivity.
  - now rewrite (IHphi1 r r' h), (IHphi2 r r' h).
  - now rewrite (IHphi1 r r' h), (IHphi2 r r' h).
  - now rewrite (IHphi1 r r' h), (IHphi2 r r' h).
  - rewrite (IHphi (up r) (up r')).
    + reflexivity.
    + intros [|n]; simpl; [reflexivity | now rewrite h].
  - rewrite (IHphi (up r) (up r')).
    + reflexivity.
    + intros [|n]; simpl; [reflexivity | now rewrite h].
Qed.

Lemma rename_comp : forall phi (r r' : nat -> nat),
  rename r (rename r' phi) = rename (fun n => r (r' n)) phi.
Proof.
  induction phi; simpl; intros r r'; try reflexivity.
  - now rewrite !Term.rename_comp.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - rewrite (IHphi (up r) (up r')).
    apply f_equal.
    apply rename_ext.
    intros [|n]; reflexivity.
  - rewrite (IHphi (up r) (up r')).
    apply f_equal.
    apply rename_ext.
    intros [|n]; reflexivity.
Qed.

Lemma rename_up_succ : forall phi (r : nat -> nat),
  rename (up r) (rename S phi) = rename S (rename r phi).
Proof.
  intros phi r.
  rewrite !rename_comp.
  apply rename_ext.
  intro n. reflexivity.
Qed.

Lemma subst_ext : forall phi (sigma tau : nat -> term),
  (forall n, sigma n = tau n) -> subst sigma phi = subst tau phi.
Proof.
  induction phi; simpl; intros sigma tau h; try reflexivity.
  - rewrite (Term.subst_ext t sigma tau h).
    rewrite (Term.subst_ext t0 sigma tau h).
    reflexivity.
  - now rewrite (IHphi1 sigma tau h), (IHphi2 sigma tau h).
  - now rewrite (IHphi1 sigma tau h), (IHphi2 sigma tau h).
  - now rewrite (IHphi1 sigma tau h), (IHphi2 sigma tau h).
  - rewrite (IHphi (Term.upSubst sigma) (Term.upSubst tau)).
    + reflexivity.
    + intros [|n]; simpl; [reflexivity | now rewrite h].
  - rewrite (IHphi (Term.upSubst sigma) (Term.upSubst tau)).
    + reflexivity.
    + intros [|n]; simpl; [reflexivity | now rewrite h].
Qed.

Lemma subst_rename : forall phi (sigma : nat -> term) (r : nat -> nat),
  subst sigma (rename r phi) = subst (fun n => sigma (r n)) phi.
Proof.
  induction phi; simpl; intros sigma r; try reflexivity.
  - now rewrite !Term.subst_rename.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - rewrite (IHphi (Term.upSubst sigma) (up r)).
    apply f_equal.
    apply subst_ext.
    intros [|n]; reflexivity.
  - rewrite (IHphi (Term.upSubst sigma) (up r)).
    apply f_equal.
    apply subst_ext.
    intros [|n]; reflexivity.
Qed.

Lemma rename_subst : forall phi (r : nat -> nat) (sigma : nat -> term),
  rename r (subst sigma phi) =
    subst (fun n => Term.rename r (sigma n)) phi.
Proof.
  induction phi; simpl; intros r sigma; try reflexivity.
  - now rewrite !Term.rename_subst.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - now rewrite IHphi1, IHphi2.
  - rewrite (IHphi (up r) (Term.upSubst sigma)).
    apply f_equal.
    apply subst_ext.
    intros [|n]; simpl.
    + reflexivity.
    + rewrite !Term.rename_comp.
      apply Term.rename_ext.
      intro k. reflexivity.
  - rewrite (IHphi (up r) (Term.upSubst sigma)).
    apply f_equal.
    apply subst_ext.
    intros [|n]; simpl.
    + reflexivity.
    + rewrite !Term.rename_comp.
      apply Term.rename_ext.
      intro k. reflexivity.
Qed.

Lemma subst_instTerm_rename_up : forall phi (r : nat -> nat) t,
  subst (instTerm (Term.rename r t)) (rename (up r) phi) =
    rename r (subst (instTerm t) phi).
Proof.
  intros phi r t.
  rewrite subst_rename.
  rewrite rename_subst.
  apply subst_ext.
  intros [|n]; reflexivity.
Qed.

Lemma Sat_instTerm : forall (M : Model) phi t (e : nat -> M),
  Sat M e (subst (instTerm t) phi) <->
    Sat M (scons M (Term.eval M e t) e) phi.
Proof.
  intros M phi t e.
  eapply iff_trans.
  - apply Sat_subst.
  - apply Sat_ext.
    intros [|n]; reflexivity.
Qed.

Inductive Prov : list formula -> formula -> Prop :=
| P_ass : forall G a, In a G -> Prov G a
| P_impI : forall G a b, Prov (a :: G) b -> Prov G (pImp a b)
| P_impE : forall G a b, Prov G (pImp a b) -> Prov G a -> Prov G b
| P_botE : forall G a, Prov G pBot -> Prov G a
| P_lem : forall G a, Prov G (pOr a (pImp a pBot))
| P_andI : forall G a b, Prov G a -> Prov G b -> Prov G (pAnd a b)
| P_andE1 : forall G a b, Prov G (pAnd a b) -> Prov G a
| P_andE2 : forall G a b, Prov G (pAnd a b) -> Prov G b
| P_orI1 : forall G a b, Prov G a -> Prov G (pOr a b)
| P_orI2 : forall G a b, Prov G b -> Prov G (pOr a b)
| P_orE : forall G a b c,
    Prov G (pOr a b) ->
    Prov (a :: G) c ->
    Prov (b :: G) c ->
    Prov G c
| P_allI : forall G a,
    Prov (map (rename S) G) a ->
    Prov G (pAll a)
| P_allE : forall G a t,
    Prov G (pAll a) ->
    Prov G (subst (instTerm t) a)
| P_exI : forall G a t,
    Prov G (subst (instTerm t) a) ->
    Prov G (pEx a)
| P_exE : forall G a c,
    Prov G (pEx a) ->
    Prov (a :: map (rename S) G) (rename S c) ->
    Prov G c
| P_eqRefl : forall G t, Prov G (pEq t t)
| P_eqElim : forall G s t a,
    Prov G (pEq s t) ->
    Prov G (subst (instTerm s) a) ->
    Prov G (subst (instTerm t) a).

Lemma cons_sub : forall (a : formula) (G G' : list formula),
  (forall x, In x G -> In x G') ->
  forall x, In x (a :: G) -> In x (a :: G').
Proof.
  intros a G G' hsub x hx.
  simpl in hx |- *.
  destruct hx as [hx | hx].
  - left. exact hx.
  - right. exact (hsub x hx).
Qed.

Lemma mem_map_sub : forall (f : formula -> formula) (G G' : list formula),
  (forall x, In x G -> In x G') ->
  forall x, In x (map f G) -> In x (map f G').
Proof.
  intros f G G' hsub x hx.
  apply in_map_iff in hx.
  destruct hx as [y [hy hx]].
  subst x.
  apply in_map.
  exact (hsub y hx).
Qed.

Lemma Prov_weaken : forall G a,
  Prov G a ->
  forall G', (forall x, In x G -> In x G') -> Prov G' a.
Proof.
  intros G a h.
  induction h; intros G' hsub.
  - exact (P_ass G' a (hsub a H)).
  - exact (P_impI G' a b (IHh (a :: G') (cons_sub a G G' hsub))).
  - exact (P_impE G' a b (IHh1 G' hsub) (IHh2 G' hsub)).
  - exact (P_botE G' a (IHh G' hsub)).
  - exact (P_lem G' a).
  - exact (P_andI G' a b (IHh1 G' hsub) (IHh2 G' hsub)).
  - exact (P_andE1 G' a b (IHh G' hsub)).
  - exact (P_andE2 G' a b (IHh G' hsub)).
  - exact (P_orI1 G' a b (IHh G' hsub)).
  - exact (P_orI2 G' a b (IHh G' hsub)).
  - exact (P_orE G' a b c (IHh1 G' hsub)
      (IHh2 (a :: G') (cons_sub a G G' hsub))
      (IHh3 (b :: G') (cons_sub b G G' hsub))).
  - exact (P_allI G' a (IHh (map (rename S) G')
      (mem_map_sub (rename S) G G' hsub))).
  - exact (P_allE G' a t (IHh G' hsub)).
  - exact (P_exI G' a t (IHh G' hsub)).
  - exact (P_exE G' a c (IHh1 G' hsub)
      (IHh2 (a :: map (rename S) G')
        (cons_sub a (map (rename S) G) (map (rename S) G')
          (mem_map_sub (rename S) G G' hsub)))).
  - exact (P_eqRefl G' t).
  - exact (P_eqElim G' s t a (IHh1 G' hsub) (IHh2 G' hsub)).
Qed.

Lemma Prov_cons : forall G a b,
  Prov G b -> Prov (a :: G) b.
Proof.
  intros G a b h.
  apply (Prov_weaken G b h).
  intros x hx.
  simpl. right. exact hx.
Qed.

Lemma map_rename_up_succ : forall (r : nat -> nat) G,
  map (rename (up r)) (map (rename S) G) =
    map (rename S) (map (rename r) G).
Proof.
  intros r G.
  induction G as [|phi G IH]; simpl.
  - reflexivity.
  - rewrite rename_up_succ.
    rewrite IH.
    reflexivity.
Qed.

Lemma Prov_rename : forall G phi,
  Prov G phi -> forall r,
  Prov (map (rename r) G) (rename r phi).
Proof.
  intros G phi h.
  induction h; intro r; simpl.
  - apply P_ass.
    apply in_map.
    exact H.
  - apply P_impI.
    exact (IHh r).
  - exact (P_impE (map (rename r) G) (rename r a) (rename r b)
      (IHh1 r) (IHh2 r)).
  - exact (P_botE (map (rename r) G) (rename r a) (IHh r)).
  - exact (P_lem (map (rename r) G) (rename r a)).
  - exact (P_andI (map (rename r) G) (rename r a) (rename r b)
      (IHh1 r) (IHh2 r)).
  - exact (P_andE1 (map (rename r) G) (rename r a) (rename r b)
      (IHh r)).
  - exact (P_andE2 (map (rename r) G) (rename r a) (rename r b)
      (IHh r)).
  - exact (P_orI1 (map (rename r) G) (rename r a) (rename r b)
      (IHh r)).
  - exact (P_orI2 (map (rename r) G) (rename r a) (rename r b)
      (IHh r)).
  - exact (P_orE (map (rename r) G) (rename r a) (rename r b)
      (rename r c) (IHh1 r) (IHh2 r) (IHh3 r)).
  - apply P_allI.
    rewrite <- map_rename_up_succ.
    exact (IHh (up r)).
  - rewrite <- subst_instTerm_rename_up.
    exact (P_allE (map (rename r) G) (rename (up r) a)
      (Term.rename r t) (IHh r)).
  - apply (P_exI (map (rename r) G) (rename (up r) a)
      (Term.rename r t)).
    rewrite subst_instTerm_rename_up.
    exact (IHh r).
  - assert (hEx : Prov (map (rename r) G) (pEx (rename (up r) a))).
    {
      exact (IHh1 r).
    }
    assert (hbody :
        Prov (rename (up r) a :: map (rename S) (map (rename r) G))
          (rename S (rename r c))).
    {
      rewrite <- map_rename_up_succ.
      rewrite <- rename_up_succ.
      change (Prov (map (rename (up r)) (a :: map (rename S) G))
        (rename (up r) (rename S c))).
      exact (IHh2 (up r)).
    }
    exact (P_exE (map (rename r) G) (rename (up r) a) (rename r c)
      hEx hbody).
  - exact (P_eqRefl (map (rename r) G) (Term.rename r t)).
  - assert (hEq :
        Prov (map (rename r) G)
          (pEq (Term.rename r s) (Term.rename r t))).
    {
      exact (IHh1 r).
    }
    assert (hA :
        Prov (map (rename r) G)
          (subst (instTerm (Term.rename r s)) (rename (up r) a))).
    {
      rewrite subst_instTerm_rename_up.
      exact (IHh2 r).
    }
    pose proof (P_eqElim (map (rename r) G)
      (Term.rename r s) (Term.rename r t) (rename (up r) a)
      hEq hA) as hElim.
    rewrite subst_instTerm_rename_up in hElim.
    exact hElim.
Qed.

Lemma Prov_cut : forall G phi,
  Prov G phi ->
  forall De, (forall x, In x G -> Prov De x) -> Prov De phi.
Proof.
  intros G phi h.
  induction h; intros De hD.
  - exact (hD a H).
  - apply P_impI.
    apply IHh.
    intros x hx.
    simpl in hx.
    destruct hx as [hx | hx].
    + subst x.
      apply P_ass. simpl. left. reflexivity.
    + apply Prov_cons.
      exact (hD x hx).
  - exact (P_impE De a b (IHh1 De hD) (IHh2 De hD)).
  - exact (P_botE De a (IHh De hD)).
  - exact (P_lem De a).
  - exact (P_andI De a b (IHh1 De hD) (IHh2 De hD)).
  - exact (P_andE1 De a b (IHh De hD)).
  - exact (P_andE2 De a b (IHh De hD)).
  - exact (P_orI1 De a b (IHh De hD)).
  - exact (P_orI2 De a b (IHh De hD)).
  - apply (P_orE De a b c (IHh1 De hD)).
    + apply IHh2.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x.
        apply P_ass. simpl. left. reflexivity.
      * apply Prov_cons.
        exact (hD x hx).
    + apply IHh3.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x.
        apply P_ass. simpl. left. reflexivity.
      * apply Prov_cons.
        exact (hD x hx).
  - apply P_allI.
    apply IHh.
    intros x hx.
    apply in_map_iff in hx.
    destruct hx as [x0 [hx hx0]].
    subst x.
    exact (Prov_rename De x0 (hD x0 hx0) S).
  - exact (P_allE De a t (IHh De hD)).
  - exact (P_exI De a t (IHh De hD)).
  - apply (P_exE De a c (IHh1 De hD)).
    apply IHh2.
    intros x hx.
    simpl in hx.
    destruct hx as [hx | hx].
    + subst x.
      apply P_ass. simpl. left. reflexivity.
    + apply in_map_iff in hx.
      destruct hx as [x0 [hx hx0]].
      subst x.
      apply Prov_cons.
      exact (Prov_rename De x0 (hD x0 hx0) S).
  - exact (P_eqRefl De t).
  - exact (P_eqElim De s t a (IHh1 De hD) (IHh2 De hD)).
Qed.

Lemma soundness : forall (M : Model) G a,
  Prov G a ->
  forall e : nat -> M, (forall x, In x G -> Sat M e x) -> Sat M e a.
Proof.
  intros M G a h.
  induction h; intros e hG; simpl.
  - exact (hG a H).
  - intros ha.
    apply IHh.
    intros x hx.
    simpl in hx.
    destruct hx as [hx | hx].
    + subst x. exact ha.
    + exact (hG x hx).
  - exact (IHh1 e hG (IHh2 e hG)).
  - exfalso. exact (IHh e hG).
  - destruct (classic (Sat M e a)) as [ha | hna].
    + left. exact ha.
    + right. exact hna.
  - split; [exact (IHh1 e hG) | exact (IHh2 e hG)].
  - exact (proj1 (IHh e hG)).
  - exact (proj2 (IHh e hG)).
  - left. exact (IHh e hG).
  - right. exact (IHh e hG).
  - destruct (IHh1 e hG) as [ha | hb].
    + apply IHh2.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact ha.
      * exact (hG x hx).
    + apply IHh3.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact hb.
      * exact (hG x hx).
  - intros d.
    apply IHh.
    intros x hx.
    apply in_map_iff in hx.
    destruct hx as [g [hg_eq hg]].
    subst x.
    apply (proj2 (Sat_rename_succ M g e d)).
    exact (hG g hg).
  - apply (proj2 (Sat_instTerm M a t e)).
    exact (IHh e hG (Term.eval M e t)).
  - exists (Term.eval M e t).
    apply (proj1 (Sat_instTerm M a t e)).
    exact (IHh e hG).
  - destruct (IHh1 e hG) as [d hd].
    pose proof (IHh2 (scons M d e)) as hc_shift.
    assert (hctx : forall x, In x (a :: map (rename S) G) ->
      Sat M (scons M d e) x).
    {
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      - subst x. exact hd.
      - apply in_map_iff in hx.
        destruct hx as [g [hg_eq hg]].
        subst x.
        apply (proj2 (Sat_rename_succ M g e d)).
        exact (hG g hg).
    }
    apply (proj1 (Sat_rename_succ M c e d)).
    exact (hc_shift hctx).
  - reflexivity.
  - pose proof (IHh1 e hG) as heq.
    pose proof (proj1 (Sat_instTerm M a s e) (IHh2 e hG)) as hs.
    assert (henv : forall n,
      scons M (Term.eval M e s) e n =
        scons M (Term.eval M e t) e n).
    {
      intros [|n]; simpl.
      - exact heq.
      - reflexivity.
    }
    pose proof (proj1 (Sat_ext M a
      (scons M (Term.eval M e s) e)
      (scons M (Term.eval M e t) e) henv) hs) as ht.
    apply (proj2 (Sat_instTerm M a t e)).
    exact ht.
Qed.

Definition BProv (B : formula -> Prop) (G : list formula)
    (phi : formula) : Prop :=
  exists L, (forall x, In x L -> B x) /\ Prov (L ++ G) phi.

Lemma BProv_mono : forall (B : formula -> Prop) G G' phi,
  (forall x, In x G -> In x G') ->
  BProv B G phi -> BProv B G' phi.
Proof.
  intros B G G' phi hsub [L [hL hp]].
  exists L.
  split; [exact hL |].
  apply (Prov_weaken (L ++ G) phi hp).
  intros x hx.
  apply in_app_iff in hx.
  apply in_app_iff.
  destruct hx as [hx | hx].
  - left. exact hx.
  - right. exact (hsub x hx).
Qed.

Lemma BProv_ax : forall (B : formula -> Prop) G phi,
  B phi -> BProv B G phi.
Proof.
  intros B G phi hphi.
  exists [phi].
  split.
  - intros x hx.
    simpl in hx.
    destruct hx as [hx | hx]; [subst x; exact hphi | contradiction].
  - apply P_ass.
    simpl. left. reflexivity.
Qed.

Lemma BProv_of_Prov : forall (B : formula -> Prop) G phi,
  Prov G phi -> BProv B G phi.
Proof.
  intros B G phi h.
  exists [].
  split.
  - intros x hx. contradiction.
  - simpl. exact h.
Qed.

Lemma BProv_mp : forall (B : formula -> Prop) G a b,
  BProv B G (pImp a b) -> BProv B G a -> BProv B G b.
Proof.
  intros B G a b [L1 [hL1 hpimp]] [L2 [hL2 hpa]].
  exists (L1 ++ L2).
  split.
  - intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    + exact (hL1 x hx).
    + exact (hL2 x hx).
  - apply (P_impE ((L1 ++ L2) ++ G) a b).
    + apply (Prov_weaken (L1 ++ G) (pImp a b) hpimp).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. left. exact hx.
      * right. exact hx.
    + apply (Prov_weaken (L2 ++ G) a hpa).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. right. exact hx.
      * right. exact hx.
Qed.

Lemma BProv_bound_list : forall (B : formula -> Prop) D L,
  (forall x, In x L -> BProv B D x) ->
  exists Lb, (forall x, In x Lb -> B x) /\
    forall x, In x L -> Prov (Lb ++ D) x.
Proof.
  intros B D L.
  induction L as [|a L IH]; intro hL.
  - exists [].
    split.
    + intros x hx. contradiction.
    + intros x hx. contradiction.
  - destruct (hL a (or_introl eq_refl)) as [La [hLa hpa]].
    destruct (IH (fun x hx => hL x (or_intror hx))) as
      [Lb [hLb hpL]].
    exists (La ++ Lb).
    split.
    + intros x hx.
      apply in_app_iff in hx.
      destruct hx as [hx | hx].
      * exact (hLa x hx).
      * exact (hLb x hx).
    + intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x.
        apply (Prov_weaken (La ++ D) a hpa).
        intros y hy.
        apply in_app_iff in hy.
        apply in_app_iff.
        destruct hy as [hy | hy].
        -- left. apply in_app_iff. left. exact hy.
        -- right. exact hy.
      * apply (Prov_weaken (Lb ++ D) x (hpL x hx)).
        intros y hy.
        apply in_app_iff in hy.
        apply in_app_iff.
        destruct hy as [hy | hy].
        -- left. apply in_app_iff. right. exact hy.
        -- right. exact hy.
Qed.

Lemma BProv_lift : forall (B C : formula -> Prop) G D phi,
  BProv B G phi ->
  (forall b, B b -> BProv C D b) ->
  (forall g, In g G -> BProv C D g) ->
  BProv C D phi.
Proof.
  intros B C G D phi [Lb [hLb hp]] hB hG.
  assert (hctx : forall x, In x (Lb ++ G) -> BProv C D x).
  {
    intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    - exact (hB x (hLb x hx)).
    - exact (hG x hx).
  }
  destruct (BProv_bound_list C D (Lb ++ G) hctx) as
    [Lc [hLc hpctx]].
  exists Lc.
  split; [exact hLc |].
  exact (Prov_cut (Lb ++ G) phi hp (Lc ++ D) hpctx).
Qed.

Lemma BProv_cut : forall (B : formula -> Prop) G D phi,
  BProv B G phi ->
  (forall g, In g G -> BProv B D g) ->
  BProv B D phi.
Proof.
  intros B G D phi h hG.
  eapply BProv_lift.
  - exact h.
  - intros b hb.
    apply BProv_ax.
    exact hb.
  - exact hG.
Qed.

Lemma BProv_theory_mono : forall (B C : formula -> Prop) G phi,
  (forall b, B b -> C b) -> BProv B G phi -> BProv C G phi.
Proof.
  intros B C G phi hBC h.
  eapply BProv_lift.
  - exact h.
  - intros b hb.
    apply BProv_ax.
    exact (hBC b hb).
  - intros g hg.
    apply BProv_of_Prov.
    exact (P_ass G g hg).
Qed.

Lemma soundness_BProv : forall (M : Model) (B : formula -> Prop) G phi,
  BProv B G phi ->
  forall e : nat -> M,
  (forall b, B b -> Sat M e b) ->
  (forall g, In g G -> Sat M e g) ->
  Sat M e phi.
Proof.
  intros M B G phi [L [hL hp]] e hB hG.
  apply (soundness M (L ++ G) phi hp e).
  intros x hx.
  apply in_app_iff in hx.
  destruct hx as [hx | hx].
  - exact (hB x (hL x hx)).
  - exact (hG x hx).
Qed.

Definition substZero : nat -> term :=
  fun n =>
    match n with
    | 0 => tZero
    | S k => tVar k
    end.

Definition substZeroAt (p : nat) : nat -> term :=
  fun n =>
    if n <? p then tVar n
    else if n =? p then tZero
    else tVar (n - 1).

Lemma substZeroAt_lt : forall p n,
  n < p -> substZeroAt p n = tVar n.
Proof.
  intros p n h.
  unfold substZeroAt.
  destruct (Nat.ltb_spec n p); [reflexivity | lia].
Qed.

Lemma substZeroAt_eq : forall p,
  substZeroAt p p = tZero.
Proof.
  intro p.
  unfold substZeroAt.
  destruct (Nat.ltb_spec p p); [lia |].
  destruct (Nat.eqb_spec p p); [reflexivity | congruence].
Qed.

Lemma substZeroAt_gt : forall p n,
  p < n -> substZeroAt p n = tVar (n - 1).
Proof.
  intros p n h.
  unfold substZeroAt.
  destruct (Nat.ltb_spec n p); [lia |].
  destruct (Nat.eqb_spec n p); [lia | reflexivity].
Qed.

Lemma substZeroAt_zero :
  substZeroAt 0 = substZero.
Proof.
  apply functional_extensionality.
  intros [|n].
  - apply substZeroAt_eq.
  - unfold substZero.
    rewrite substZeroAt_gt; [|lia].
    f_equal.
    lia.
Qed.

Lemma upSubst_substZeroAt : forall p,
  Term.upSubst (substZeroAt p) = substZeroAt (S p).
Proof.
  intro p.
  apply functional_extensionality.
  intros [|n].
  - reflexivity.
  - simpl.
    destruct (lt_eq_lt_dec n p) as [[hlt | heq] | hgt].
    + rewrite (substZeroAt_lt p n hlt).
      rewrite (substZeroAt_lt (S p) (S n)); [reflexivity | lia].
    + subst n.
      rewrite substZeroAt_eq.
      rewrite substZeroAt_eq.
      reflexivity.
    + rewrite (substZeroAt_gt p n hgt).
      rewrite (substZeroAt_gt (S p) (S n)); [|lia].
      simpl.
      f_equal.
      lia.
Qed.

Definition substSuccVar : nat -> term :=
  fun n =>
    match n with
    | 0 => tSucc (tVar 0)
    | S k => tVar (S k)
    end.

Definition substSuccAt (p : nat) : nat -> term :=
  fun n => if n =? p then tSucc (tVar p) else tVar n.

Lemma substSuccAt_eq : forall p,
  substSuccAt p p = tSucc (tVar p).
Proof.
  intro p.
  unfold substSuccAt.
  destruct (Nat.eqb_spec p p); [reflexivity | congruence].
Qed.

Lemma substSuccAt_ne : forall p n,
  n <> p -> substSuccAt p n = tVar n.
Proof.
  intros p n h.
  unfold substSuccAt.
  destruct (Nat.eqb_spec n p); [congruence | reflexivity].
Qed.

Lemma substSuccAt_zero :
  substSuccAt 0 = substSuccVar.
Proof.
  apply functional_extensionality.
  intros [|n].
  - apply substSuccAt_eq.
  - apply substSuccAt_ne. lia.
Qed.

Lemma upSubst_substSuccAt : forall p,
  Term.upSubst (substSuccAt p) = substSuccAt (S p).
Proof.
  intro p.
  apply functional_extensionality.
  intros [|n].
  - reflexivity.
  - simpl.
    destruct (Nat.eq_dec n p) as [heq | hne].
    + subst n.
      rewrite substSuccAt_eq.
      rewrite substSuccAt_eq.
      reflexivity.
    + rewrite (substSuccAt_ne p n hne).
      rewrite (substSuccAt_ne (S p) (S n)); [reflexivity | lia].
Qed.

Definition succInj : formula :=
  pAll (pAll (pImp
    (pEq (tSucc (tVar 1)) (tSucc (tVar 0)))
    (pEq (tVar 1) (tVar 0)))).

Definition zeroNotSucc : formula :=
  pAll (pImp (pEq (tSucc (tVar 0)) tZero) pBot).

Definition addZero : formula :=
  pAll (pEq (tAdd (tVar 0) tZero) (tVar 0)).

Definition addSucc : formula :=
  pAll (pAll (pEq
    (tAdd (tVar 1) (tSucc (tVar 0)))
    (tSucc (tAdd (tVar 1) (tVar 0))))).

Definition mulZero : formula :=
  pAll (pEq (tMul (tVar 0) tZero) tZero).

Definition mulSucc : formula :=
  pAll (pAll (pEq
    (tMul (tVar 1) (tSucc (tVar 0)))
    (tAdd (tMul (tVar 1) (tVar 0)) (tVar 1)))).

Definition inductionForm (phi : formula) : formula :=
  pImp
    (pAnd (subst substZero phi)
      (pAll (pImp phi (subst substSuccVar phi))))
    (pAll phi).

Definition Ax (f : formula) : Prop :=
  f = succInj \/ f = zeroNotSucc \/
  f = addZero \/ f = addSucc \/
  f = mulZero \/ f = mulSucc \/
  exists phi, f = inductionForm phi.

Definition Ax_s (f : formula) : Prop :=
  f = sealPA succInj \/ f = sealPA zeroNotSucc \/
  f = sealPA addZero \/ f = sealPA addSucc \/
  f = sealPA mulZero \/ f = sealPA mulSucc \/
  exists phi, f = sealPA (inductionForm phi).

Lemma sentence_ax_s : forall f, Ax_s f -> Sentence f.
Proof.
  intros f hf.
  unfold Ax_s in hf.
  destruct hf as [hf | [hf | [hf | [hf | [hf | [hf | [phi hf]]]]]]];
    subst f; apply sealPA_sentence.
Qed.

Lemma Ax_s_succInj : Ax_s (sealPA succInj).
Proof.
  unfold Ax_s. now left.
Qed.

Lemma Ax_s_zeroNotSucc : Ax_s (sealPA zeroNotSucc).
Proof.
  unfold Ax_s. right. now left.
Qed.

Lemma Ax_s_addZero : Ax_s (sealPA addZero).
Proof.
  unfold Ax_s. right. right. now left.
Qed.

Lemma Ax_s_addSucc : Ax_s (sealPA addSucc).
Proof.
  unfold Ax_s. right. right. right. now left.
Qed.

Lemma Ax_s_mulZero : Ax_s (sealPA mulZero).
Proof.
  unfold Ax_s. right. right. right. right. now left.
Qed.

Lemma Ax_s_mulSucc : Ax_s (sealPA mulSucc).
Proof.
  unfold Ax_s. right. right. right. right. right. now left.
Qed.

Lemma Ax_s_induction : forall phi, Ax_s (sealPA (inductionForm phi)).
Proof.
  intro phi.
  unfold Ax_s.
  right. right. right. right. right. right.
  exists phi. reflexivity.
Qed.

Lemma sat_substZero : forall (M : Model) phi (e : nat -> M),
  Sat M e (subst substZero phi) <->
    Sat M (scons M (zero M) e) phi.
Proof.
  intros M phi e.
  eapply iff_trans.
  - apply Sat_subst.
  - apply Sat_ext.
    intros [|n]; reflexivity.
Qed.

Lemma sat_substSuccVar : forall (M : Model) phi (e : nat -> M) a,
  Sat M (scons M a e) (subst substSuccVar phi) <->
    Sat M (scons M (succ M a) e) phi.
Proof.
  intros M phi e a.
  eapply iff_trans.
  - apply Sat_subst.
  - apply Sat_ext.
    intros [|n]; reflexivity.
Qed.

Lemma sat_axiom : forall (M : Model) (e : nat -> M) f,
  Ax f -> Sat M e f.
Proof.
  intros M e f hf.
  unfold Ax in hf.
  destruct hf as [hf | [hf | [hf | [hf | [hf | [hf | [phi hf]]]]]]];
    subst f; simpl.
  - intros a b h.
    exact (succ_injective M a b h).
  - intros a h.
    exact (zero_not_succ M a h).
  - intro a.
    exact (add_zero M a).
  - intros a b.
    exact (add_succ M a b).
  - intro a.
    exact (mul_zero M a).
  - intros a b.
    exact (mul_succ M a b).
  - intros [hzero hstep] a.
    apply (induction_schema M (fun x => Sat M (scons M x e) phi)).
    + exact (proj1 (sat_substZero M phi e) hzero).
    + intros n ih.
      apply (proj1 (sat_substSuccVar M phi e n)).
      exact (hstep n ih).
Qed.

Lemma sat_axiom_s : forall (M : Model) (e : nat -> M) f,
  Ax_s f -> Sat M e f.
Proof.
  intros M e f hf.
  unfold Ax_s in hf.
  destruct hf as [hf | [hf | [hf | [hf | [hf | [hf | [phi hf]]]]]]];
    subst f.
  - exact (proj2 (seal_valid M succInj)
      (fun e0 => sat_axiom M e0 succInj (or_introl eq_refl)) e).
  - exact (proj2 (seal_valid M zeroNotSucc)
      (fun e0 => sat_axiom M e0 zeroNotSucc
        (or_intror (or_introl eq_refl))) e).
  - exact (proj2 (seal_valid M addZero)
      (fun e0 => sat_axiom M e0 addZero
        (or_intror (or_intror (or_introl eq_refl)))) e).
  - exact (proj2 (seal_valid M addSucc)
      (fun e0 => sat_axiom M e0 addSucc
        (or_intror (or_intror (or_intror (or_introl eq_refl))))) e).
  - exact (proj2 (seal_valid M mulZero)
      (fun e0 => sat_axiom M e0 mulZero
        (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) e).
  - exact (proj2 (seal_valid M mulSucc)
      (fun e0 => sat_axiom M e0 mulSucc
        (or_intror (or_intror (or_intror
          (or_intror (or_intror (or_introl eq_refl))))))) e).
  - exact (proj2 (seal_valid M (inductionForm phi))
      (fun e0 => sat_axiom M e0 (inductionForm phi)
          (or_intror (or_intror (or_intror
          (or_intror (or_intror (or_intror (ex_intro _ phi eq_refl)))))))) e).
Qed.

Definition leAt (a b : nat) : formula :=
  pEx (pEq (tAdd (tVar (S a)) (tVar 0)) (tVar (S b))).

Definition ltAt (a b : nat) : formula :=
  pEx (pEq (tAdd (tVar (S a)) (tSucc (tVar 0))) (tVar (S b))).

Definition dvdAt (a b : nat) : formula :=
  pEx (pEq (tMul (tVar (S a)) (tVar 0)) (tVar (S b))).

Definition eqConstAt (a n : nat) : formula :=
  pEq (tVar a) (Term.numeral n).

Definition zeroAt (a : nat) : formula := eqConstAt a 0.

Definition oneAt (a : nat) : formula := eqConstAt a 1.

Definition twoAt (a : nat) : formula := eqConstAt a 2.

Definition nonzeroAt (a : nat) : formula :=
  pEx (pEq (tSucc (tVar 0)) (tVar (S a))).

Definition boolAt (a : nat) : formula :=
  pOr (zeroAt a) (oneAt a).

Definition doubleEqAt (value half : nat) : formula :=
  pEq (tVar value) (tAdd (tVar half) (tVar half)).

Definition oddDoubleEqAt (value half : nat) : formula :=
  pEq (tVar value) (tSucc (tAdd (tVar half) (tVar half))).

Definition div2StepAt (value half bit : nat) : formula :=
  pAnd (boolAt bit)
    (pEq (tVar value)
      (tAdd (tAdd (tVar half) (tVar half)) (tVar bit))).

Definition remAt (rem value modulus : nat) : formula :=
  pEx (pAnd
    (ltAt (S rem) (S modulus))
    (pEq (tVar (S value))
      (tAdd (tMul (tVar 0) (tVar (S modulus)))
        (tVar (S rem))))).

Definition betaModTerm (step idx : nat) : term :=
  tSucc (tMul (tSucc (tVar idx)) (tVar step)).

Definition betaAt (out code step idx : nat) : formula :=
  pEx (pAnd
    (pEq (tVar 0) (Term.rename S (betaModTerm step idx)))
    (remAt (S out) (S code) 0)).

Definition betaAtConstIdx (out code step idxValue : nat) : formula :=
  pEx (pAnd (eqConstAt 0 idxValue)
    (betaAt (S out) (S code) (S step) 0)).

Definition betaAtSuccIdx (out code step idx : nat) : formula :=
  pEx (pAnd
    (pEq (tVar 0) (tSucc (tVar (S idx))))
    (betaAt (S out) (S code) (S step) 0)).

Definition BetaModulus (step idx : nat) : nat :=
  1 + S idx * step.

Definition BetaEntry (code step idx value : nat) : Prop :=
  exists q, code = q * BetaModulus step idx + value /\
    value < BetaModulus step idx.

Fixpoint betaFact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => S k * betaFact k
  end.

Fixpoint BetaModuliProduct (step n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => BetaModuliProduct step k * BetaModulus step k
  end.

Definition BetaDiv2Step
    (code step idx cur next bit : nat) : Prop :=
  BetaEntry code step idx cur /\
    BetaEntry code step (S idx) next /\
      (bit = 0 \/ bit = 1) /\ cur = next + next + bit.

Definition BetaDiv2StepsThrough (code step last : nat) : Prop :=
  forall k, k <= last ->
    exists cur next bit, BetaDiv2Step code step k cur next bit.

Definition BetaDiv2Bit (code step idx bit : nat) : Prop :=
  exists cur next, BetaDiv2Step code step idx cur next bit.

Definition HFMemTrace (elem set code step : nat) : Prop :=
  BetaEntry code step 0 set /\
    BetaDiv2StepsThrough code step elem /\
      BetaDiv2Bit code step elem 1.

Definition betaDiv2StepWitnessAt (code step idx : nat) : formula :=
  pEx (pEx (pEx
    (pAnd
      (betaAt 2 (S (S (S code))) (S (S (S step)))
        (S (S (S idx))))
      (pAnd
        (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
          (S (S (S idx))))
        (div2StepAt 2 1 0))))).

Definition betaDiv2StepAt (code step limit : nat) : formula :=
  pAll (pImp (ltAt 0 (S limit))
    (betaDiv2StepWitnessAt (S code) (S step) 0)).

Definition betaDiv2StepsThroughAt (code step last : nat) : formula :=
  pAll (pImp (leAt 0 (S last))
    (betaDiv2StepWitnessAt (S code) (S step) 0)).

Definition betaDiv2BitAt (bit code step idx : nat) : formula :=
  pEx (pEx
    (pAnd
      (betaAt 1 (S (S code)) (S (S step)) (S (S idx)))
      (pAnd
        (betaAtSuccIdx 0 (S (S code)) (S (S step)) (S (S idx)))
        (div2StepAt 1 0 (S (S bit)))))).

Definition hfMemAt (elem set : nat) : formula :=
  pEx (pEx
    (pAnd
      (betaAtConstIdx (S (S set)) 1 0 0)
      (pAnd
        (betaDiv2StepsThroughAt 1 0 (S (S elem)))
        (pEx
          (pAnd
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (S (S (S elem))))))))).

Lemma leAt_nat : forall (e : nat -> nat) a b,
  Sat natModel e (leAt a b) <-> e a <= e b.
Proof.
  intros e a b.
  unfold leAt. simpl.
  split.
  - intros [d hd].
    lia.
  - intro h.
    exists (e b - e a).
    lia.
Qed.

Lemma ltAt_nat : forall (e : nat -> nat) a b,
  Sat natModel e (ltAt a b) <-> e a < e b.
Proof.
  intros e a b.
  unfold ltAt. simpl.
  split.
  - intros [d hd].
    lia.
  - intro h.
    exists (e b - e a - 1).
    lia.
Qed.

Lemma dvdAt_nat : forall (e : nat -> nat) a b,
  Sat natModel e (dvdAt a b) <-> Nat.divide (e a) (e b).
Proof.
  intros e a b.
  unfold dvdAt. simpl.
  split.
  - intros [q hq].
    exists q.
    rewrite Nat.mul_comm.
    symmetry. exact hq.
  - intros [q hq].
    exists q.
    rewrite Nat.mul_comm.
    symmetry. exact hq.
Qed.

Lemma eqConstAt_nat : forall (e : nat -> nat) a n,
  Sat natModel e (eqConstAt a n) <-> e a = n.
Proof.
  intros e a n.
  unfold eqConstAt. simpl.
  rewrite Term.eval_numeral_natModel.
  reflexivity.
Qed.

Lemma zeroAt_nat : forall (e : nat -> nat) a,
  Sat natModel e (zeroAt a) <-> e a = 0.
Proof.
  intros e a.
  apply eqConstAt_nat.
Qed.

Lemma oneAt_nat : forall (e : nat -> nat) a,
  Sat natModel e (oneAt a) <-> e a = 1.
Proof.
  intros e a.
  apply eqConstAt_nat.
Qed.

Lemma twoAt_nat : forall (e : nat -> nat) a,
  Sat natModel e (twoAt a) <-> e a = 2.
Proof.
  intros e a.
  apply eqConstAt_nat.
Qed.

Lemma nonzeroAt_nat : forall (e : nat -> nat) a,
  Sat natModel e (nonzeroAt a) <-> e a <> 0.
Proof.
  intros e a.
  unfold nonzeroAt. simpl.
  split.
  - intros [d hd] hzero.
    lia.
  - intro h.
    exists (e a - 1).
    lia.
Qed.

Lemma boolAt_nat : forall (e : nat -> nat) a,
  Sat natModel e (boolAt a) <-> e a = 0 \/ e a = 1.
Proof.
  intros e a.
  unfold boolAt, zeroAt, oneAt, eqConstAt. simpl.
  reflexivity.
Qed.

Lemma doubleEqAt_nat : forall (e : nat -> nat) value half,
  Sat natModel e (doubleEqAt value half) <->
    e value = e half + e half.
Proof.
  intros e value half.
  unfold doubleEqAt. simpl.
  reflexivity.
Qed.

Lemma oddDoubleEqAt_nat : forall (e : nat -> nat) value half,
  Sat natModel e (oddDoubleEqAt value half) <->
    e value = e half + e half + 1.
Proof.
  intros e value half.
  unfold oddDoubleEqAt. simpl.
  split; intro h; lia.
Qed.

Lemma div2StepAt_nat : forall (e : nat -> nat) value half bit,
  Sat natModel e (div2StepAt value half bit) <->
    (e bit = 0 \/ e bit = 1) /\
      e value = e half + e half + e bit.
Proof.
  intros e value half bit.
  unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt. simpl.
  split; intros [hbit hval].
  - split; [exact hbit | lia].
  - split; [exact hbit | lia].
Qed.

Lemma betaModTerm_nat : forall (e : nat -> nat) step idx,
  Term.eval natModel e (betaModTerm step idx) =
    1 + S (e idx) * e step.
Proof.
  intros e step idx.
  unfold betaModTerm. simpl.
  lia.
Qed.

Lemma remAt_nat : forall (e : nat -> nat) rem value modulus,
  Sat natModel e (remAt rem value modulus) <->
    exists q, e value = q * e modulus + e rem /\
      e rem < e modulus.
Proof.
  intros e rem value modulus.
  unfold remAt. simpl.
  split.
  - intros [q [hlt hval]].
    exists q.
    split.
    + exact hval.
    + exact (proj1 (ltAt_nat (scons nat q e) (S rem) (S modulus)) hlt).
  - intros [q [hval hlt]].
    exists q.
    split.
    + exact (proj2 (ltAt_nat (scons nat q e) (S rem) (S modulus)) hlt).
    + exact hval.
Qed.

Lemma betaAt_nat : forall (e : nat -> nat) out code step idx,
  Sat natModel e (betaAt out code step idx) <->
    exists q,
      e code = q * (1 + S (e idx) * e step) + e out /\
        e out < 1 + S (e idx) * e step.
Proof.
  intros e out code step idx.
  unfold betaAt. simpl.
  split.
  - intros [m [hmod hrem]].
    assert (hm : m = 1 + S (e idx) * e step).
    {
      unfold betaModTerm in hmod. simpl in hmod. lia.
    }
    destruct (proj1 (remAt_nat (scons nat m e) (S out) (S code) 0) hrem)
      as [q [hval hlt]].
    exists q.
    subst m.
    split; simpl in *; assumption.
  - intros [q [hval hlt]].
    exists (1 + S (e idx) * e step).
    split.
    + unfold betaModTerm. simpl. lia.
    + apply (proj2 (remAt_nat (scons nat (1 + S (e idx) * e step) e)
        (S out) (S code) 0)).
      exists q.
      split; simpl; assumption.
Qed.

Lemma betaAtConstIdx_nat : forall (e : nat -> nat) out code step idxValue,
  Sat natModel e (betaAtConstIdx out code step idxValue) <->
    exists q,
      e code = q * (1 + S idxValue * e step) + e out /\
        e out < 1 + S idxValue * e step.
Proof.
  intros e out code step idxValue.
  unfold betaAtConstIdx. simpl.
  split.
  - intros [i [hi hbeta]].
    pose proof (proj1 (eqConstAt_nat (scons nat i e) 0 idxValue) hi) as hi'.
    simpl in hi'.
    subst i.
    destruct (proj1 (betaAt_nat (scons nat idxValue e)
        (S out) (S code) (S step) 0) hbeta) as [q [hval hlt]].
    exists q.
    split; simpl in *; assumption.
  - intros [q [hval hlt]].
    exists idxValue.
    split.
    + exact (proj2 (eqConstAt_nat (scons nat idxValue e) 0 idxValue) eq_refl).
    + apply (proj2 (betaAt_nat (scons nat idxValue e)
        (S out) (S code) (S step) 0)).
      exists q.
      split; simpl; assumption.
Qed.

Lemma betaAtSuccIdx_nat : forall (e : nat -> nat) out code step idx,
  Sat natModel e (betaAtSuccIdx out code step idx) <->
    exists q,
      e code = q * (1 + S (S (e idx)) * e step) + e out /\
        e out < 1 + S (S (e idx)) * e step.
Proof.
  intros e out code step idx.
  unfold betaAtSuccIdx. simpl.
  split.
  - intros [i [hi hbeta]].
    assert (hi' : i = S (e idx)) by exact hi.
    subst i.
    destruct (proj1 (betaAt_nat (scons nat (S (e idx)) e)
        (S out) (S code) (S step) 0) hbeta) as [q [hval hlt]].
    exists q.
    split; simpl in *; assumption.
  - intros [q [hval hlt]].
    exists (S (e idx)).
    split.
    + reflexivity.
    + apply (proj2 (betaAt_nat (scons nat (S (e idx)) e)
        (S out) (S code) (S step) 0)).
      exists q.
      split; simpl; assumption.
Qed.

Lemma betaAt_nat_entry : forall (e : nat -> nat) out code step idx,
  Sat natModel e (betaAt out code step idx) <->
    BetaEntry (e code) (e step) (e idx) (e out).
Proof.
  intros e out code step idx.
  unfold BetaEntry, BetaModulus.
  apply betaAt_nat.
Qed.

Lemma betaAtConstIdx_nat_entry :
    forall (e : nat -> nat) out code step idxValue,
  Sat natModel e (betaAtConstIdx out code step idxValue) <->
    BetaEntry (e code) (e step) idxValue (e out).
Proof.
  intros e out code step idxValue.
  unfold BetaEntry, BetaModulus.
  apply betaAtConstIdx_nat.
Qed.

Lemma betaAtSuccIdx_nat_entry :
    forall (e : nat -> nat) out code step idx,
  Sat natModel e (betaAtSuccIdx out code step idx) <->
    BetaEntry (e code) (e step) (S (e idx)) (e out).
Proof.
  intros e out code step idx.
  unfold BetaEntry, BetaModulus.
  apply betaAtSuccIdx_nat.
Qed.

Lemma betaDiv2StepWitnessAt_nat :
    forall (e : nat -> nat) code step idx,
  Sat natModel e (betaDiv2StepWitnessAt code step idx) <->
    exists cur next bit,
      BetaEntry (e code) (e step) (e idx) cur /\
      BetaEntry (e code) (e step) (S (e idx)) next /\
      (bit = 0 \/ bit = 1) /\ cur = next + next + bit.
Proof.
  intros e code step idx.
  unfold betaDiv2StepWitnessAt. simpl.
  split.
  - intros [cur [next [bit [hcur [hnext hstep]]]]].
    pose proof (proj1 (betaAt_nat_entry
      (scons nat bit (scons nat next (scons nat cur e)))
      2 (S (S (S code))) (S (S (S step))) (S (S (S idx)))) hcur)
      as hcur'.
    pose proof (proj1 (betaAtSuccIdx_nat_entry
      (scons nat bit (scons nat next (scons nat cur e)))
      1 (S (S (S code))) (S (S (S step))) (S (S (S idx)))) hnext)
      as hnext'.
    pose proof (proj1 (div2StepAt_nat
      (scons nat bit (scons nat next (scons nat cur e))) 2 1 0) hstep)
      as hstep'.
    simpl in hcur', hnext', hstep'.
    destruct hstep' as [hbit hval].
    exists cur, next, bit.
    repeat split; assumption.
  - intros [cur [next [bit [hcur [hnext [hbit hval]]]]]].
    exists cur, next, bit.
    split.
    + apply (proj2 (betaAt_nat_entry
        (scons nat bit (scons nat next (scons nat cur e)))
        2 (S (S (S code))) (S (S (S step))) (S (S (S idx))))).
      simpl. exact hcur.
    + split.
      * apply (proj2 (betaAtSuccIdx_nat_entry
          (scons nat bit (scons nat next (scons nat cur e)))
          1 (S (S (S code))) (S (S (S step))) (S (S (S idx))))).
        simpl. exact hnext.
      * apply (proj2 (div2StepAt_nat
          (scons nat bit (scons nat next (scons nat cur e))) 2 1 0)).
        simpl. split; assumption.
Qed.

Lemma betaDiv2StepAt_nat : forall (e : nat -> nat) code step limit,
  Sat natModel e (betaDiv2StepAt code step limit) <->
    forall k, k < e limit ->
      exists cur next bit,
        BetaEntry (e code) (e step) k cur /\
        BetaEntry (e code) (e step) (S k) next /\
        (bit = 0 \/ bit = 1) /\ cur = next + next + bit.
Proof.
  intros e code step limit.
  unfold betaDiv2StepAt. simpl.
  split.
  - intros h k hk.
    assert (hkSat : Sat natModel (scons nat k e) (ltAt 0 (S limit))).
    {
      apply (proj2 (ltAt_nat (scons nat k e) 0 (S limit))).
      simpl. exact hk.
    }
    pose proof (proj1 (betaDiv2StepWitnessAt_nat
      (scons nat k e) (S code) (S step) 0) (h k hkSat)) as hw.
    simpl in hw. exact hw.
  - intros h k hkSat.
    assert (hk : k < e limit).
    {
      pose proof (proj1 (ltAt_nat (scons nat k e) 0 (S limit)) hkSat)
        as hlt.
      simpl in hlt. exact hlt.
    }
    apply (proj2 (betaDiv2StepWitnessAt_nat
      (scons nat k e) (S code) (S step) 0)).
    simpl. exact (h k hk).
Qed.

Lemma betaDiv2StepsThroughAt_nat :
    forall (e : nat -> nat) code step last,
  Sat natModel e (betaDiv2StepsThroughAt code step last) <->
    forall k, k <= e last ->
      exists cur next bit,
        BetaEntry (e code) (e step) k cur /\
        BetaEntry (e code) (e step) (S k) next /\
        (bit = 0 \/ bit = 1) /\ cur = next + next + bit.
Proof.
  intros e code step last.
  unfold betaDiv2StepsThroughAt. simpl.
  split.
  - intros h k hk.
    assert (hkSat : Sat natModel (scons nat k e) (leAt 0 (S last))).
    {
      apply (proj2 (leAt_nat (scons nat k e) 0 (S last))).
      simpl. exact hk.
    }
    pose proof (proj1 (betaDiv2StepWitnessAt_nat
      (scons nat k e) (S code) (S step) 0) (h k hkSat)) as hw.
    simpl in hw. exact hw.
  - intros h k hkSat.
    assert (hk : k <= e last).
    {
      pose proof (proj1 (leAt_nat (scons nat k e) 0 (S last)) hkSat)
        as hle.
      simpl in hle. exact hle.
    }
    apply (proj2 (betaDiv2StepWitnessAt_nat
      (scons nat k e) (S code) (S step) 0)).
    simpl. exact (h k hk).
Qed.

Lemma betaDiv2BitAt_nat : forall (e : nat -> nat) bit code step idx,
  Sat natModel e (betaDiv2BitAt bit code step idx) <->
    BetaDiv2Bit (e code) (e step) (e idx) (e bit).
Proof.
  intros e bit code step idx.
  unfold betaDiv2BitAt, BetaDiv2Bit. simpl.
  split.
  - intros [cur [next [hcur [hnext hstep]]]].
    pose proof (proj1 (betaAt_nat_entry
      (scons nat next (scons nat cur e))
      1 (S (S code)) (S (S step)) (S (S idx))) hcur) as hcur'.
    pose proof (proj1 (betaAtSuccIdx_nat_entry
      (scons nat next (scons nat cur e))
      0 (S (S code)) (S (S step)) (S (S idx))) hnext) as hnext'.
    pose proof (proj1 (div2StepAt_nat
      (scons nat next (scons nat cur e)) 1 0 (S (S bit))) hstep)
      as hstep'.
    simpl in hcur', hnext', hstep'.
    destruct hstep' as [hbit hval].
    exists cur, next.
    unfold BetaDiv2Step.
    repeat split; assumption.
  - intros [cur [next [hcur [hnext [hbit hval]]]]].
    exists cur, next.
    split.
    + apply (proj2 (betaAt_nat_entry
        (scons nat next (scons nat cur e))
        1 (S (S code)) (S (S step)) (S (S idx)))).
      simpl. exact hcur.
    + split.
      * apply (proj2 (betaAtSuccIdx_nat_entry
          (scons nat next (scons nat cur e))
          0 (S (S code)) (S (S step)) (S (S idx)))).
        simpl. exact hnext.
      * apply (proj2 (div2StepAt_nat
          (scons nat next (scons nat cur e)) 1 0 (S (S bit)))).
        simpl. split; assumption.
Qed.

Lemma hfMemAt_nat_trace : forall (e : nat -> nat) elem set,
  Sat natModel e (hfMemAt elem set) <->
    exists code step, HFMemTrace (e elem) (e set) code step.
Proof.
  intros e elem set.
  unfold hfMemAt. simpl.
  split.
  - intros [code [step [hstart [hsteps [bit [hone hbit]]]]]].
    pose (E := scons nat step (scons nat code e)).
    assert (hstart' : BetaEntry code step 0 (e set)).
    {
      pose proof (proj1 (betaAtConstIdx_nat_entry E (S (S set)) 1 0 0)
        hstart) as hs.
      unfold E in hs. simpl in hs. exact hs.
    }
    assert (hsteps' : BetaDiv2StepsThrough code step (e elem)).
    {
      pose proof (proj1 (betaDiv2StepsThroughAt_nat E 1 0 (S (S elem)))
        hsteps) as hs.
      unfold BetaDiv2StepsThrough.
      intros k hk.
      assert (hkE : k <= E (S (S elem))).
      {
        unfold E. simpl. exact hk.
      }
      destruct (hs k hkE) as [cur [next [b [hcur [hnext [hb hv]]]]]].
      exists cur, next, b.
      unfold BetaDiv2Step.
      unfold E in hcur, hnext. simpl in hcur, hnext.
      repeat split; assumption.
    }
    assert (hbit' : BetaDiv2Bit code step (e elem) 1).
    {
      pose proof (proj1 (oneAt_nat (scons nat bit E) 0) hone) as hone'.
      pose proof (proj1 (betaDiv2BitAt_nat (scons nat bit E)
        0 2 1 (S (S (S elem)))) hbit) as hb.
      unfold E in hb. simpl in hb.
      subst bit. exact hb.
    }
    exists code, step.
    unfold HFMemTrace.
    repeat split; assumption.
  - intros [code [step [hstart [hsteps hbit]]]].
    pose (E := scons nat step (scons nat code e)).
    exists code, step.
    repeat split.
    + apply (proj2 (betaAtConstIdx_nat_entry E (S (S set)) 1 0 0)).
      unfold E. simpl. exact hstart.
    + apply (proj2 (betaDiv2StepsThroughAt_nat E 1 0 (S (S elem)))).
      intros k hk.
      unfold E in hk. simpl in hk.
      destruct (hsteps k hk) as [cur [next [bit [hcur [hnext [hbit0 hval]]]]]].
      exists cur, next, bit.
      unfold E. simpl.
      repeat split; assumption.
    + exists 1.
      split.
      * apply (proj2 (oneAt_nat (scons nat 1 E) 0)).
        reflexivity.
      * apply (proj2 (betaDiv2BitAt_nat (scons nat 1 E)
          0 2 1 (S (S (S elem))))).
        unfold E. simpl. exact hbit.
Qed.

Definition Coprime (m n : nat) : Prop := Nat.gcd m n = 1.

Lemma Coprime_1_l : forall n, Coprime 1 n.
Proof.
  intro n.
  unfold Coprime.
  apply Nat.gcd_unique.
  - exists 1. lia.
  - exists n. lia.
  - intros q hq _.
    exact hq.
Qed.

Lemma Coprime_sym : forall m n, Coprime m n -> Coprime n m.
Proof.
  unfold Coprime.
  intros m n h.
  rewrite Nat.gcd_comm.
  exact h.
Qed.

Lemma Coprime_of_dvd_left : forall d m n,
  Nat.divide d m -> Coprime m n -> Coprime d n.
Proof.
  unfold Coprime.
  intros d m n hdm hcop.
  apply Nat.gcd_unique.
  - exists d. lia.
  - exists n. lia.
  - intros q hqd hqn.
    assert (hqm : Nat.divide q m).
    {
      exact (Nat.divide_trans q d m hqd hdm).
    }
    pose proof (Nat.gcd_greatest m n q hqm hqn) as hqg.
    rewrite hcop in hqg.
    exact hqg.
Qed.

Lemma Coprime_eq_one_of_dvd : forall d n,
  Coprime d n -> Nat.divide d n -> d = 1.
Proof.
  unfold Coprime.
  intros d n hcop hdn.
  assert (hdg : Nat.divide d (Nat.gcd d n)).
  {
    apply Nat.gcd_greatest.
    - exists 1. lia.
    - exact hdn.
  }
  rewrite hcop in hdg.
  apply Nat.divide_1_r.
  exact hdg.
Qed.

Lemma Coprime_dvd_of_dvd_mul_left : forall d n k,
  Coprime d n -> Nat.divide d (k * n) -> Nat.divide d k.
Proof.
  unfold Coprime.
  intros d n k hcop hdkn.
  rewrite Nat.mul_comm in hdkn.
  exact (Nat.gauss d n k hdkn hcop).
Qed.

Lemma Coprime_mul_left : forall a b c,
  Coprime a c -> Coprime b c -> Coprime (a * b) c.
Proof.
  intros a b c hac hbc.
  unfold Coprime in *.
  apply Nat.gcd_unique.
  - exists (a * b). lia.
  - exists c. lia.
  - intros q hqprod hqc.
    assert (hq_b : Coprime q b).
    {
      apply Coprime_of_dvd_left with (m := c).
      - exact hqc.
      - apply Coprime_sym. exact hbc.
    }
    unfold Coprime in hq_b.
    assert (hqa : Nat.divide q a).
    {
      rewrite Nat.mul_comm in hqprod.
      exact (Nat.gauss q b a hqprod hq_b).
    }
    pose proof (Nat.gcd_greatest a c q hqa hqc) as hqg.
    rewrite hac in hqg.
    exact hqg.
Qed.

Lemma betaFact_pos : forall n, 0 < betaFact n.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Lemma dvd_betaFact_of_pos_le : forall k n,
  0 < k -> k <= n -> Nat.divide k (betaFact n).
Proof.
  intros k n hk hkn.
  induction n as [|n IH].
  - lia.
  - simpl.
    destruct (Nat.eq_dec k (S n)) as [heq | hne].
    + subst k.
      exists (betaFact n). nia.
    + assert (hkle : k <= n) by lia.
      destruct (IH hkle) as [q hq].
      exists (S n * q). nia.
Qed.

Lemma BetaModulus_pos : forall step idx, 0 < BetaModulus step idx.
Proof.
  intros step idx.
  unfold BetaModulus.
  lia.
Qed.

Lemma BetaModuliProduct_pos : forall step n,
  0 < BetaModuliProduct step n.
Proof.
  intros step n.
  induction n as [|n IH]; simpl.
  - lia.
  - pose proof (BetaModulus_pos step n).
    nia.
Qed.

Lemma BetaModulus_coprime_step : forall step idx,
  Coprime (BetaModulus step idx) step.
Proof.
  intros step idx.
  unfold Coprime.
  set (d := Nat.gcd (BetaModulus step idx) step).
  change (d = 1).
  assert (hdm : Nat.divide d (BetaModulus step idx)).
  {
    unfold d. apply Nat.gcd_divide_l.
  }
  assert (hdstep : Nat.divide d step).
  {
    unfold d. apply Nat.gcd_divide_r.
  }
  assert (hdprod : Nat.divide d (S idx * step)).
  {
    apply Nat.divide_mul_r.
    exact hdstep.
  }
  assert (hdone : Nat.divide d 1).
  {
    pose proof (Nat.divide_sub_r d (BetaModulus step idx)
      (S idx * step) hdm hdprod) as hsub.
    replace (BetaModulus step idx - S idx * step) with 1 in hsub
      by (unfold BetaModulus; nia).
    exact hsub.
  }
  apply Nat.divide_1_r.
  exact hdone.
Qed.

Lemma BetaModulus_sub : forall step i j,
  i <= j ->
  BetaModulus step j - BetaModulus step i = (j - i) * step.
Proof.
  intros step i j hij.
  unfold BetaModulus.
  nia.
Qed.

Lemma BetaModulus_pair_coprime_of_dvd_step : forall step i j,
  i < j ->
  Nat.divide (j - i) step ->
  Coprime (BetaModulus step i) (BetaModulus step j).
Proof.
  intros step i j hij hdiff.
  unfold Coprime.
  set (d := Nat.gcd (BetaModulus step i) (BetaModulus step j)).
  change (d = 1).
  assert (hdi : Nat.divide d (BetaModulus step i)).
  {
    unfold d. apply Nat.gcd_divide_l.
  }
  assert (hdj : Nat.divide d (BetaModulus step j)).
  {
    unfold d. apply Nat.gcd_divide_r.
  }
  assert (hcopStep : Coprime d step).
  {
    apply Coprime_of_dvd_left with (m := BetaModulus step i).
    - exact hdi.
    - apply BetaModulus_coprime_step.
  }
  assert (hddiffstep : Nat.divide d ((j - i) * step)).
  {
    pose proof (Nat.divide_sub_r d (BetaModulus step j)
      (BetaModulus step i) hdj hdi) as hsub.
    rewrite BetaModulus_sub in hsub by lia.
    exact hsub.
  }
  assert (hddiff : Nat.divide d (j - i)).
  {
    apply (Coprime_dvd_of_dvd_mul_left d step (j - i)).
    - exact hcopStep.
    - exact hddiffstep.
  }
  assert (hdstep' : Nat.divide d step).
  {
    exact (Nat.divide_trans d (j - i) step hddiff hdiff).
  }
  apply Coprime_eq_one_of_dvd with (n := step).
  - exact hcopStep.
  - exact hdstep'.
Qed.

Lemma BetaModulus_pair_coprime_of_lt_le : forall i j N,
  i < j -> j <= N ->
  Coprime (BetaModulus (betaFact N) i)
    (BetaModulus (betaFact N) j).
Proof.
  intros i j N hij hjN.
  apply BetaModulus_pair_coprime_of_dvd_step.
  - exact hij.
  - apply dvd_betaFact_of_pos_le; lia.
Qed.

Lemma BetaModuliProduct_coprime_modulus_of_le : forall n j N,
  n <= j -> j <= N ->
  Coprime (BetaModuliProduct (betaFact N) n)
    (BetaModulus (betaFact N) j).
Proof.
  intros n.
  induction n as [|n IH]; intros j N hnj hjN.
  - simpl.
    apply Coprime_1_l.
  - simpl.
    apply Coprime_mul_left.
    + apply IH; lia.
    + apply BetaModulus_pair_coprime_of_lt_le; lia.
Qed.

Lemma BetaModuliProduct_coprime_next_of_le : forall n N,
  n <= N ->
  Coprime (BetaModuliProduct (betaFact N) n)
    (BetaModulus (betaFact N) n).
Proof.
  intros n N hn.
  apply BetaModuliProduct_coprime_modulus_of_le; lia.
Qed.

Lemma BetaEntry_value_lt : forall code step idx value,
  BetaEntry code step idx value ->
  value < BetaModulus step idx.
Proof.
  intros code step idx value [_ [_ hlt]].
  exact hlt.
Qed.

Lemma BetaEntry_mod_eq : forall code step idx value,
  BetaEntry code step idx value ->
  code mod BetaModulus step idx = value.
Proof.
  intros code step idx value [q [hcode hlt]].
  rewrite hcode.
  rewrite Nat.add_comm.
  rewrite Nat.Div0.mod_add.
  apply Nat.mod_small.
  exact hlt.
Qed.

Lemma BetaEntry_of_mod_eq : forall code step idx value,
  value < BetaModulus step idx ->
  code mod BetaModulus step idx = value ->
  BetaEntry code step idx value.
Proof.
  intros code step idx value hlt hmod.
  exists (code / BetaModulus step idx).
  split.
  - rewrite <- hmod.
    rewrite Nat.mul_comm.
    apply Nat.div_mod_eq.
  - exact hlt.
Qed.

Lemma BetaModuliProduct_dvd_of_lt : forall step i n,
  i < n -> Nat.divide (BetaModulus step i) (BetaModuliProduct step n).
Proof.
  intros step i n hi.
  induction n as [|n IH].
  - lia.
  - simpl.
    destruct (Nat.eq_dec i n) as [heq | hne].
    + subst i.
      exists (BetaModuliProduct step n).
      reflexivity.
    + assert (hin : i < n) by lia.
      destruct (IH hin) as [q hq].
      exists (q * BetaModulus step n).
      rewrite hq.
      nia.
Qed.

Lemma mod_mod_of_dvd : forall a m d,
  0 < d -> Nat.divide d m -> (a mod m) mod d = a mod d.
Proof.
  intros a m d hdpos [q hq].
  subst m.
  replace (q * d) with (d * q) by nia.
  rewrite Nat.Div0.mod_mul_r.
  replace (d * ((a / d) mod q)) with (((a / d) mod q) * d) by nia.
  rewrite Nat.Div0.mod_add.
  apply Nat.mod_small.
  apply Nat.mod_upper_bound.
  lia.
Qed.

Lemma mod_eq_of_mod_BetaModuliProduct_eq :
    forall code old step idx n,
  idx < n ->
  code mod BetaModuliProduct step n =
    old mod BetaModuliProduct step n ->
  code mod BetaModulus step idx = old mod BetaModulus step idx.
Proof.
  intros code old step idx n hi hmod.
  pose proof (BetaModuliProduct_dvd_of_lt step idx n hi) as hd.
  pose proof (BetaModulus_pos step idx) as hpos.
  rewrite <- (mod_mod_of_dvd code (BetaModuliProduct step n)
    (BetaModulus step idx) hpos hd).
  rewrite hmod.
  apply mod_mod_of_dvd.
  - exact hpos.
  - exact hd.
Qed.

Lemma BetaEntry_of_mod_BetaModuliProduct_eq :
    forall code old step idx n value,
  idx < n ->
  code mod BetaModuliProduct step n =
    old mod BetaModuliProduct step n ->
  BetaEntry old step idx value ->
  BetaEntry code step idx value.
Proof.
  intros code old step idx n value hi hmod hold.
  apply BetaEntry_of_mod_eq.
  - exact (BetaEntry_value_lt old step idx value hold).
  - rewrite (mod_eq_of_mod_BetaModuliProduct_eq code old step idx n hi hmod).
    exact (BetaEntry_mod_eq old step idx value hold).
Qed.

Lemma BetaModulus_pair_coprime_of_lt_le_mul_betaFact :
    forall i j N scale,
  i < j -> j <= N ->
  Coprime (BetaModulus (betaFact N * scale) i)
    (BetaModulus (betaFact N * scale) j).
Proof.
  intros i j N scale hij hjN.
  apply BetaModulus_pair_coprime_of_dvd_step.
  - exact hij.
  - destruct (dvd_betaFact_of_pos_le (j - i) N) as [q hq]; try lia.
    exists (q * scale).
    rewrite hq.
    nia.
Qed.

Lemma BetaModuliProduct_coprime_modulus_of_le_mul_betaFact :
    forall n j N scale,
  n <= j -> j <= N ->
  Coprime (BetaModuliProduct (betaFact N * scale) n)
    (BetaModulus (betaFact N * scale) j).
Proof.
  intros n.
  induction n as [|n IH]; intros j N scale hnj hjN.
  - simpl.
    apply Coprime_1_l.
  - simpl.
    apply Coprime_mul_left.
    + apply IH; lia.
    + apply BetaModulus_pair_coprime_of_lt_le_mul_betaFact; lia.
Qed.

Lemma BetaModuliProduct_coprime_next_of_le_mul_betaFact :
    forall n N scale,
  n <= N ->
  Coprime (BetaModuliProduct (betaFact N * scale) n)
    (BetaModulus (betaFact N * scale) n).
Proof.
  intros n N scale hn.
  apply BetaModuliProduct_coprime_modulus_of_le_mul_betaFact; lia.
Qed.

Lemma coprime_bezout_left : forall m n,
  0 < m -> Coprime m n -> exists x y, x * m = 1 + y * n.
Proof.
  intros m n hm hcop.
  unfold Coprime in hcop.
  destruct (Nat.gcd_bezout_pos m n hm) as [x [y hxy]].
  rewrite hcop in hxy.
  exists x, y.
  exact hxy.
Qed.

Lemma crt_two_mod : forall m n a b,
  0 < m -> 0 < n -> Coprime m n -> a < m -> b < n ->
  exists c, c mod m = a /\ c mod n = b.
Proof.
  intros m n a b hm hn hcop ha hb.
  destruct (coprime_bezout_left m n hm hcop) as [x [y hxy]].
  set (delta := b + n - a mod n).
  exists (a + m * (x * delta)).
  split.
  - replace (m * (x * delta)) with ((x * delta) * m) by nia.
    rewrite Nat.Div0.mod_add.
    apply Nat.mod_small.
    exact ha.
  - assert (hdelta : (a + delta) mod n = b).
    {
      unfold delta.
      assert (hnneq : n <> 0) by lia.
      pose proof (Nat.mod_upper_bound a n hnneq) as hr.
      pose proof (Nat.div_mod_eq a n) as hdiv.
      replace (a + (b + n - a mod n)) with
        (b + (a / n + 1) * n) by nia.
      rewrite Nat.Div0.mod_add.
      apply Nat.mod_small.
      exact hb.
    }
    assert (hmx : m * x = 1 + y * n) by nia.
    replace (m * (x * delta)) with (delta + (y * delta) * n) by nia.
    replace (a + (delta + y * delta * n)) with
      ((a + delta) + (y * delta) * n) by nia.
    rewrite Nat.Div0.mod_add.
    exact hdelta.
Qed.

Lemma beta_entries_exist_lt_mul_betaFact :
    forall N n scale,
  n <= S N ->
  forall value : nat -> nat,
  (forall i, i < n ->
    value i < BetaModulus (betaFact N * scale) i) ->
  exists code,
    forall i, i < n ->
      BetaEntry code (betaFact N * scale) i (value i).
Proof.
  intros N n.
  induction n as [|n IH]; intros scale hn value hsmall.
  - exists 0.
    intros i hi.
    lia.
  - assert (hnOld : n <= S N) by lia.
    destruct (IH scale hnOld value) as [old hold].
    {
      intros i hi.
      apply hsmall.
      lia.
    }
    set (step := betaFact N * scale).
    set (prod := BetaModuliProduct step n).
    set (modn := BetaModulus step n).
    assert (hprodPos : 0 < prod).
    {
      unfold prod.
      apply BetaModuliProduct_pos.
    }
    assert (hmodnPos : 0 < modn).
    {
      unfold modn.
      apply BetaModulus_pos.
    }
    assert (hnN : n <= N) by lia.
    assert (hcop : Coprime prod modn).
    {
      unfold prod, modn, step.
      apply BetaModuliProduct_coprime_next_of_le_mul_betaFact.
      exact hnN.
    }
    assert (ha : old mod prod < prod).
    {
      apply Nat.mod_upper_bound.
      lia.
    }
    assert (hb : value n < modn).
    {
      unfold modn, step.
      apply hsmall.
      lia.
    }
    destruct (crt_two_mod prod modn (old mod prod) (value n)
      hprodPos hmodnPos hcop ha hb) as [code [hprod hnew]].
    exists code.
    intros i hi.
    destruct (Nat.eq_dec i n) as [heq | hne].
    + subst i.
      apply BetaEntry_of_mod_eq.
      * unfold step.
        apply hsmall.
        lia.
      * unfold modn in hnew.
        exact hnew.
    + assert (hin : i < n) by lia.
      apply BetaEntry_of_mod_BetaModuliProduct_eq with (old := old) (n := n).
      * exact hin.
      * unfold prod in hprod.
        exact hprod.
      * apply hold.
        exact hin.
Qed.

Lemma beta_entries_exist_through_mul_betaFact :
    forall N scale (value : nat -> nat),
  (forall i, i <= N ->
    value i < BetaModulus (betaFact N * scale) i) ->
  exists code,
    forall i, i <= N ->
      BetaEntry code (betaFact N * scale) i (value i).
Proof.
  intros N scale value hsmall.
  assert (hN : S N <= S N) by lia.
  destruct (beta_entries_exist_lt_mul_betaFact N (S N) scale
    hN value) as [code hcode].
  {
    intros i hi.
    apply hsmall.
    lia.
  }
  exists code.
  intros i hi.
  apply hcode.
  lia.
Qed.

Lemma shiftr_succ_div2 : forall set k,
  Nat.shiftr set (S k) = Nat.shiftr set k / 2.
Proof.
  intros set k.
  replace (S k) with (k + 1) by lia.
  rewrite <- (Nat.shiftr_shiftr set k 1).
  rewrite Nat.shiftr_div_pow2.
  simpl.
  reflexivity.
Qed.

Lemma shiftRight_lt_trace_modulus : forall elem set i,
  Nat.shiftr set i <
    BetaModulus (betaFact (S elem) * S set) i.
Proof.
  intros elem set i.
  pose proof (Nat.shiftr_upper_bound set i) as hshift.
  pose proof (betaFact_pos (S elem)) as hbf.
  unfold BetaModulus.
  nia.
Qed.

Lemma mod_two_eq_zero_or_one : forall n, n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intro n.
  assert (h2 : 2 <> 0) by lia.
  pose proof (Nat.mod_upper_bound n 2 h2) as h.
  lia.
Qed.

Lemma div2_step_shiftr : forall set k,
  let cur := Nat.shiftr set k in
  let next := Nat.shiftr set (S k) in
  let bit := cur mod 2 in
  (bit = 0 \/ bit = 1) /\ cur = next + next + bit.
Proof.
  intros set k cur next bit.
  assert (hbit : bit = 0 \/ bit = 1).
  {
    unfold bit.
    apply mod_two_eq_zero_or_one.
  }
  assert (hnext : next = cur / 2).
  {
    unfold next, cur.
    apply shiftr_succ_div2.
  }
  pose proof (Nat.div_mod_eq cur 2) as hdiv.
  split.
  - exact hbit.
  - unfold bit.
    nia.
Qed.

Lemma div2_step_shiftr_one : forall set elem,
  hf_mem elem set ->
  let cur := Nat.shiftr set elem in
  let next := Nat.shiftr set (S elem) in
  cur = next + next + 1.
Proof.
  intros set elem hmem cur next.
  assert (hbitTrue : Nat.testbit cur 0 = true).
  {
    unfold cur.
    rewrite Nat.shiftr_spec'.
    replace (0 + elem) with elem by lia.
    unfold hf_mem in hmem.
    exact hmem.
  }
  pose proof (Nat.bit0_mod cur) as hbitmod.
  rewrite hbitTrue in hbitmod.
  simpl in hbitmod.
  assert (hmod : cur mod 2 = 1).
  {
    symmetry.
    exact hbitmod.
  }
  assert (hnext : next = cur / 2).
  {
    unfold next, cur.
    apply shiftr_succ_div2.
  }
  pose proof (Nat.div_mod_eq cur 2) as hdiv.
  nia.
Qed.

Lemma HFMemTrace_exists_of_mem : forall elem set,
  hf_mem elem set -> exists code step, HFMemTrace elem set code step.
Proof.
  intros elem set hmem.
  set (N := S elem).
  set (scale := S set).
  set (step := betaFact N * scale).
  set (value := fun k => Nat.shiftr set k).
  assert (hsmall : forall i, i <= N -> value i < BetaModulus step i).
  {
    intros i _.
    unfold value, step, N, scale.
    apply shiftRight_lt_trace_modulus.
  }
  destruct (beta_entries_exist_through_mul_betaFact N scale value hsmall)
    as [code hcode].
  exists code, step.
  unfold HFMemTrace.
  split.
  - assert (h0le : 0 <= N) by lia.
    pose proof (hcode 0 h0le) as h0.
    unfold value in h0.
    rewrite Nat.shiftr_0_r in h0.
    exact h0.
  - split.
    + unfold BetaDiv2StepsThrough.
      intros k hk.
      set (cur := Nat.shiftr set k).
      set (next := Nat.shiftr set (S k)).
      set (bit := cur mod 2).
      assert (hcur : BetaEntry code step k cur).
      {
        assert (hkle : k <= N) by lia.
        pose proof (hcode k hkle) as h.
        unfold value in h.
        exact h.
      }
      assert (hnext : BetaEntry code step (S k) next).
      {
        assert (hskle : S k <= N) by lia.
        pose proof (hcode (S k) hskle) as h.
        unfold value in h.
        exact h.
      }
      pose proof (div2_step_shiftr set k) as hstep.
      exists cur, next, bit.
      unfold BetaDiv2Step.
      repeat split.
      * exact hcur.
      * exact hnext.
      * unfold cur, bit in hstep.
        exact (proj1 hstep).
      * unfold cur, next, bit in hstep.
        exact (proj2 hstep).
    + unfold BetaDiv2Bit.
      set (cur := Nat.shiftr set elem).
      set (next := Nat.shiftr set (S elem)).
      assert (hcur : BetaEntry code step elem cur).
      {
        assert (hemle : elem <= N) by lia.
        pose proof (hcode elem hemle) as h.
        unfold value in h.
        exact h.
      }
      assert (hnext : BetaEntry code step (S elem) next).
      {
        assert (hsemle : S elem <= N) by lia.
        pose proof (hcode (S elem) hsemle) as h.
        unfold value in h.
        exact h.
      }
      assert (hcurEq : cur = next + next + 1).
      {
        unfold cur, next.
        apply div2_step_shiftr_one.
        exact hmem.
      }
      exists cur, next.
      unfold BetaDiv2Step.
      repeat split.
      * exact hcur.
      * exact hnext.
      * right. reflexivity.
      * exact hcurEq.
Qed.

Lemma BetaEntry_functional : forall code step idx a b,
  BetaEntry code step idx a -> BetaEntry code step idx b -> a = b.
Proof.
  intros code step idx a b ha hb.
  transitivity (code mod BetaModulus step idx).
  - symmetry. apply BetaEntry_mod_eq. exact ha.
  - apply BetaEntry_mod_eq. exact hb.
Qed.

Lemma BetaDiv2Step_div_two : forall code step idx cur next bit,
  BetaDiv2Step code step idx cur next bit -> cur / 2 = next.
Proof.
  intros code step idx cur next bit [_ [_ [hbit hcur]]].
  destruct hbit as [hbit | hbit]; subst bit; rewrite hcur.
  - replace (next + next + 0) with (2 * next + 0) by lia.
    symmetry.
    apply Nat.div_unique with (r := 0); lia.
  - replace (next + next + 1) with (2 * next + 1) by lia.
    symmetry.
    apply Nat.div_unique with (r := 1); lia.
Qed.

Lemma BetaDiv2Step_bit_one_testbit_zero :
    forall code step idx cur next,
  BetaDiv2Step code step idx cur next 1 ->
  Nat.testbit cur 0 = true.
Proof.
  intros code step idx cur next [_ [_ [_ hcur]]].
  rewrite hcur.
  replace (next + next + 1) with (2 * next + 1) by lia.
  apply Nat.testbit_odd_0.
Qed.

Lemma HFMemTrace_entry_shiftr : forall elem set code step,
  HFMemTrace elem set code step ->
  forall k value,
    k <= S elem ->
    BetaEntry code step k value ->
    value = Nat.shiftr set k.
Proof.
  intros elem set code step htrace k.
  induction k as [|k IH]; intros value hle hvalue.
  - destruct htrace as [hstart _].
    pose proof (BetaEntry_functional code step 0 value set
      hvalue hstart) as hv.
    rewrite Nat.shiftr_0_r.
    exact hv.
  - destruct htrace as [hstart [hsteps hbit]].
    assert (hk : k <= elem) by lia.
    destruct (hsteps k hk) as [cur [next [bit hstep]]].
    assert (hcur : cur = Nat.shiftr set k).
    {
      apply IH.
      - lia.
      - exact (proj1 hstep).
    }
    assert (hvalue_next : value = next).
    {
      apply BetaEntry_functional with (code := code) (step := step)
        (idx := S k).
      - exact hvalue.
      - exact (proj1 (proj2 hstep)).
    }
    transitivity next.
    + exact hvalue_next.
    + transitivity (cur / 2).
      * symmetry.
        apply BetaDiv2Step_div_two with
          (code := code) (step := step) (idx := k) (bit := bit).
        exact hstep.
      * rewrite hcur.
        symmetry.
        apply shiftr_succ_div2.
Qed.

Lemma HFMemTrace_mem : forall elem set code step,
  HFMemTrace elem set code step -> hf_mem elem set.
Proof.
  intros elem set code step htrace.
  destruct htrace as [hstart [hsteps hbitTrace]].
  destruct hbitTrace as [cur [next hstep]].
  assert (htraceFull : HFMemTrace elem set code step).
  {
    unfold HFMemTrace.
    split.
    - exact hstart.
    - split.
      + exact hsteps.
      + exists cur, next.
        exact hstep.
  }
  assert (hcur : cur = Nat.shiftr set elem).
  {
    apply (HFMemTrace_entry_shiftr elem set code step htraceFull elem cur).
    - lia.
    - exact (proj1 hstep).
  }
  pose proof (BetaDiv2Step_bit_one_testbit_zero
    code step elem cur next hstep) as hlow.
  rewrite hcur in hlow.
  unfold hf_mem.
  rewrite Nat.shiftr_spec' in hlow.
  replace (0 + elem) with elem in hlow by lia.
  exact hlow.
Qed.

Lemma hfMemAt_sound : forall (e : nat -> nat) elem set,
  Sat natModel e (hfMemAt elem set) -> hf_mem (e elem) (e set).
Proof.
  intros e elem set h.
  destruct (proj1 (hfMemAt_nat_trace e elem set) h) as
    [code [step htrace]].
  exact (HFMemTrace_mem (e elem) (e set) code step htrace).
Qed.

Lemma hfMemAt_complete : forall (e : nat -> nat) elem set,
  hf_mem (e elem) (e set) -> Sat natModel e (hfMemAt elem set).
Proof.
  intros e elem set hmem.
  destruct (HFMemTrace_exists_of_mem (e elem) (e set) hmem) as
    [code [step htrace]].
  apply (proj2 (hfMemAt_nat_trace e elem set)).
  exists code, step.
  exact htrace.
Qed.

Lemma hfMemAt_exact : forall (e : nat -> nat) elem set,
  Sat natModel e (hfMemAt elem set) <-> hf_mem (e elem) (e set).
Proof.
  intros e elem set.
  split.
  - apply hfMemAt_sound.
  - apply hfMemAt_complete.
Qed.

Lemma hfMemAt_free : forall i elem set,
  Free i (hfMemAt elem set) -> i = elem \/ i = set.
Proof.
  intros i elem set h.
  unfold hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaAtConstIdx, betaAtSuccIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt,
    eqConstAt, betaModTerm in h.
  simpl in h.
  lia.
Qed.

Definition hfUpVarMap (rho : nat -> nat) : nat -> nat :=
  fun n =>
    match n with
    | 0 => 0
    | S k => S (rho k)
    end.

Fixpoint hfFormulaAt (rho : nat -> nat) (phi : form) : formula :=
  match phi with
  | fMem i j => hfMemAt (rho i) (rho j)
  | fEq i j => pEq (tVar (rho i)) (tVar (rho j))
  | fBot => pBot
  | fImp a b => pImp (hfFormulaAt rho a) (hfFormulaAt rho b)
  | fAnd a b => pAnd (hfFormulaAt rho a) (hfFormulaAt rho b)
  | fOr a b => pOr (hfFormulaAt rho a) (hfFormulaAt rho b)
  | fAll a => pAll (hfFormulaAt (hfUpVarMap rho) a)
  | fEx a => pEx (hfFormulaAt (hfUpVarMap rho) a)
  end.

Definition translateHFFormula (phi : form) : formula :=
  hfFormulaAt (fun n => n) phi.

Lemma hfFormulaAt_exact : forall phi rho v e,
  (forall n, e (rho n) = v n) ->
  Sat natModel e (hfFormulaAt rho phi) <->
    Fol.Sat nat hf_mem v phi.
Proof.
  induction phi; simpl; intros rho v e hrho.
  - change (Sat natModel e (hfMemAt (rho n) (rho n0)) <->
      hf_mem (v n) (v n0)).
    rewrite hfMemAt_exact.
    rewrite hrho, hrho.
    reflexivity.
  - split; intro h.
    + rewrite <- (hrho n), <- (hrho n0).
      exact h.
    + rewrite (hrho n), (hrho n0).
      exact h.
  - reflexivity.
  - specialize (IHphi1 rho v e hrho).
    specialize (IHphi2 rho v e hrho).
    split; intros h ha.
    + apply (proj1 IHphi2).
      apply h.
      apply (proj2 IHphi1).
      exact ha.
    + apply (proj2 IHphi2).
      apply h.
      apply (proj1 IHphi1).
      exact ha.
  - specialize (IHphi1 rho v e hrho).
    specialize (IHphi2 rho v e hrho).
    split; intros h.
    + split.
      * apply (proj1 IHphi1). exact (proj1 h).
      * apply (proj1 IHphi2). exact (proj2 h).
    + split.
      * apply (proj2 IHphi1). exact (proj1 h).
      * apply (proj2 IHphi2). exact (proj2 h).
  - specialize (IHphi1 rho v e hrho).
    specialize (IHphi2 rho v e hrho).
    split; intros h.
    + destruct h as [h | h].
      * left. apply (proj1 IHphi1). exact h.
      * right. apply (proj1 IHphi2). exact h.
    + destruct h as [h | h].
      * left. apply (proj2 IHphi1). exact h.
      * right. apply (proj2 IHphi2). exact h.
  - split; intros h d.
    + assert (hrho' : forall n,
        scons nat d e (hfUpVarMap rho n) = scons nat d v n).
      {
        intros [|n]; simpl.
        - reflexivity.
        - apply hrho.
      }
      apply (proj1 (IHphi (hfUpVarMap rho)
        (scons nat d v) (scons nat d e) hrho')).
      exact (h d).
    + assert (hrho' : forall n,
        scons nat d e (hfUpVarMap rho n) = scons nat d v n).
      {
        intros [|n]; simpl.
        - reflexivity.
        - apply hrho.
      }
      apply (proj2 (IHphi (hfUpVarMap rho)
        (scons nat d v) (scons nat d e) hrho')).
      exact (h d).
  - split; intros h.
    + destruct h as [d hd].
      exists d.
      assert (hrho' : forall n,
        scons nat d e (hfUpVarMap rho n) = scons nat d v n).
      {
        intros [|n]; simpl.
        - reflexivity.
        - apply hrho.
      }
      apply (proj1 (IHphi (hfUpVarMap rho)
        (scons nat d v) (scons nat d e) hrho')).
      exact hd.
    + destruct h as [d hd].
      exists d.
      assert (hrho' : forall n,
        scons nat d e (hfUpVarMap rho n) = scons nat d v n).
      {
        intros [|n]; simpl.
        - reflexivity.
        - apply hrho.
      }
      apply (proj2 (IHphi (hfUpVarMap rho)
        (scons nat d v) (scons nat d e) hrho')).
      exact hd.
Qed.

Lemma translateHFFormula_exact : forall phi v,
  Sat natModel v (translateHFFormula phi) <->
    Fol.Sat nat hf_mem v phi.
Proof.
  intros phi v.
  unfold translateHFFormula.
  apply hfFormulaAt_exact.
  intro n. reflexivity.
Qed.

Lemma hfFormulaAt_free : forall phi rho i,
  Free i (hfFormulaAt rho phi) ->
    exists n, Fol.Free n phi /\ i = rho n.
Proof.
  induction phi; simpl; intros rho i h.
  - destruct (hfMemAt_free i (rho n) (rho n0) h) as [hi | hi].
    + exists n. split; [left; reflexivity | exact hi].
    + exists n0. split; [right; reflexivity | exact hi].
  - destruct h as [h | h].
    + exists n. split; [left; reflexivity | exact h].
    + exists n0. split; [right; reflexivity | exact h].
  - contradiction.
  - destruct h as [h | h].
    + destruct (IHphi1 rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHphi2 rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct h as [h | h].
    + destruct (IHphi1 rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHphi2 rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct h as [h | h].
    + destruct (IHphi1 rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHphi2 rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct (IHphi (hfUpVarMap rho) (S i) h) as [n [hn hi]].
    destruct n as [|n].
    + simpl in hi. discriminate hi.
    + exists n.
      split.
      * exact hn.
      * simpl in hi.
        injection hi as hi.
        exact hi.
  - destruct (IHphi (hfUpVarMap rho) (S i) h) as [n [hn hi]].
    destruct n as [|n].
    + simpl in hi. discriminate hi.
    + exists n.
      split.
      * exact hn.
      * simpl in hi.
        injection hi as hi.
        exact hi.
Qed.

Lemma hfFormulaAt_sentence_of_HF_sentence : forall phi rho,
  Fol.Sentence phi -> Sentence (hfFormulaAt rho phi).
Proof.
  intros phi rho hphi i hi.
  destruct (hfFormulaAt_free phi rho i hi) as [n [hn _]].
  exact (hphi n hn).
Qed.

Lemma translateHFFormula_sentence_of_HF_sentence : forall phi,
  Fol.Sentence phi -> Sentence (translateHFFormula phi).
Proof.
  intros phi hphi.
  apply hfFormulaAt_sentence_of_HF_sentence.
  exact hphi.
Qed.

Lemma translated_HF_axiom_sat_nat : forall phi,
  HFAx_s phi -> forall v, Sat natModel v (translateHFFormula phi).
Proof.
  intros phi hphi v.
  apply (proj2 (translateHFFormula_exact phi v)).
  exact (standard_sat_HF v phi hphi).
Qed.

Lemma translated_HF_axiom_sentence : forall g,
  HFAx_s g -> Sentence (translateHFFormula g).
Proof.
  intros g hg.
  apply translateHFFormula_sentence_of_HF_sentence.
  exact (Sentences_HF g hg).
Qed.

Lemma translated_HFFin_axiom_sentence : forall g,
  HFFinAx_s g -> Sentence (translateHFFormula g).
Proof.
  intros g hg.
  apply translateHFFormula_sentence_of_HF_sentence.
  exact (Sentences_HFFin g hg).
Qed.

Definition translatedHFAx (phi : formula) : Prop :=
  exists g, HFAx_s g /\ phi = translateHFFormula g.

Definition translatedHFFinAx (phi : formula) : Prop :=
  exists g, HFFinAx_s g /\ phi = translateHFFormula g.

Lemma translatedHFAx_intro : forall g,
  HFAx_s g -> translatedHFAx (translateHFFormula g).
Proof.
  intros g hg.
  exists g.
  split; [exact hg | reflexivity].
Qed.

Lemma translatedHFFinAx_intro : forall g,
  HFFinAx_s g -> translatedHFFinAx (translateHFFormula g).
Proof.
  intros g hg.
  exists g.
  split; [exact hg | reflexivity].
Qed.

Lemma translatedHFFinAx_of_translatedHFAx : forall phi,
  translatedHFAx phi -> translatedHFFinAx phi.
Proof.
  intros phi [g [hg hphi]].
  subst phi.
  apply translatedHFFinAx_intro.
  apply HFFinAx_s_of_HFAx_s.
  exact hg.
Qed.

Lemma Sentences_translatedHFAx : forall phi,
  translatedHFAx phi -> Sentence phi.
Proof.
  intros phi [g [hg hphi]].
  subst phi.
  exact (translated_HF_axiom_sentence g hg).
Qed.

Lemma Sentences_translatedHFFinAx : forall phi,
  translatedHFFinAx phi -> Sentence phi.
Proof.
  intros phi [g [hg hphi]].
  subst phi.
  exact (translated_HFFin_axiom_sentence g hg).
Qed.

Lemma BProv_translatedHFAx_of_HFAx : forall g,
  HFAx_s g -> BProv translatedHFAx [] (translateHFFormula g).
Proof.
  intros g hg.
  apply BProv_ax.
  apply translatedHFAx_intro.
  exact hg.
Qed.

Lemma BProv_translatedHFFinAx_of_HFFinAx : forall g,
  HFFinAx_s g -> BProv translatedHFFinAx [] (translateHFFormula g).
Proof.
  intros g hg.
  apply BProv_ax.
  apply translatedHFFinAx_intro.
  exact hg.
Qed.

Lemma BProv_lift_translatedHFAx_to_PA :
  (forall f, translatedHFAx f -> BProv Ax_s [] f) ->
  forall f, BProv translatedHFAx [] f -> BProv Ax_s [] f.
Proof.
  intros hAx f h.
  apply (BProv_lift translatedHFAx Ax_s [] [] f h).
  - intros b hb. exact (hAx b hb).
  - intros g hg. contradiction.
Qed.

Lemma BProv_lift_translatedHFFinAx_to_PA :
  (forall f, translatedHFFinAx f -> BProv Ax_s [] f) ->
  forall f, BProv translatedHFFinAx [] f -> BProv Ax_s [] f.
Proof.
  intros hAx f h.
  apply (BProv_lift translatedHFFinAx Ax_s [] [] f h).
  - intros b hb. exact (hAx b hb).
  - intros g hg. contradiction.
Qed.

Lemma standard_sat_translatedHFAx : forall e,
  forall g, translatedHFAx g -> Sat natModel e g.
Proof.
  intros e g [phi [hphi hg]].
  subst g.
  exact (translated_HF_axiom_sat_nat phi hphi e).
Qed.

End Formula.

End PA.

Fixpoint termGraphAt (rho : nat -> nat) (out : nat) (t : PA.term) : form :=
  match t with
  | PA.tVar n => fEq out (rho n)
  | PA.tZero => HF_emptyAt out
  | PA.tSucc a =>
      fEx (fAnd
        (termGraphAt (fun n => rho n + 1) 0 a)
        (HF_succAt (out + 1) 0))
  | PA.tAdd a b =>
      fEx (fEx (fAnd
        (termGraphAt (fun n => rho n + 2) 1 a)
        (fAnd
          (termGraphAt (fun n => rho n + 2) 0 b)
          (addGraphAt (out + 2) 1 0))))
  | PA.tMul a b =>
      fEx (fEx (fEx (fAnd
        (termGraphAt (fun n => rho n + 3) 1 a)
        (fAnd
          (termGraphAt (fun n => rho n + 3) 2 b)
          (fAnd (fEq 0 (out + 3)) mulGraph)))))
  end.

Lemma termGraphAt_free : forall t rho out i,
  Free i (termGraphAt rho out t) ->
    i = out \/ exists n, PA.Term.Free n t /\ i = rho n.
Proof.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros rho out i h.
  - destruct h as [h | h].
    + left. exact h.
    + right. exists n. split; [reflexivity | exact h].
  - left. apply (HF_emptyAt_free i out h).
  - destruct h as [h | h].
    + destruct (IHa (fun n => rho n + 1) 0 (S i) h)
        as [hi | [n [hn hi]]].
      * lia.
      * right. exists n. split; [exact hn | lia].
    + destruct (HF_succAt_free (S i) (out + 1) 0 h) as [hi | hi]; lia.
  - destruct h as [h | [h | h]].
    + destruct (IHa (fun n => rho n + 2) 1 (S (S i)) h)
        as [hi | [n [hn hi]]].
      * lia.
      * right. exists n. split; [left; exact hn | lia].
    + destruct (IHb (fun n => rho n + 2) 0 (S (S i)) h)
        as [hi | [n [hn hi]]].
      * lia.
      * right. exists n. split; [right; exact hn | lia].
    + destruct (addGraphAt_free (S (S i)) (out + 2) 1 0 h)
        as [hi | [hi | hi]]; lia.
  - destruct h as [h | [h | [h | h]]].
    + destruct (IHa (fun n => rho n + 3) 1 (S (S (S i))) h)
        as [hi | [n [hn hi]]].
      * lia.
      * right. exists n. split; [left; exact hn | lia].
    + destruct (IHb (fun n => rho n + 3) 2 (S (S (S i))) h)
        as [hi | [n [hn hi]]].
      * lia.
      * right. exists n. split; [right; exact hn | lia].
    + destruct h as [hi | hi]; lia.
    + destruct (mulGraph_free (S (S (S i))) h) as [hi | [hi | hi]]; lia.
Qed.

Lemma termGraphAt_map_ext : forall t rho sigma out,
  (forall n, rho n = sigma n) ->
  termGraphAt rho out t = termGraphAt sigma out t.
Proof.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros rho sigma out h; try reflexivity.
  - rewrite h. reflexivity.
  - rewrite (IHa (fun n => rho n + 1) (fun n => sigma n + 1) 0).
    + reflexivity.
    + intro n. now rewrite h.
  - rewrite (IHa (fun n => rho n + 2) (fun n => sigma n + 2) 1).
    + rewrite (IHb (fun n => rho n + 2) (fun n => sigma n + 2) 0).
      * reflexivity.
      * intro n. now rewrite h.
    + intro n. now rewrite h.
  - rewrite (IHa (fun n => rho n + 3) (fun n => sigma n + 3) 1).
    + rewrite (IHb (fun n => rho n + 3) (fun n => sigma n + 3) 2).
      * reflexivity.
      * intro n. now rewrite h.
    + intro n. now rewrite h.
Qed.

Lemma termGraphAt_substZeroAt_insert_model : forall V
    (M : FirstOrderAdjunctionModel V) t p k rho out e,
  out < k ->
  Sat V (foam_mem V M) e
    (termGraphAt (substZeroAfterMap p k rho) out
      (PA.Term.subst (PA.Formula.substZeroAt p) t)) <->
  Sat V (foam_mem V M) (insertAt (k + p) (foam_empty V M) e)
    (termGraphAt (substZeroBeforeMap p k rho) out t).
Proof.
  intros V M t.
  induction t as [n | | t IH | a IHa b IHb | a IHa b IHb];
    intros p k rho out e hout; simpl.
  - destruct (lt_eq_lt_dec n p) as [[hlt | heq] | hgt].
    + rewrite (PA.Formula.substZeroAt_lt p n hlt).
      simpl.
      rewrite (substZeroAfterMap_lt p k n rho hlt).
      rewrite (substZeroBeforeMap_lt p k n rho hlt).
      split; intro h.
      * change (e out = e (k + n)) in h.
        change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e (k + n)).
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e); [|lia].
        rewrite (insertAt_lt V (k + p) (k + n) (foam_empty V M) e);
          [exact h | lia].
      * change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e (k + n)) in h.
        change (e out = e (k + n)).
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e) in h;
          [|lia].
        rewrite (insertAt_lt V (k + p) (k + n) (foam_empty V M) e) in h;
          [exact h | lia].
    + subst n.
      rewrite PA.Formula.substZeroAt_eq.
      simpl.
      rewrite substZeroBeforeMap_eq.
      split; intro h.
      * pose proof (proj1 (foam_HF_emptyAt_empty V M e out) h)
          as houtEmpty.
        change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e (k + p)).
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
          [|lia].
        rewrite insertAt_eq.
        exact houtEmpty.
      * apply (proj2 (foam_HF_emptyAt_empty V M e out)).
        change (e out = foam_empty V M).
        change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e (k + p)) in h.
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e) in h;
          [|lia].
        rewrite insertAt_eq in h.
        exact h.
    + rewrite (PA.Formula.substZeroAt_gt p n hgt).
      simpl.
      assert (hslot :
        insertAt (k + p) (foam_empty V M) e
          (substZeroBeforeMap p k rho n) =
        e (substZeroAfterMap p k rho (n - 1))).
      {
        rewrite (substZeroBeforeMap_gt p k n rho hgt).
        rewrite (substZeroAfterMap_ge p k (n - 1) rho); [|lia].
        rewrite (insertAt_gt V (k + p)
          (rho (n - p - 1) + k + p + 1) (foam_empty V M) e);
          [|lia].
        replace (rho (n - p - 1) + k + p + 1 - 1)
          with (rho (n - 1 - p) + k + p).
        - reflexivity.
        - replace (n - p - 1) with (n - 1 - p) by lia.
          lia.
      }
      split; intro h.
      * change (e out = e (substZeroAfterMap p k rho (n - 1))) in h.
        change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e
            (substZeroBeforeMap p k rho n)).
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
          [|lia].
        rewrite hslot.
        exact h.
      * change (insertAt (k + p) (foam_empty V M) e out =
          insertAt (k + p) (foam_empty V M) e
            (substZeroBeforeMap p k rho n)) in h.
        change (e out = e (substZeroAfterMap p k rho (n - 1))).
        rewrite (insertAt_lt V (k + p) out (foam_empty V M) e) in h;
          [|lia].
        rewrite hslot in h.
        exact h.
  - split; intro h.
    + pose proof (proj1 (foam_HF_emptyAt_empty V M e out) h)
        as houtEmpty.
      apply (proj2 (foam_HF_emptyAt_empty V M
        (insertAt (k + p) (foam_empty V M) e) out)).
      change (insertAt (k + p) (foam_empty V M) e out =
        foam_empty V M).
      rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
        [exact houtEmpty | lia].
    + pose proof (proj1 (foam_HF_emptyAt_empty V M
        (insertAt (k + p) (foam_empty V M) e) out) h)
        as houtEmpty.
      apply (proj2 (foam_HF_emptyAt_empty V M e out)).
      change (e out = foam_empty V M).
      change (insertAt (k + p) (foam_empty V M) e out =
        foam_empty V M) in houtEmpty.
      rewrite (insertAt_lt V (k + p) out (foam_empty V M) e) in houtEmpty;
        [exact houtEmpty | lia].
  - split.
    + intros [x [ht hs]].
      exists x.
      split.
      * assert (htMap : Sat V (foam_mem V M) (scons V x e)
          (termGraphAt (substZeroAfterMap p (k + 1) rho) 0
            (PA.Term.subst (PA.Formula.substZeroAt p) t))).
        {
          rewrite <- (termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) t)
            (fun n => substZeroAfterMap p k rho n + 1)
            (substZeroAfterMap p (k + 1) rho) 0).
          - exact ht.
          - intro n. apply substZeroAfterMap_add.
        }
        pose proof (proj1 (IH p (k + 1) rho 0
          (scons V x e) ltac:(lia)) htMap) as htIns.
        assert (henv : forall n,
          scons V x (insertAt (k + p) (foam_empty V M) e) n =
            insertAt (k + 1 + p) (foam_empty V M) (scons V x e) n).
        {
          intro n.
          rewrite (scons_insertAt_prefix V p k (foam_empty V M) x e n).
          replace (S k + p) with (k + 1 + p) by lia.
          reflexivity.
        }
        pose proof (proj2 (Sat_ext V (foam_mem V M)
          (termGraphAt (substZeroBeforeMap p (k + 1) rho) 0 t)
          (scons V x (insertAt (k + p) (foam_empty V M) e))
          (insertAt (k + 1 + p) (foam_empty V M) (scons V x e)) henv))
          htIns as htEnv.
        rewrite (termGraphAt_map_ext t
          (substZeroBeforeMap p (k + 1) rho)
          (fun n => substZeroBeforeMap p k rho n + 1) 0) in htEnv.
        -- exact htEnv.
        -- intro n. symmetry. apply substZeroBeforeMap_add.
      * refine (proj1 (Sat_ext_free V (foam_mem V M)
          (HF_succAt (out + 1) 0)
          (scons V x e)
          (scons V x (insertAt (k + p) (foam_empty V M) e)) _) hs).
        intros i hi.
        destruct (HF_succAt_free i (out + 1) 0 hi) as [hiout | hi0];
          subst i.
        -- replace (out + 1) with (S out) by lia.
           simpl.
           rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
             [reflexivity | lia].
        -- reflexivity.
    + intros [x [ht hs]].
      exists x.
      split.
      * rewrite (termGraphAt_map_ext
          (PA.Term.subst (PA.Formula.substZeroAt p) t)
          (fun n => substZeroAfterMap p k rho n + 1)
          (substZeroAfterMap p (k + 1) rho) 0).
        -- apply (proj2 (IH p (k + 1) rho 0
             (scons V x e) ltac:(lia))).
           assert (henv : forall n,
             scons V x (insertAt (k + p) (foam_empty V M) e) n =
               insertAt (k + 1 + p) (foam_empty V M) (scons V x e) n).
           {
             intro n.
             rewrite (scons_insertAt_prefix V p k (foam_empty V M) x e n).
             replace (S k + p) with (k + 1 + p) by lia.
             reflexivity.
           }
           apply (proj1 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p (k + 1) rho) 0 t)
             (scons V x (insertAt (k + p) (foam_empty V M) e))
             (insertAt (k + 1 + p) (foam_empty V M)
               (scons V x e)) henv)).
           rewrite (termGraphAt_map_ext t
             (substZeroBeforeMap p (k + 1) rho)
             (fun n => substZeroBeforeMap p k rho n + 1) 0).
           ++ exact ht.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- intro n. apply substZeroAfterMap_add.
      * refine (proj2 (Sat_ext_free V (foam_mem V M)
          (HF_succAt (out + 1) 0)
          (scons V x e)
          (scons V x (insertAt (k + p) (foam_empty V M) e)) _) hs).
        intros i hi.
        destruct (HF_succAt_free i (out + 1) 0 hi) as [hiout | hi0];
          subst i.
        -- replace (out + 1) with (S out) by lia.
           simpl.
           rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
             [reflexivity | lia].
        -- reflexivity.
  - split.
    + intros [x [y [ha [hb hg]]]].
      exists x, y.
      split.
      * assert (haMap : Sat V (foam_mem V M)
          (scons V y (scons V x e))
          (termGraphAt (substZeroAfterMap p (k + 2) rho) 1
            (PA.Term.subst (PA.Formula.substZeroAt p) a))).
        {
          rewrite <- (termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (fun n => substZeroAfterMap p k rho n + 2)
            (substZeroAfterMap p (k + 2) rho) 1).
          - exact ha.
          - intro n. apply substZeroAfterMap_add.
        }
        pose proof (proj1 (IHa p (k + 2) rho 1
          (scons V y (scons V x e)) ltac:(lia)) haMap) as haIns.
        assert (henv : forall n,
          scons V y (scons V x (insertAt (k + p) (foam_empty V M) e)) n =
            insertAt (k + 2 + p) (foam_empty V M)
              (scons V y (scons V x e)) n).
        {
          intro n.
          rewrite (scons2_insertAt_prefix V p k
            (foam_empty V M) x y e n).
          replace (S (S k) + p) with (k + 2 + p) by lia.
          reflexivity.
        }
        pose proof (proj2 (Sat_ext V (foam_mem V M)
          (termGraphAt (substZeroBeforeMap p (k + 2) rho) 1 a)
          (scons V y (scons V x (insertAt (k + p) (foam_empty V M) e)))
          (insertAt (k + 2 + p) (foam_empty V M)
            (scons V y (scons V x e))) henv)) haIns as haEnv.
        rewrite (termGraphAt_map_ext a
          (substZeroBeforeMap p (k + 2) rho)
          (fun n => substZeroBeforeMap p k rho n + 2) 1) in haEnv.
        -- exact haEnv.
        -- intro n. symmetry. apply substZeroBeforeMap_add.
      * split.
        -- assert (hbMap : Sat V (foam_mem V M)
            (scons V y (scons V x e))
            (termGraphAt (substZeroAfterMap p (k + 2) rho) 0
              (PA.Term.subst (PA.Formula.substZeroAt p) b))).
           {
             rewrite <- (termGraphAt_map_ext
               (PA.Term.subst (PA.Formula.substZeroAt p) b)
               (fun n => substZeroAfterMap p k rho n + 2)
               (substZeroAfterMap p (k + 2) rho) 0).
             - exact hb.
             - intro n. apply substZeroAfterMap_add.
           }
           pose proof (proj1 (IHb p (k + 2) rho 0
             (scons V y (scons V x e)) ltac:(lia)) hbMap) as hbIns.
           assert (henv : forall n,
             scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e)) n =
               insertAt (k + 2 + p) (foam_empty V M)
                 (scons V y (scons V x e)) n).
           {
             intro n.
             rewrite (scons2_insertAt_prefix V p k
               (foam_empty V M) x y e n).
             replace (S (S k) + p) with (k + 2 + p) by lia.
             reflexivity.
           }
           pose proof (proj2 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p (k + 2) rho) 0 b)
             (scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e)))
             (insertAt (k + 2 + p) (foam_empty V M)
               (scons V y (scons V x e))) henv)) hbIns as hbEnv.
           rewrite (termGraphAt_map_ext b
             (substZeroBeforeMap p (k + 2) rho)
             (fun n => substZeroBeforeMap p k rho n + 2) 0) in hbEnv.
           ++ exact hbEnv.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- refine (proj1 (Sat_ext_free V (foam_mem V M)
             (addGraphAt (out + 2) 1 0)
             (scons V y (scons V x e))
             (scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e))) _) hg).
           intros i hi.
           destruct (addGraphAt_free i (out + 2) 1 0 hi)
             as [hiout | [hi1 | hi0]]; subst i.
           ++ replace (out + 2) with (S (S out)) by lia.
              simpl.
              rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
                [reflexivity | lia].
           ++ reflexivity.
           ++ reflexivity.
    + intros [x [y [ha [hb hg]]]].
      exists x, y.
      split.
      * rewrite (termGraphAt_map_ext
          (PA.Term.subst (PA.Formula.substZeroAt p) a)
          (fun n => substZeroAfterMap p k rho n + 2)
          (substZeroAfterMap p (k + 2) rho) 1).
        -- apply (proj2 (IHa p (k + 2) rho 1
             (scons V y (scons V x e)) ltac:(lia))).
           assert (henv : forall n,
             scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e)) n =
               insertAt (k + 2 + p) (foam_empty V M)
                 (scons V y (scons V x e)) n).
           {
             intro n.
             rewrite (scons2_insertAt_prefix V p k
               (foam_empty V M) x y e n).
             replace (S (S k) + p) with (k + 2 + p) by lia.
             reflexivity.
           }
           apply (proj1 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p (k + 2) rho) 1 a)
             (scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e)))
             (insertAt (k + 2 + p) (foam_empty V M)
               (scons V y (scons V x e))) henv)).
           rewrite (termGraphAt_map_ext a
             (substZeroBeforeMap p (k + 2) rho)
             (fun n => substZeroBeforeMap p k rho n + 2) 1).
           ++ exact ha.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- intro n. apply substZeroAfterMap_add.
      * split.
        -- rewrite (termGraphAt_map_ext
             (PA.Term.subst (PA.Formula.substZeroAt p) b)
             (fun n => substZeroAfterMap p k rho n + 2)
             (substZeroAfterMap p (k + 2) rho) 0).
           ++ apply (proj2 (IHb p (k + 2) rho 0
                (scons V y (scons V x e)) ltac:(lia))).
              assert (henv : forall n,
                scons V y (scons V x
                  (insertAt (k + p) (foam_empty V M) e)) n =
                  insertAt (k + 2 + p) (foam_empty V M)
                    (scons V y (scons V x e)) n).
              {
                intro n.
                rewrite (scons2_insertAt_prefix V p k
                  (foam_empty V M) x y e n).
                replace (S (S k) + p) with (k + 2 + p) by lia.
                reflexivity.
              }
              apply (proj1 (Sat_ext V (foam_mem V M)
                (termGraphAt (substZeroBeforeMap p (k + 2) rho) 0 b)
                (scons V y (scons V x
                  (insertAt (k + p) (foam_empty V M) e)))
                (insertAt (k + 2 + p) (foam_empty V M)
                  (scons V y (scons V x e))) henv)).
              rewrite (termGraphAt_map_ext b
                (substZeroBeforeMap p (k + 2) rho)
                (fun n => substZeroBeforeMap p k rho n + 2) 0).
              ** exact hb.
              ** intro n. symmetry. apply substZeroBeforeMap_add.
           ++ intro n. apply substZeroAfterMap_add.
        -- refine (proj2 (Sat_ext_free V (foam_mem V M)
             (addGraphAt (out + 2) 1 0)
             (scons V y (scons V x e))
             (scons V y (scons V x
               (insertAt (k + p) (foam_empty V M) e))) _) hg).
           intros i hi.
           destruct (addGraphAt_free i (out + 2) 1 0 hi)
             as [hiout | [hi1 | hi0]]; subst i.
           ++ replace (out + 2) with (S (S out)) by lia.
              simpl.
              rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
                [reflexivity | lia].
           ++ reflexivity.
           ++ reflexivity.
  - split.
    + intros [y [x [z [ha [hb [hcopy hg]]]]]].
      exists y, x, z.
      split.
      * assert (haMap : Sat V (foam_mem V M)
          (scons V z (scons V x (scons V y e)))
          (termGraphAt (substZeroAfterMap p (k + 3) rho) 1
            (PA.Term.subst (PA.Formula.substZeroAt p) a))).
        {
          rewrite <- (termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (fun n => substZeroAfterMap p k rho n + 3)
            (substZeroAfterMap p (k + 3) rho) 1).
          - exact ha.
          - intro n. apply substZeroAfterMap_add.
        }
        pose proof (proj1 (IHa p (k + 3) rho 1
          (scons V z (scons V x (scons V y e))) ltac:(lia)) haMap)
          as haIns.
        assert (henv : forall n,
          scons V z (scons V x (scons V y
            (insertAt (k + p) (foam_empty V M) e))) n =
            insertAt (k + 3 + p) (foam_empty V M)
              (scons V z (scons V x (scons V y e))) n).
        {
          intro n.
          rewrite (scons3_insertAt_prefix V p k
            (foam_empty V M) y x z e n).
          replace (S (S (S k)) + p) with (k + 3 + p) by lia.
          reflexivity.
        }
        pose proof (proj2 (Sat_ext V (foam_mem V M)
          (termGraphAt (substZeroBeforeMap p (k + 3) rho) 1 a)
          (scons V z (scons V x (scons V y
            (insertAt (k + p) (foam_empty V M) e))))
          (insertAt (k + 3 + p) (foam_empty V M)
            (scons V z (scons V x (scons V y e)))) henv)) haIns as haEnv.
        rewrite (termGraphAt_map_ext a
          (substZeroBeforeMap p (k + 3) rho)
          (fun n => substZeroBeforeMap p k rho n + 3) 1) in haEnv.
        -- exact haEnv.
        -- intro n. symmetry. apply substZeroBeforeMap_add.
      * split.
        -- assert (hbMap : Sat V (foam_mem V M)
            (scons V z (scons V x (scons V y e)))
            (termGraphAt (substZeroAfterMap p (k + 3) rho) 2
              (PA.Term.subst (PA.Formula.substZeroAt p) b))).
           {
             rewrite <- (termGraphAt_map_ext
               (PA.Term.subst (PA.Formula.substZeroAt p) b)
               (fun n => substZeroAfterMap p k rho n + 3)
               (substZeroAfterMap p (k + 3) rho) 2).
             - exact hb.
             - intro n. apply substZeroAfterMap_add.
           }
           pose proof (proj1 (IHb p (k + 3) rho 2
             (scons V z (scons V x (scons V y e))) ltac:(lia)) hbMap)
             as hbIns.
           assert (henv : forall n,
             scons V z (scons V x (scons V y
               (insertAt (k + p) (foam_empty V M) e))) n =
               insertAt (k + 3 + p) (foam_empty V M)
                 (scons V z (scons V x (scons V y e))) n).
           {
             intro n.
             rewrite (scons3_insertAt_prefix V p k
               (foam_empty V M) y x z e n).
             replace (S (S (S k)) + p) with (k + 3 + p) by lia.
             reflexivity.
           }
           pose proof (proj2 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p (k + 3) rho) 2 b)
             (scons V z (scons V x (scons V y
               (insertAt (k + p) (foam_empty V M) e))))
             (insertAt (k + 3 + p) (foam_empty V M)
               (scons V z (scons V x (scons V y e)))) henv)) hbIns
             as hbEnv.
           rewrite (termGraphAt_map_ext b
             (substZeroBeforeMap p (k + 3) rho)
             (fun n => substZeroBeforeMap p k rho n + 3) 2) in hbEnv.
           ++ exact hbEnv.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- split.
           ++ replace (out + 3) with (S (S (S out))) in hcopy by lia.
              simpl in hcopy.
              replace (out + 3) with (S (S (S out))) by lia.
              simpl.
              rewrite (insertAt_lt V (k + p) out (foam_empty V M) e);
                [exact hcopy | lia].
           ++ refine (proj1 (Sat_ext_free V (foam_mem V M) mulGraph
                (scons V z (scons V x (scons V y e)))
                (scons V z (scons V x (scons V y
                  (insertAt (k + p) (foam_empty V M) e)))) _) hg).
              intros i hi.
              destruct (mulGraph_free i hi) as [hi0 | [hi1 | hi2]];
                subst i; reflexivity.
    + intros [y [x [z [ha [hb [hcopy hg]]]]]].
      exists y, x, z.
      split.
      * rewrite (termGraphAt_map_ext
          (PA.Term.subst (PA.Formula.substZeroAt p) a)
          (fun n => substZeroAfterMap p k rho n + 3)
          (substZeroAfterMap p (k + 3) rho) 1).
        -- apply (proj2 (IHa p (k + 3) rho 1
             (scons V z (scons V x (scons V y e))) ltac:(lia))).
           assert (henv : forall n,
             scons V z (scons V x (scons V y
               (insertAt (k + p) (foam_empty V M) e))) n =
               insertAt (k + 3 + p) (foam_empty V M)
                 (scons V z (scons V x (scons V y e))) n).
           {
             intro n.
             rewrite (scons3_insertAt_prefix V p k
               (foam_empty V M) y x z e n).
             replace (S (S (S k)) + p) with (k + 3 + p) by lia.
             reflexivity.
           }
           apply (proj1 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p (k + 3) rho) 1 a)
             (scons V z (scons V x (scons V y
               (insertAt (k + p) (foam_empty V M) e))))
             (insertAt (k + 3 + p) (foam_empty V M)
               (scons V z (scons V x (scons V y e)))) henv)).
           rewrite (termGraphAt_map_ext a
             (substZeroBeforeMap p (k + 3) rho)
             (fun n => substZeroBeforeMap p k rho n + 3) 1).
           ++ exact ha.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- intro n. apply substZeroAfterMap_add.
      * split.
        -- rewrite (termGraphAt_map_ext
             (PA.Term.subst (PA.Formula.substZeroAt p) b)
             (fun n => substZeroAfterMap p k rho n + 3)
             (substZeroAfterMap p (k + 3) rho) 2).
           ++ apply (proj2 (IHb p (k + 3) rho 2
                (scons V z (scons V x (scons V y e))) ltac:(lia))).
              assert (henv : forall n,
                scons V z (scons V x (scons V y
                  (insertAt (k + p) (foam_empty V M) e))) n =
                  insertAt (k + 3 + p) (foam_empty V M)
                    (scons V z (scons V x (scons V y e))) n).
              {
                intro n.
                rewrite (scons3_insertAt_prefix V p k
                  (foam_empty V M) y x z e n).
                replace (S (S (S k)) + p) with (k + 3 + p) by lia.
                reflexivity.
              }
              apply (proj1 (Sat_ext V (foam_mem V M)
                (termGraphAt (substZeroBeforeMap p (k + 3) rho) 2 b)
                (scons V z (scons V x (scons V y
                  (insertAt (k + p) (foam_empty V M) e))))
                (insertAt (k + 3 + p) (foam_empty V M)
                  (scons V z (scons V x (scons V y e)))) henv)).
              rewrite (termGraphAt_map_ext b
                (substZeroBeforeMap p (k + 3) rho)
                (fun n => substZeroBeforeMap p k rho n + 3) 2).
              ** exact hb.
              ** intro n. symmetry. apply substZeroBeforeMap_add.
           ++ intro n. apply substZeroAfterMap_add.
        -- split.
           ++ replace (out + 3) with (S (S (S out))) in hcopy by lia.
              simpl in hcopy.
              replace (out + 3) with (S (S (S out))) by lia.
              simpl.
              change (z = insertAt (k + p) (foam_empty V M) e out) in hcopy.
              rewrite (insertAt_lt V (k + p) out (foam_empty V M) e) in hcopy;
                [exact hcopy | lia].
           ++ refine (proj2 (Sat_ext_free V (foam_mem V M) mulGraph
                (scons V z (scons V x (scons V y e)))
                (scons V z (scons V x (scons V y
                  (insertAt (k + p) (foam_empty V M) e)))) _) hg).
              intros i hi.
              destruct (mulGraph_free i hi) as [hi0 | [hi1 | hi2]];
                subst i; reflexivity.
Qed.

Lemma termGraphAt_exact : forall t rho out v e,
  (forall n, e (rho n) = ordinal_code (v n)) ->
  (Sat nat hf_mem e (termGraphAt rho out t) <->
    e out = ordinal_code (PA.Term.eval PA.natModel v t)).
Proof.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    intros rho out v e hrho; simpl.
  - split.
    + intro h.
      transitivity (e (rho n)); [ exact h | exact (hrho n) ].
    + intro h.
      transitivity (ordinal_code (v n)); [ exact h | symmetry; exact (hrho n) ].
  - split.
    + intro h.
      pose proof (proj1 (HF_emptyAt_empty ackermannHFModel e out) h) as hzero.
      change (e out = hf_empty) in hzero.
      exact hzero.
    + intro h.
      apply (proj2 (HF_emptyAt_empty ackermannHFModel e out)).
      change (e out = hf_empty).
      exact h.
  - split.
    + intro h.
      destruct h as [x [ht hs]].
      assert (hrho' : forall n,
        scons nat x e (rho n + 1) = ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 1) with (S (rho n)) by lia.
        simpl.
        exact (hrho n).
      }
      pose proof (proj1 (IHa (fun n => rho n + 1) 0 v
        (scons nat x e) hrho') ht) as htval.
      change (x = ordinal_code (PA.Term.eval PA.natModel v a)) in htval.
      pose proof (proj1 (HF_succAt_spec ackermannHFModel
        (scons nat x e) (out + 1) 0) hs) as hsval.
      replace (out + 1) with (S out) in hsval by lia.
      simpl in hsval.
      change (e out = hf_adjoin x x) in hsval.
      rewrite hsval, htval.
      reflexivity.
    + intro h.
      pose (x := ordinal_code (PA.Term.eval PA.natModel v a)).
      exists x.
      split.
      * assert (hrho' : forall n,
          scons nat x e (rho n + 1) = ordinal_code (v n)).
        {
          intro n.
          replace (rho n + 1) with (S (rho n)) by lia.
          simpl.
          exact (hrho n).
        }
        apply (proj2 (IHa (fun n => rho n + 1) 0 v
          (scons nat x e) hrho')).
        unfold x. reflexivity.
      * apply (proj2 (HF_succAt_spec ackermannHFModel
          (scons nat x e) (out + 1) 0)).
        replace (out + 1) with (S out) by lia.
        simpl.
        rewrite h.
        unfold x.
        reflexivity.
  - split.
    + intro h.
      destruct h as [x [y [ha [hb hadd]]]].
      assert (hrho' : forall n,
        scons nat y (scons nat x e) (rho n + 2) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 2) with (S (S (rho n))) by lia.
        simpl.
        exact (hrho n).
      }
      pose proof (proj1 (IHa (fun n => rho n + 2) 1 v
        (scons nat y (scons nat x e)) hrho') ha) as hx.
      pose proof (proj1 (IHb (fun n => rho n + 2) 0 v
        (scons nat y (scons nat x e)) hrho') hb) as hy.
      change (x = ordinal_code (PA.Term.eval PA.natModel v a)) in hx.
      change (y = ordinal_code (PA.Term.eval PA.natModel v b)) in hy.
      pose proof (addGraphAt_value_of_ordinal_inputs (out + 2) 1 0
        (PA.Term.eval PA.natModel v a) (PA.Term.eval PA.natModel v b)
        (scons nat y (scons nat x e)) hx hy hadd) as hout.
      replace (out + 2) with (S (S out)) in hout by lia.
      simpl in hout.
      change (e out = ordinal_code
        (PA.Term.eval PA.natModel v a + PA.Term.eval PA.natModel v b))
        in hout.
      exact hout.
    + intro h.
      pose (x := ordinal_code (PA.Term.eval PA.natModel v a)).
      pose (y := ordinal_code (PA.Term.eval PA.natModel v b)).
      assert (hrho' : forall n,
        scons nat y (scons nat x e) (rho n + 2) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 2) with (S (S (rho n))) by lia.
        simpl.
        exact (hrho n).
      }
      exists x, y.
      split.
      * apply (proj2 (IHa (fun n => rho n + 2) 1 v
          (scons nat y (scons nat x e)) hrho')).
        unfold x. reflexivity.
      * split.
        -- apply (proj2 (IHb (fun n => rho n + 2) 0 v
            (scons nat y (scons nat x e)) hrho')).
           unfold y. reflexivity.
        -- apply (addGraphAt_ordinal_code (out + 2) 1 0
            (PA.Term.eval PA.natModel v a)
            (PA.Term.eval PA.natModel v b)
            (scons nat y (scons nat x e))).
           ++ replace (out + 2) with (S (S out)) by lia.
              simpl.
              change (e out = ordinal_code
                (PA.Term.eval PA.natModel v a +
                 PA.Term.eval PA.natModel v b)).
              exact h.
           ++ unfold x. reflexivity.
           ++ unfold y. reflexivity.
  - split.
    + intro h.
      destruct h as [y [x [z [ha [hb [hcopy hmul]]]]]].
      assert (hrho' : forall n,
        scons nat z (scons nat x (scons nat y e)) (rho n + 3) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 3) with (S (S (S (rho n)))) by lia.
        simpl.
        exact (hrho n).
      }
      pose proof (proj1 (IHa (fun n => rho n + 3) 1 v
        (scons nat z (scons nat x (scons nat y e))) hrho') ha) as hx.
      pose proof (proj1 (IHb (fun n => rho n + 3) 2 v
        (scons nat z (scons nat x (scons nat y e))) hrho') hb) as hy.
      change (x = ordinal_code (PA.Term.eval PA.natModel v a)) in hx.
      change (y = ordinal_code (PA.Term.eval PA.natModel v b)) in hy.
      pose proof (mulGraph_value_of_ordinal_inputs
        (PA.Term.eval PA.natModel v a) (PA.Term.eval PA.natModel v b)
        (scons nat z (scons nat x (scons nat y e))) hx hy hmul) as hz.
      replace (out + 3) with (S (S (S out))) in hcopy by lia.
      simpl in hcopy.
      rewrite hcopy in hz.
      change (e out = ordinal_code
        (PA.Term.eval PA.natModel v a * PA.Term.eval PA.natModel v b))
        in hz.
      exact hz.
    + intro h.
      pose (y := ordinal_code (PA.Term.eval PA.natModel v b)).
      pose (x := ordinal_code (PA.Term.eval PA.natModel v a)).
      pose (z := ordinal_code
        (PA.Term.eval PA.natModel v a * PA.Term.eval PA.natModel v b)).
      assert (hrho' : forall n,
        scons nat z (scons nat x (scons nat y e)) (rho n + 3) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 3) with (S (S (S (rho n)))) by lia.
        simpl.
        exact (hrho n).
      }
      exists y, x, z.
      split.
      * apply (proj2 (IHa (fun n => rho n + 3) 1 v
          (scons nat z (scons nat x (scons nat y e))) hrho')).
        unfold x. reflexivity.
      * split.
        -- apply (proj2 (IHb (fun n => rho n + 3) 2 v
            (scons nat z (scons nat x (scons nat y e))) hrho')).
           unfold y. reflexivity.
        -- split.
           ++ replace (out + 3) with (S (S (S out))) by lia.
              simpl.
              unfold z.
              symmetry.
              change (e out = ordinal_code
                (PA.Term.eval PA.natModel v a *
                 PA.Term.eval PA.natModel v b)) in h.
              exact h.
           ++ unfold z, x, y.
              apply (mulGraph_ordinal_code
                (PA.Term.eval PA.natModel v a)
                (PA.Term.eval PA.natModel v b) e).
Qed.

Fixpoint formulaAt (rho : nat -> nat) (phi : PA.formula) : form :=
  match phi with
  | PA.pEq a b =>
      fEx (fEx (fAnd
        (termGraphAt (fun n => rho n + 2) 1 a)
        (fAnd
          (termGraphAt (fun n => rho n + 2) 0 b)
          (fEq 1 0))))
  | PA.pBot => fBot
  | PA.pImp a b => fImp (formulaAt rho a) (formulaAt rho b)
  | PA.pAnd a b => fAnd (formulaAt rho a) (formulaAt rho b)
  | PA.pOr a b => fOr (formulaAt rho a) (formulaAt rho b)
  | PA.pAll a => fAll (fImp domainForm (formulaAt (upVarMap rho) a))
  | PA.pEx a => fEx (fAnd domainForm (formulaAt (upVarMap rho) a))
  end.

Lemma formulaAt_map_ext : forall phi rho sigma,
  (forall n, rho n = sigma n) ->
  formulaAt rho phi = formulaAt sigma phi.
Proof.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; simpl; intros rho sigma h;
      try reflexivity.
  - rewrite (termGraphAt_map_ext a
      (fun n => rho n + 2) (fun n => sigma n + 2) 1).
    + rewrite (termGraphAt_map_ext b
        (fun n => rho n + 2) (fun n => sigma n + 2) 0).
      * reflexivity.
      * intro n. now rewrite h.
    + intro n. now rewrite h.
  - now rewrite (IHa rho sigma h), (IHb rho sigma h).
  - now rewrite (IHa rho sigma h), (IHb rho sigma h).
  - now rewrite (IHa rho sigma h), (IHb rho sigma h).
  - assert (hup : forall n, upVarMap rho n = upVarMap sigma n).
    {
      intros [|n]; simpl; [reflexivity | now rewrite h].
    }
    now rewrite (IHa (upVarMap rho) (upVarMap sigma) hup).
  - assert (hup : forall n, upVarMap rho n = upVarMap sigma n).
    {
      intros [|n]; simpl; [reflexivity | now rewrite h].
    }
    now rewrite (IHa (upVarMap rho) (upVarMap sigma) hup).
Qed.

Lemma formulaAt_substZeroAt_insert_model : forall V
    (M : FirstOrderAdjunctionModel V) phi p rho e,
  Sat V (foam_mem V M) e
    (formulaAt (substZeroAfterMap p 0 rho)
      (PA.Formula.subst (PA.Formula.substZeroAt p) phi)) <->
  Sat V (foam_mem V M) (insertAt p (foam_empty V M) e)
    (formulaAt (substZeroBeforeMap p 0 rho) phi).
Proof.
  intros V M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IH | a IH]; intros p rho e; simpl.
  - split.
    + intros [x [y [ha [hb heq]]]].
      exists x, y.
      split.
      * assert (haMap : Sat V (foam_mem V M)
          (scons V y (scons V x e))
          (termGraphAt (substZeroAfterMap p 2 rho) 1
            (PA.Term.subst (PA.Formula.substZeroAt p) a))).
        {
          rewrite <- (termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (fun n => substZeroAfterMap p 0 rho n + 2)
            (substZeroAfterMap p 2 rho) 1).
          - exact ha.
          - intro n. apply substZeroAfterMap_add.
        }
        pose proof (proj1 (termGraphAt_substZeroAt_insert_model
          V M a p 2 rho 1 (scons V y (scons V x e)) ltac:(lia))
          haMap) as haIns.
        assert (henv : forall n,
          scons V y (scons V x (insertAt p (foam_empty V M) e)) n =
            insertAt (2 + p) (foam_empty V M)
              (scons V y (scons V x e)) n).
        {
          intro n.
          rewrite (scons2_insertAt V p
            (foam_empty V M) x y e n).
          replace (S (S p)) with (2 + p) by lia.
          reflexivity.
        }
        pose proof (proj2 (Sat_ext V (foam_mem V M)
          (termGraphAt (substZeroBeforeMap p 2 rho) 1 a)
          (scons V y (scons V x (insertAt p (foam_empty V M) e)))
          (insertAt (2 + p) (foam_empty V M)
            (scons V y (scons V x e))) henv)) haIns as haEnv.
        rewrite (termGraphAt_map_ext a
          (substZeroBeforeMap p 2 rho)
          (fun n => substZeroBeforeMap p 0 rho n + 2) 1) in haEnv.
        -- exact haEnv.
        -- intro n. symmetry. apply substZeroBeforeMap_add.
      * split.
        -- assert (hbMap : Sat V (foam_mem V M)
            (scons V y (scons V x e))
            (termGraphAt (substZeroAfterMap p 2 rho) 0
              (PA.Term.subst (PA.Formula.substZeroAt p) b))).
           {
             rewrite <- (termGraphAt_map_ext
               (PA.Term.subst (PA.Formula.substZeroAt p) b)
               (fun n => substZeroAfterMap p 0 rho n + 2)
               (substZeroAfterMap p 2 rho) 0).
             - exact hb.
             - intro n. apply substZeroAfterMap_add.
           }
           pose proof (proj1 (termGraphAt_substZeroAt_insert_model
             V M b p 2 rho 0 (scons V y (scons V x e)) ltac:(lia))
             hbMap) as hbIns.
           assert (henv : forall n,
             scons V y (scons V x (insertAt p (foam_empty V M) e)) n =
               insertAt (2 + p) (foam_empty V M)
                 (scons V y (scons V x e)) n).
           {
             intro n.
             rewrite (scons2_insertAt V p
               (foam_empty V M) x y e n).
             replace (S (S p)) with (2 + p) by lia.
             reflexivity.
           }
           pose proof (proj2 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p 2 rho) 0 b)
             (scons V y (scons V x (insertAt p (foam_empty V M) e)))
             (insertAt (2 + p) (foam_empty V M)
               (scons V y (scons V x e))) henv)) hbIns as hbEnv.
           rewrite (termGraphAt_map_ext b
             (substZeroBeforeMap p 2 rho)
             (fun n => substZeroBeforeMap p 0 rho n + 2) 0) in hbEnv.
           ++ exact hbEnv.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- exact heq.
    + intros [x [y [ha [hb heq]]]].
      exists x, y.
      split.
      * rewrite (termGraphAt_map_ext
          (PA.Term.subst (PA.Formula.substZeroAt p) a)
          (fun n => substZeroAfterMap p 0 rho n + 2)
          (substZeroAfterMap p 2 rho) 1).
        -- apply (proj2 (termGraphAt_substZeroAt_insert_model
             V M a p 2 rho 1 (scons V y (scons V x e)) ltac:(lia))).
           assert (henv : forall n,
             scons V y (scons V x (insertAt p (foam_empty V M) e)) n =
               insertAt (2 + p) (foam_empty V M)
                 (scons V y (scons V x e)) n).
           {
             intro n.
             rewrite (scons2_insertAt V p
               (foam_empty V M) x y e n).
             replace (S (S p)) with (2 + p) by lia.
             reflexivity.
           }
           apply (proj1 (Sat_ext V (foam_mem V M)
             (termGraphAt (substZeroBeforeMap p 2 rho) 1 a)
             (scons V y (scons V x (insertAt p (foam_empty V M) e)))
             (insertAt (2 + p) (foam_empty V M)
               (scons V y (scons V x e))) henv)).
           rewrite (termGraphAt_map_ext a
             (substZeroBeforeMap p 2 rho)
             (fun n => substZeroBeforeMap p 0 rho n + 2) 1).
           ++ exact ha.
           ++ intro n. symmetry. apply substZeroBeforeMap_add.
        -- intro n. apply substZeroAfterMap_add.
      * split.
        -- rewrite (termGraphAt_map_ext
             (PA.Term.subst (PA.Formula.substZeroAt p) b)
             (fun n => substZeroAfterMap p 0 rho n + 2)
             (substZeroAfterMap p 2 rho) 0).
           ++ apply (proj2 (termGraphAt_substZeroAt_insert_model
                V M b p 2 rho 0 (scons V y (scons V x e)) ltac:(lia))).
              assert (henv : forall n,
                scons V y (scons V x (insertAt p (foam_empty V M) e)) n =
                  insertAt (2 + p) (foam_empty V M)
                    (scons V y (scons V x e)) n).
              {
                intro n.
                rewrite (scons2_insertAt V p
                  (foam_empty V M) x y e n).
                replace (S (S p)) with (2 + p) by lia.
                reflexivity.
              }
              apply (proj1 (Sat_ext V (foam_mem V M)
                (termGraphAt (substZeroBeforeMap p 2 rho) 0 b)
                (scons V y (scons V x (insertAt p (foam_empty V M) e)))
                (insertAt (2 + p) (foam_empty V M)
                  (scons V y (scons V x e))) henv)).
              rewrite (termGraphAt_map_ext b
                (substZeroBeforeMap p 2 rho)
                (fun n => substZeroBeforeMap p 0 rho n + 2) 0).
              ** exact hb.
              ** intro n. symmetry. apply substZeroBeforeMap_add.
           ++ intro n. apply substZeroAfterMap_add.
        -- exact heq.
  - reflexivity.
  - split; intros h ha.
    + apply (proj1 (IHb p rho e)).
      apply h.
      apply (proj2 (IHa p rho e)).
      exact ha.
    + apply (proj2 (IHb p rho e)).
      apply h.
      apply (proj1 (IHa p rho e)).
      exact ha.
  - split; intros [ha hb].
    + split.
      * apply (proj1 (IHa p rho e)). exact ha.
      * apply (proj1 (IHb p rho e)). exact hb.
    + split.
      * apply (proj2 (IHa p rho e)). exact ha.
      * apply (proj2 (IHb p rho e)). exact hb.
  - split; intros h.
    + destruct h as [ha | hb].
      * left. apply (proj1 (IHa p rho e)). exact ha.
      * right. apply (proj1 (IHb p rho e)). exact hb.
    + destruct h as [ha | hb].
      * left. apply (proj2 (IHa p rho e)). exact ha.
      * right. apply (proj2 (IHb p rho e)). exact hb.
  - split; intros hall d hdDomain.
    + assert (hdDomain' :
        Sat V (foam_mem V M) (scons V d e) domainForm).
      {
        apply (proj1 (domainForm_scons_insertAt V (foam_mem V M)
          p (foam_empty V M) d e)).
        exact hdDomain.
      }
      pose proof (hall d hdDomain') as hbody.
      rewrite PA.Formula.upSubst_substZeroAt in hbody.
      assert (hbodyNorm : Sat V (foam_mem V M) (scons V d e)
        (formulaAt (substZeroAfterMap (S p) 0 rho)
          (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a))).
      {
        rewrite <- (formulaAt_map_ext
          (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a)
          (upVarMap (substZeroAfterMap p 0 rho))
          (substZeroAfterMap (S p) 0 rho)).
        - exact hbody.
        - apply upVarMap_substZeroAfterMap_zero.
      }
      pose proof (proj1 (IH (S p) rho (scons V d e)) hbodyNorm)
        as hbodyIns.
      assert (henv : forall n,
        scons V d (insertAt p (foam_empty V M) e) n =
          insertAt (S p) (foam_empty V M) (scons V d e) n).
      {
        intro n.
        apply scons_insertAt.
      }
      pose proof (proj2 (Sat_ext V (foam_mem V M)
        (formulaAt (substZeroBeforeMap (S p) 0 rho) a)
        (scons V d (insertAt p (foam_empty V M) e))
        (insertAt (S p) (foam_empty V M) (scons V d e)) henv))
        hbodyIns as hbodyEnv.
      rewrite (formulaAt_map_ext a
        (substZeroBeforeMap (S p) 0 rho)
        (upVarMap (substZeroBeforeMap p 0 rho))) in hbodyEnv.
      * exact hbodyEnv.
      * intro n. symmetry. apply upVarMap_substZeroBeforeMap_zero.
    + assert (hdDomain' :
        Sat V (foam_mem V M)
          (scons V d (insertAt p (foam_empty V M) e)) domainForm).
      {
        apply (proj2 (domainForm_scons_insertAt V (foam_mem V M)
          p (foam_empty V M) d e)).
        exact hdDomain.
      }
      pose proof (hall d hdDomain') as hbody.
      assert (hbodyNorm : Sat V (foam_mem V M)
        (scons V d (insertAt p (foam_empty V M) e))
        (formulaAt (substZeroBeforeMap (S p) 0 rho) a)).
      {
        rewrite (formulaAt_map_ext a
          (substZeroBeforeMap (S p) 0 rho)
          (upVarMap (substZeroBeforeMap p 0 rho))).
        - exact hbody.
        - intro n. symmetry. apply upVarMap_substZeroBeforeMap_zero.
      }
      assert (henv : forall n,
        scons V d (insertAt p (foam_empty V M) e) n =
          insertAt (S p) (foam_empty V M) (scons V d e) n).
      {
        intro n.
        apply scons_insertAt.
      }
      pose proof (proj1 (Sat_ext V (foam_mem V M)
        (formulaAt (substZeroBeforeMap (S p) 0 rho) a)
        (scons V d (insertAt p (foam_empty V M) e))
        (insertAt (S p) (foam_empty V M) (scons V d e)) henv))
        hbodyNorm as hbodyIns.
      pose proof (proj2 (IH (S p) rho (scons V d e)) hbodyIns)
        as hbodyAfter.
      rewrite PA.Formula.upSubst_substZeroAt.
      rewrite (formulaAt_map_ext
        (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a)
        (upVarMap (substZeroAfterMap p 0 rho))
        (substZeroAfterMap (S p) 0 rho)).
      * exact hbodyAfter.
      * apply upVarMap_substZeroAfterMap_zero.
  - split.
    + intros [d [hdDomain hbody]].
      exists d.
      split.
      * apply (proj2 (domainForm_scons_insertAt V (foam_mem V M)
          p (foam_empty V M) d e)).
        exact hdDomain.
      * rewrite PA.Formula.upSubst_substZeroAt in hbody.
        assert (hbodyNorm : Sat V (foam_mem V M) (scons V d e)
          (formulaAt (substZeroAfterMap (S p) 0 rho)
            (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a))).
        {
          rewrite <- (formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a)
            (upVarMap (substZeroAfterMap p 0 rho))
            (substZeroAfterMap (S p) 0 rho)).
          - exact hbody.
          - apply upVarMap_substZeroAfterMap_zero.
        }
        pose proof (proj1 (IH (S p) rho (scons V d e)) hbodyNorm)
          as hbodyIns.
        assert (henv : forall n,
          scons V d (insertAt p (foam_empty V M) e) n =
            insertAt (S p) (foam_empty V M) (scons V d e) n).
        {
          intro n.
          apply scons_insertAt.
        }
        pose proof (proj2 (Sat_ext V (foam_mem V M)
          (formulaAt (substZeroBeforeMap (S p) 0 rho) a)
          (scons V d (insertAt p (foam_empty V M) e))
          (insertAt (S p) (foam_empty V M) (scons V d e)) henv))
          hbodyIns as hbodyEnv.
        rewrite (formulaAt_map_ext a
          (substZeroBeforeMap (S p) 0 rho)
          (upVarMap (substZeroBeforeMap p 0 rho))) in hbodyEnv.
        -- exact hbodyEnv.
        -- intro n. symmetry. apply upVarMap_substZeroBeforeMap_zero.
    + intros [d [hdDomain hbody]].
      exists d.
      split.
      * apply (proj1 (domainForm_scons_insertAt V (foam_mem V M)
          p (foam_empty V M) d e)).
        exact hdDomain.
      * assert (hbodyNorm : Sat V (foam_mem V M)
          (scons V d (insertAt p (foam_empty V M) e))
          (formulaAt (substZeroBeforeMap (S p) 0 rho) a)).
        {
          rewrite (formulaAt_map_ext a
            (substZeroBeforeMap (S p) 0 rho)
            (upVarMap (substZeroBeforeMap p 0 rho))).
          - exact hbody.
          - intro n. symmetry. apply upVarMap_substZeroBeforeMap_zero.
        }
        assert (henv : forall n,
          scons V d (insertAt p (foam_empty V M) e) n =
            insertAt (S p) (foam_empty V M) (scons V d e) n).
        {
          intro n.
          apply scons_insertAt.
        }
        pose proof (proj1 (Sat_ext V (foam_mem V M)
          (formulaAt (substZeroBeforeMap (S p) 0 rho) a)
          (scons V d (insertAt p (foam_empty V M) e))
          (insertAt (S p) (foam_empty V M) (scons V d e)) henv))
          hbodyNorm as hbodyIns.
        pose proof (proj2 (IH (S p) rho (scons V d e)) hbodyIns)
          as hbodyAfter.
        rewrite PA.Formula.upSubst_substZeroAt.
        rewrite (formulaAt_map_ext
          (PA.Formula.subst (PA.Formula.substZeroAt (S p)) a)
          (upVarMap (substZeroAfterMap p 0 rho))
          (substZeroAfterMap (S p) 0 rho)).
        -- exact hbodyAfter.
        -- apply upVarMap_substZeroAfterMap_zero.
Qed.

Lemma formulaAt_substZero_insert_model : forall V
    (M : FirstOrderAdjunctionModel V) phi rho e,
  Sat V (foam_mem V M) e
    (formulaAt rho (PA.Formula.subst PA.Formula.substZero phi)) <->
  Sat V (foam_mem V M) (insertAt 0 (foam_empty V M) e)
    (formulaAt (upVarMap rho) phi).
Proof.
  intros V M phi rho e.
  split; intro h.
  - assert (hNormL : Sat V (foam_mem V M) e
      (formulaAt (substZeroAfterMap 0 0 rho)
        (PA.Formula.subst (PA.Formula.substZeroAt 0) phi))).
    {
      rewrite PA.Formula.substZeroAt_zero.
      rewrite (formulaAt_map_ext
        (PA.Formula.subst PA.Formula.substZero phi)
        (substZeroAfterMap 0 0 rho) rho).
      - exact h.
      - apply substZeroAfterMap_zero_zero.
    }
    pose proof (proj1 (formulaAt_substZeroAt_insert_model
      V M phi 0 rho e) hNormL) as hNormR.
    rewrite (formulaAt_map_ext phi
      (substZeroBeforeMap 0 0 rho) (upVarMap rho)) in hNormR.
    + exact hNormR.
    + apply substZeroBeforeMap_zero_zero.
  - assert (hNormR : Sat V (foam_mem V M)
      (insertAt 0 (foam_empty V M) e)
      (formulaAt (substZeroBeforeMap 0 0 rho) phi)).
    {
      rewrite (formulaAt_map_ext phi
        (substZeroBeforeMap 0 0 rho) (upVarMap rho)).
      - exact h.
      - apply substZeroBeforeMap_zero_zero.
    }
    pose proof (proj2 (formulaAt_substZeroAt_insert_model
      V M phi 0 rho e) hNormR) as hNormL.
    rewrite PA.Formula.substZeroAt_zero in hNormL.
    rewrite (formulaAt_map_ext
      (PA.Formula.subst PA.Formula.substZero phi)
      (substZeroAfterMap 0 0 rho) rho) in hNormL.
    + exact hNormL.
    + apply substZeroAfterMap_zero_zero.
Qed.

Lemma formulaAt_substZero_scons_model : forall V
    (M : FirstOrderAdjunctionModel V) phi rho e,
  Sat V (foam_mem V M) e
    (formulaAt rho (PA.Formula.subst PA.Formula.substZero phi)) <->
  Sat V (foam_mem V M) (scons V (foam_empty V M) e)
    (formulaAt (upVarMap rho) phi).
Proof.
  intros V M phi rho e.
  eapply iff_trans.
  - apply formulaAt_substZero_insert_model.
  - apply Sat_ext.
    intro n.
    apply insertAt_zero.
Qed.

Lemma formulaAt_free : forall phi rho i,
  Free i (formulaAt rho phi) ->
    exists n, PA.Formula.Free n phi /\ i = rho n.
Proof.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; simpl; intros rho i h.
  - destruct h as [h | [h | h]].
    + destruct (termGraphAt_free a (fun n => rho n + 2) 1 (S (S i)) h)
        as [hi | [n [hn hi]]].
      * lia.
      * exists n. split; [left; exact hn | lia].
    + destruct (termGraphAt_free b (fun n => rho n + 2) 0 (S (S i)) h)
        as [hi | [n [hn hi]]].
      * lia.
      * exists n. split; [right; exact hn | lia].
    + destruct h as [hi | hi]; lia.
  - contradiction.
  - destruct h as [h | h].
    + destruct (IHa rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHb rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct h as [h | h].
    + destruct (IHa rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHb rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct h as [h | h].
    + destruct (IHa rho i h) as [n [hn hi]].
      exists n. split; [left; exact hn | exact hi].
    + destruct (IHb rho i h) as [n [hn hi]].
      exists n. split; [right; exact hn | exact hi].
  - destruct h as [h | h].
    + pose proof (domainForm_free (S i) h) as hi. lia.
    + destruct (IHa (upVarMap rho) (S i) h) as [n [hn hi]].
      destruct n as [|n].
      * simpl in hi. lia.
      * exists n. split; [exact hn | simpl in hi; lia].
  - destruct h as [h | h].
    + pose proof (domainForm_free (S i) h) as hi. lia.
    + destruct (IHa (upVarMap rho) (S i) h) as [n [hn hi]].
      destruct n as [|n].
      * simpl in hi. lia.
      * exists n. split; [exact hn | simpl in hi; lia].
Qed.

Lemma termGraphAt_var_spec : forall A (mem : A -> A -> Prop) rho out n e,
  Sat A mem e (termGraphAt rho out (PA.tVar n)) <-> e out = e (rho n).
Proof.
  reflexivity.
Qed.

Lemma termGraphAt_zero_spec : forall A (mem : A -> A -> Prop) rho out e,
  Sat A mem e (termGraphAt rho out PA.tZero) <->
    forall x, ~ mem x (e out).
Proof.
  intros A mem rho out e.
  simpl.
  apply HF_emptyAt_spec.
Qed.

Lemma termGraphAt_succ_var_spec :
  forall A (mem : A -> A -> Prop) rho out n e,
    Sat A mem e (termGraphAt rho out (PA.tSucc (PA.tVar n))) <->
      forall x, mem x (e out) <-> mem x (e (rho n)) \/ x = e (rho n).
Proof.
  intros A mem rho out n e.
  simpl.
  split.
  - intros [x [hx hs]] y.
    assert (hx' : x = e (rho n)).
    {
      change (x = scons A x e (rho n + 1)) in hx.
      replace (rho n + 1) with (S (rho n)) in hx by lia.
      simpl in hx.
      exact hx.
    }
    pose proof (proj1 (HF_adjoinAt_spec A mem
      (scons A x e) (out + 1) 0 0) hs y) as hy.
    change (mem y (scons A x e (out + 1)) <->
      mem y (scons A x e 0) \/ y = scons A x e 0) in hy.
    replace (out + 1) with (S out) in hy by lia.
    simpl in hy.
    rewrite hx' in hy.
    exact hy.
  - intro h.
    exists (e (rho n)).
    split.
    + change (e (rho n) = scons A (e (rho n)) e (rho n + 1)).
      replace (rho n + 1) with (S (rho n)) by lia.
      reflexivity.
    + apply (proj2 (HF_adjoinAt_spec A mem
        (scons A (e (rho n)) e) (out + 1) 0 0)).
      intro y.
      change (mem y (scons A (e (rho n)) e (out + 1)) <->
        mem y (scons A (e (rho n)) e 0) \/
          y = scons A (e (rho n)) e 0).
      replace (out + 1) with (S out) by lia.
      simpl.
      exact (h y).
Qed.

Lemma formulaAt_eq_var_spec :
  forall A (mem : A -> A -> Prop) rho m n e,
    Sat A mem e (formulaAt rho (PA.pEq (PA.tVar m) (PA.tVar n))) <->
      e (rho m) = e (rho n).
Proof.
  intros A mem rho m n e.
  simpl.
  split.
  - intros [x [y [hx [hy hxy]]]].
    pose proof (proj1 (termGraphAt_var_spec A mem
      (fun n => rho n + 2) 1 m (scons A y (scons A x e))) hx)
      as hx'.
    pose proof (proj1 (termGraphAt_var_spec A mem
      (fun n => rho n + 2) 0 n (scons A y (scons A x e))) hy)
      as hy'.
    change (x = scons A y (scons A x e) (rho m + 2)) in hx'.
    change (y = scons A y (scons A x e) (rho n + 2)) in hy'.
    replace (rho m + 2) with (S (S (rho m))) in hx' by lia.
    replace (rho n + 2) with (S (S (rho n))) in hy' by lia.
    simpl in hx', hy'.
    rewrite <- hx'.
    rewrite <- hy'.
    exact hxy.
  - intro h.
    exists (e (rho m)).
    exists (e (rho n)).
    repeat split.
    + apply (proj2 (termGraphAt_var_spec A mem
        (fun n => rho n + 2) 1 m
        (scons A (e (rho n)) (scons A (e (rho m)) e)))).
      change (e (rho m) =
        scons A (e (rho n)) (scons A (e (rho m)) e) (rho m + 2)).
      replace (rho m + 2) with (S (S (rho m))) by lia.
      reflexivity.
    + apply (proj2 (termGraphAt_var_spec A mem
        (fun n => rho n + 2) 0 n
        (scons A (e (rho n)) (scons A (e (rho m)) e)))).
      change (e (rho n) =
        scons A (e (rho n)) (scons A (e (rho m)) e) (rho n + 2)).
      replace (rho n + 2) with (S (S (rho n))) by lia.
      reflexivity.
    + exact h.
Qed.

Lemma formulaAt_zeroNotSucc_valid :
  forall A (mem : A -> A -> Prop) rho e,
    Sat A mem e (formulaAt rho PA.Formula.zeroNotSucc).
Proof.
  intros A mem rho e a _ hEq.
  destruct hEq as [sx [z [hsx [hz heq]]]].
  pose (E := scons A z (scons A sx (scons A a e))).
  pose proof (proj1 (termGraphAt_succ_var_spec A mem
    (fun n => upVarMap rho n + 2) 1 0 E) hsx) as hsx'.
  pose proof (proj1 (termGraphAt_zero_spec A mem
    (fun n => upVarMap rho n + 2) 0 E) hz) as hz'.
  assert (haSucc : mem a sx).
  {
    pose proof (hsx' a) as hspec.
    change (mem a sx <-> mem a a \/ a = a) in hspec.
    exact (proj2 hspec (or_intror eq_refl)).
  }
  rewrite heq in haSucc.
  exact (hz' a haSucc).
Qed.

Lemma addGraphAt_zero_right_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) out left right,
  e out = e left ->
  e right = foam_empty V M ->
  Sat V (foam_mem V M) e (addGraphAt out left right).
Proof.
  intros V M e out left right hout hright.
  unfold addGraphAt.
  pose (f := foam_zero_succ_rec_graph V M (e left)).
  exists f.
  split.
  - apply (proj2 (foam_HF_succRecApproxAt_spec V M
      (scons V f e) 0 (S left) (S right))).
    change (foam_succ_rec_approx V M (e left) f (e right)).
    rewrite hright.
    unfold f.
    apply foam_zero_succ_rec_graph_succRecApprox.
  - apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0)).
    change (foam_mem V M (foam_kpair_obj V M (e right) (e out)) f).
    rewrite hright, hout.
    unfold f.
    apply foam_zero_succ_rec_graph_base.
Qed.

Lemma addGraphAt_of_succRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) out left right f,
  foam_succ_rec_approx V M (e left) f (e right) ->
  foam_mem V M (foam_kpair_obj V M (e right) (e out)) f ->
  Sat V (foam_mem V M) e (addGraphAt out left right).
Proof.
  intros V M e out left right f hf hout.
  unfold addGraphAt.
  exists f.
  split.
  - apply (proj2 (foam_HF_succRecApproxAt_spec V M
      (scons V f e) 0 (S left) (S right))).
    change (foam_succ_rec_approx V M (e left) f (e right)).
    exact hf.
  - apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0)).
    change (foam_mem V M (foam_kpair_obj V M (e right) (e out)) f).
    exact hout.
Qed.

Lemma addGraphAt_succ_right_of_succRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V)
    outSucc left rightSucc right f z,
  OrdinalLike (foam_mem V M) (e right) ->
  e rightSucc = foam_adjoin V M (e right) (e right) ->
  e outSucc = foam_adjoin V M z z ->
  foam_succ_rec_approx V M (e left) f (e right) ->
  foam_mem V M (foam_kpair_obj V M (e right) z) f ->
  Sat V (foam_mem V M) e (addGraphAt outSucc left rightSucc).
Proof.
  intros V M e outSucc left rightSucc right f z hrightOrd hrightSucc
    houtSucc hf hout.
  pose (g := foam_succ_rec_graph_succ V M f (e right) z).
  apply (addGraphAt_of_succRecApprox_model V M e outSucc left rightSucc g).
  - change (foam_succ_rec_approx V M (e left) g (e rightSucc)).
    rewrite hrightSucc.
    unfold g.
    exact (foam_succ_rec_graph_succ_succRecApprox V M (e left) f
      (e right) z hrightOrd hf hout).
  - change (foam_mem V M (foam_kpair_obj V M (e rightSucc) (e outSucc)) g).
    rewrite hrightSucc, houtSucc.
    unfold g.
    exact (foam_succ_rec_graph_succ_new V M f (e right) z).
Qed.

Lemma termGraphAt_succ_var_firstOrder_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out n e,
  e out = foam_adjoin V M (e (rho n)) (e (rho n)) ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tSucc (PA.tVar n))).
Proof.
  intros V M rho out n e hout.
  simpl.
  exists (e (rho n)).
  split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 1) 0 n (scons V (e (rho n)) e))).
    change (e (rho n) = scons V (e (rho n)) e (rho n + 1)).
    replace (rho n + 1) with (S (rho n)) by lia.
    reflexivity.
  - apply (proj2 (foam_HF_succAt_spec V M
      (scons V (e (rho n)) e) (out + 1) 0)).
    change (scons V (e (rho n)) e (out + 1) =
      foam_adjoin V M (e (rho n)) (e (rho n))).
    replace (out + 1) with (S out) by lia.
    simpl.
    exact hout.
Qed.

Lemma termGraphAt_add_var_zero_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out n e,
  e out = e (rho n) ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tAdd (PA.tVar n) PA.tZero)).
Proof.
  intros V M rho out n e hout.
  simpl.
  exists (e (rho n)).
  exists (foam_empty V M).
  repeat split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 2) 1 n
      (scons V (foam_empty V M) (scons V (e (rho n)) e)))).
    change (e (rho n) =
      scons V (foam_empty V M) (scons V (e (rho n)) e) (rho n + 2)).
    replace (rho n + 2) with (S (S (rho n))) by lia.
    reflexivity.
  - apply (proj2 (foam_HF_emptyAt_empty V M
      (scons V (foam_empty V M) (scons V (e (rho n)) e)) 0)).
    reflexivity.
  - apply (addGraphAt_zero_right_model V M
      (scons V (foam_empty V M) (scons V (e (rho n)) e))
      (out + 2) 1 0).
    + replace (out + 2) with (S (S out)) by lia.
      simpl.
      exact hout.
    + reflexivity.
Qed.

Lemma termGraphAt_add_var_var_of_succRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f,
  foam_succ_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) (e out)) f ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tAdd (PA.tVar left) (PA.tVar right))).
Proof.
  intros V M rho out left right e f hf hout.
  simpl.
  exists (e (rho left)).
  exists (e (rho right)).
  repeat split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 2) 1 left
      (scons V (e (rho right)) (scons V (e (rho left)) e)))).
    change (e (rho left) =
      scons V (e (rho right)) (scons V (e (rho left)) e)
        (rho left + 2)).
    replace (rho left + 2) with (S (S (rho left))) by lia.
    reflexivity.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 2) 0 right
      (scons V (e (rho right)) (scons V (e (rho left)) e)))).
    change (e (rho right) =
      scons V (e (rho right)) (scons V (e (rho left)) e)
        (rho right + 2)).
    replace (rho right + 2) with (S (S (rho right))) by lia.
    reflexivity.
  - apply (addGraphAt_of_succRecApprox_model V M
      (scons V (e (rho right)) (scons V (e (rho left)) e))
      (out + 2) 1 0 f).
    + change (foam_succ_rec_approx V M (e (rho left)) f (e (rho right))).
      exact hf.
    + replace (out + 2) with (S (S out)) by lia.
      simpl.
      exact hout.
Qed.

Lemma termGraphAt_add_var_succ_var_of_succRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f z,
  OrdinalLike (foam_mem V M) (e (rho right)) ->
  e out = foam_adjoin V M z z ->
  foam_succ_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) z) f ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out
      (PA.tAdd (PA.tVar left) (PA.tSucc (PA.tVar right)))).
Proof.
  intros V M rho out left right e f z hrightOrd hout hf hz.
  simpl.
  pose (sy := foam_adjoin V M (e (rho right)) (e (rho right))).
  exists (e (rho left)).
  exists sy.
  repeat split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 2) 1 left
      (scons V sy (scons V (e (rho left)) e)))).
    change (e (rho left) =
      scons V sy (scons V (e (rho left)) e) (rho left + 2)).
    replace (rho left + 2) with (S (S (rho left))) by lia.
    reflexivity.
  - apply (termGraphAt_succ_var_firstOrder_model V M
      (fun n => rho n + 2) 0 right
      (scons V sy (scons V (e (rho left)) e))).
    change (sy = foam_adjoin V M
      (scons V sy (scons V (e (rho left)) e) (rho right + 2))
      (scons V sy (scons V (e (rho left)) e) (rho right + 2))).
    replace (rho right + 2) with (S (S (rho right))) by lia.
    simpl.
    unfold sy.
    reflexivity.
  - apply (addGraphAt_succ_right_of_succRecApprox_model V M
      (scons V sy (scons V (e (rho left)) e))
      (out + 2) 1 0 (rho right + 2) f z).
    + change (OrdinalLike (foam_mem V M)
        (scons V sy (scons V (e (rho left)) e) (rho right + 2))).
      replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      exact hrightOrd.
    + change (sy = foam_adjoin V M
        (scons V sy (scons V (e (rho left)) e) (rho right + 2))
        (scons V sy (scons V (e (rho left)) e) (rho right + 2))).
      replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      unfold sy.
      reflexivity.
    + replace (out + 2) with (S (S out)) by lia.
      simpl.
      exact hout.
    + replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      exact hf.
    + replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      exact hz.
Qed.

Lemma termGraphAt_succ_add_var_var_of_succRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f z,
  e out = foam_adjoin V M z z ->
  foam_succ_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) z) f ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out
      (PA.tSucc (PA.tAdd (PA.tVar left) (PA.tVar right)))).
Proof.
  intros V M rho out left right e f z hout hf hz.
  simpl.
  exists z.
  split.
  - apply (termGraphAt_add_var_var_of_succRecApprox_model V M
      (fun n => rho n + 1) 0 left right (scons V z e) f).
    + change (foam_succ_rec_approx V M
        (scons V z e (rho left + 1)) f
        (scons V z e (rho right + 1))).
      replace (rho left + 1) with (S (rho left)) by lia.
      replace (rho right + 1) with (S (rho right)) by lia.
      simpl.
      exact hf.
    + change (foam_mem V M
        (foam_kpair_obj V M (scons V z e (rho right + 1))
          (scons V z e 0)) f).
      replace (rho right + 1) with (S (rho right)) by lia.
      simpl.
      exact hz.
  - apply (proj2 (foam_HF_succAt_spec V M (scons V z e)
      (out + 1) 0)).
    change (scons V z e (out + 1) = foam_adjoin V M z z).
    replace (out + 1) with (S out) by lia.
    simpl.
    exact hout.
Qed.

Lemma formulaAt_addSucc_valid_model_of_succRecTotal : forall V
    (M : FirstOrderAdjunctionModel V),
  (forall s m, OrdinalLike (foam_mem V M) m ->
    foam_succ_rec_total V M s m) ->
  forall rho e, Sat V (foam_mem V M) e (formulaAt rho PA.Formula.addSucc).
Proof.
  intros V M hTotal rho e x _ y hyDomain.
  pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
    (scons V y (scons V x e)) 0) hyDomain) as hyOrd.
  destruct (hTotal x y hyOrd) as [f [z [hf hz]]].
  pose (sz := foam_adjoin V M z z).
  pose (sigma := fun n => upVarMap (upVarMap rho) n + 2).
  pose (Eeq := scons V sz (scons V sz (scons V y (scons V x e)))).
  simpl.
  exists sz.
  exists sz.
  split.
  - change (Sat V (foam_mem V M) Eeq
      (termGraphAt sigma 1
        (PA.tAdd (PA.tVar 1) (PA.tSucc (PA.tVar 0))))).
    apply (termGraphAt_add_var_succ_var_of_succRecApprox_model V M
      sigma 1 1 0 Eeq f z).
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hyOrd.
    + unfold Eeq, sz.
      simpl.
      reflexivity.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hf.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hz.
  - split.
    + change (Sat V (foam_mem V M) Eeq
        (termGraphAt sigma 0
          (PA.tSucc (PA.tAdd (PA.tVar 1) (PA.tVar 0))))).
      apply (termGraphAt_succ_add_var_var_of_succRecApprox_model V M
        sigma 0 1 0 Eeq f z).
      * unfold Eeq, sz.
        simpl.
        reflexivity.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hf.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hz.
    + reflexivity.
Qed.

Lemma formulaAt_addSucc_valid_model_of_mem_max_exists : forall V
    (M : FirstOrderAdjunctionModel V),
  (forall a, (exists x, foam_mem V M x a) ->
    exists p, foam_mem V M p a /\
      forall q, foam_mem V M q a -> ~ foam_mem V M p q) ->
  forall rho e, Sat V (foam_mem V M) e (formulaAt rho PA.Formula.addSucc).
Proof.
  intros V M hMax rho e.
  apply (formulaAt_addSucc_valid_model_of_succRecTotal V M).
  intros s m hm.
  exact (foam_succ_rec_total_of_ordinalLike_of_mem_max_exists V M
    hMax s m hm).
Qed.

Lemma formulaAt_addSucc_valid_finite_model : forall V
    (M : FirstOrderFiniteAdjunctionModel V) rho e,
  Sat V (foam_mem V M) e (formulaAt rho PA.Formula.addSucc).
Proof.
  intros V M rho e.
  apply (formulaAt_addSucc_valid_model_of_succRecTotal V M).
  intros s m hm.
  exact (fofam_succ_rec_total_of_ordinalLike V M s m hm).
Qed.

Lemma formulaAt_addZero_valid_model : forall V
    (M : FirstOrderAdjunctionModel V) rho e,
  Sat V (foam_mem V M) e (formulaAt rho PA.Formula.addZero).
Proof.
  intros V M rho e x _.
  simpl.
  exists x.
  exists x.
  repeat split.
  - change (Sat V (foam_mem V M)
      (scons V x (scons V x (scons V x e)))
      (termGraphAt (fun n => upVarMap rho n + 2) 1
        (PA.tAdd (PA.tVar 0) PA.tZero))).
    apply termGraphAt_add_var_zero_model.
    reflexivity.
Qed.

Lemma mulStepAt_empty_model : forall V
    (M : FirstOrderAdjunctionModel V) e f a m,
  e m = foam_empty V M ->
  Sat V (foam_mem V M) e (mulStepAt f a m).
Proof.
  intros V M e f a m hm k t y hkm.
  change (foam_mem V M k (e m)) in hkm.
  rewrite hm in hkm.
  exact (False_rect _ (foam_empty_spec V M k hkm)).
Qed.

Lemma mulGraphAt_of_mulRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) out left right f,
  foam_mul_rec_approx V M (e left) f (e right) ->
  foam_mem V M (foam_kpair_obj V M (e right) (e out)) f ->
  Sat V (foam_mem V M) e (mulGraphAt out left right).
Proof.
  intros V M e out left right f hf hout.
  unfold mulGraphAt.
  exists f.
  split.
  - apply (proj2 (foam_mulRecApproxAt_spec V M
      (scons V f e) 0 (S left) (S right))).
    change (foam_mul_rec_approx V M (e left) f (e right)).
    exact hf.
  - apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0)).
    change (foam_mem V M (foam_kpair_obj V M (e right) (e out)) f).
    exact hout.
Qed.

Lemma mulGraphAt_succ_right_of_mulRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V)
    out left rightSucc right f z g y,
  OrdinalLike (foam_mem V M) (e right) ->
  e rightSucc = foam_adjoin V M (e right) (e right) ->
  e out = y ->
  foam_mul_rec_approx V M (e left) f (e right) ->
  foam_mem V M (foam_kpair_obj V M (e right) z) f ->
  foam_succ_rec_approx V M z g (e left) ->
  foam_mem V M (foam_kpair_obj V M (e left) y) g ->
  Sat V (foam_mem V M) e (mulGraphAt out left rightSucc).
Proof.
  intros V M e out left rightSucc right f z g y hrightOrd hrightSucc
    hout hf hz hg hy.
  pose (h := foam_mul_rec_graph_succ V M f (e right) y).
  apply (mulGraphAt_of_mulRecApprox_model V M e out left rightSucc h).
  - change (foam_mul_rec_approx V M (e left) h (e rightSucc)).
    rewrite hrightSucc.
    unfold h.
    apply (foam_mul_rec_graph_succ_mulRecApprox V M (e left) f
      (e right) z y hrightOrd hf hz).
    exists g.
    split; assumption.
  - change (foam_mem V M (foam_kpair_obj V M (e rightSucc) (e out)) h).
    rewrite hrightSucc, hout.
    unfold h.
    apply foam_mul_rec_graph_succ_new.
Qed.

Lemma mulGraphAt_zero_right_model : forall V
    (M : FirstOrderAdjunctionModel V) (e : nat -> V) out left right,
  e out = foam_empty V M ->
  e right = foam_empty V M ->
  Sat V (foam_mem V M) e (mulGraphAt out left right).
Proof.
  intros V M e out left right hout hright.
  unfold mulGraphAt.
  pose (f := foam_zero_succ_rec_graph V M (foam_empty V M)).
  pose proof (foam_zero_succ_rec_graph_succRecApprox V M (foam_empty V M))
    as hf.
  destruct hf as [hfun [hkeys [hbase [htotal _hstep]]]].
  exists f.
  split.
  - unfold mulRecApproxAt.
    repeat split.
    + apply (proj2 (foam_HF_pairFunctionalAt_spec V M (scons V f e) 0)).
      exact hfun.
    + apply (proj2 (foam_HF_pairKeysBelowSuccAt_spec V M
        (scons V f e) 0 (S right))).
      change (foam_pair_keys_below_succ V M f (e right)).
      rewrite hright.
      exact hkeys.
    + apply (proj2 (foam_HF_pairZeroBaseAt_spec V M (scons V f e) 0)).
      exact hbase.
    + apply (proj2 (foam_HF_pairTotalBelowSuccAt_spec V M
        (scons V f e) 0 (S right))).
      change (foam_pair_total_below_succ V M f (e right)).
      rewrite hright.
      exact htotal.
    + apply (mulStepAt_empty_model V M (scons V f e) 0 (S left) (S right)).
      simpl.
      exact hright.
  - apply (proj2 (foam_HF_pairMemAt_spec V M
      (scons V f e) (S right) (S out) 0)).
    change (foam_mem V M (foam_kpair_obj V M (e right) (e out)) f).
    rewrite hright, hout.
    unfold f.
    apply foam_zero_succ_rec_graph_base.
Qed.

Lemma termGraphAt_mul_var_var_of_mulRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f,
  foam_mul_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) (e out)) f ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tMul (PA.tVar left) (PA.tVar right))).
Proof.
  intros V M rho out left right e f hf hout.
  simpl.
  exists (e (rho right)).
  exists (e (rho left)).
  exists (e out).
  split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 3) 1 left
      (scons V (e out)
        (scons V (e (rho left)) (scons V (e (rho right)) e))))).
    change (e (rho left) =
      scons V (e out)
        (scons V (e (rho left)) (scons V (e (rho right)) e))
        (rho left + 3)).
    replace (rho left + 3) with (S (S (S (rho left)))) by lia.
    reflexivity.
  - split.
    + apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
        (fun n => rho n + 3) 2 right
        (scons V (e out)
          (scons V (e (rho left)) (scons V (e (rho right)) e))))).
      change (e (rho right) =
        scons V (e out)
          (scons V (e (rho left)) (scons V (e (rho right)) e))
          (rho right + 3)).
      replace (rho right + 3) with (S (S (S (rho right)))) by lia.
      reflexivity.
    + split.
      * replace (out + 3) with (S (S (S out))) by lia.
        simpl.
        reflexivity.
      * apply (mulGraphAt_of_mulRecApprox_model V M
          (scons V (e out)
            (scons V (e (rho left)) (scons V (e (rho right)) e)))
          0 1 2 f).
        -- change (foam_mul_rec_approx V M
            (e (rho left)) f (e (rho right))).
           exact hf.
        -- change (foam_mem V M
            (foam_kpair_obj V M (e (rho right)) (e out)) f).
           exact hout.
Qed.

Lemma termGraphAt_mul_var_succ_var_of_mulRecApprox_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f z g y,
  OrdinalLike (foam_mem V M) (e (rho right)) ->
  e out = y ->
  foam_mul_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) z) f ->
  foam_succ_rec_approx V M z g (e (rho left)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho left)) y) g ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out
      (PA.tMul (PA.tVar left) (PA.tSucc (PA.tVar right)))).
Proof.
  intros V M rho out left right e f z g y hrightOrd hout hf hz hg hy.
  simpl.
  pose (sy := foam_adjoin V M (e (rho right)) (e (rho right))).
  pose (E := scons V y (scons V (e (rho left)) (scons V sy e))).
  exists sy.
  exists (e (rho left)).
  exists y.
  split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 3) 1 left E)).
    unfold E.
    change (e (rho left) =
      scons V y (scons V (e (rho left)) (scons V sy e))
        (rho left + 3)).
    replace (rho left + 3) with (S (S (S (rho left)))) by lia.
    reflexivity.
  - split.
    + apply (termGraphAt_succ_var_firstOrder_model V M
        (fun n => rho n + 3) 2 right E).
      unfold E.
      change (sy = foam_adjoin V M
        (scons V y (scons V (e (rho left)) (scons V sy e))
          (rho right + 3))
        (scons V y (scons V (e (rho left)) (scons V sy e))
          (rho right + 3))).
      replace (rho right + 3) with (S (S (S (rho right)))) by lia.
      simpl.
      unfold sy.
      reflexivity.
    + split.
      * unfold E.
        replace (out + 3) with (S (S (S out))) by lia.
        simpl.
        symmetry.
        exact hout.
      * apply (mulGraphAt_succ_right_of_mulRecApprox_model V M E
          0 1 2 (rho right + 3) f z g y).
        -- unfold E.
           replace (rho right + 3) with (S (S (S (rho right)))) by lia.
           simpl.
           exact hrightOrd.
        -- unfold E.
           replace (rho right + 3) with (S (S (S (rho right)))) by lia.
           simpl.
           unfold sy.
           reflexivity.
        -- reflexivity.
        -- unfold E.
           replace (rho right + 3) with (S (S (S (rho right)))) by lia.
           simpl.
           exact hf.
        -- unfold E.
           replace (rho right + 3) with (S (S (S (rho right)))) by lia.
           simpl.
           exact hz.
        -- unfold E.
           simpl.
           exact hg.
        -- unfold E.
           simpl.
           exact hy.
Qed.

Lemma termGraphAt_add_mul_var_var_var_of_traces_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out left right e f z g y,
  e out = y ->
  foam_mul_rec_approx V M (e (rho left)) f (e (rho right)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho right)) z) f ->
  foam_succ_rec_approx V M z g (e (rho left)) ->
  foam_mem V M (foam_kpair_obj V M (e (rho left)) y) g ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out
      (PA.tAdd
        (PA.tMul (PA.tVar left) (PA.tVar right))
        (PA.tVar left))).
Proof.
  intros V M rho out left right e f z g y hout hf hz hg hy.
  simpl.
  pose (E := scons V (e (rho left)) (scons V z e)).
  exists z.
  exists (e (rho left)).
  split.
  - apply (termGraphAt_mul_var_var_of_mulRecApprox_model V M
      (fun n => rho n + 2) 1 left right E f).
    + unfold E.
      replace (rho left + 2) with (S (S (rho left))) by lia.
      replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      exact hf.
    + unfold E.
      replace (rho right + 2) with (S (S (rho right))) by lia.
      simpl.
      exact hz.
  - split.
    + apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
        (fun n => rho n + 2) 0 left E)).
      unfold E.
      change (e (rho left) =
        scons V (e (rho left)) (scons V z e) (rho left + 2)).
      replace (rho left + 2) with (S (S (rho left))) by lia.
      reflexivity.
    + apply (addGraphAt_of_succRecApprox_model V M E
        (out + 2) 1 0 g).
      * unfold E.
        change (foam_succ_rec_approx V M z g (e (rho left))).
        exact hg.
      * replace (out + 2) with (S (S out)) by lia.
        unfold E.
        simpl.
        rewrite hout.
        exact hy.
Qed.

Lemma termGraphAt_mul_var_zero_model : forall V
    (M : FirstOrderAdjunctionModel V) rho out n e,
  e out = foam_empty V M ->
  Sat V (foam_mem V M) e
    (termGraphAt rho out (PA.tMul (PA.tVar n) PA.tZero)).
Proof.
  intros V M rho out n e hout.
  simpl.
  exists (foam_empty V M).
  exists (e (rho n)).
  exists (foam_empty V M).
  repeat split.
  - apply (proj2 (termGraphAt_var_spec V (foam_mem V M)
      (fun n => rho n + 3) 1 n
      (scons V (foam_empty V M)
        (scons V (e (rho n)) (scons V (foam_empty V M) e))))).
    change (e (rho n) =
      scons V (foam_empty V M)
        (scons V (e (rho n)) (scons V (foam_empty V M) e))
        (rho n + 3)).
    replace (rho n + 3) with (S (S (S (rho n)))) by lia.
    reflexivity.
  - apply (proj2 (foam_HF_emptyAt_empty V M
      (scons V (foam_empty V M)
        (scons V (e (rho n)) (scons V (foam_empty V M) e))) 2)).
    reflexivity.
  - replace (out + 3) with (S (S (S out))) by lia.
    simpl.
    symmetry.
    exact hout.
  - apply (mulGraphAt_zero_right_model V M
      (scons V (foam_empty V M)
        (scons V (e (rho n)) (scons V (foam_empty V M) e)))
      0 1 2).
    + reflexivity.
    + reflexivity.
Qed.

Lemma formulaAt_mulZero_valid_model : forall V
    (M : FirstOrderAdjunctionModel V) rho e,
  Sat V (foam_mem V M) e (formulaAt rho PA.Formula.mulZero).
Proof.
  intros V M rho e x _.
  simpl.
  exists (foam_empty V M).
  exists (foam_empty V M).
  repeat split.
  - change (Sat V (foam_mem V M)
      (scons V (foam_empty V M) (scons V (foam_empty V M) (scons V x e)))
      (termGraphAt (fun n => upVarMap rho n + 2) 1
        (PA.tMul (PA.tVar 0) PA.tZero))).
    apply termGraphAt_mul_var_zero_model.
    reflexivity.
  - apply (proj2 (foam_HF_emptyAt_empty V M
      (scons V (foam_empty V M) (scons V (foam_empty V M) (scons V x e))) 0)).
    reflexivity.
Qed.

Lemma formulaAt_mulSucc_valid_finite_model : forall V
    (M : FirstOrderFiniteAdjunctionModel V) rho e,
  Sat V (foam_mem V M) e (formulaAt rho PA.Formula.mulSucc).
Proof.
  intros V M rho e x hxDomain y hyDomain.
  pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
    (scons V x e) 0) hxDomain) as hxOrd.
  pose proof (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
    (scons V y (scons V x e)) 0) hyDomain) as hyOrd.
  destruct (fofam_mul_rec_total_of_ordinalLike V M x y hxOrd hyOrd)
    as [f [z [hf hz]]].
  destruct (fofam_succ_rec_total_of_ordinalLike V M z x hxOrd)
    as [g [w [hg hw]]].
  pose (sigma := fun n => upVarMap (upVarMap rho) n + 2).
  pose (Eeq := scons V w (scons V w (scons V y (scons V x e)))).
  simpl.
  exists w.
  exists w.
  split.
  - change (Sat V (foam_mem V M) Eeq
      (termGraphAt sigma 1
        (PA.tMul (PA.tVar 1) (PA.tSucc (PA.tVar 0))))).
    apply (termGraphAt_mul_var_succ_var_of_mulRecApprox_model V M
      sigma 1 1 0 Eeq f z g w).
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hyOrd.
    + unfold Eeq.
      simpl.
      reflexivity.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hf.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hz.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hg.
    + unfold sigma, Eeq, upVarMap.
      simpl.
      exact hw.
  - split.
    + change (Sat V (foam_mem V M) Eeq
        (termGraphAt sigma 0
          (PA.tAdd
            (PA.tMul (PA.tVar 1) (PA.tVar 0))
            (PA.tVar 1)))).
      apply (termGraphAt_add_mul_var_var_var_of_traces_model V M
        sigma 0 1 0 Eeq f z g w).
      * unfold Eeq.
        simpl.
        reflexivity.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hf.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hz.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hg.
      * unfold sigma, Eeq, upVarMap.
        simpl.
        exact hw.
    + reflexivity.
Qed.

Lemma formulaAt_succInj_of_irrefl :
  forall A (mem : A -> A -> Prop),
    (forall a, ~ mem a a) ->
    forall rho e, Sat A mem e (formulaAt rho PA.Formula.succInj).
Proof.
  intros A mem hIrrefl rho e a ha b hb hEq.
  destruct hEq as [sa [sb [hsa [hsb heq]]]].
  pose (E := scons A sb (scons A sa (scons A b (scons A a e)))).
  pose proof (proj1 (termGraphAt_succ_var_spec A mem
    (fun n => upVarMap (upVarMap rho) n + 2) 1 1 E) hsa) as hsa'.
  pose proof (proj1 (termGraphAt_succ_var_spec A mem
    (fun n => upVarMap (upVarMap rho) n + 2) 0 0 E) hsb) as hsb'.
  assert (hsaSpec : forall x, mem x sa <-> mem x a \/ x = a).
  {
    intro x.
    pose proof (hsa' x) as hx.
    change (mem x sa <-> mem x a \/ x = a) in hx.
    exact hx.
  }
  assert (hsbSpec : forall x, mem x sb <-> mem x b \/ x = b).
  {
    intro x.
    pose proof (hsb' x) as hx.
    change (mem x sb <-> mem x b \/ x = b) in hx.
    exact hx.
  }
  pose proof (proj1 (HF_ordinalLikeAt_spec A mem (scons A a e) 0) ha)
    as haOrd.
  pose proof (proj1 (HF_ordinalLikeAt_spec A mem
    (scons A b (scons A a e)) 0) hb) as hbOrd.
  assert (hab : a = b).
  {
    assert (haSucc : mem a sb).
    {
      rewrite <- heq.
      exact (proj2 (hsaSpec a) (or_intror eq_refl)).
    }
    destruct (proj1 (hsbSpec a) haSucc) as [hab | hab].
    - assert (hbSucc : mem b sa).
      {
        rewrite heq.
        exact (proj2 (hsbSpec b) (or_intror eq_refl)).
      }
      destruct (proj1 (hsaSpec b) hbSucc) as [hba | hba].
      + destruct hbOrd as [hbTrans _].
        assert (hbb : mem b b).
        {
          eapply hbTrans; eauto.
        }
        exfalso.
        exact (hIrrefl b hbb).
      + symmetry. exact hba.
    - exact hab.
  }
  apply (proj2 (formulaAt_eq_var_spec A mem
    (upVarMap (upVarMap rho)) 1 0 (scons A b (scons A a e)))).
  exact hab.
Qed.

Lemma formulaAt_closeN_valid :
  forall A (mem : A -> A -> Prop) phi,
    (forall rho e, Sat A mem e (formulaAt rho phi)) ->
    forall k rho e, Sat A mem e (formulaAt rho (PA.Formula.closeN k phi)).
Proof.
  intros A mem phi h k.
  revert phi h.
  induction k as [|k IH]; intros phi h rho e; simpl.
  - apply h.
  - apply IH.
    intros rho' e' x _.
    apply h.
Qed.

Lemma formulaAt_sealPA_valid :
  forall A (mem : A -> A -> Prop) phi,
    (forall rho e, Sat A mem e (formulaAt rho phi)) ->
    forall rho e, Sat A mem e (formulaAt rho (PA.Formula.sealPA phi)).
Proof.
  intros A mem phi h rho e.
  unfold PA.Formula.sealPA.
  apply formulaAt_closeN_valid.
  exact h.
Qed.

Lemma formulaAt_exact : forall phi rho v e,
  (forall n, e (rho n) = ordinal_code (v n)) ->
  (Sat nat hf_mem e (formulaAt rho phi) <->
    PA.Formula.Sat PA.natModel v phi).
Proof.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; simpl; intros rho v e hrho.
  - split.
    + intro h.
      destruct h as [x [y [ha [hb heq]]]].
      assert (hrho' : forall n,
        scons nat y (scons nat x e) (rho n + 2) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 2) with (S (S (rho n))) by lia.
        simpl.
        exact (hrho n).
      }
      pose proof (proj1 (termGraphAt_exact a (fun n => rho n + 2) 1 v
        (scons nat y (scons nat x e)) hrho') ha) as hx.
      pose proof (proj1 (termGraphAt_exact b (fun n => rho n + 2) 0 v
        (scons nat y (scons nat x e)) hrho') hb) as hy.
      change (x = ordinal_code (PA.Term.eval PA.natModel v a)) in hx.
      change (y = ordinal_code (PA.Term.eval PA.natModel v b)) in hy.
      apply ordinal_code_injective.
      rewrite <- hx, <- hy.
      exact heq.
    + intro h.
      pose (x := ordinal_code (PA.Term.eval PA.natModel v a)).
      pose (y := ordinal_code (PA.Term.eval PA.natModel v b)).
      assert (hrho' : forall n,
        scons nat y (scons nat x e) (rho n + 2) =
          ordinal_code (v n)).
      {
        intro n.
        replace (rho n + 2) with (S (S (rho n))) by lia.
        simpl.
        exact (hrho n).
      }
      exists x, y.
      split.
      * apply (proj2 (termGraphAt_exact a (fun n => rho n + 2) 1 v
          (scons nat y (scons nat x e)) hrho')).
        unfold x. reflexivity.
      * split.
        -- apply (proj2 (termGraphAt_exact b (fun n => rho n + 2) 0 v
            (scons nat y (scons nat x e)) hrho')).
           unfold y. reflexivity.
        -- unfold x, y.
           now rewrite h.
  - reflexivity.
  - split.
    + intros h ha.
      apply (proj1 (IHb rho v e hrho)).
      apply h.
      apply (proj2 (IHa rho v e hrho)).
      exact ha.
    + intros h ha.
      apply (proj2 (IHb rho v e hrho)).
      apply h.
      apply (proj1 (IHa rho v e hrho)).
      exact ha.
  - split.
    + intros [ha hb].
      split.
      * apply (proj1 (IHa rho v e hrho)). exact ha.
      * apply (proj1 (IHb rho v e hrho)). exact hb.
    + intros [ha hb].
      split.
      * apply (proj2 (IHa rho v e hrho)). exact ha.
      * apply (proj2 (IHb rho v e hrho)). exact hb.
  - split.
    + intros [ha | hb].
      * left. apply (proj1 (IHa rho v e hrho)). exact ha.
      * right. apply (proj1 (IHb rho v e hrho)). exact hb.
    + intros [ha | hb].
      * left. apply (proj2 (IHa rho v e hrho)). exact ha.
      * right. apply (proj2 (IHb rho v e hrho)). exact hb.
  - split.
    + intros h n.
      assert (hdom : Sat nat hf_mem (scons nat (ordinal_code n) e) domainForm).
      {
        exact (domain_ordinal_code n e).
      }
      assert (hrho' : forall k,
        scons nat (ordinal_code n) e (upVarMap rho k) =
          ordinal_code (scons nat n v k)).
      {
        intro k.
        destruct k as [|k].
        - reflexivity.
        - simpl.
          replace (rho k + 1) with (S (rho k)) by lia.
          simpl.
          exact (hrho k).
      }
      apply (proj1 (IHa (upVarMap rho) (scons nat n v)
        (scons nat (ordinal_code n) e) hrho')).
      exact (h (ordinal_code n) hdom).
    + intros h x hxdom.
      destruct (proj1 (domain_exact (scons nat x e)) hxdom) as [n hn].
      assert (hx : x = ordinal_code n) by (symmetry; exact hn).
      assert (hrho' : forall k,
        scons nat x e (upVarMap rho k) =
          ordinal_code (scons nat n v k)).
      {
        intro k.
        destruct k as [|k].
        - exact hx.
        - simpl.
          replace (rho k + 1) with (S (rho k)) by lia.
          simpl.
          exact (hrho k).
      }
      apply (proj2 (IHa (upVarMap rho) (scons nat n v)
        (scons nat x e) hrho')).
      exact (h n).
  - split.
    + intros [x [hxdom hbody]].
      destruct (proj1 (domain_exact (scons nat x e)) hxdom) as [n hn].
      assert (hx : x = ordinal_code n) by (symmetry; exact hn).
      assert (hrho' : forall k,
        scons nat x e (upVarMap rho k) =
          ordinal_code (scons nat n v k)).
      {
        intro k.
        destruct k as [|k].
        - exact hx.
        - simpl.
          replace (rho k + 1) with (S (rho k)) by lia.
          simpl.
          exact (hrho k).
      }
      exists n.
      apply (proj1 (IHa (upVarMap rho) (scons nat n v)
        (scons nat x e) hrho')).
      exact hbody.
    + intros [n hn].
      exists (ordinal_code n).
      split.
      * exact (domain_ordinal_code n e).
      * assert (hrho' : forall k,
          scons nat (ordinal_code n) e (upVarMap rho k) =
            ordinal_code (scons nat n v k)).
        {
          intro k.
          destruct k as [|k].
          - reflexivity.
          - simpl.
            replace (rho k + 1) with (S (rho k)) by lia.
            simpl.
            exact (hrho k).
        }
        apply (proj2 (IHa (upVarMap rho) (scons nat n v)
          (scons nat (ordinal_code n) e) hrho')).
        exact hn.
Qed.

Definition translateFormula (phi : PA.formula) : form :=
  formulaAt (fun n => n) phi.

Lemma translateFormula_exact : forall phi v,
  Sat nat hf_mem (fun n => ordinal_code (v n)) (translateFormula phi) <->
    PA.Formula.Sat PA.natModel v phi.
Proof.
  intros phi v.
  unfold translateFormula.
  apply formulaAt_exact.
  intro n.
  reflexivity.
Qed.

Lemma formulaAt_sentence_of_PA_sentence : forall phi rho,
  PA.Formula.Sentence phi -> Sentence (formulaAt rho phi).
Proof.
  intros phi rho hphi i hi.
  destruct (formulaAt_free phi rho i hi) as [n [hn _]].
  exact (hphi n hn).
Qed.

Lemma translateFormula_sentence_of_PA_sentence : forall phi,
  PA.Formula.Sentence phi -> Sentence (translateFormula phi).
Proof.
  intros phi hphi.
  unfold translateFormula.
  apply formulaAt_sentence_of_PA_sentence.
  exact hphi.
Qed.

Lemma translated_PA_axiom_sentence : forall phi,
  PA.Formula.Ax_s phi -> Sentence (translateFormula phi).
Proof.
  intros phi hphi.
  apply translateFormula_sentence_of_PA_sentence.
  exact (PA.Formula.sentence_ax_s phi hphi).
Qed.

Lemma translated_PA_axiom_sat_codes : forall phi,
  PA.Formula.Ax_s phi -> forall v,
    Sat nat hf_mem (fun n => ordinal_code (v n)) (translateFormula phi).
Proof.
  intros phi hphi v.
  apply (proj2 (translateFormula_exact phi v)).
  exact (PA.Formula.sat_axiom_s PA.natModel v phi hphi).
Qed.

Lemma translated_zeroNotSucc_sat : forall A (mem : A -> A -> Prop) e,
  Sat A mem e (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)).
Proof.
  intros A mem e.
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  apply formulaAt_zeroNotSucc_valid.
Qed.

Lemma translated_succInj_sat_of_irrefl :
  forall A (mem : A -> A -> Prop),
    (forall a, ~ mem a a) ->
    forall e,
      Sat A mem e (translateFormula (PA.Formula.sealPA PA.Formula.succInj)).
Proof.
  intros A mem hIrrefl e.
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  exact (formulaAt_succInj_of_irrefl A mem hIrrefl rho env).
Qed.

Lemma translated_succInj_sat_of_HFAx_s :
  forall V (mem : V -> V -> Prop) (v e : nat -> V),
    (forall g, HFAx_s g -> Sat V mem v g) ->
    Sat V mem e (translateFormula (PA.Formula.sealPA PA.Formula.succInj)).
Proof.
  intros V mem v e hHF.
  apply translated_succInj_sat_of_irrefl.
  exact (semantic_mem_irrefl_of_HFAx_s V mem v hHF).
Qed.

Lemma translated_addZero_sat_model :
  forall V (M : FirstOrderAdjunctionModel V) e,
    Sat V (foam_mem V M) e
      (translateFormula (PA.Formula.sealPA PA.Formula.addZero)).
Proof.
  intros V M e.
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  apply formulaAt_addZero_valid_model.
Qed.

Lemma translated_addZero_sat_of_HFAx_s :
  forall V (mem : V -> V -> Prop) (v e : nat -> V),
    (forall g, HFAx_s g -> Sat V mem v g) ->
    Sat V mem e (translateFormula (PA.Formula.sealPA PA.Formula.addZero)).
Proof.
  intros V mem v e hHF.
  pose (M := firstOrderAdjunctionModel_of_HFAx_s V mem v hHF).
  exact (translated_addZero_sat_model V M e).
Qed.

Lemma translated_mulZero_sat_model :
  forall V (M : FirstOrderAdjunctionModel V) e,
    Sat V (foam_mem V M) e
      (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)).
Proof.
  intros V M e.
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  apply formulaAt_mulZero_valid_model.
Qed.

Lemma translated_mulZero_sat_of_HFAx_s :
  forall V (mem : V -> V -> Prop) (v e : nat -> V),
    (forall g, HFAx_s g -> Sat V mem v g) ->
    Sat V mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)).
Proof.
  intros V mem v e hHF.
  pose (M := firstOrderAdjunctionModel_of_HFAx_s V mem v hHF).
  exact (translated_mulZero_sat_model V M e).
Qed.

Lemma translated_addSucc_sat_of_HFFinAx_s :
  forall V (mem : V -> V -> Prop) (v e : nat -> V),
    (forall g, HFFinAx_s g -> Sat V mem v g) ->
    Sat V mem e (translateFormula (PA.Formula.sealPA PA.Formula.addSucc)).
Proof.
  intros V mem v e hHF.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  exact (formulaAt_addSucc_valid_finite_model V M rho env).
Qed.

Lemma translated_mulSucc_sat_of_HFFinAx_s :
  forall V (mem : V -> V -> Prop) (v e : nat -> V),
    (forall g, HFFinAx_s g -> Sat V mem v g) ->
    Sat V mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulSucc)).
Proof.
  intros V mem v e hHF.
  pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
  unfold translateFormula.
  apply formulaAt_sealPA_valid.
  intros rho env.
  exact (formulaAt_mulSucc_valid_finite_model V M rho env).
Qed.

Lemma BProv_HF_translated_zeroNotSucc :
  BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)).
Proof.
  apply completeness_inf.
  - exact Sentences_HF.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_zeroNotSucc.
  - intros Dom mem v _hHF.
    apply translated_zeroNotSucc_sat.
Qed.

Lemma BProv_HF_translated_succInj :
  BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.succInj)).
Proof.
  apply completeness_inf.
  - exact Sentences_HF.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_succInj.
  - intros Dom mem v hHF.
    exact (translated_succInj_sat_of_HFAx_s Dom mem v v hHF).
Qed.

Lemma BProv_HF_translated_addZero :
  BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addZero)).
Proof.
  apply completeness_inf.
  - exact Sentences_HF.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_addZero.
  - intros Dom mem v hHF.
    exact (translated_addZero_sat_of_HFAx_s Dom mem v v hHF).
Qed.

Lemma BProv_HF_translated_mulZero :
  BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)).
Proof.
  apply completeness_inf.
  - exact Sentences_HF.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_mulZero.
  - intros Dom mem v hHF.
    exact (translated_mulZero_sat_of_HFAx_s Dom mem v v hHF).
Qed.

Lemma BProv_theory_mono : forall (B C : form -> Prop) G phi,
  (forall b, B b -> C b) -> BProv B G phi -> BProv C G phi.
Proof.
  intros B C G phi hBC [L [hL hp]].
  exists L.
  split.
  - intros x hx.
    apply hBC.
    exact (hL x hx).
  - exact hp.
Qed.

Lemma BProv_ax : forall (B : form -> Prop) G phi,
  B phi -> BProv B G phi.
Proof.
  intros B G phi hphi.
  exists [phi].
  split.
  - intros x hx.
    simpl in hx.
    destruct hx as [hx | hx]; [ subst x; exact hphi | contradiction ].
  - simpl.
    apply P_ass.
    left. reflexivity.
Qed.

Lemma BProv_of_Prov : forall (B : form -> Prop) G phi,
  Prov G phi -> BProv B G phi.
Proof.
  intros B G phi h.
  exists [].
  split.
  - intros x hx. contradiction.
  - simpl. exact h.
Qed.

Lemma BProv_bound_list : forall (B : form -> Prop) D L,
  (forall x, In x L -> BProv B D x) ->
  exists Lb, (forall x, In x Lb -> B x) /\
    forall x, In x L -> Prov (Lb ++ D) x.
Proof.
  intros B D L.
  induction L as [|a L IH]; intro hL.
  - exists [].
    split.
    + intros x hx. contradiction.
    + intros x hx. contradiction.
  - destruct (hL a (or_introl eq_refl)) as [La [hLa hpa]].
    destruct (IH (fun x hx => hL x (or_intror hx))) as
      [Lb [hLb hpL]].
    exists (La ++ Lb).
    split.
    + intros x hx.
      apply in_app_iff in hx.
      destruct hx as [hx | hx].
      * exact (hLa x hx).
      * exact (hLb x hx).
    + intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x.
        apply (Prov_weaken (La ++ D) a hpa).
        intros y hy.
        apply in_app_iff in hy.
        apply in_app_iff.
        destruct hy as [hy | hy].
        -- left. apply in_app_iff. left. exact hy.
        -- right. exact hy.
      * apply (Prov_weaken (Lb ++ D) x (hpL x hx)).
        intros y hy.
        apply in_app_iff in hy.
        apply in_app_iff.
        destruct hy as [hy | hy].
        -- left. apply in_app_iff. right. exact hy.
        -- right. exact hy.
Qed.

Lemma BProv_lift : forall (B C : form -> Prop) G D phi,
  BProv B G phi ->
  (forall b, B b -> BProv C D b) ->
  (forall g, In g G -> BProv C D g) ->
  BProv C D phi.
Proof.
  intros B C G D phi [Lb [hLb hp]] hB hG.
  assert (hctx : forall x, In x (Lb ++ G) -> BProv C D x).
  {
    intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    - exact (hB x (hLb x hx)).
    - exact (hG x hx).
  }
  destruct (BProv_bound_list C D (Lb ++ G) hctx) as
    [Lc [hLc hpctx]].
  exists Lc.
  split; [ exact hLc | ].
  exact (Prov_cut (Lb ++ G) phi hp (Lc ++ D) hpctx).
Qed.

Lemma BProv_HFFin_translated_zeroNotSucc :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)).
Proof.
  apply (BProv_theory_mono HFAx_s HFFinAx_s []
    (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc))).
  - intros g hg. apply HFFinAx_s_of_HFAx_s. exact hg.
  - exact BProv_HF_translated_zeroNotSucc.
Qed.

Lemma BProv_HFFin_translated_succInj :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.succInj)).
Proof.
  apply (BProv_theory_mono HFAx_s HFFinAx_s []
    (translateFormula (PA.Formula.sealPA PA.Formula.succInj))).
  - intros g hg. apply HFFinAx_s_of_HFAx_s. exact hg.
  - exact BProv_HF_translated_succInj.
Qed.

Lemma BProv_HFFin_translated_addZero :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addZero)).
Proof.
  apply (BProv_theory_mono HFAx_s HFFinAx_s []
    (translateFormula (PA.Formula.sealPA PA.Formula.addZero))).
  - intros g hg. apply HFFinAx_s_of_HFAx_s. exact hg.
  - exact BProv_HF_translated_addZero.
Qed.

Lemma BProv_HFFin_translated_addSucc :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addSucc)).
Proof.
  apply completeness_inf.
  - exact Sentences_HFFin.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_addSucc.
  - intros Dom mem v hHF.
    exact (translated_addSucc_sat_of_HFFinAx_s Dom mem v v hHF).
Qed.

Lemma BProv_HFFin_translated_mulSucc :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulSucc)).
Proof.
  apply completeness_inf.
  - exact Sentences_HFFin.
  - apply translated_PA_axiom_sentence.
    apply PA.Formula.Ax_s_mulSucc.
  - intros Dom mem v hHF.
    exact (translated_mulSucc_sat_of_HFFinAx_s Dom mem v v hHF).
Qed.

Lemma BProv_HFFin_translated_mulZero :
  BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)).
Proof.
  apply (BProv_theory_mono HFAx_s HFFinAx_s []
    (translateFormula (PA.Formula.sealPA PA.Formula.mulZero))).
  - intros g hg. apply HFFinAx_s_of_HFAx_s. exact hg.
  - exact BProv_HF_translated_mulZero.
Qed.

Definition translatedPAAx (g : form) : Prop :=
  exists phi, PA.Formula.Ax_s phi /\ g = translateFormula phi.

Lemma translatedPAAx_intro : forall phi,
  PA.Formula.Ax_s phi -> translatedPAAx (translateFormula phi).
Proof.
  intros phi hphi.
  exists phi. split; [ exact hphi | reflexivity ].
Qed.

Lemma Sentences_translatedPAAx : forall g,
  translatedPAAx g -> Sentence g.
Proof.
  intros g [phi [hphi ->]].
  apply translated_PA_axiom_sentence.
  exact hphi.
Qed.

Lemma rename_eq_of_sentence : forall g,
  Sentence g -> forall r, rename r g = g.
Proof.
  intros g hg r.
  transitivity (rename (fun n => n) g).
  - apply rename_ext_free.
    intros n hn.
    exfalso. exact (hg n hn).
  - apply rename_id.
Qed.

Lemma map_rename_S_eq_of_translatedPAAx_list : forall L,
  (forall x, In x L -> translatedPAAx x) -> map (rename S) L = L.
Proof.
  induction L as [|x xs IH]; intros hL; simpl.
  - reflexivity.
  - rewrite (rename_eq_of_sentence x).
    + rewrite (IH (fun y hy => hL y (or_intror hy))).
      reflexivity.
    + apply Sentences_translatedPAAx.
      apply hL. simpl. left. reflexivity.
Qed.

Lemma BProv_translatedPAAx_of_PAAx : forall phi,
  PA.Formula.Ax_s phi -> BProv translatedPAAx [] (translateFormula phi).
Proof.
  intros phi hphi.
  apply BProv_ax.
  apply translatedPAAx_intro.
  exact hphi.
Qed.

Definition translateContext (G : list PA.formula) : list form :=
  map translateFormula G.

Lemma mem_translateContext_of_mem : forall G phi,
  In phi G -> In (translateFormula phi) (translateContext G).
Proof.
  intros G phi hphi.
  unfold translateContext.
  apply in_map.
  exact hphi.
Qed.

Lemma BProv_translate_ass : forall G phi,
  In phi G -> BProv translatedPAAx (translateContext G) (translateFormula phi).
Proof.
  intros G phi hphi.
  apply BProv_of_Prov.
  apply P_ass.
  apply mem_translateContext_of_mem.
  exact hphi.
Qed.

Lemma BProv_translate_ax : forall phi,
  PA.Formula.Ax_s phi -> BProv translatedPAAx [] (translateFormula phi).
Proof.
  apply BProv_translatedPAAx_of_PAAx.
Qed.

Lemma BProv_translate_impI : forall G a b,
  BProv translatedPAAx
    (translateFormula a :: translateContext G) (translateFormula b) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pImp a b)).
Proof.
  intros G a b [L [hL hp]].
  unfold translateFormula. simpl. fold (translateFormula a).
  fold (translateFormula b).
  exists L.
  split; [ exact hL | ].
  apply P_impI.
  apply (Prov_weaken (L ++ translateFormula a :: translateContext G)
    (translateFormula b) hp).
  intros x hx.
  apply in_app_iff in hx.
  simpl in hx.
  simpl.
  destruct hx as [hx | [hx | hx]].
  - right. apply in_app_iff. left. exact hx.
  - left. exact hx.
  - right. apply in_app_iff. right. exact hx.
Qed.

Lemma BProv_translate_impE : forall G a b,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pImp a b)) ->
  BProv translatedPAAx (translateContext G) (translateFormula a) ->
  BProv translatedPAAx (translateContext G) (translateFormula b).
Proof.
  intros G a b hab ha.
  unfold translateFormula in hab. simpl in hab. fold (translateFormula a) in hab.
  fold (translateFormula b) in hab.
  exact (BProv_mp translatedPAAx (translateContext G)
    (translateFormula a) (translateFormula b) hab ha).
Qed.

Lemma BProv_translate_botE : forall G a,
  BProv translatedPAAx (translateContext G) fBot ->
  BProv translatedPAAx (translateContext G) (translateFormula a).
Proof.
  intros G a [L [hL hp]].
  exists L.
  split; [ exact hL | ].
  apply P_botE.
  exact hp.
Qed.

Lemma BProv_translate_lem : forall G a,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pOr a (PA.pImp a PA.pBot))).
Proof.
  intros G a.
  unfold translateFormula. simpl. fold (translateFormula a).
  apply BProv_of_Prov.
  apply P_lem.
Qed.

Lemma BProv_translate_andI : forall G a b,
  BProv translatedPAAx (translateContext G) (translateFormula a) ->
  BProv translatedPAAx (translateContext G) (translateFormula b) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pAnd a b)).
Proof.
  intros G a b [La [hLa hpa]] [Lb [hLb hpb]].
  unfold translateFormula. simpl. fold (translateFormula a).
  fold (translateFormula b).
  exists (La ++ Lb).
  split.
  - intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    + exact (hLa x hx).
    + exact (hLb x hx).
  - apply P_andI.
    + apply (Prov_weaken (La ++ translateContext G) (translateFormula a) hpa).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. left. exact hx.
      * right. exact hx.
    + apply (Prov_weaken (Lb ++ translateContext G) (translateFormula b) hpb).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. right. exact hx.
      * right. exact hx.
Qed.

Lemma BProv_translate_andE1 : forall G a b,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pAnd a b)) ->
  BProv translatedPAAx (translateContext G) (translateFormula a).
Proof.
  intros G a b [L [hL hp]].
  unfold translateFormula in hp. simpl in hp. fold (translateFormula a) in hp.
  fold (translateFormula b) in hp.
  exists L.
  split; [ exact hL | ].
  exact (P_andE1 (L ++ translateContext G)
    (translateFormula a) (translateFormula b) hp).
Qed.

Lemma BProv_translate_andE2 : forall G a b,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pAnd a b)) ->
  BProv translatedPAAx (translateContext G) (translateFormula b).
Proof.
  intros G a b [L [hL hp]].
  unfold translateFormula in hp. simpl in hp. fold (translateFormula a) in hp.
  fold (translateFormula b) in hp.
  exists L.
  split; [ exact hL | ].
  exact (P_andE2 (L ++ translateContext G)
    (translateFormula a) (translateFormula b) hp).
Qed.

Lemma BProv_translate_orI1 : forall G a b,
  BProv translatedPAAx (translateContext G) (translateFormula a) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pOr a b)).
Proof.
  intros G a b [L [hL hp]].
  unfold translateFormula. simpl. fold (translateFormula a).
  fold (translateFormula b).
  exists L.
  split; [ exact hL | ].
  exact (P_orI1 (L ++ translateContext G)
    (translateFormula a) (translateFormula b) hp).
Qed.

Lemma BProv_translate_orI2 : forall G a b,
  BProv translatedPAAx (translateContext G) (translateFormula b) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pOr a b)).
Proof.
  intros G a b [L [hL hp]].
  unfold translateFormula. simpl. fold (translateFormula a).
  fold (translateFormula b).
  exists L.
  split; [ exact hL | ].
  exact (P_orI2 (L ++ translateContext G)
    (translateFormula a) (translateFormula b) hp).
Qed.

Lemma BProv_translate_orE : forall G a b c,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pOr a b)) ->
  BProv translatedPAAx
    (translateFormula a :: translateContext G) (translateFormula c) ->
  BProv translatedPAAx
    (translateFormula b :: translateContext G) (translateFormula c) ->
  BProv translatedPAAx (translateContext G) (translateFormula c).
Proof.
  intros G a b c [Lo [hLo hpo]] [La [hLa hpa]] [Lb [hLb hpb]].
  unfold translateFormula in hpo. simpl in hpo. fold (translateFormula a) in hpo.
  fold (translateFormula b) in hpo.
  exists (Lo ++ La ++ Lb).
  split.
  - intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    + exact (hLo x hx).
    + apply in_app_iff in hx.
      destruct hx as [hx | hx].
      * exact (hLa x hx).
      * exact (hLb x hx).
  - apply (P_orE ((Lo ++ La ++ Lb) ++ translateContext G)
      (translateFormula a) (translateFormula b) (translateFormula c)).
    + apply (Prov_weaken (Lo ++ translateContext G)
        (fOr (translateFormula a) (translateFormula b)) hpo).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. left. exact hx.
      * right. exact hx.
    + apply (Prov_weaken (La ++ translateFormula a :: translateContext G)
        (translateFormula c) hpa).
      intros x hx.
      apply in_app_iff in hx.
      simpl in hx.
      simpl.
      destruct hx as [hx | [hx | hx]].
      * right. apply in_app_iff. left.
        apply in_app_iff. right. apply in_app_iff. left. exact hx.
      * left. exact hx.
      * right. apply in_app_iff. right. exact hx.
    + apply (Prov_weaken (Lb ++ translateFormula b :: translateContext G)
        (translateFormula c) hpb).
      intros x hx.
      apply in_app_iff in hx.
      simpl in hx.
      simpl.
      destruct hx as [hx | [hx | hx]].
      * right. apply in_app_iff. left.
        apply in_app_iff. right. apply in_app_iff. right. exact hx.
      * left. exact hx.
      * right. apply in_app_iff. right. exact hx.
Qed.

Lemma BProv_translate_allI_raw : forall G a,
  BProv translatedPAAx (map (rename S) (translateContext G))
    (fImp domainForm (formulaAt (upVarMap (fun n => n)) a)) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pAll a)).
Proof.
  intros G a [L [hL hp]].
  pose proof (map_rename_S_eq_of_translatedPAAx_list L hL) as hLmap.
  change (BProv translatedPAAx (translateContext G)
    (fAll (fImp domainForm (formulaAt (upVarMap (fun n => n)) a)))).
  exists L.
  split; [ exact hL | ].
  apply P_allI.
  apply (Prov_weaken
    (L ++ map (rename S) (translateContext G))
    (fImp domainForm (formulaAt (upVarMap (fun n => n)) a)) hp).
  intros x hx.
  apply in_app_iff in hx.
  rewrite map_app.
  apply in_app_iff.
  destruct hx as [hx | hx].
  - left. rewrite hLmap. exact hx.
  - right. exact hx.
Qed.

Lemma BProv_translate_exI_raw : forall G a k,
  BProv translatedPAAx (translateContext G)
    (rename (inst k)
      (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a))) ->
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pEx a)).
Proof.
  intros G a k [L [hL hp]].
  change (BProv translatedPAAx (translateContext G)
    (fEx (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a)))).
  exists L.
  split; [ exact hL | ].
  exact (P_exI (L ++ translateContext G)
    (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a)) k hp).
Qed.

Lemma BProv_translate_exE_raw : forall G a c,
  BProv translatedPAAx (translateContext G)
    (translateFormula (PA.pEx a)) ->
  BProv translatedPAAx
    (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a) ::
      map (rename S) (translateContext G))
    (rename S (translateFormula c)) ->
  BProv translatedPAAx (translateContext G) (translateFormula c).
Proof.
  intros G a c [Le [hLe hpe]] [Lb [hLb hpb]].
  unfold translateFormula in hpe. simpl in hpe.
  fold (formulaAt (upVarMap (fun n : nat => n)) a) in hpe.
  pose proof (map_rename_S_eq_of_translatedPAAx_list Lb hLb) as hLbmap.
  exists (Le ++ Lb).
  split.
  - intros x hx.
    apply in_app_iff in hx.
    destruct hx as [hx | hx].
    + exact (hLe x hx).
    + exact (hLb x hx).
  - apply (P_exE ((Le ++ Lb) ++ translateContext G)
      (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a))
      (translateFormula c)).
    + apply (Prov_weaken (Le ++ translateContext G)
        (fEx (fAnd domainForm
          (formulaAt (upVarMap (fun n : nat => n)) a))) hpe).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. left. exact hx.
      * right. exact hx.
    + apply (Prov_weaken
        (Lb ++
          fAnd domainForm (formulaAt (upVarMap (fun n => n)) a) ::
          map (rename S) (translateContext G))
        (rename S (translateFormula c)) hpb).
      intros x hx.
      apply in_app_iff in hx.
      simpl in hx.
      simpl.
      destruct hx as [hx | [hx | hx]].
      * right. rewrite map_app. apply in_app_iff. left.
        rewrite map_app. apply in_app_iff. right.
        rewrite hLbmap. exact hx.
      * left. exact hx.
      * right. rewrite map_app. apply in_app_iff. right. exact hx.
Qed.

Lemma BProv_lift_translatedPAAx_to_HF :
  (forall g, translatedPAAx g -> BProv HFAx_s [] g) ->
  forall g, BProv translatedPAAx [] g -> BProv HFAx_s [] g.
Proof.
  intros hAx g h.
  eapply BProv_lift.
  - exact h.
  - exact hAx.
  - intros x hx. contradiction.
Qed.

Lemma BProv_lift_translatedPAAx_to_HFFin :
  (forall g, translatedPAAx g -> BProv HFFinAx_s [] g) ->
  forall g, BProv translatedPAAx [] g -> BProv HFFinAx_s [] g.
Proof.
  intros hAx g h.
  eapply BProv_lift.
  - exact h.
  - exact hAx.
  - intros x hx. contradiction.
Qed.

Lemma standard_sat_translatedPAAx : forall e g,
  translatedPAAx g -> Sat nat hf_mem e g.
Proof.
  intros e g [phi [hphi hg]].
  subst g.
  pose proof (translated_PA_axiom_sentence phi hphi) as hsent.
  pose proof (translated_PA_axiom_sat_codes phi hphi (fun _ => 0)) as hcoded.
  apply (proj1 (Sat_sentence_inv nat hf_mem (translateFormula phi)
    hsent (fun _ => ordinal_code 0) e)).
  exact hcoded.
Qed.

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
