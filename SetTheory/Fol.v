(* ===================================================================== *)
(*  Fol.v                                                                 *)
(*                                                                       *)
(*  GENERIC first-order logic over the language of set theory: one        *)
(*  binary relation symbol (rendered fMem) and equality (fEq), with       *)
(*  De Bruijn variables.  Nothing in this file mentions any particular    *)
(*  theory: it provides                                                   *)
(*                                                                       *)
(*   - the formula syntax `form` and renaming (`rename`, `up`, `inst`)    *)
(*     with its equational theory;                                        *)
(*   - free variables (`Free`), variable bounds (`bound`, `freshFor`),    *)
(*     sentences (`Sentence`), and universal closure (`closeN`, `seal`);  *)
(*   - a surjective enumeration of formulas (`Enum`), via Cantor pairing; *)
(*   - Tarski satisfaction `Sat` over an arbitrary structure (V, mem),    *)
(*     with the environment/renaming lemmas `Sat_ext`, `Sat_rename`,      *)
(*     freeness invariance `Sat_ext_free`, and the sealing bridge         *)
(*     `closeN_valid` / `extract`;                                        *)
(*   - formula-definable relations `relOf`, and the auxiliary notions     *)
(*     `Sub`, `SetLike`, `Functional` used to state schemas.              *)
(*                                                                       *)
(*  Downstream: Calculus.v (proof calculus + soundness), Completeness.v   *)
(*  (Goedel completeness / compactness), Zf.v (first-order ZF), and       *)
(*  Equivalence.v (the Closure axiomatization T and T <-> ZF).            *)
(*                                                                       *)
(*  - Created (UTC): 2026-07-01T21:20:00Z                                 *)
(*  - Repository HEAD: c73d98802cf8385db7100480fdc5019105812718           *)
(* ===================================================================== *)

From Stdlib Require Import List PeanoNat Lia Setoid.
From Stdlib Require Import Cantor.
Import ListNotations.

(* ===================== syntax: formulas and renaming ================== *)

Inductive form : Type :=
| fMem : nat -> nat -> form
| fEq  : nat -> nat -> form
| fBot : form
| fImp : form -> form -> form
| fAnd : form -> form -> form
| fOr  : form -> form -> form
| fAll : form -> form
| fEx  : form -> form.
Definition fIff (a b : form) : form := fAnd (fImp a b) (fImp b a).
(* ------------------ renaming of De Bruijn variables -------------------- *)

Definition up (r : nat -> nat) : nat -> nat :=
  fun n => match n with O => O | S k => S (r k) end.

Fixpoint rename (r : nat -> nat) (f : form) {struct f} : form :=
  match f with
  | fMem i j => fMem (r i) (r j)
  | fEq i j  => fEq (r i) (r j)
  | fBot     => fBot
  | fImp a b => fImp (rename r a) (rename r b)
  | fAnd a b => fAnd (rename r a) (rename r b)
  | fOr a b  => fOr (rename r a) (rename r b)
  | fAll a   => fAll (rename (up r) a)
  | fEx a    => fEx (rename (up r) a)
  end.

(* instantiate de Bruijn 0 by variable k (and decrement the rest) *)
Definition inst (k : nat) : nat -> nat :=
  fun n => match n with O => k | S m => m end.

(* ------------- free variables, and the renaming equational theory ------ *)

Fixpoint Free (n : nat) (f : form) : Prop :=
  match f with
  | fMem i j => n = i \/ n = j
  | fEq i j  => n = i \/ n = j
  | fBot     => False
  | fImp a b => Free n a \/ Free n b
  | fAnd a b => Free n a \/ Free n b
  | fOr a b  => Free n a \/ Free n b
  | fAll a   => Free (S n) a
  | fEx a    => Free (S n) a
  end.

(* renamings agreeing on the free variables act equally *)
Lemma rename_ext_free :
  forall f r r', (forall n, Free n f -> r n = r' n) -> rename r f = rename r' f.
Proof.
  induction f; intros r r' H; simpl.
  - rewrite (H n (or_introl eq_refl)), (H n0 (or_intror eq_refl)); reflexivity.
  - rewrite (H n (or_introl eq_refl)), (H n0 (or_intror eq_refl)); reflexivity.
  - reflexivity.
  - f_equal; [ apply IHf1 | apply IHf2 ]; intros m Hm; apply H; [ left | right ]; exact Hm.
  - f_equal; [ apply IHf1 | apply IHf2 ]; intros m Hm; apply H; [ left | right ]; exact Hm.
  - f_equal; [ apply IHf1 | apply IHf2 ]; intros m Hm; apply H; [ left | right ]; exact Hm.
  - f_equal. apply IHf. intros m Hm. destruct m as [| k]; simpl;
      [ reflexivity | f_equal; apply H; exact Hm ].
  - f_equal. apply IHf. intros m Hm. destruct m as [| k]; simpl;
      [ reflexivity | f_equal; apply H; exact Hm ].
Qed.

(* renamings agreeing pointwise act equally *)
Lemma rename_ext : forall f r r', (forall n, r n = r' n) -> rename r f = rename r' f.
Proof. intros f r r' H. apply rename_ext_free. intros n _. apply H. Qed.

(* renaming composition *)
Lemma rename_comp :
  forall f r r', rename r (rename r' f) = rename (fun n => r (r' n)) f.
Proof.
  induction f; intros r r'; simpl; try reflexivity.
  - rewrite IHf1, IHf2; reflexivity.
  - rewrite IHf1, IHf2; reflexivity.
  - rewrite IHf1, IHf2; reflexivity.
  - f_equal. rewrite IHf. apply rename_ext. intro n; destruct n; simpl; reflexivity.
  - f_equal. rewrite IHf. apply rename_ext. intro n; destruct n; simpl; reflexivity.
Qed.

(* cons on renamings, and the identity inst k . up sigma = scons_nat k sigma *)
Definition scons_nat (k : nat) (s : nat -> nat) : nat -> nat :=
  fun n => match n with O => k | S m => s m end.

Lemma inst_up : forall k s n, inst k (up s n) = scons_nat k s n.
Proof. intros k s n. destruct n; reflexivity. Qed.

Lemma rename_inst_up :
  forall a k s, rename (inst k) (rename (up s) a) = rename (scons_nat k s) a.
Proof.
  intros a k s. rewrite rename_comp. apply rename_ext. intro n. apply inst_up.
Qed.

(* Pushing a renaming [r] past an instantiation [inst k]: used to normalize the
   quantifier and equality-elimination cases of [Prov_rename]. *)
Lemma rename_inst_push : forall a r k,
  rename r (rename (inst k) a) = rename (inst (r k)) (rename (up r) a).
Proof.
  intros a r k. rewrite !rename_comp. apply rename_ext.
  intro n; destruct n; reflexivity.
Qed.

Lemma rename_id : forall a, rename (fun n => n) a = a.
Proof.
  induction a; simpl; try reflexivity.
  - rewrite IHa1, IHa2; reflexivity.
  - rewrite IHa1, IHa2; reflexivity.
  - rewrite IHa1, IHa2; reflexivity.
  - f_equal. transitivity (rename (fun n => n) a).
    + apply rename_ext. intro n; destruct n; reflexivity.
    + exact IHa.
  - f_equal. transitivity (rename (fun n => n) a).
    + apply rename_ext. intro n; destruct n; reflexivity.
    + exact IHa.
Qed.

(* ============== variable bounds, freshness, sentences, sealing ======== *)

Fixpoint bound (f : form) : nat :=
  match f with
  | fMem i j => S i + S j
  | fEq i j  => S i + S j
  | fBot     => 0
  | fImp a b => bound a + bound b
  | fAnd a b => bound a + bound b
  | fOr a b  => bound a + bound b
  | fAll a   => bound a
  | fEx a    => bound a
  end.

Lemma free_lt_bound : forall f n, Free n f -> n < bound f.
Proof.
  induction f as [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa | a IHa ];
    intros n Hn; simpl in *.
  - destruct Hn; lia.
  - destruct Hn; lia.
  - destruct Hn.
  - destruct Hn as [Hn|Hn]; [ apply IHa in Hn | apply IHb in Hn ]; lia.
  - destruct Hn as [Hn|Hn]; [ apply IHa in Hn | apply IHb in Hn ]; lia.
  - destruct Hn as [Hn|Hn]; [ apply IHa in Hn | apply IHb in Hn ]; lia.
  - apply IHa in Hn; lia.
  - apply IHa in Hn; lia.
Qed.

Fixpoint lmax (l : list nat) : nat :=
  match l with [] => 0 | x :: r => max x (lmax r) end.

Lemma le_lmax : forall x l, In x l -> x <= lmax l.
Proof.
  induction l as [| y r IHr]; intros Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (lmax r); [ apply IHr; exact Hin | apply Nat.le_max_r ].
Qed.

Definition freshFor (L : list form) : nat := lmax (map bound L).

Lemma freshFor_not_free : forall L f, In f L -> ~ Free (freshFor L) f.
Proof.
  intros L f Hin Hfree. apply free_lt_bound in Hfree.
  assert (bound f <= freshFor L) by (unfold freshFor; apply le_lmax; apply in_map; exact Hin).
  lia.
Qed.

Definition rho_w (w : nat) : nat -> nat := fun n => if Nat.eqb n w then 0 else S n.

Lemma rho_inst :
  forall a w, ~ Free (S w) a -> rename (rho_w w) (rename (inst w) a) = a.
Proof.
  intros a w Hfree. rewrite rename_comp.
  rewrite (rename_ext_free a (fun n => rho_w w (inst w n)) (fun n => n)).
  - apply rename_id.
  - intros n Hn. destruct n as [| m]; simpl.
    + unfold rho_w. rewrite Nat.eqb_refl. reflexivity.
    + unfold rho_w. destruct (Nat.eqb m w) eqn:E.
      * apply Nat.eqb_eq in E. subst m. exfalso. apply Hfree. exact Hn.
      * reflexivity.
Qed.

Lemma rho_under :
  forall a w, ~ Free (S w) a -> rename (up (rho_w w)) a = rename (up S) a.
Proof.
  intros a w Hfree. apply rename_ext_free. intros n Hn.
  destruct n as [| m]; simpl.
  - reflexivity.
  - unfold rho_w. destruct (Nat.eqb m w) eqn:E.
    + apply Nat.eqb_eq in E. subst m. exfalso. apply Hfree. exact Hn.
    + reflexivity.
Qed.

Lemma map_rho_S :
  forall G w, (forall g, In g G -> ~ Free w g) ->
    map (rename (rho_w w)) G = map (rename S) G.
Proof.
  intros G w H. apply map_ext_in. intros g Hg. apply rename_ext_free. intros n Hn.
  unfold rho_w. destruct (Nat.eqb n w) eqn:E.
  - apply Nat.eqb_eq in E. subst n. exfalso. apply (H g Hg). exact Hn.
  - reflexivity.
Qed.
Definition Sentence (f : form) : Prop := forall n, ~ Free n f.
Definition Sentences (B : form -> Prop) : Prop := forall f, B f -> Sentence f.

(* Closed formulas are invariant under every variable renaming.  This belongs
   to the formula layer rather than any particular translated theory. *)
Lemma rename_eq_of_sentence : forall f,
  Sentence f -> forall r, rename r f = f.
Proof.
  intros f hf r.
  transitivity (rename (fun n => n) f).
  - apply rename_ext_free. intros n hn. exfalso. exact (hf n hn).
  - apply rename_id.
Qed.

Fixpoint closeN (k : nat) (f : form) : form :=
  match k with O => f | S k' => closeN k' (fAll f) end.

Lemma Free_closeN : forall k f n, Free n (closeN k f) -> Free (k + n) f.
Proof. induction k as [| k IHk]; intros f n H; [ exact H | exact (IHk (fAll f) n H) ]. Qed.

Definition seal (f : form) : form := closeN (bound f) f.

Lemma Sentence_seal : forall f, Sentence (seal f).
Proof.
  intros f n H. unfold seal in H. apply Free_closeN in H. apply free_lt_bound in H. lia.
Qed.

(* ============== enumeration of formulas (Cantor pairing) ============== *)

(* ---- [4d] enumeration of formulas (a surjection nat -> form) ---- *)

Fixpoint code (f : form) : nat :=
  match f with
  | fMem i j => Cantor.to_nat (0, Cantor.to_nat (i, j))
  | fEq i j  => Cantor.to_nat (1, Cantor.to_nat (i, j))
  | fBot     => Cantor.to_nat (2, 0)
  | fImp a b => Cantor.to_nat (3, Cantor.to_nat (code a, code b))
  | fAnd a b => Cantor.to_nat (4, Cantor.to_nat (code a, code b))
  | fOr a b  => Cantor.to_nat (5, Cantor.to_nat (code a, code b))
  | fAll a   => Cantor.to_nat (6, code a)
  | fEx a    => Cantor.to_nat (7, code a)
  end.

Fixpoint decode (fuel n : nat) : form :=
  match fuel with
  | O => fBot
  | S fuel' =>
    let p := snd (Cantor.of_nat n) in
    match fst (Cantor.of_nat n) with
    | 0 => fMem (fst (Cantor.of_nat p)) (snd (Cantor.of_nat p))
    | 1 => fEq (fst (Cantor.of_nat p)) (snd (Cantor.of_nat p))
    | 2 => fBot
    | 3 => fImp (decode fuel' (fst (Cantor.of_nat p))) (decode fuel' (snd (Cantor.of_nat p)))
    | 4 => fAnd (decode fuel' (fst (Cantor.of_nat p))) (decode fuel' (snd (Cantor.of_nat p)))
    | 5 => fOr (decode fuel' (fst (Cantor.of_nat p))) (decode fuel' (snd (Cantor.of_nat p)))
    | 6 => fAll (decode fuel' p)
    | 7 => fEx (decode fuel' p)
    | _ => fBot
    end
  end.

Lemma decode_code : forall f fuel, code f < fuel -> decode fuel (code f) = f.
Proof.
  induction f as [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb | a IHa | a IHa ];
    intros fuel Hlt; destruct fuel as [| fuel']; try (cbn [code] in Hlt; lia).
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd]. reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd]. reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd]. reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    pose proof (Cantor.to_nat_non_decreasing 3 (Cantor.to_nat (code a, code b))) as B1.
    pose proof (Cantor.to_nat_non_decreasing (code a) (code b)) as B2.
    cbn [code] in Hlt.
    rewrite (IHa fuel' ltac:(lia)), (IHb fuel' ltac:(lia)). reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    pose proof (Cantor.to_nat_non_decreasing 4 (Cantor.to_nat (code a, code b))) as B1.
    pose proof (Cantor.to_nat_non_decreasing (code a) (code b)) as B2.
    cbn [code] in Hlt.
    rewrite (IHa fuel' ltac:(lia)), (IHb fuel' ltac:(lia)). reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    pose proof (Cantor.to_nat_non_decreasing 5 (Cantor.to_nat (code a, code b))) as B1.
    pose proof (Cantor.to_nat_non_decreasing (code a) (code b)) as B2.
    cbn [code] in Hlt.
    rewrite (IHa fuel' ltac:(lia)), (IHb fuel' ltac:(lia)). reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    pose proof (Cantor.to_nat_non_decreasing 6 (code a)) as B1.
    cbn [code] in Hlt.
    rewrite (IHa fuel' ltac:(lia)). reflexivity.
  - cbn [decode code]. rewrite !Cantor.cancel_of_to. cbn [fst snd].
    pose proof (Cantor.to_nat_non_decreasing 7 (code a)) as B1.
    cbn [code] in Hlt.
    rewrite (IHa fuel' ltac:(lia)). reflexivity.
Qed.

Definition Enum (n : nat) : form := decode (S n) n.

Lemma Enum_surj : forall f, exists n, Enum n = f.
Proof. intro f. exists (code f). unfold Enum. apply decode_code. lia. Qed.

(* =================== Tarski semantics over a structure ================ *)

Section Semantics.

Variable V : Type.
Variable mem : V -> V -> Prop.
Infix "∈" := mem (at level 70, no associativity).

Definition Sub (a b : V) : Prop := forall x, x ∈ a -> x ∈ b.

Definition scons (d : V) (e : nat -> V) : nat -> V :=
  fun n => match n with O => d | S k => e k end.

Fixpoint Sat (e : nat -> V) (f : form) {struct f} : Prop :=
  match f with
  | fMem i j => (e i) ∈ (e j)
  | fEq i j  => e i = e j
  | fBot     => False
  | fImp a b => Sat e a -> Sat e b
  | fAnd a b => Sat e a /\ Sat e b
  | fOr a b  => Sat e a \/ Sat e b
  | fAll a   => forall d, Sat (scons d e) a
  | fEx a    => exists d, Sat (scons d e) a
  end.
(* ---------- satisfaction depends only on the free variables ------------ *)

Lemma Sat_ext_free :
  forall f e1 e2, (forall n, Free n f -> e1 n = e2 n) -> (Sat e1 f <-> Sat e2 f).
Proof.
  induction f; intros e1 e2 H; cbn [Sat].
  - rewrite (H n (or_introl eq_refl)), (H n0 (or_intror eq_refl)); tauto.
  - rewrite (H n (or_introl eq_refl)), (H n0 (or_intror eq_refl)); tauto.
  - tauto.
  - assert (Ha := IHf1 e1 e2 (fun n Hn => H n (or_introl Hn)));
    assert (Hb := IHf2 e1 e2 (fun n Hn => H n (or_intror Hn))); tauto.
  - assert (Ha := IHf1 e1 e2 (fun n Hn => H n (or_introl Hn)));
    assert (Hb := IHf2 e1 e2 (fun n Hn => H n (or_intror Hn))); tauto.
  - assert (Ha := IHf1 e1 e2 (fun n Hn => H n (or_introl Hn)));
    assert (Hb := IHf2 e1 e2 (fun n Hn => H n (or_intror Hn))); tauto.
  - assert (Hd : forall d, forall n, Free n f -> scons d e1 n = scons d e2 n).
    { intros d n Hn. destruct n as [| m]; [ reflexivity | apply H; exact Hn ]. }
    split; intros HH d;
      [ apply (proj1 (IHf (scons d e1) (scons d e2) (Hd d)))
      | apply (proj2 (IHf (scons d e1) (scons d e2) (Hd d))) ]; apply HH.
  - assert (Hd : forall d, forall n, Free n f -> scons d e1 n = scons d e2 n).
    { intros d n Hn. destruct n as [| m]; [ reflexivity | apply H; exact Hn ]. }
    split; intros [d HH]; exists d;
      [ apply (proj1 (IHf (scons d e1) (scons d e2) (Hd d)))
      | apply (proj2 (IHf (scons d e1) (scons d e2) (Hd d))) ]; exact HH.
Qed.

(* satisfaction respects pointwise-equal environments *)
Lemma Sat_ext :
  forall f e1 e2, (forall n, e1 n = e2 n) -> (Sat e1 f <-> Sat e2 f).
Proof. intros f e1 e2 H. apply Sat_ext_free. intros n _. apply H. Qed.
Lemma up_env :
  forall r d e n, scons d e (up r n) = scons d (fun m => e (r m)) n.
Proof. intros r d e n. destruct n; reflexivity. Qed.

Lemma Sat_rename :
  forall f r e, Sat e (rename r f) <-> Sat (fun n => e (r n)) f.
Proof.
  induction f; intros r e; simpl.
  - tauto.
  - tauto.
  - tauto.
  - specialize (IHf1 r e); specialize (IHf2 r e); tauto.
  - specialize (IHf1 r e); specialize (IHf2 r e); tauto.
  - specialize (IHf1 r e); specialize (IHf2 r e); tauto.
  - split; intros HH d; specialize (HH d).
    + apply (proj1 (Sat_ext f (fun n => scons d e (up r n))
                            (scons d (fun m => e (r m))) (fun n => up_env r d e n))).
      apply (proj1 (IHf (up r) (scons d e))). exact HH.
    + apply (proj2 (IHf (up r) (scons d e))).
      apply (proj2 (Sat_ext f (fun n => scons d e (up r n))
                            (scons d (fun m => e (r m))) (fun n => up_env r d e n))).
      exact HH.
  - split; intros [d HH]; exists d.
    + apply (proj1 (Sat_ext f (fun n => scons d e (up r n))
                            (scons d (fun m => e (r m))) (fun n => up_env r d e n))).
      apply (proj1 (IHf (up r) (scons d e))). exact HH.
    + apply (proj2 (IHf (up r) (scons d e))).
      apply (proj2 (Sat_ext f (fun n => scons d e (up r n))
                            (scons d (fun m => e (r m))) (fun n => up_env r d e n))).
      exact HH.
Qed.

(* The standard semantic transport step: rename a formula and identify the
   resulting environment pointwise with the intended target environment. *)
Lemma Sat_rename_ext : forall f r e e',
  (forall n, e (r n) = e' n) ->
  (Sat e (rename r f) <-> Sat e' f).
Proof.
  intros f r e e' h.
  rewrite Sat_rename.
  apply Sat_ext.
  exact h.
Qed.

(* environment lemmas for the quantifier/equality cases *)
Lemma inst_env : forall k e n, e (inst k n) = scons (e k) e n.
Proof. intros k e n. destruct n; reflexivity. Qed.
(* relation defined by a formula psi with vars 0,1 the two arguments *)
Definition relOf (psi : form) (e : nat -> V) : V -> V -> Prop :=
  fun z x => Sat (scons z (scons x e)) psi.

Definition SetLike (R : V -> V -> Prop) : Prop :=
  forall x, exists y, forall z, R z x -> z ∈ y.

Definition Functional (R : V -> V -> Prop) : Prop :=
  forall x y1 y2, R y1 x -> R y2 x -> y1 = y2.


End Semantics.

(* ============ sealing is semantically transparent; extraction ========= *)

Lemma closeN_valid :
  forall (V : Type) (mem : V -> V -> Prop) k g,
    (forall e, Sat V mem e (closeN k g)) <-> (forall e, Sat V mem e g).
Proof.
  intros V mem k. induction k as [| k IHk]; intro g; [ tauto | ].
  cbn [closeN]. rewrite (IHk (fAll g)). split.
  - intros H e'.
    assert (PF : forall n, scons V (e' 0) (fun n => e' (S n)) n = e' n)
      by (intro n; destruct n; reflexivity).
    apply (proj1 (Sat_ext V mem g (scons V (e' 0) (fun n => e' (S n))) e' PF)).
    exact (H (fun n => e' (S n)) (e' 0)).
  - intros H e d. apply H.
Qed.

Lemma seal_valid :
  forall (V : Type) (mem : V -> V -> Prop) g,
    (forall e, Sat V mem e (seal g)) <-> (forall e, Sat V mem e g).
Proof. intros V mem g. apply closeN_valid. Qed.

Lemma Sat_sentence_inv :
  forall (V : Type) (mem : V -> V -> Prop) g,
    Sentence g -> forall v1 v2, Sat V mem v1 g <-> Sat V mem v2 g.
Proof.
  intros V mem g Hg v1 v2. apply Sat_ext_free. intros n Hn. exfalso. exact (Hg n Hn).
Qed.

(* extract a universal instance of a sealed axiom from a model of a theory *)
Lemma extract :
  forall (B : form -> Prop) (V : Type) (mem : V -> V -> Prop) v g,
    (forall g', B g' -> Sat V mem v g') -> B (seal g) -> forall e, Sat V mem e g.
Proof.
  intros B V mem v g HT Hin.
  apply (proj1 (closeN_valid V mem (bound g) g)). intro e'.
  apply (proj1 (Sat_sentence_inv V mem (seal g) (Sentence_seal g) v e')). apply HT. exact Hin.
Qed.
