(* ===================================================================== *)
(*  Deep.v                                                                *)
(*                                                                       *)
(*  A DEEP embedding of the first-order language of set theory, used to   *)
(*  tighten the faithfulness of the forward direction (Forward.v).        *)
(*                                                                       *)
(*  Forward.v renders the schemas with the metatheory's predicates        *)
(*  (V -> Prop), i.e. SECOND-order.  Here the schemas range over genuine  *)
(*  syntactic first-order formulas `form`, interpreted by a Tarski        *)
(*  satisfaction relation `Sat`.  We then re-derive the forward trade,    *)
(*  exhibiting each relation used (pairing, membership, successor, and a   *)
(*  function graph) as a concrete `form` and checking its `Sat`-meaning.  *)
(*  This certifies that the schema-trade uses only genuinely FIRST-ORDER  *)
(*  definable instances.                                                  *)
(*                                                                       *)
(*  Scope note: the forward direction ports because every relation is a   *)
(*  simple formula.  The reverse direction (ZF => Closure) does NOT port  *)
(*  cheaply: its use of Replacement is essential, and the collected map   *)
(*  n |-> W_n is first-order definable only via the syntactic recursion   *)
(*  theorem -- the heavy object-level construction Reverse.v sidesteps     *)
(*  with a meta-level `nat`.  See README.                                 *)
(*                                                                       *)
(*  - Created (UTC): 2026-06-30T04:48:30Z                                 *)
(*  - Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9          *)
(* ===================================================================== *)

From Stdlib Require Import ClassicalEpsilon.

Section Deep.

Variable V : Type.
Variable mem : V -> V -> Prop.
Infix "∈" := mem (at level 70, no associativity).
Definition Sub (a b : V) : Prop := forall x, x ∈ a -> x ∈ b.
Variable witness : V.

(* ----------------------- first-order syntax --------------------------- *)

Inductive form : Type :=
| fMem : nat -> nat -> form
| fEq  : nat -> nat -> form
| fBot : form
| fImp : form -> form -> form
| fAnd : form -> form -> form
| fOr  : form -> form -> form
| fAll : form -> form
| fEx  : form -> form.

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

Definition fIff (a b : form) : form := fAnd (fImp a b) (fImp b a).

(* ------------ satisfaction respects pointwise-equal environments ------- *)

Lemma scons_ext :
  forall d e1 e2, (forall n, e1 n = e2 n) -> forall n, scons d e1 n = scons d e2 n.
Proof. intros d e1 e2 H n. destruct n; simpl; [ reflexivity | apply H ]. Qed.

Lemma Sat_ext :
  forall f e1 e2, (forall n, e1 n = e2 n) -> (Sat e1 f <-> Sat e2 f).
Proof.
  induction f; intros e1 e2 H; simpl.
  - rewrite (H n), (H n0); tauto.
  - rewrite (H n), (H n0); tauto.
  - tauto.
  - specialize (IHf1 e1 e2 H); specialize (IHf2 e1 e2 H); tauto.
  - specialize (IHf1 e1 e2 H); specialize (IHf2 e1 e2 H); tauto.
  - specialize (IHf1 e1 e2 H); specialize (IHf2 e1 e2 H); tauto.
  - split; intros HH d.
    + apply (proj1 (IHf (scons d e1) (scons d e2) (scons_ext d e1 e2 H))). apply HH.
    + apply (proj2 (IHf (scons d e1) (scons d e2) (scons_ext d e1 e2 H))). apply HH.
  - split; intros [d HH]; exists d.
    + apply (proj1 (IHf (scons d e1) (scons d e2) (scons_ext d e1 e2 H))). exact HH.
    + apply (proj2 (IHf (scons d e1) (scons d e2) (scons_ext d e1 e2 H))). exact HH.
Qed.

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

(* --------------- the surviving axioms, as first-order schemas ---------- *)

Hypothesis Extensionality :
  forall a b, (forall x, x ∈ a <-> x ∈ b) -> a = b.

(* genuine first-order Separation: the predicate is a formula phi whose    *)
(* free variable 0 is the element and whose other free vars are parameters *)
Hypothesis SeparationFO :
  forall (phi : form) (e : nat -> V) (a : V),
    exists s, forall x, x ∈ s <-> (x ∈ a /\ Sat (scons x e) phi).

Hypothesis Powerset :
  forall a, exists p, forall x, x ∈ p <-> Sub x a.

(* relation defined by a formula psi with vars 0,1 the two arguments *)
Definition relOf (psi : form) (e : nat -> V) : V -> V -> Prop :=
  fun z x => Sat (scons z (scons x e)) psi.

Definition SetLike (R : V -> V -> Prop) : Prop :=
  forall x, exists y, forall z, R z x -> z ∈ y.

(* genuine first-order Closure: the relation is a formula psi *)
Hypothesis ClosureFO :
  forall (psi : form) (e : nat -> V),
    SetLike (relOf psi e) ->
    forall s, exists w, Sub s w /\ (forall u v, relOf psi e u v -> v ∈ w -> u ∈ w).

(* --------------------------- operators -------------------------------- *)

Definition power (a : V) : V :=
  proj1_sig (constructive_indefinite_description _ (Powerset a)).
Lemma power_spec : forall a x, x ∈ power a <-> Sub x a.
Proof. intro a. exact (proj2_sig (constructive_indefinite_description _ (Powerset a))). Qed.
Lemma power_intro : forall a x, Sub x a -> x ∈ power a.
Proof. intros a x H. exact (proj2 (power_spec a x) H). Qed.
Lemma power_elim : forall a x, x ∈ power a -> Sub x a.
Proof. intros a x H. exact (proj1 (power_spec a x) H). Qed.

Definition sepF (a : V) (phi : form) (e : nat -> V) : V :=
  proj1_sig (constructive_indefinite_description _ (SeparationFO phi e a)).
Lemma sepF_spec :
  forall a phi e x, x ∈ sepF a phi e <-> (x ∈ a /\ Sat (scons x e) phi).
Proof. intros a phi e. exact (proj2_sig (constructive_indefinite_description _ (SeparationFO phi e a))). Qed.

Lemma Sub_refl : forall a, Sub a a.
Proof. intros a x H. exact H. Qed.

Lemma self_in_power : forall a, a ∈ power a.
Proof. intro a. apply power_intro. apply Sub_refl. Qed.

(* ------------------------------ empty set ----------------------------- *)

Definition emptyset : V := sepF witness fBot (fun _ => witness).
Lemma emptyset_spec : forall x, ~ x ∈ emptyset.
Proof.
  intros x H. apply (proj1 (sepF_spec witness fBot (fun _ => witness) x)) in H.
  destruct H as [_ HF]. exact HF.
Qed.

Definition single_empty : V := power emptyset.
Definition pair_empty   : V := power single_empty.

Lemma in_single_empty : forall x, x ∈ single_empty <-> x = emptyset.
Proof.
  intro x. unfold single_empty. split.
  - intro H. apply power_elim in H. apply Extensionality. intro y. split.
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
  rewrite <- Heq in H. exact (emptyset_spec emptyset H).
Qed.

Lemma empty_in_pair : emptyset ∈ pair_empty.
Proof.
  unfold pair_empty. apply power_intro. intros y Hy. exfalso. exact (emptyset_spec y Hy).
Qed.

Lemma single_in_pair : single_empty ∈ pair_empty.
Proof. unfold pair_empty. apply power_intro. apply Sub_refl. Qed.

(* ============================== PAIRING ============================== *)

(* vars: 0=z, 1=x; params via e: e0=∅, e1=a, e2={∅}, e3=b *)
Definition psi_pair : form :=
  fOr (fAnd (fEq 1 2) (fEq 0 3)) (fAnd (fEq 1 4) (fEq 0 5)).
Definition e_pair (a b : V) : nat -> V :=
  fun n => match n with 0 => emptyset | 1 => a | 2 => single_empty | 3 => b | _ => witness end.
Definition e_ab (a b : V) : nat -> V :=
  fun n => match n with 0 => a | 1 => b | _ => witness end.

Lemma Hrel_pair :
  forall a b z x,
    relOf psi_pair (e_pair a b) z x
    <-> ((x = emptyset /\ z = a) \/ (x = single_empty /\ z = b)).
Proof. intros a b z x. unfold relOf, psi_pair, e_pair. simpl. tauto. Qed.

Theorem Pairing :
  forall a b, exists p, forall x, x ∈ p <-> (x = a \/ x = b).
Proof.
  intros a b.
  assert (HSL : SetLike (relOf psi_pair (e_pair a b))).
  { intro x.
    destruct (classic (x = emptyset)) as [Hx | Hx].
    - exists (power a). intros z Hz. apply (proj1 (Hrel_pair a b z x)) in Hz.
      destruct Hz as [[_ Hza] | [Hxs _]].
      + subst z. apply self_in_power.
      + exfalso. apply empty_neq_single. rewrite <- Hx. exact Hxs.
    - destruct (classic (x = single_empty)) as [Hs | Hs].
      + exists (power b). intros z Hz. apply (proj1 (Hrel_pair a b z x)) in Hz.
        destruct Hz as [[Hxe _] | [_ Hzb]].
        * exfalso. apply Hx. exact Hxe.
        * subst z. apply self_in_power.
      + exists emptyset. intros z Hz. apply (proj1 (Hrel_pair a b z x)) in Hz.
        destruct Hz as [[Hxe _] | [Hxs _]].
        * exfalso. apply Hx. exact Hxe.
        * exfalso. apply Hs. exact Hxs. }
  destruct (ClosureFO psi_pair (e_pair a b) HSL pair_empty) as [w [Hsub Hclosed]].
  assert (Ha : a ∈ w).
  { apply (Hclosed a emptyset).
    - apply (proj2 (Hrel_pair a b a emptyset)). left. split; reflexivity.
    - apply Hsub. exact empty_in_pair. }
  assert (Hb : b ∈ w).
  { apply (Hclosed b single_empty).
    - apply (proj2 (Hrel_pair a b b single_empty)). right. split; reflexivity.
    - apply Hsub. exact single_in_pair. }
  exists (sepF w (fOr (fEq 0 1) (fEq 0 2)) (e_ab a b)).
  intro x. split.
  - intro H. apply (proj1 (sepF_spec w (fOr (fEq 0 1) (fEq 0 2)) (e_ab a b) x)) in H.
    destruct H as [_ Hx]. unfold e_ab in Hx. simpl in Hx. exact Hx.
  - intro H. apply (proj2 (sepF_spec w (fOr (fEq 0 1) (fEq 0 2)) (e_ab a b) x)). split.
    + destruct H as [Hxa | Hxb]; [ subst x; exact Ha | subst x; exact Hb ].
    + unfold e_ab. simpl. exact H.
Qed.

(* =============================== UNION =============================== *)

(* membership relation: relOf psi_mem e z x = z ∈ x *)
Definition psi_mem : form := fMem 0 1.
Lemma Hrel_mem : forall e z x, relOf psi_mem e z x <-> z ∈ x.
Proof. intros e z x. unfold relOf, psi_mem. simpl. tauto. Qed.

(* separation predicate for the union: element 0=x, param e0=s *)
Definition phi_un : form := fEx (fAnd (fMem 1 0) (fMem 0 2)).
Definition e_un (s : V) : nat -> V := fun n => match n with 0 => s | _ => witness end.

Theorem Union :
  forall s, exists u, forall x, x ∈ u <-> exists v, x ∈ v /\ v ∈ s.
Proof.
  intro s.
  assert (HSL : SetLike (relOf psi_mem (fun _ => witness))).
  { intro x. exists x. intros z Hz. apply (proj1 (Hrel_mem (fun _ => witness) z x)) in Hz. exact Hz. }
  destruct (ClosureFO psi_mem (fun _ => witness) HSL s) as [w [Hsub Hclosed]].
  exists (sepF w phi_un (e_un s)).
  intro x. split.
  - intro H. apply (proj1 (sepF_spec w phi_un (e_un s) x)) in H.
    destruct H as [_ Hpred]. unfold phi_un, e_un in Hpred. simpl in Hpred. exact Hpred.
  - intro H. apply (proj2 (sepF_spec w phi_un (e_un s) x)). split.
    + destruct H as [v [Hxv Hvs]]. apply (Hclosed x v).
      * apply (proj2 (Hrel_mem (fun _ => witness) x v)). exact Hxv.
      * apply Hsub. exact Hvs.
    + unfold phi_un, e_un. simpl. exact H.
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

(* successor relation: relOf psi_succ e z x = forall t, t∈z <-> (t∈x \/ t=x) *)
Definition psi_succ : form :=
  fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2))).
Lemma Hrel_succ :
  forall e z x, relOf psi_succ e z x <-> (forall t, t ∈ z <-> (t ∈ x \/ t = x)).
Proof.
  intros e z x. unfold relOf, psi_succ, fIff. simpl.
  split; intros H t; specialize (H t); tauto.
Qed.

Theorem Infinity :
  exists I,
    (exists e0, e0 ∈ I /\ forall z, ~ z ∈ e0) /\
    (forall x, x ∈ I ->
       exists sx, sx ∈ I /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).
Proof.
  assert (HSL : SetLike (relOf psi_succ (fun _ => witness))).
  { intro x. destruct (succ_exists x) as [sx Hsx].
    exists (power sx). intros z Hz0.
    pose proof (proj1 (Hrel_succ (fun _ => witness) z x) Hz0) as Hz.
    assert (Hzs : z = sx).
    { apply Extensionality. intro t. split.
      - intro Ht. apply (proj2 (Hsx t)). exact (proj1 (Hz t) Ht).
      - intro Ht. apply (proj2 (Hz t)).  exact (proj1 (Hsx t) Ht). }
    subst z. apply self_in_power. }
  destruct (ClosureFO psi_succ (fun _ => witness) HSL single_empty) as [w [Hsub Hclosed]].
  exists w. split.
  - exists emptyset. split.
    + apply Hsub. exact empty_in_single.
    + exact emptyset_spec.
  - intros x Hx. destruct (succ_exists x) as [sx Hsx].
    exists sx. split.
    + apply (Hclosed sx x).
      * apply (proj2 (Hrel_succ (fun _ => witness) sx x)). exact Hsx.
      * exact Hx.
    + exact Hsx.
Qed.

(* ============================ REPLACEMENT =========================== *)

Definition Functional (R : V -> V -> Prop) : Prop :=
  forall x y1 y2, R y1 x -> R y2 x -> y1 = y2.

(* swap vars 0,1 and shift the rest up by one (to pass a new binder) *)
Definition rho : nat -> nat :=
  fun n => match n with 0 => 1 | 1 => 0 | S (S k) => S (S (S k)) end.

(* separation predicate for the image: "exists x (=var0 here), x in a /\ psi(y,x)" *)
Definition chi (psi : form) : form := fEx (fAnd (fMem 0 2) (rename rho psi)).

Lemma rho_env :
  forall d y a e n, (scons d (scons y (scons a e))) (rho n) = (scons y (scons d e)) n.
Proof. intros d y a e n. destruct n as [| [| k]]; reflexivity. Qed.

Lemma chi_spec :
  forall psi e a y,
    Sat (scons y (scons a e)) (chi psi) <-> exists d, d ∈ a /\ relOf psi e y d.
Proof.
  intros psi e a y. unfold chi, relOf. simpl. split.
  - intros [d [Hda Hpsi]]. exists d. split.
    + exact Hda.
    + apply (proj1 (Sat_rename psi rho (scons d (scons y (scons a e))))) in Hpsi.
      apply (proj1 (Sat_ext psi (fun n => scons d (scons y (scons a e)) (rho n))
                            (scons y (scons d e)) (fun n => rho_env d y a e n))) in Hpsi.
      exact Hpsi.
  - intros [d [Hda Hpsi]]. exists d. split.
    + exact Hda.
    + apply (proj2 (Sat_rename psi rho (scons d (scons y (scons a e))))).
      apply (proj2 (Sat_ext psi (fun n => scons d (scons y (scons a e)) (rho n))
                            (scons y (scons d e)) (fun n => rho_env d y a e n))).
      exact Hpsi.
Qed.

Theorem ReplacementFO :
  forall (psi : form) (e : nat -> V),
    Functional (relOf psi e) ->
    forall a, exists r, forall y, y ∈ r <-> exists x, x ∈ a /\ relOf psi e y x.
Proof.
  intros psi e Hfun a.
  assert (HSL : SetLike (relOf psi e)).
  { intro x. destruct (classic (exists y0, relOf psi e y0 x)) as [[y0 Hy0] | Hno].
    - exists (power y0). intros z Hz.
      assert (z = y0) by (apply (Hfun x z y0); [ exact Hz | exact Hy0 ]).
      subst z. apply self_in_power.
    - exists emptyset. intros z Hz. exfalso. apply Hno. exists z. exact Hz. }
  destruct (ClosureFO psi e HSL a) as [w [Hsub Hclosed]].
  exists (sepF w (chi psi) (scons a e)).
  intro y. split.
  - intro H. apply (proj1 (sepF_spec w (chi psi) (scons a e) y)) in H.
    destruct H as [_ Hpred]. exact (proj1 (chi_spec psi e a y) Hpred).
  - intro H. apply (proj2 (sepF_spec w (chi psi) (scons a e) y)). split.
    + destruct H as [x [Hxa Hyx]]. apply (Hclosed y x).
      * exact Hyx.
      * apply Hsub. exact Hxa.
    + exact (proj2 (chi_spec psi e a y) H).
Qed.

End Deep.

Check Pairing.
Check Union.
Check ReplacementFO.
Check Infinity.
