(* ===================================================================== *)
(*  Equivalence.v                                                         *)
(*                                                                       *)
(*  THE CLOSURE AXIOMATIZATION T AND ITS EQUIVALENCE WITH ZF.  This is    *)
(*  the only file specific to the axiomatization T = {Extensionality,     *)
(*  Regularity, Separation, Powerset, Closure}.  Building on the generic  *)
(*  modules (Fol, Calculus, Completeness) and the first-order ZF module   *)
(*  (Zf), it proves:                                                      *)
(*                                                                       *)
(*   - the deep FORWARD trade: from the first-order schemas               *)
(*     SeparationFO + ClosureFO (with Powerset and a nonempty domain),    *)
(*     Pairing, Union, first-order Replacement, and Infinity are          *)
(*     theorems -- each schema instance exhibited as a concrete formula;  *)
(*   - `ZF_provable_holds_in_T`: in any T-model, every ZF-provable        *)
(*     formula holds (soundness + the forward trade);                     *)
(*   - the Closure schema as a closed formula (`Closure_form`) with its   *)
(*     satisfaction bridge, and T as a sentence theory `Tax_s`;           *)
(*   - `Tmodel_sat_ZF` / `ZFmodel_sat_T`: T and ZF have exactly the same  *)
(*     models (the deep reverse uses Zf.ClosureFO_of_ZF -- the internal   *)
(*     recursion theorem);                                                *)
(*   - the syntactic equivalence, both directions:                        *)
(*         ZF_implies_T, T_implies_ZF, and the headline T_iff_ZF.         *)
(*                                                                       *)
(*  - Created (UTC): 2026-07-01T21:20:00Z                                 *)
(*  - Repository HEAD: c73d98802cf8385db7100480fdc5019105812718           *)
(* ===================================================================== *)

From SetTheory Require Import Fol Calculus Completeness Zf.
From Stdlib Require Import List PeanoNat Setoid ClassicalEpsilon.
Import ListNotations.

(* ===================================================================== *)
(*  The deep forward direction: a Section assuming the T-schemas over an  *)
(*  abstract structure (V, mem), deriving the four generative ZF axioms   *)
(*  with genuinely first-order schema instances, and the cross-theory     *)
(*  corollary ZF |- phi  ->  T |= phi.                                    *)
(* ===================================================================== *)

Section DeepForward.

Variable V : Type.
Variable mem : V -> V -> Prop.
Local Infix "∈" := mem (at level 70, no associativity).

Local Notation Sat := (Fol.Sat V mem).
Local Notation scons := (Fol.scons V).
Local Notation relOf := (Fol.relOf V mem).
Local Notation SetLike := (Fol.SetLike V mem).
Local Notation Sub := (Fol.Sub V mem).
Local Notation Functional := (Fol.Functional V).
Local Notation Sat_rename_ext := (Fol.Sat_rename_ext V mem).
Local Notation Sat_rename_relOf := (Fol.Sat_rename_relOf V mem).
Local Notation rsep_env := (Zf.rsep_env V).
Local Notation soundness := (Calculus.soundness V mem).

Variable witness : V.

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


(* genuine first-order Closure: the relation is a formula psi *)
Hypothesis ClosureFO :
  forall (psi : form) (e : nat -> V),
    SetLike (relOf psi e) ->
    forall s, exists w, Sub s w /\ (forall u v, relOf psi e u v -> v ∈ w -> u ∈ w).

(* Regularity is a T-axiom (shared with ZF).  Unused by the forward trade *)
(* below, but needed so that a T-model satisfies ZF's Regularity axiom in   *)
(* the soundness corollary.                                                 *)
Hypothesis Regularity :
  forall a, (exists x, x ∈ a) ->
            exists m, m ∈ a /\ ~ (exists z, z ∈ m /\ z ∈ a).
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
  assert (Hfun : Functional (relOf psi_pair (e_pair a b))).
  { unfold Functional. intros x z1 z2 Hz1 Hz2.
    apply (proj1 (Hrel_pair a b z1 x)) in Hz1.
    apply (proj1 (Hrel_pair a b z2 x)) in Hz2.
    pose proof empty_neq_single as Hne.
    destruct Hz1 as [[Hx1 Hz1] | [Hx1 Hz1]];
      destruct Hz2 as [[Hx2 Hz2] | [Hx2 Hz2]]; congruence. }
  pose proof (functional_setlike_of_host power self_in_power witness
    (relOf psi_pair (e_pair a b)) Hfun) as HSL.
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
  assert (Hfun : Functional (relOf psi_succ (fun _ => witness))).
  { unfold Functional. intros x z1 z2 Hz1 Hz2.
    pose proof (proj1 (Hrel_succ (fun _ => witness) z1 x) Hz1) as H1.
    pose proof (proj1 (Hrel_succ (fun _ => witness) z2 x) Hz2) as H2.
    apply Extensionality. intro t. rewrite (H1 t), (H2 t). reflexivity. }
  pose proof (functional_setlike_of_host power self_in_power witness
    (relOf psi_succ (fun _ => witness)) Hfun) as HSL.
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
  intros psi e a y. unfold chi. simpl. split.
  - intros [d [Hda Hpsi]]. exists d. split.
    + exact Hda.
    + apply (proj1 (Sat_rename_relOf psi rho
                      (scons d (scons y (scons a e))) e y d
                      (fun n => rho_env d y a e n))) in Hpsi.
      exact Hpsi.
  - intros [d [Hda Hpsi]]. exists d. split.
    + exact Hda.
    + apply (proj2 (Sat_rename_relOf psi rho
                      (scons d (scons y (scons a e))) e y d
                      (fun n => rho_env d y a e n))).
      exact Hpsi.
Qed.

Theorem ReplacementFO :
  forall (psi : form) (e : nat -> V),
    Functional (relOf psi e) ->
    forall a, exists r, forall y, y ∈ r <-> exists x, x ∈ a /\ relOf psi e y x.
Proof.
  intros psi e Hfun a.
  pose proof (functional_setlike_of_host power self_in_power witness
    (relOf psi e) Hfun) as HSL.
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

(* ===================================================================== *)
(*  CROSS-THEORY COROLLARY: everything ZF proves holds in every model of  *)
(*  the Closure axiomatization T.  (The ZF axiom formulas and the axiom   *)
(*  set ZFax live in Zf.v; here we check each against this T-model.)      *)
(* ===================================================================== *)


(* --- this T-model satisfies each ZF axiom --- *)

Lemma sat_Ext : forall e, Sat e Ext_form.
Proof. exact (proj2 (bridge_Ext V mem) Extensionality). Qed.

Lemma sat_Pair : forall e, Sat e Pair_form.
Proof. exact (proj2 (bridge_Pair V mem) Pairing). Qed.

Lemma sat_Union : forall e, Sat e Union_form.
Proof. exact (proj2 (bridge_Union V mem) Union). Qed.

Lemma sat_Pow : forall e, Sat e Pow_form.
Proof. exact (proj2 (bridge_Pow V mem) Powerset). Qed.

Lemma sat_Inf : forall e, Sat e Inf_form.
Proof. intro e. exact (proj2 (bridge_Inf V mem e) Infinity). Qed.

Lemma sat_Reg : forall e, Sat e Reg_form.
Proof. exact (proj2 (bridge_Reg V mem) Regularity). Qed.

Lemma sat_Sep : forall phi e, Sat e (Sep_form phi).
Proof. exact (proj2 (bridge_Sep V mem) SeparationFO). Qed.

Lemma sat_Repl : forall psi e, Sat e (Repl_form psi).
Proof.
  intros psi e. apply (proj2 (bridge_Repl V mem psi e)).
  exact (ReplacementFO psi e).
Qed.

Lemma sat_ZFax : forall f, ZFax f -> forall e, Sat e f.
Proof.
  intros f Hf e.
  destruct Hf as [-> | [-> | [-> | [-> | [-> | [-> | [[phi ->] | [psi ->]]]]]]]].
  - apply sat_Ext.
  - apply sat_Pair.
  - apply sat_Union.
  - apply sat_Pow.
  - apply sat_Inf.
  - apply sat_Reg.
  - apply sat_Sep.
  - apply sat_Repl.
Qed.

(* In this (arbitrary) model of T, every ZF-provable formula holds. *)
Theorem ZF_provable_holds_in_T :
  forall phi, ZFprov phi -> forall e, Sat e phi.
Proof.
  intros phi [G [HG Hprov]] e.
  apply (soundness G phi Hprov e).
  intros x Hx. exact (sat_ZFax x (HG x Hx) e).
Qed.

End DeepForward.

(* free dependency audit: which T-hypotheses each derivation consumed *)
Check Pairing.
Check Union.
Check ReplacementFO.
Check Infinity.
Check ZF_provable_holds_in_T.

(* ===================================================================== *)
(*  The Closure schema as a closed formula, and its satisfaction bridge   *)
(*  to the abstract set-like/closure statement.                           *)
(* ===================================================================== *)

(* set-like binders  forall x, exists y, forall z   (z=0,y=1,x=2);
   psi(z,x): 0->0, 1->2, (2+j)->(3+j) *)
Definition r_sl : nat -> nat := fun n => match n with O => 0 | 1 => 2 | S (S j) => S (S (S j)) end.
(* closure body binders forall s, exists w, forall d1, forall d2 (d2=0,d1=1,w=2,s=3);
   psi(d1,d2): 0->1, 1->0, (2+j)->(4+j) *)
Definition r_cl : nat -> nat := fun n => match n with O => 1 | 1 => O | S (S j) => S (S (S (S j))) end.

Definition SetLikeForm (psi : form) : form :=
  fAll (fEx (fAll (fImp (rename r_sl psi) (fMem 0 1)))).
Definition ClosureBodyForm (psi : form) : form :=
  fAll (fEx (fAnd (fAll (fImp (fMem 0 2) (fMem 0 1)))
                  (fAll (fAll (fImp (fAnd (rename r_cl psi) (fMem 0 2)) (fMem 1 2)))))).
Definition Closure_form (psi : form) : form :=
  fImp (SetLikeForm psi) (ClosureBodyForm psi).

Section ClosureBridge.
  Variable V : Type.
  Variable mem : V -> V -> Prop.

  Lemma r_sl_env : forall z y x (e : nat -> V) n,
    scons V z (scons V y (scons V x e)) (r_sl n) = scons V z (scons V x e) n.
  Proof. intros. destruct n as [| [| j]]; reflexivity. Qed.

  Lemma r_cl_env : forall d2 d1 w s (e : nat -> V) n,
    scons V d2 (scons V d1 (scons V w (scons V s e))) (r_cl n) = scons V d1 (scons V d2 e) n.
  Proof. intros. destruct n as [| [| j]]; reflexivity. Qed.

  (* the rename-r_cl atom denotes relOf psi e d1 d2 *)
  Lemma rcl_rel : forall psi e d1 d2 w s,
    Sat V mem (scons V d2 (scons V d1 (scons V w (scons V s e)))) (rename r_cl psi)
    <-> relOf V mem psi e d1 d2.
  Proof.
    intros psi e d1 d2 w s.
    apply (Sat_rename_relOf V mem psi r_cl
             (scons V d2 (scons V d1 (scons V w (scons V s e)))) e d1 d2
             (r_cl_env d2 d1 w s e)).
  Qed.

  Lemma bridge_SetLike : forall psi e,
    Sat V mem e (SetLikeForm psi) <-> SetLike V mem (relOf V mem psi e).
  Proof.
    intros psi e. unfold SetLikeForm, SetLike. cbn [Sat]. split.
    - intros H x. destruct (H x) as [y Hy]. exists y. intros z Hz.
      apply Hy.
      apply (proj2 (Sat_rename_relOf V mem psi r_sl
                      (scons V z (scons V y (scons V x e))) e z x
                      (r_sl_env z y x e))). exact Hz.
    - intros H x. destruct (H x) as [y Hy]. exists y. intros z Hz.
      apply Hy.
      apply (proj1 (Sat_rename_relOf V mem psi r_sl
                      (scons V z (scons V y (scons V x e))) e z x
                      (r_sl_env z y x e))). exact Hz.
  Qed.

  Lemma bridge_ClosureBody : forall psi e,
    Sat V mem e (ClosureBodyForm psi) <->
    (forall s, exists w, Sub V mem s w /\
        (forall u v, relOf V mem psi e u v -> mem v w -> mem u w)).
  Proof.
    intros psi e. unfold ClosureBodyForm, Sub. cbn [Sat]. split.
    - intros H s. destruct (H s) as [w [Hsub Hcl]]. exists w. split.
      + intros t Ht. exact (Hsub t Ht).
      + intros u v Hrel Hvw. apply (Hcl u v). split; [ | exact Hvw ].
        apply (proj2 (rcl_rel psi e u v w s)). exact Hrel.
    - intros H s. destruct (H s) as [w [Hsub Hcl]]. exists w. split.
      + intros t Ht. exact (Hsub t Ht).
      + intros d1 d2 [Hr Hvw]. apply (Hcl d1 d2); [ | exact Hvw ].
        apply (proj1 (rcl_rel psi e d1 d2 w s)). exact Hr.
  Qed.

  Lemma bridge_Closure : forall psi e,
    Sat V mem e (Closure_form psi) <->
    (SetLike V mem (relOf V mem psi e) ->
     forall s, exists w, Sub V mem s w /\
        (forall u v, relOf V mem psi e u v -> mem v w -> mem u w)).
  Proof.
    intros psi e. unfold Closure_form. cbn [Sat].
    rewrite bridge_SetLike, bridge_ClosureBody. tauto.
  Qed.

End ClosureBridge.
(* --- ZF and T as sentence theories --- *)

Definition Tax_s (f : form) : Prop :=
  f = seal Ext_form \/ f = seal Reg_form \/ f = seal Pow_form \/
  (exists phi, f = seal (Sep_form phi)) \/ (exists psi, f = seal (Closure_form psi)).
Lemma Sentences_Tax : Sentences Tax_s.
Proof. intros f Hf. destruct Hf as [->|[->|[->|[[phi ->]|[psi ->]]]]]; apply Sentence_seal. Qed.
Lemma bridge_Closure_fwd :
  forall (V : Type) (mem : V -> V -> Prop), (forall psi e, Sat V mem e (Closure_form psi)) ->
    (forall psi e, SetLike V mem (relOf V mem psi e) ->
       forall s, exists w, Sub V mem s w /\
          (forall u v, relOf V mem psi e u v -> mem v w -> mem u w)).
Proof. intros V mem H psi e. exact (proj1 (bridge_Closure V mem psi e) (H psi e)). Qed.
(* every T-model is a ZF-model *)
Lemma Tmodel_sat_ZF :
  forall (V : Type) (mem : V -> V -> Prop) v,
    (forall g, Tax_s g -> Sat V mem v g) -> (forall g, ZFax_s g -> Sat V mem v g).
Proof.
  intros V mem v HT.
  assert (HE : forall e, Sat V mem e Ext_form)
    by (apply (extract Tax_s V mem v Ext_form HT); left; reflexivity).
  assert (HR : forall e, Sat V mem e Reg_form)
    by (apply (extract Tax_s V mem v Reg_form HT); right; left; reflexivity).
  assert (HP : forall e, Sat V mem e Pow_form)
    by (apply (extract Tax_s V mem v Pow_form HT); right; right; left; reflexivity).
  assert (HS : forall phi e, Sat V mem e (Sep_form phi)).
  { intro phi. apply (extract Tax_s V mem v (Sep_form phi) HT).
    right; right; right; left. exists phi. reflexivity. }
  assert (HC : forall psi e, Sat V mem e (Closure_form psi)).
  { intro psi. apply (extract Tax_s V mem v (Closure_form psi) HT).
    right; right; right; right. exists psi. reflexivity. }
  pose proof (bridge_Ext_fwd V mem HE) as AxE.
  pose proof (bridge_Reg_fwd V mem HR) as AxR.
  pose proof (bridge_Pow_fwd V mem HP) as AxP.
  pose proof (bridge_Sep_fwd V mem HS) as AxS.
  pose proof (bridge_Closure_fwd V mem HC) as AxC.
  intros g Hg.
  destruct Hg as [->|[->|[->|[->|[->|[->|[[phi ->]|[psi ->]]]]]]]].
  - apply HT. left. reflexivity.
  - apply HT. right; left. reflexivity.
  - apply HT. right; right; left. reflexivity.
  - exact (proj2 (closeN_valid V mem (bound Pair_form) Pair_form)
                 (sat_Pair V mem (v 0) AxE AxS AxP AxC) v).
  - exact (proj2 (closeN_valid V mem (bound Union_form) Union_form)
                 (sat_Union V mem (v 0) AxS AxC) v).
  - exact (proj2 (closeN_valid V mem (bound Inf_form) Inf_form)
                 (sat_Inf V mem (v 0) AxE AxS AxP AxC) v).
  - apply HT. right; right; right; left. exists phi. reflexivity.
  - exact (proj2 (closeN_valid V mem (bound (Repl_form psi)) (Repl_form psi))
                 (sat_Repl V mem (v 0) AxS AxP AxC psi) v).
Qed.

(* FORWARD SYNTACTIC DIRECTION: everything ZF proves, T proves. *)
Theorem ZF_implies_T :
  forall phi, Sentence phi -> BProv ZFax_s nil phi -> BProv Tax_s nil phi.
Proof.
  intros phi _ HZF.
  apply (theory_transfer ZFax_s Tax_s nil phi Sentences_Tax).
  - intros Dom m v HTsat. exact (Tmodel_sat_ZF Dom m v HTsat).
  - exact HZF.
Qed.
(* ===================================================================== *)
(*  Part C.  Every first-order ZF model satisfies the Closure schema,     *)
(*  hence is a T-model; generic theory transfer yields the converse       *)
(*  syntactic direction and the full deductive equivalence.               *)
(* ===================================================================== *)

(* every ZF model satisfies every instance of the (open) Closure formula *)
Lemma ZFmodel_sat_Closure :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
    (forall g, ZFax_s g -> Sat V mem v g) ->
    forall psi (e : nat -> V), Sat V mem e (Closure_form psi).
Proof.
  intros V mem v HZ psi e.
  assert (AxE : forall a b, (forall x, mem x a <-> mem x b) -> a = b).
  { apply bridge_Ext_fwd.
    apply (extract ZFax_s V mem v Ext_form HZ). left. reflexivity. }
  assert (AxS : forall (phi : form) (e' : nat -> V) (a : V),
             exists s, forall x, mem x s <-> (mem x a /\ Sat V mem (scons V x e') phi)).
  { apply bridge_Sep_fwd. intros phi e'.
    apply (extract ZFax_s V mem v (Sep_form phi) HZ).
    do 6 right. left. exists phi. reflexivity. }
  assert (AxP : forall a b, exists p, forall x, mem x p <-> (x = a \/ x = b)).
  { apply bridge_Pair_fwd.
    apply (extract ZFax_s V mem v Pair_form HZ). do 3 right. left. reflexivity. }
  assert (AxU : forall u, exists w, forall x, mem x w <-> exists y, mem x y /\ mem y u).
  { apply bridge_Union_fwd.
    apply (extract ZFax_s V mem v Union_form HZ). do 4 right. left. reflexivity. }
  assert (AxI : exists I,
             (exists e0, mem e0 I /\ forall z, ~ mem z e0) /\
             (forall x, mem x I ->
                exists sx, mem sx I /\ forall t, mem t sx <-> (mem t x \/ t = x))).
  { apply (bridge_Inf_fwd V mem v).
    apply (extract ZFax_s V mem v Inf_form HZ).
    do 5 right. left. reflexivity. }
  assert (AxR : forall (psi' : form) (e' : nat -> V),
             Functional V (relOf V mem psi' e') ->
             forall a, exists r, forall y,
               mem y r <-> exists x, mem x a /\ relOf V mem psi' e' y x).
  { apply bridge_Repl_fwd. intros psi' e'.
    apply (extract ZFax_s V mem v (Repl_form psi') HZ).
    do 7 right. exists psi'. reflexivity. }
  apply (proj2 (bridge_Closure V mem psi e)).
  intros HSL s.
  exact (ClosureFO_of_ZF V mem AxE AxS AxP AxU AxI AxR psi e HSL s).
Qed.

(* every ZF-model is a T-model (converse of Tmodel_sat_ZF) *)
Lemma ZFmodel_sat_T :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
    (forall g, ZFax_s g -> Sat V mem v g) ->
    forall g, Tax_s g -> Sat V mem v g.
Proof.
  intros V mem v HZ g Hg.
  destruct Hg as [-> | [-> | [-> | [[phi ->] | [psi ->]]]]].
  - apply HZ. left. reflexivity.
  - apply HZ. right; left. reflexivity.
  - apply HZ. right; right; left. reflexivity.
  - apply HZ. do 6 right. left. exists phi. reflexivity.
  - exact (proj2 (closeN_valid V mem (bound (Closure_form psi)) (Closure_form psi))
                 (ZFmodel_sat_Closure V mem v HZ psi) v).
Qed.

(* T and ZF have exactly the same models *)
Theorem T_ZF_same_models :
  forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
    (forall g, Tax_s g -> Sat Dom m v g) <-> (forall g, ZFax_s g -> Sat Dom m v g).
Proof.
  intros Dom m v. split.
  - exact (Tmodel_sat_ZF Dom m v).
  - exact (ZFmodel_sat_T Dom m v).
Qed.

(* THE CONVERSE SYNTACTIC DIRECTION: everything T proves, ZF proves. *)
Theorem T_implies_ZF :
  forall phi, Sentence phi -> BProv Tax_s nil phi -> BProv ZFax_s nil phi.
Proof.
  intros phi _ HT.
  apply (theory_transfer Tax_s ZFax_s nil phi Sentences_ZF).
  - intros Dom m v HZsat. exact (ZFmodel_sat_T Dom m v HZsat).
  - exact HT.
Qed.

(* THE HEADLINE: deductive equivalence of T and ZF, both directions. *)
Theorem T_iff_ZF :
  forall phi, Sentence phi -> (BProv Tax_s nil phi <-> BProv ZFax_s nil phi).
Proof.
  intros phi Hphi. split.
  - exact (T_implies_ZF phi Hphi).
  - exact (ZF_implies_T phi Hphi).
Qed.

(* cross-check: the same equivalence, derived instead as an instance of    *)
(* the general same-models theorem `theory_equiv` from Completeness.v      *)
Theorem T_iff_ZF_via_theory_equiv :
  forall phi, Sentence phi -> (BProv Tax_s nil phi <-> BProv ZFax_s nil phi).
Proof.
  exact (theory_equiv Tax_s ZFax_s Sentences_Tax Sentences_ZF T_ZF_same_models).
Qed.

Check ZFmodel_sat_Closure.
Check ZFmodel_sat_T.
Check T_ZF_same_models.
Check T_implies_ZF.
Check T_iff_ZF.
Print Assumptions T_iff_ZF.
