(* ===================================================================== *)
(*  Calculus.v                                                            *)
(*                                                                       *)
(*  GENERIC classical natural deduction over the formulas of Fol.v, and   *)
(*  its proof theory -- independent of any particular theory:             *)
(*                                                                       *)
(*   - the calculus `Prov : list form -> form -> Prop` (assumption,       *)
(*     intro/elim rules for the connectives and quantifiers, excluded     *)
(*     middle, equality reflexivity and the Leibniz rule `P_eqElim`);     *)
(*   - admissible rules: weakening, proof by contradiction, double        *)
(*     negation elimination, cut, and renaming admissibility              *)
(*     `Prov_rename`;                                                     *)
(*   - consistency `Con`;                                                 *)
(*   - the derived equality kit (symmetry, transitivity, congruence);     *)
(*   - eigenvariable generalization and the Henkin-witness core lemmas;   *)
(*   - SOUNDNESS: `Prov G a -> forall e, (e |= G) -> Sat e a` over any    *)
(*     structure (V, mem).                                                *)
(*                                                                       *)
(*  - Created (UTC): 2026-07-01T21:20:00Z                                 *)
(*  - Repository HEAD: c73d98802cf8385db7100480fdc5019105812718           *)
(* ===================================================================== *)

From SetTheory Require Import Fol.
From Stdlib Require Import List PeanoNat Classical Lia Setoid.
Import ListNotations.

(* ===================================================================== *)
(*  The natural-deduction calculus.  Terms are variables only (the        *)
(*  signature is purely relational), so quantifier instantiation          *)
(*  substitutes a variable for de Bruijn 0 -- which is just a renaming.   *)
(* ===================================================================== *)

Inductive Prov : list form -> form -> Prop :=
| P_ass    : forall G a, In a G -> Prov G a
| P_impI   : forall G a b, Prov (a :: G) b -> Prov G (fImp a b)
| P_impE   : forall G a b, Prov G (fImp a b) -> Prov G a -> Prov G b
| P_botE   : forall G a, Prov G fBot -> Prov G a
| P_lem    : forall G a, Prov G (fOr a (fImp a fBot))
| P_andI   : forall G a b, Prov G a -> Prov G b -> Prov G (fAnd a b)
| P_andE1  : forall G a b, Prov G (fAnd a b) -> Prov G a
| P_andE2  : forall G a b, Prov G (fAnd a b) -> Prov G b
| P_orI1   : forall G a b, Prov G a -> Prov G (fOr a b)
| P_orI2   : forall G a b, Prov G b -> Prov G (fOr a b)
| P_orE    : forall G a b c, Prov G (fOr a b) -> Prov (a :: G) c -> Prov (b :: G) c -> Prov G c
| P_allI   : forall G a, Prov (map (rename S) G) a -> Prov G (fAll a)
| P_allE   : forall G a k, Prov G (fAll a) -> Prov G (rename (inst k) a)
| P_exI    : forall G a k, Prov G (rename (inst k) a) -> Prov G (fEx a)
| P_exE    : forall G a c, Prov G (fEx a) -> Prov (a :: map (rename S) G) (rename S c) -> Prov G c
| P_eqRefl : forall G k, Prov G (fEq k k)
(* proper Leibniz: from i=j and a[0:=i] infer a[0:=j] (a is the property with
   a hole at de Bruijn 0). Gives symmetry/transitivity/congruence; still sound. *)
| P_eqElim : forall G i j a,
    Prov G (fEq i j) -> Prov G (rename (inst i) a) -> Prov G (rename (inst j) a).
(* ====================== [1] proof-theory infrastructure =============== *)

(* Weakening: enlarging the context preserves provability. *)
Lemma Prov_weaken :
  forall G a, Prov G a -> forall G', (forall x, In x G -> In x G') -> Prov G' a.
Proof.
  intros G a H.
  induction H as
    [ G a Hin
    | G a b Hpre IH
    | G a b H1 IHab H2 IHa
    | G a Hpre IH
    | G a
    | G a b H1 IHa H2 IHb
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b c H1 IHor H2 IHa H3 IHb
    | G a Hpre IH
    | G a k Hpre IH
    | G a k Hpre IH
    | G a c H1 IHex H2 IHbody
    | G k
    | G i j a H1 IHeq H2 IHa ];
    intros G' Hsub.
  - apply P_ass. exact (Hsub a Hin).
  - apply P_impI. apply IH. intros x Hx. destruct Hx as [Heq | HxG].
    + left. exact Heq.
    + right. exact (Hsub x HxG).
  - exact (P_impE G' a b (IHab G' Hsub) (IHa G' Hsub)).
  - apply (P_botE G' a). exact (IH G' Hsub).
  - apply P_lem.
  - apply P_andI; [ exact (IHa G' Hsub) | exact (IHb G' Hsub) ].
  - exact (P_andE1 G' a b (IH G' Hsub)).
  - exact (P_andE2 G' a b (IH G' Hsub)).
  - apply P_orI1. exact (IH G' Hsub).
  - apply P_orI2. exact (IH G' Hsub).
  - apply (P_orE G' a b c).
    + exact (IHor G' Hsub).
    + apply IHa. intros x Hx. destruct Hx as [Heq | HxG]; [ left; exact Heq | right; exact (Hsub x HxG) ].
    + apply IHb. intros x Hx. destruct Hx as [Heq | HxG]; [ left; exact Heq | right; exact (Hsub x HxG) ].
  - apply P_allI. apply IH. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [x0 [Heq Hx0]]. subst x.
    apply in_map. exact (Hsub x0 Hx0).
  - apply (P_allE G' a k). exact (IH G' Hsub).
  - apply (P_exI G' a k). exact (IH G' Hsub).
  - apply (P_exE G' a c).
    + exact (IHex G' Hsub).
    + apply IHbody. intros x Hx. destruct Hx as [Heq | HxM].
      * left. exact Heq.
      * right. apply in_map_iff in HxM. destruct HxM as [x0 [Heq Hx0]]. subst x.
        apply in_map. exact (Hsub x0 Hx0).
  - apply P_eqRefl.
  - apply (P_eqElim G' i j a); [ exact (IHeq G' Hsub) | exact (IHa G' Hsub) ].
Qed.

(* A handy corollary: prepend an unused hypothesis. *)
Lemma Prov_cons : forall G a b, Prov G b -> Prov (a :: G) b.
Proof. intros G a b H. apply (Prov_weaken G b H). intros x Hx. right. exact Hx. Qed.

(* Disjunction elimination in implication form.  All three premises share a
   context, which makes this form especially convenient for BProv lifting. *)
Lemma Prov_orE_imp : forall G a b c,
  Prov G (fOr a b) ->
  Prov G (fImp a c) ->
  Prov G (fImp b c) ->
  Prov G c.
Proof.
  intros G a b c Hor Ha Hb.
  apply (P_orE G a b c Hor).
  - apply (P_impE (a :: G) a c).
    + apply Prov_cons. exact Ha.
    + apply P_ass. left. reflexivity.
  - apply (P_impE (b :: G) b c).
    + apply Prov_cons. exact Hb.
    + apply P_ass. left. reflexivity.
Qed.

(* Proof by contradiction as a derived rule. *)
Lemma Prov_byContra : forall G a, Prov (fImp a fBot :: G) fBot -> Prov G a.
Proof.
  intros G a H. apply (P_orE G a (fImp a fBot)).
  - apply P_lem.
  - apply P_ass. left. reflexivity.
  - apply P_botE. exact H.
Qed.

(* Double-negation elimination. *)
Lemma Prov_dne : forall G a, Prov G (fImp (fImp a fBot) fBot) -> Prov G a.
Proof.
  intros G a H. apply Prov_byContra.
  apply (P_impE (fImp a fBot :: G) (fImp a fBot) fBot).
  - apply Prov_cons. exact H.
  - apply P_ass. left. reflexivity.
Qed.
(* ====================== [2] consistency ================================ *)

Definition Con (G : list form) : Prop := ~ Prov G fBot.

(* --- equality kit: the proper Leibniz rule makes equality an equivalence  *)
(* with full congruence (impossible with the old replace-everywhere rule).  *)

Lemma Prov_eq_sym : forall G i j, Prov G (fEq i j) -> Prov G (fEq j i).
Proof.
  intros G i j H. change (Prov G (rename (inst j) (fEq 0 (S i)))).
  apply (P_eqElim G i j (fEq 0 (S i))).
  - exact H.
  - change (Prov G (fEq i i)). apply P_eqRefl.
Qed.

Lemma Prov_eq_trans :
  forall G i j k, Prov G (fEq i j) -> Prov G (fEq j k) -> Prov G (fEq i k).
Proof.
  intros G i j k H1 H2. change (Prov G (rename (inst k) (fEq (S i) 0))).
  apply (P_eqElim G j k (fEq (S i) 0)).
  - exact H2.
  - change (Prov G (fEq i j)). exact H1.
Qed.

Lemma Prov_mem_cong1 :
  forall G i j k, Prov G (fEq i j) -> Prov G (fMem i k) -> Prov G (fMem j k).
Proof.
  intros G i j k H1 H2. change (Prov G (rename (inst j) (fMem 0 (S k)))).
  apply (P_eqElim G i j (fMem 0 (S k))).
  - exact H1.
  - change (Prov G (fMem i k)). exact H2.
Qed.

Lemma Prov_mem_cong2 :
  forall G i j k, Prov G (fEq i j) -> Prov G (fMem k i) -> Prov G (fMem k j).
Proof.
  intros G i j k H1 H2. change (Prov G (rename (inst j) (fMem (S k) 0))).
  apply (P_eqElim G i j (fMem (S k) 0)).
  - exact H1.
  - change (Prov G (fMem k i)). exact H2.
Qed.
(* ===================== [4] Lindenbaum / Henkin ======================= *)

(* ---- [4a] renaming admissibility for the calculus ---- *)

Lemma map_rename_up_S :
  forall r G, map (rename (up r)) (map (rename S) G) = map (rename S) (map (rename r) G).
Proof.
  intros r G. rewrite !map_map. apply map_ext. intro x.
  rewrite !rename_comp. apply rename_ext. intro n; reflexivity.
Qed.

Lemma Prov_rename :
  forall G phi, Prov G phi -> forall r, Prov (map (rename r) G) (rename r phi).
Proof.
  intros G phi H.
  induction H as
    [ G a Hin
    | G a b Hpre IH
    | G a b H1 IHab H2 IHa
    | G a Hpre IH
    | G a
    | G a b H1 IHa H2 IHb
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b c H1 IHor H2 IHa H3 IHb
    | G a Hpre IH
    | G a k Hpre IH
    | G a k Hpre IH
    | G a c H1 IHex H2 IHbody
    | G k
    | G i j a H1 IHeq H2 IHa ];
    intro r.
  - apply P_ass. apply in_map. exact Hin.
  - apply P_impI. exact (IH r).
  - exact (P_impE _ (rename r a) (rename r b) (IHab r) (IHa r)).
  - apply (P_botE _ (rename r a)). exact (IH r).
  - apply P_lem.
  - apply P_andI; [ exact (IHa r) | exact (IHb r) ].
  - exact (P_andE1 _ (rename r a) (rename r b) (IH r)).
  - exact (P_andE2 _ (rename r a) (rename r b) (IH r)).
  - apply P_orI1. exact (IH r).
  - apply P_orI2. exact (IH r).
  - exact (P_orE _ (rename r a) (rename r b) (rename r c) (IHor r) (IHa r) (IHb r)).
  - apply P_allI. rewrite <- (map_rename_up_S r G). exact (IH (up r)).
  - (* P_allE *)
    pose proof (rename_inst_push a r k) as Heqj.
    rewrite Heqj. apply (P_allE _ (rename (up r) a) (r k)). exact (IH r).
  - (* P_exI *)
    apply (P_exI _ (rename (up r) a) (r k)).
    pose proof (rename_inst_push a r k) as Heqj.
    rewrite <- Heqj. exact (IH r).
  - (* P_exE *)
    apply (P_exE _ (rename (up r) a) (rename r c)).
    + exact (IHex r).
    + assert (Hc : rename S (rename r c) = rename (up r) (rename S c)).
      { rewrite !rename_comp. apply rename_ext. intro n; reflexivity. }
      rewrite Hc. rewrite <- (map_rename_up_S r G). exact (IHbody (up r)).
  - apply P_eqRefl.
  - (* P_eqElim *)
    pose proof (rename_inst_push a r j) as Heqj.
    rewrite Heqj. apply (P_eqElim _ (r i) (r j) (rename (up r) a)).
    + exact (IHeq r).
    + pose proof (rename_inst_push a r i) as Heqi.
      rewrite <- Heqi. exact (IHa r).
Qed.
(* eigenvariable generalization: from G |- a[w/0] with w fresh, G shifted |- a *)
Lemma generalize_fresh :
  forall G a w, (forall g, In g G -> ~ Free w g) -> ~ Free (S w) a ->
    Prov G (rename (inst w) a) -> Prov (map (rename S) G) a.
Proof.
  intros G a w HwG Hwa Hp.
  pose proof (Prov_rename _ _ Hp (rho_w w)) as Hr.
  rewrite (rho_inst a w Hwa) in Hr.
  rewrite (map_rho_S G w HwG) in Hr.
  exact Hr.
Qed.

(* context exchange (same elements => same provability) *)
Lemma Prov_exch :
  forall G G' phi, (forall x, In x G <-> In x G') -> Prov G phi -> Prov G' phi.
Proof.
  intros G G' phi H Hp. apply (Prov_weaken G phi Hp). intros x Hx. apply H. exact Hx.
Qed.

(* the Prov-level cores of the Henkin lemmas, with an arbitrary fresh witness *)
Lemma henkin_ex_core :
  forall G a w, ~ Free (S w) a -> (forall g, In g G -> ~ Free w g) ->
    Prov (rename (inst w) a :: fEx a :: G) fBot -> Prov (fEx a :: G) fBot.
Proof.
  intros G a w Hwa HwG Hbad.
  apply (P_exE (fEx a :: G) a fBot).
  - apply P_ass. left. reflexivity.
  - pose proof (Prov_rename _ _ Hbad (rho_w w)) as Hr. simpl in Hr.
    rewrite (rho_inst a w Hwa), (rho_under a w Hwa), (map_rho_S G w HwG) in Hr.
    simpl. exact Hr.
Qed.

Lemma henkin_all_core :
  forall G a w, ~ Free (S w) a -> (forall g, In g G -> ~ Free w g) ->
    Prov (fImp (rename (inst w) a) fBot :: fImp (fAll a) fBot :: G) fBot ->
    Prov (fImp (fAll a) fBot :: G) fBot.
Proof.
  intros G a w Hwa HwG Hbad.
  apply Prov_byContra in Hbad.
  assert (HwG' : forall g, In g (fImp (fAll a) fBot :: G) -> ~ Free w g).
  { intros g [<- | Hg].
    - intro Hf. simpl in Hf. destruct Hf as [Hf | Hf]; [ exact (Hwa Hf) | exact Hf ].
    - exact (HwG g Hg). }
  pose proof (generalize_fresh (fImp (fAll a) fBot :: G) a w HwG' Hwa Hbad) as Hgen.
  apply P_allI in Hgen.
  apply (P_impE (fImp (fAll a) fBot :: G) (fAll a) fBot).
  - apply P_ass. left. reflexivity.
  - exact Hgen.
Qed.
(* ---- [4c] cut: replacing assumptions by derivations ---- *)

Lemma Prov_cut :
  forall G phi, Prov G phi -> forall De, (forall x, In x G -> Prov De x) -> Prov De phi.
Proof.
  intros G phi H.
  induction H as
    [ G a Hin
    | G a b Hpre IH
    | G a b H1 IHab H2 IHa
    | G a Hpre IH
    | G a
    | G a b H1 IHa H2 IHb
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b c H1 IHor H2 IHa H3 IHb
    | G a Hpre IH
    | G a k Hpre IH
    | G a k Hpre IH
    | G a c H1 IHex H2 IHbody
    | G k
    | G i j a H1 IHeq H2 IHa ];
    intros De HD.
  - exact (HD a Hin).
  - apply P_impI. apply IH. intros x Hx. destruct Hx as [Heq | HxG].
    + subst x. apply P_ass. left. reflexivity.
    + apply Prov_cons. exact (HD x HxG).
  - exact (P_impE _ a b (IHab De HD) (IHa De HD)).
  - apply (P_botE _ a). exact (IH De HD).
  - apply P_lem.
  - apply P_andI; [ exact (IHa De HD) | exact (IHb De HD) ].
  - exact (P_andE1 _ a b (IH De HD)).
  - exact (P_andE2 _ a b (IH De HD)).
  - apply P_orI1. exact (IH De HD).
  - apply P_orI2. exact (IH De HD).
  - apply (P_orE _ a b c).
    + exact (IHor De HD).
    + apply IHa. intros x Hx. destruct Hx as [Heq | HxG];
        [ subst x; apply P_ass; left; reflexivity | apply Prov_cons; exact (HD x HxG) ].
    + apply IHb. intros x Hx. destruct Hx as [Heq | HxG];
        [ subst x; apply P_ass; left; reflexivity | apply Prov_cons; exact (HD x HxG) ].
  - apply P_allI. apply IH. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [x0 [Heq Hx0]]. subst x.
    exact (Prov_rename _ _ (HD x0 Hx0) S).
  - apply (P_allE _ a k). exact (IH De HD).
  - apply (P_exI _ a k). exact (IH De HD).
  - apply (P_exE _ a c).
    + exact (IHex De HD).
    + apply IHbody. intros x Hx. destruct Hx as [Heq | HxM].
      * subst x. apply P_ass. left. reflexivity.
      * apply in_map_iff in HxM. destruct HxM as [x0 [Heq Hx0]]. subst x.
        apply Prov_cons. exact (Prov_rename _ _ (HD x0 Hx0) S).
  - apply P_eqRefl.
  - apply (P_eqElim _ i j a); [ exact (IHeq De HD) | exact (IHa De HD) ].
Qed.

(* ===================== soundness for Tarski semantics ================== *)

Section Soundness.

Variable V : Type.
Variable mem : V -> V -> Prop.
Local Notation Sat := (Fol.Sat V mem).
Local Notation scons := (Fol.scons V).
Local Notation Sat_ext := (Fol.Sat_ext V mem).
Local Notation Sat_rename := (Fol.Sat_rename V mem).
Local Notation inst_env := (Fol.inst_env V).

(* environment lemma for the context shift *)
Lemma shift_sat :
  forall G e d, (forall x, In x G -> Sat e x) ->
                forall y, In y (map (rename S) G) -> Sat (scons d e) y.
Proof.
  intros G e d HG y Hy. apply in_map_iff in Hy. destruct Hy as [x [Hxr Hxin]]. subst y.
  apply (proj2 (Sat_rename x S (scons d e))).
  apply (proj2 (Sat_ext x (fun n => scons d e (S n)) e (fun n => eq_refl))).
  exact (HG x Hxin).
Qed.
Theorem soundness :
  forall G a, Prov G a -> forall e, (forall x, In x G -> Sat e x) -> Sat e a.
Proof.
  intros G a H.
  induction H as
    [ G a Hin
    | G a b Hpre IH
    | G a b H1 IHab H2 IHa
    | G a Hpre IH
    | G a
    | G a b H1 IHa H2 IHb
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b Hpre IH
    | G a b c H1 IHor H2 IHa H3 IHb
    | G a Hpre IH
    | G a k Hpre IH
    | G a k Hpre IH
    | G a c H1 IHex H2 IHbody
    | G k
    | G i j a H1 IHeq H2 IHa ];
    intros e HG.
  - exact (HG a Hin).
  - simpl. intro Ha. apply (IH e). intros x Hx. destruct Hx as [Hxa | HxG].
    + subst x. exact Ha.
    + exact (HG x HxG).
  - exact (IHab e HG (IHa e HG)).
  - destruct (IH e HG).
  - simpl. exact (classic (Sat e a)).
  - simpl. split; [ exact (IHa e HG) | exact (IHb e HG) ].
  - exact (proj1 (IH e HG)).
  - exact (proj2 (IH e HG)).
  - simpl. left. exact (IH e HG).
  - simpl. right. exact (IH e HG).
  - destruct (IHor e HG) as [Ha | Hb].
    + apply (IHa e). intros x Hx. destruct Hx as [Hxa | HxG]; [ subst x; exact Ha | exact (HG x HxG) ].
    + apply (IHb e). intros x Hx. destruct Hx as [Hxb | HxG]; [ subst x; exact Hb | exact (HG x HxG) ].
  - simpl. intro d. exact (IH (scons d e) (shift_sat G e d HG)).
  - apply (proj2 (Sat_rename a (inst k) e)).
    apply (proj2 (Sat_ext a (fun n => e (inst k n)) (scons (e k) e) (inst_env k e))).
    exact (IH e HG (e k)).
  - simpl. exists (e k).
    apply (proj1 (Sat_ext a (fun n => e (inst k n)) (scons (e k) e) (inst_env k e))).
    apply (proj1 (Sat_rename a (inst k) e)). exact (IH e HG).
  - destruct (IHex e HG) as [d Hd].
    assert (Hc : Sat (scons d e) (rename S c)).
    { apply (IHbody (scons d e)). intros y Hy. destruct Hy as [Hya | HyG].
      - subst y. exact Hd.
      - exact (shift_sat G e d HG y HyG). }
    apply (proj1 (Sat_rename c S (scons d e))) in Hc.
    apply (proj1 (Sat_ext c (fun n => scons d e (S n)) e (fun n => eq_refl))) in Hc.
    exact Hc.
  - simpl. reflexivity.
  - (* P_eqElim *)
    assert (Hij : e i = e j) by exact (IHeq e HG).
    apply (proj2 (Sat_rename a (inst j) e)).
    apply (proj2 (Sat_ext a (fun n => e (inst j n)) (scons (e j) e) (inst_env j e))).
    pose proof (IHa e HG) as Ha.
    apply (proj1 (Sat_rename a (inst i) e)) in Ha.
    apply (proj1 (Sat_ext a (fun n => e (inst i n)) (scons (e i) e) (inst_env i e))) in Ha.
    rewrite Hij in Ha. exact Ha.
Qed.

End Soundness.

Check soundness.
Check Prov_rename.
Check Prov_cut.
