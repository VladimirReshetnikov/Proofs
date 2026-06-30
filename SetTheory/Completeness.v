(* ===================================================================== *)
(*  Completeness.v  (STAGED, work in progress)                            *)
(*                                                                       *)
(*  Goal: Goedel/Henkin completeness for the natural-deduction calculus   *)
(*  `Prov` of Deep.v, w.r.t. Tarski satisfaction `Sat`:                   *)
(*      (forall model e, e |= G -> Sat e phi)  ->  Prov G phi.            *)
(*                                                                       *)
(*  Staged build, green milestones:                                      *)
(*    [1] proof-theory infrastructure   <-- this file, so far            *)
(*    [2] consistency + classical kit                                    *)
(*    [3] enumeration of `form`                                          *)
(*    [4] Lindenbaum / Henkin maximal-consistent extension               *)
(*    [5] quotient term model + truth lemma                              *)
(*    [6] completeness                                                   *)
(*                                                                       *)
(*  Build:  coqc -Q . SetTheory Deep.v                                    *)
(*          coqc -Q . SetTheory Completeness.v                            *)
(* ===================================================================== *)

From SetTheory Require Import Deep.
From Stdlib Require Import List PeanoNat Classical.
Import ListNotations.

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

(* Deduction theorem.  One direction is the P_impI constructor; here is the  *)
(* converse. *)
Lemma Prov_deduction_elim : forall G a b, Prov G (fImp a b) -> Prov (a :: G) b.
Proof.
  intros G a b H. apply (P_impE (a :: G) a b).
  - apply Prov_cons. exact H.
  - apply P_ass. left. reflexivity.
Qed.

(* Modus ponens, explosion, and proof by contradiction as derived rules. *)
Lemma Prov_mp : forall G a b, Prov G (fImp a b) -> Prov G a -> Prov G b.
Proof. intros G a b. apply P_impE. Qed.

Lemma Prov_absurd : forall G a, Prov G a -> Prov G (fImp a fBot) -> Prov G fBot.
Proof. intros G a Ha Hna. exact (P_impE G a fBot Hna Ha). Qed.

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

(* ====================== [2] consistency + classical kit =============== *)

Definition Con (G : list form) : Prop := ~ Prov G fBot.

(* phi is provable iff its negation is refutable *)
Lemma Prov_neg_refute : forall G phi, Prov G phi <-> Prov (fImp phi fBot :: G) fBot.
Proof.
  intros G phi. split.
  - intro H. apply (P_impE (fImp phi fBot :: G) phi fBot).
    + apply P_ass. left. reflexivity.
    + apply Prov_cons. exact H.
  - apply Prov_byContra.
Qed.

(* The Lindenbaum step: a consistent context can be consistently extended by *)
(* phi or by ~phi. *)
Lemma Con_cons_or :
  forall G phi, Con G -> Con (phi :: G) \/ Con (fImp phi fBot :: G).
Proof.
  intros G phi HG. destruct (classic (Con (phi :: G))) as [H | H].
  - left. exact H.
  - right. intro Hbad.
    assert (Hphi : Prov (phi :: G) fBot) by (apply NNPP; exact H).
    apply HG.
    apply (P_impE G (fImp phi fBot) fBot).
    + apply P_impI. exact Hbad.
    + apply P_impI. exact Hphi.
Qed.

(* If neither phi nor ~phi can be consistently added, G was inconsistent. *)
Lemma Con_cons_neg :
  forall G phi, Con G -> ~ Prov (phi :: G) fBot -> Con (phi :: G).
Proof. intros G phi HG H. exact H. Qed.

(* Extending a context by something it already proves keeps consistency. *)
Lemma Con_redundant :
  forall G phi, Con G -> Prov G phi -> Con (phi :: G).
Proof.
  intros G phi HG Hp Hbad. apply HG.
  apply (P_impE G phi fBot).
  - apply P_impI. exact Hbad.
  - exact Hp.
Qed.

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
