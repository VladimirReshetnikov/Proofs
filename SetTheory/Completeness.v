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
From Stdlib Require Import List PeanoNat Classical Lia Setoid.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import Cantor.
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

(* formula size, used for the strong induction in the truth lemma          *)
(* (renaming-instantiation preserves size, so the quantifier cases recurse) *)
Fixpoint fsize (f : form) : nat :=
  match f with
  | fMem _ _ => 1 | fEq _ _ => 1 | fBot => 1
  | fImp a b => S (fsize a + fsize b)
  | fAnd a b => S (fsize a + fsize b)
  | fOr a b  => S (fsize a + fsize b)
  | fAll a   => S (fsize a)
  | fEx a    => S (fsize a)
  end.

Lemma rename_size : forall f r, fsize (rename r f) = fsize f.
Proof.
  induction f; intro r; simpl; try reflexivity.
  - rewrite (IHf1 r), (IHf2 r); reflexivity.
  - rewrite (IHf1 r), (IHf2 r); reflexivity.
  - rewrite (IHf1 r), (IHf2 r); reflexivity.
  - rewrite (IHf (up r)); reflexivity.
  - rewrite (IHf (up r)); reflexivity.
Qed.

(* renamings agreeing pointwise act equally *)
Lemma rename_ext : forall f r r', (forall n, r n = r' n) -> rename r f = rename r' f.
Proof.
  induction f; intros r r' H; simpl; try reflexivity.
  - rewrite (H n), (H n0); reflexivity.
  - rewrite (H n), (H n0); reflexivity.
  - rewrite (IHf1 r r' H), (IHf2 r r' H); reflexivity.
  - rewrite (IHf1 r r' H), (IHf2 r r' H); reflexivity.
  - rewrite (IHf1 r r' H), (IHf2 r r' H); reflexivity.
  - f_equal. apply IHf. intro n; destruct n; simpl; [ reflexivity | rewrite H; reflexivity ].
  - f_equal. apply IHf. intro n; destruct n; simpl; [ reflexivity | rewrite H; reflexivity ].
Qed.

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

(* ================ [3a] maximal-consistent Henkin theory =============== *)

(* discharge "every element of an explicit context is in T" *)
Ltac ctxT :=
  intros ? Hx; cbn in Hx;
  repeat match goal with
         | [ H : _ \/ _ |- _ ] => destruct H as [<- | H]
         | [ H : False  |- _ ] => destruct H
         end; assumption.

Section CanonicalModel.

  Variable T : form -> Prop.
  Hypothesis T_cons   : ~ T fBot.
  Hypothesis T_compl  : forall phi, T phi \/ T (fImp phi fBot).
  Hypothesis T_closed : forall G phi, (forall x, In x G -> T x) -> Prov G phi -> T phi.
  Hypothesis T_henkin_ex  : forall a, T (fEx a) -> exists k, T (rename (inst k) a).
  Hypothesis T_henkin_all : forall a, (forall k, T (rename (inst k) a)) -> T (fAll a).

  Lemma T_prov0 : forall phi, Prov [] phi -> T phi.
  Proof. intros phi H. apply (T_closed [] phi); [ intros x [] | exact H ]. Qed.

  Lemma T_mp : forall a b, T (fImp a b) -> T a -> T b.
  Proof.
    intros a b Hab Ha. apply (T_closed (fImp a b :: a :: nil) b); [ ctxT | ].
    apply (P_impE _ a b); apply P_ass; [ left; reflexivity | right; left; reflexivity ].
  Qed.

  Lemma T_neg_iff : forall phi, T (fImp phi fBot) <-> ~ T phi.
  Proof.
    intro phi. split.
    - intros Hn Hp. exact (T_cons (T_mp phi fBot Hn Hp)).
    - intro Hn. destruct (T_compl phi) as [Hp | Hnp]; [ contradiction | exact Hnp ].
  Qed.

  Lemma T_imp_iff : forall a b, T (fImp a b) <-> (T a -> T b).
  Proof.
    intros a b. split.
    - intros Hab Ha. exact (T_mp a b Hab Ha).
    - intro Himp. destruct (T_compl a) as [Ha | Hna].
      + assert (Hb := Himp Ha).
        apply (T_closed (b :: nil) (fImp a b)); [ ctxT | ].
        apply P_impI. apply P_ass. right. left. reflexivity.
      + apply (T_closed (fImp a fBot :: nil) (fImp a b)); [ ctxT | ].
        apply P_impI. apply P_botE.
        apply (P_impE _ a fBot); apply P_ass; [ right; left; reflexivity | left; reflexivity ].
  Qed.

  Lemma T_and_iff : forall a b, T (fAnd a b) <-> (T a /\ T b).
  Proof.
    intros a b. split.
    - intro H. split.
      + apply (T_closed (fAnd a b :: nil) a); [ ctxT | ].
        apply (P_andE1 _ a b). apply P_ass. left. reflexivity.
      + apply (T_closed (fAnd a b :: nil) b); [ ctxT | ].
        apply (P_andE2 _ a b). apply P_ass. left. reflexivity.
    - intros [Ha Hb]. apply (T_closed (a :: b :: nil) (fAnd a b)); [ ctxT | ].
      apply P_andI; apply P_ass; [ left; reflexivity | right; left; reflexivity ].
  Qed.

  Lemma T_or_iff : forall a b, T (fOr a b) <-> (T a \/ T b).
  Proof.
    intros a b. split.
    - intro H. destruct (T_compl a) as [Ha | Hna]; [ left; exact Ha | ].
      destruct (T_compl b) as [Hb | Hnb]; [ right; exact Hb | ].
      exfalso. apply T_cons.
      apply (T_closed (fOr a b :: fImp a fBot :: fImp b fBot :: nil) fBot); [ ctxT | ].
      apply (P_orE _ a b).
      + apply P_ass. left. reflexivity.
      + apply (P_impE _ a fBot); apply P_ass;
          [ right; right; left; reflexivity | left; reflexivity ].
      + apply (P_impE _ b fBot); apply P_ass;
          [ right; right; right; left; reflexivity | left; reflexivity ].
    - intros [Ha | Hb].
      + apply (T_closed (a :: nil) (fOr a b)); [ ctxT | ].
        apply P_orI1. apply P_ass. left. reflexivity.
      + apply (T_closed (b :: nil) (fOr a b)); [ ctxT | ].
        apply P_orI2. apply P_ass. left. reflexivity.
  Qed.

  Lemma T_all_iff : forall a, T (fAll a) <-> (forall k, T (rename (inst k) a)).
  Proof.
    intro a. split.
    - intros H k. apply (T_closed (fAll a :: nil) (rename (inst k) a)); [ ctxT | ].
      apply (P_allE _ a k). apply P_ass. left. reflexivity.
    - apply T_henkin_all.
  Qed.

  Lemma T_ex_iff : forall a, T (fEx a) <-> (exists k, T (rename (inst k) a)).
  Proof.
    intro a. split.
    - apply T_henkin_ex.
    - intros [k Hk]. apply (T_closed (rename (inst k) a :: nil) (fEx a)); [ ctxT | ].
      apply (P_exI _ a k). apply P_ass. left. reflexivity.
  Qed.

  (* the canonical equivalence on variables *)
  Definition ceq (i j : nat) : Prop := T (fEq i j).

  Lemma ceq_refl : forall i, ceq i i.
  Proof. intro i. apply T_prov0. apply P_eqRefl. Qed.

  Lemma ceq_sym : forall i j, ceq i j -> ceq j i.
  Proof.
    intros i j H. apply (T_closed (fEq i j :: nil) (fEq j i)); [ ctxT | ].
    apply Prov_eq_sym. apply P_ass. left. reflexivity.
  Qed.

  Lemma ceq_trans : forall i j k, ceq i j -> ceq j k -> ceq i k.
  Proof.
    intros i j k H1 H2.
    apply (T_closed (fEq i j :: fEq j k :: nil) (fEq i k)); [ ctxT | ].
    apply (Prov_eq_trans _ i j k); apply P_ass; [ left; reflexivity | right; left; reflexivity ].
  Qed.

  Definition cmem (i j : nat) : Prop := T (fMem i j).

  Lemma cmem_cong :
    forall i i' j j', ceq i i' -> ceq j j' -> cmem i j -> cmem i' j'.
  Proof.
    intros i i' j j' Hi Hj H.
    apply (T_closed (fEq i i' :: fEq j j' :: fMem i j :: nil) (fMem i' j')); [ ctxT | ].
    apply (Prov_mem_cong2 _ j j' i').
    - apply P_ass. right. left. reflexivity.
    - apply (Prov_mem_cong1 _ i i' j).
      + apply P_ass. left. reflexivity.
      + apply P_ass. right. right. left. reflexivity.
  Qed.

  (* ---- [3b] the quotient term model and the truth lemma ---- *)

  (* canonical representative of a ceq-class, via Hilbert epsilon *)
  Definition rep (i : nat) : nat := epsilon (inhabits 0) (fun j => ceq i j).

  Lemma rep_ceq : forall i, ceq i (rep i).
  Proof.
    intro i. apply (epsilon_spec (inhabits 0) (fun j => ceq i j)).
    exists i. apply ceq_refl.
  Qed.

  Lemma rep_respects : forall i j, ceq i j -> rep i = rep j.
  Proof.
    intros i j H. unfold rep. f_equal.
    apply functional_extensionality. intro k. apply propositional_extensionality.
    split; intro Hk.
    - apply (ceq_trans j i k); [ apply ceq_sym; exact H | exact Hk ].
    - apply (ceq_trans i j k); [ exact H | exact Hk ].
  Qed.

  Lemma rep_idem : forall i, rep (rep i) = rep i.
  Proof. intro i. apply rep_respects. apply ceq_sym. apply rep_ceq. Qed.

  Definition D : Type := { n : nat | rep n = n }.
  Definition mkD (i : nat) : D := exist _ (rep i) (rep_idem i).
  Definition memD (x y : D) : Prop := cmem (proj1_sig x) (proj1_sig y).

  Lemma D_eq : forall x y : D, proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros [x px] [y py] H. simpl in H. subst y. f_equal. apply proof_irrelevance.
  Qed.

  Lemma mkD_proj : forall x : D, mkD (proj1_sig x) = x.
  Proof. intro x. destruct x as [v pv]. apply D_eq. simpl. exact pv. Qed.

  (* The truth lemma, by strong induction on formula size: under the canonical *)
  (* variable assignment i |-> [s i], satisfaction matches membership in T.    *)
  Lemma truth :
    forall n a, fsize a <= n ->
      forall s : nat -> nat,
        Sat D memD (fun i => mkD (s i)) a <-> T (rename s a).
  Proof.
    induction n as [| n IH]; intros a Hsz s.
    - destruct a; simpl in Hsz; lia.
    - destruct a as [i j | i j | | a1 a2 | a1 a2 | a1 a2 | a1 | a1 ]; simpl in Hsz.
      + (* fMem *) simpl. unfold memD. simpl. split; intro Hm.
        * apply (cmem_cong (rep (s i)) (s i) (rep (s j)) (s j));
            [ apply ceq_sym; apply rep_ceq | apply ceq_sym; apply rep_ceq | exact Hm ].
        * apply (cmem_cong (s i) (rep (s i)) (s j) (rep (s j)));
            [ apply rep_ceq | apply rep_ceq | exact Hm ].
      + (* fEq *) simpl. split; intro He.
        * assert (Hr : rep (s i) = rep (s j)).
          { change (proj1_sig (mkD (s i)) = proj1_sig (mkD (s j))). rewrite He. reflexivity. }
          apply (ceq_trans (s i) (rep (s j)) (s j)).
          -- rewrite <- Hr. apply rep_ceq.
          -- apply ceq_sym. apply rep_ceq.
        * apply D_eq. simpl. apply rep_respects. exact He.
      + (* fBot *) simpl. split; [ intro H; destruct H | intro H; exfalso; exact (T_cons H) ].
      + (* fImp *) simpl.
        rewrite (IH a1 ltac:(lia) s), (IH a2 ltac:(lia) s).
        symmetry. apply T_imp_iff.
      + (* fAnd *) simpl.
        rewrite (IH a1 ltac:(lia) s), (IH a2 ltac:(lia) s).
        symmetry. apply T_and_iff.
      + (* fOr *) simpl.
        rewrite (IH a1 ltac:(lia) s), (IH a2 ltac:(lia) s).
        symmetry. apply T_or_iff.
      + (* fAll *) simpl. split.
        * intros HSat. apply (proj2 (T_all_iff (rename (up s) a1))). intro k.
          rewrite (rename_inst_up a1 k s).
          apply (proj1 (IH a1 ltac:(lia) (scons_nat k s))).
          assert (Hpt : forall n0, scons D (mkD k) (fun i => mkD (s i)) n0
                                   = (fun i => mkD (scons_nat k s i)) n0).
          { intro n0; destruct n0; reflexivity. }
          apply (proj1 (Sat_ext D memD (mkD 0) a1 _ _ Hpt)). apply (HSat (mkD k)).
        * intros HT d.
          pose proof (proj1 (T_all_iff (rename (up s) a1)) HT (proj1_sig d)) as Hk.
          rewrite (rename_inst_up a1 (proj1_sig d) s) in Hk.
          apply (proj2 (IH a1 ltac:(lia) (scons_nat (proj1_sig d) s))) in Hk.
          assert (Hpt : forall n0, (fun i => mkD (scons_nat (proj1_sig d) s i)) n0
                                   = scons D d (fun i => mkD (s i)) n0).
          { intro n0; destruct n0; simpl; [ apply mkD_proj | reflexivity ]. }
          apply (proj1 (Sat_ext D memD (mkD 0) a1 _ _ Hpt)). exact Hk.
      + (* fEx *) simpl. split.
        * intros [d HSat]. apply (proj2 (T_ex_iff (rename (up s) a1))).
          exists (proj1_sig d). rewrite (rename_inst_up a1 (proj1_sig d) s).
          apply (proj1 (IH a1 ltac:(lia) (scons_nat (proj1_sig d) s))).
          assert (Hpt : forall n0, scons D d (fun i => mkD (s i)) n0
                                   = (fun i => mkD (scons_nat (proj1_sig d) s i)) n0).
          { intro n0; destruct n0; simpl; [ symmetry; apply mkD_proj | reflexivity ]. }
          apply (proj1 (Sat_ext D memD (mkD 0) a1 _ _ Hpt)). exact HSat.
        * intro HT. destruct (proj1 (T_ex_iff (rename (up s) a1)) HT) as [k Hk].
          rewrite (rename_inst_up a1 k s) in Hk.
          apply (proj2 (IH a1 ltac:(lia) (scons_nat k s))) in Hk.
          exists (mkD k).
          assert (Hpt : forall n0, (fun i => mkD (scons_nat k s i)) n0
                                   = scons D (mkD k) (fun i => mkD (s i)) n0).
          { intro n0; destruct n0; reflexivity. }
          apply (proj1 (Sat_ext D memD (mkD 0) a1 _ _ Hpt)). exact Hk.
  Qed.

  (* canonical assignment: satisfaction matches T outright *)
  Corollary truth_id : forall a, Sat D memD (fun i => mkD i) a <-> T a.
  Proof.
    intro a. pose proof (truth (fsize a) a (le_n _) (fun i => i)) as H.
    rewrite rename_id in H. exact H.
  Qed.

  (* MODEL EXISTENCE: every maximal-consistent Henkin theory is satisfiable. *)
  Theorem model_exists :
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      forall a, Sat Dom m v a <-> T a.
  Proof. exists D, memD, (fun i => mkD i). exact truth_id. Qed.

End CanonicalModel.

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
    assert (Heqj : rename r (rename (inst k) a) = rename (inst (r k)) (rename (up r) a)).
    { rewrite !rename_comp. apply rename_ext. intro n; destruct n; reflexivity. }
    rewrite Heqj. apply (P_allE _ (rename (up r) a) (r k)). exact (IH r).
  - (* P_exI *)
    apply (P_exI _ (rename (up r) a) (r k)).
    assert (Heqj : rename r (rename (inst k) a) = rename (inst (r k)) (rename (up r) a)).
    { rewrite !rename_comp. apply rename_ext. intro n; destruct n; reflexivity. }
    rewrite <- Heqj. exact (IH r).
  - (* P_exE *)
    apply (P_exE _ (rename (up r) a) (rename r c)).
    + exact (IHex r).
    + assert (Hc : rename S (rename r c) = rename (up r) (rename S c)).
      { rewrite !rename_comp. apply rename_ext. intro n; reflexivity. }
      rewrite Hc. rewrite <- (map_rename_up_S r G). exact (IHbody (up r)).
  - apply P_eqRefl.
  - (* P_eqElim *)
    assert (Heqj : rename r (rename (inst j) a) = rename (inst (r j)) (rename (up r) a)).
    { rewrite !rename_comp. apply rename_ext. intro n; destruct n; reflexivity. }
    rewrite Heqj. apply (P_eqElim _ (r i) (r j) (rename (up r) a)).
    + exact (IHeq r).
    + assert (Heqi : rename r (rename (inst i) a) = rename (inst (r i)) (rename (up r) a)).
      { rewrite !rename_comp. apply rename_ext. intro n; destruct n; reflexivity. }
      rewrite <- Heqi. exact (IHa r).
Qed.

(* ---- [4b] free variables, freshness, and Henkin witness lemmas ---- *)

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

(* existential Henkin witness *)
Lemma henkin_ex :
  forall G a, Con (fEx a :: G) ->
    Con (rename (inst (freshFor (fEx a :: G))) a :: fEx a :: G).
Proof.
  intros G a Hcon. unfold Con. set (w := freshFor (fEx a :: G)). intro Hbad.
  assert (Hwa : ~ Free (S w) a).
  { exact (freshFor_not_free (fEx a :: G) (fEx a) (or_introl eq_refl)). }
  assert (HwG : forall g, In g G -> ~ Free w g).
  { intros g Hg. apply (freshFor_not_free (fEx a :: G) g). right. exact Hg. }
  apply Hcon. apply (P_exE (fEx a :: G) a fBot).
  - apply P_ass. left. reflexivity.
  - pose proof (Prov_rename _ _ Hbad (rho_w w)) as Hr. simpl in Hr.
    rewrite (rho_inst a w Hwa), (rho_under a w Hwa), (map_rho_S G w HwG) in Hr.
    simpl. exact Hr.
Qed.

(* universal Henkin witness (for the negation of a universal) *)
Lemma henkin_all :
  forall G a, Con (fImp (fAll a) fBot :: G) ->
    Con (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: G))) a) fBot
         :: fImp (fAll a) fBot :: G).
Proof.
  intros G a Hcon. unfold Con. set (w := freshFor (fImp (fAll a) fBot :: G)). intro Hbad.
  assert (Hwa : ~ Free (S w) a).
  { intro Hf. apply (freshFor_not_free (fImp (fAll a) fBot :: G) (fImp (fAll a) fBot)
                       (or_introl eq_refl)). simpl. left. exact Hf. }
  assert (HwG : forall g, In g (fImp (fAll a) fBot :: G) -> ~ Free w g).
  { intros g Hg. apply (freshFor_not_free (fImp (fAll a) fBot :: G) g). exact Hg. }
  apply Hcon.
  apply Prov_byContra in Hbad.
  pose proof (generalize_fresh (fImp (fAll a) fBot :: G) a w HwG Hwa Hbad) as Hgen.
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

(* ---- [4e] the Lindenbaum chain and its first three theory properties ---- *)

Definition step (G : list form) (phi : form) : list form :=
  match excluded_middle_informative (Con (phi :: G)) with
  | left _ =>
      match phi with
      | fEx a => rename (inst (freshFor (fEx a :: G))) a :: fEx a :: G
      | _ => phi :: G
      end
  | right _ =>
      match phi with
      | fAll a => fImp (rename (inst (freshFor (fImp (fAll a) fBot :: G))) a) fBot
                  :: fImp (fAll a) fBot :: G
      | _ => fImp phi fBot :: G
      end
  end.

Lemma step_con : forall G phi, Con G -> Con (step G phi).
Proof.
  intros G phi HG. unfold step.
  destruct (excluded_middle_informative (Con (phi :: G))) as [Hc | Hnc].
  - destruct phi; try exact Hc; apply henkin_ex; exact Hc.
  - destruct (Con_cons_or G phi HG) as [Hbad | Hcn]; [ contradiction | ].
    destruct phi; try exact Hcn; apply henkin_all; exact Hcn.
Qed.

Lemma step_incl : forall G phi x, In x G -> In x (step G phi).
Proof.
  intros G phi x Hx. unfold step.
  destruct (excluded_middle_informative (Con (phi :: G)));
    destruct phi; simpl; tauto.
Qed.

Lemma step_decides :
  forall G phi, In phi (step G phi) \/ In (fImp phi fBot) (step G phi).
Proof.
  intros G phi. unfold step.
  destruct (excluded_middle_informative (Con (phi :: G))).
  - left. destruct phi; simpl; tauto.
  - right. destruct phi; simpl; tauto.
Qed.

Fixpoint chain (G0 : list form) (n : nat) : list form :=
  match n with O => G0 | S m => step (chain G0 m) (Enum m) end.

Lemma chain_incl : forall G0 m x, In x (chain G0 m) -> In x (chain G0 (S m)).
Proof. intros G0 m x Hx. cbn [chain]. apply step_incl. exact Hx. Qed.

Lemma chain_mono :
  forall G0 n m, m <= n -> forall x, In x (chain G0 m) -> In x (chain G0 n).
Proof.
  intros G0 n. induction n as [| n IHn]; intros m Hle x Hx.
  - assert (m = 0) by lia. subst m. exact Hx.
  - apply Nat.le_succ_r in Hle. destruct Hle as [Hle | Heq].
    + apply chain_incl. exact (IHn m Hle x Hx).
    + subst m. exact Hx.
Qed.

Lemma chain_con : forall G0, Con G0 -> forall n, Con (chain G0 n).
Proof.
  intros G0 HG0. induction n as [| n IHn].
  - exact HG0.
  - cbn [chain]. apply step_con. exact IHn.
Qed.

Definition TL (G0 : list form) (phi : form) : Prop := exists n, Prov (chain G0 n) phi.

Lemma TL_cons : forall G0, Con G0 -> ~ TL G0 fBot.
Proof. intros G0 HG0 [n Hn]. exact (chain_con G0 HG0 n Hn). Qed.

Lemma TL_compl : forall G0 phi, TL G0 phi \/ TL G0 (fImp phi fBot).
Proof.
  intros G0 phi. destruct (Enum_surj phi) as [n Hn]. subst phi.
  destruct (step_decides (chain G0 n) (Enum n)) as [Hin | Hin].
  - left. exists (S n). cbn [chain]. apply P_ass. exact Hin.
  - right. exists (S n). cbn [chain]. apply P_ass. exact Hin.
Qed.

Lemma TL_bound :
  forall G0 G, (forall x, In x G -> TL G0 x) ->
    exists N, forall x, In x G -> Prov (chain G0 N) x.
Proof.
  intros G0 G. induction G as [| g G' IHG]; intro Hall.
  - exists 0. intros x [].
  - destruct (Hall g (or_introl eq_refl)) as [ng Hng].
    destruct IHG as [N' HN']; [ intros x Hx; apply Hall; right; exact Hx | ].
    exists (Nat.max ng N'). intros x [Heq | Hx].
    + subst x. apply (Prov_weaken (chain G0 ng) g Hng).
      intros y Hy. apply (chain_mono G0 (Nat.max ng N') ng); [ lia | exact Hy ].
    + apply (Prov_weaken (chain G0 N') x (HN' x Hx)).
      intros y Hy. apply (chain_mono G0 (Nat.max ng N') N'); [ lia | exact Hy ].
Qed.

Lemma TL_closed :
  forall G0 G phi, (forall x, In x G -> TL G0 x) -> Prov G phi -> TL G0 phi.
Proof.
  intros G0 G phi Hall Hp. destruct (TL_bound G0 G Hall) as [N HN].
  exists N. exact (Prov_cut G phi Hp (chain G0 N) HN).
Qed.

(* ---- [4f] the two Henkin properties ---- *)

Lemma step_pos_in : forall G phi, Con (phi :: G) -> In phi (step G phi).
Proof.
  intros G phi Hc. unfold step.
  destruct (excluded_middle_informative (Con (phi :: G))) as [H | H];
    [ destruct phi; simpl; tauto | contradiction ].
Qed.

Lemma step_neg_in : forall G phi, ~ Con (phi :: G) -> In (fImp phi fBot) (step G phi).
Proof.
  intros G phi Hnc. unfold step.
  destruct (excluded_middle_informative (Con (phi :: G))) as [H | H];
    [ contradiction | destruct phi; simpl; tauto ].
Qed.

Lemma step_ex_pos :
  forall G a, Con (fEx a :: G) ->
    In (rename (inst (freshFor (fEx a :: G))) a) (step G (fEx a)).
Proof.
  intros G a Hc. unfold step.
  destruct (excluded_middle_informative (Con (fEx a :: G))) as [H | H];
    [ simpl; left; reflexivity | contradiction ].
Qed.

Lemma step_all_neg :
  forall G a, ~ Con (fAll a :: G) ->
    In (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: G))) a) fBot) (step G (fAll a)).
Proof.
  intros G a Hnc. unfold step.
  destruct (excluded_middle_informative (Con (fAll a :: G))) as [H | H];
    [ contradiction | simpl; left; reflexivity ].
Qed.

Lemma TL_henkin_ex :
  forall G0, Con G0 -> forall a, TL G0 (fEx a) -> exists k, TL G0 (rename (inst k) a).
Proof.
  intros G0 HG0 a [N HN]. destruct (Enum_surj (fEx a)) as [m Hm].
  destruct (classic (Con (fEx a :: chain G0 m))) as [Hpos | Hnc].
  - exists (freshFor (fEx a :: chain G0 m)). exists (S m). cbn [chain]. rewrite Hm.
    apply P_ass. apply step_ex_pos. exact Hpos.
  - exfalso.
    assert (Hneg : Prov (chain G0 (S m)) (fImp (fEx a) fBot)).
    { cbn [chain]. rewrite Hm. apply P_ass. apply step_neg_in. exact Hnc. }
    apply (chain_con G0 HG0 (Nat.max N (S m))).
    apply (P_impE (chain G0 (Nat.max N (S m))) (fEx a) fBot).
    + apply (Prov_weaken (chain G0 (S m)) (fImp (fEx a) fBot) Hneg).
      intros y Hy. apply (chain_mono G0 (Nat.max N (S m)) (S m)); [ lia | exact Hy ].
    + apply (Prov_weaken (chain G0 N) (fEx a) HN).
      intros y Hy. apply (chain_mono G0 (Nat.max N (S m)) N); [ lia | exact Hy ].
Qed.

Lemma TL_henkin_all :
  forall G0, Con G0 -> forall a,
    (forall k, TL G0 (rename (inst k) a)) -> TL G0 (fAll a).
Proof.
  intros G0 HG0 a Hall.
  destruct (TL_compl G0 (fAll a)) as [Hpos | Hneg]; [ exact Hpos | ].
  exfalso. destruct (Enum_surj (fAll a)) as [m Hm].
  destruct (classic (Con (fAll a :: chain G0 m))) as [Hc | Hnc].
  - assert (Hposfa : TL G0 (fAll a)).
    { exists (S m). cbn [chain]. rewrite Hm. apply P_ass. apply step_pos_in. exact Hc. }
    apply (TL_cons G0 HG0).
    destruct Hposfa as [n1 H1]. destruct Hneg as [n2 H2].
    exists (Nat.max n1 n2).
    apply (P_impE (chain G0 (Nat.max n1 n2)) (fAll a) fBot).
    + apply (Prov_weaken (chain G0 n2) (fImp (fAll a) fBot) H2).
      intros y Hy. apply (chain_mono G0 (Nat.max n1 n2) n2); [ lia | exact Hy ].
    + apply (Prov_weaken (chain G0 n1) (fAll a) H1).
      intros y Hy. apply (chain_mono G0 (Nat.max n1 n2) n1); [ lia | exact Hy ].
  - assert (Hnegw : Prov (chain G0 (S m))
                      (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: chain G0 m))) a) fBot)).
    { cbn [chain]. rewrite Hm. apply P_ass. apply step_all_neg. exact Hnc. }
    set (w := freshFor (fImp (fAll a) fBot :: chain G0 m)) in *.
    destruct (Hall w) as [n1 H1].
    apply (TL_cons G0 HG0).
    exists (Nat.max n1 (S m)).
    apply (P_impE (chain G0 (Nat.max n1 (S m))) (rename (inst w) a) fBot).
    + apply (Prov_weaken (chain G0 (S m)) (fImp (rename (inst w) a) fBot) Hnegw).
      intros y Hy. apply (chain_mono G0 (Nat.max n1 (S m)) (S m)); [ lia | exact Hy ].
    + apply (Prov_weaken (chain G0 n1) (rename (inst w) a) H1).
      intros y Hy. apply (chain_mono G0 (Nat.max n1 (S m)) n1); [ lia | exact Hy ].
Qed.

(* ---- [4g] model existence for a consistent set, and completeness ---- *)

Theorem model_of_con :
  forall G0, Con G0 ->
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      forall g, In g G0 -> Sat Dom m v g.
Proof.
  intros G0 HG0.
  destruct (model_exists (TL G0)
              (TL_cons G0 HG0) (TL_compl G0) (TL_closed G0)
              (TL_henkin_ex G0 HG0) (TL_henkin_all G0 HG0)) as [Dom [m [v Hsat]]].
  exists Dom, m, v. intros g Hg. apply (proj2 (Hsat g)).
  exists 0. cbn [chain]. apply P_ass. exact Hg.
Qed.

(* COMPLETENESS: validity in all models implies provability. *)
Theorem completeness :
  forall G phi,
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi) ->
    Prov G phi.
Proof.
  intros G phi Hval. apply NNPP. intro Hnp.
  assert (Hcon : Con (fImp phi fBot :: G)).
  { intro Hbad. apply Hnp. apply Prov_byContra. exact Hbad. }
  destruct (model_of_con (fImp phi fBot :: G) Hcon) as [Dom [m [v Hsat]]].
  assert (Hphi : Sat Dom m v phi).
  { apply Hval. intros g Hg. apply Hsat. right. exact Hg. }
  assert (Hnphi : Sat Dom m v (fImp phi fBot)) by (apply Hsat; left; reflexivity).
  simpl in Hnphi. exact (Hnphi Hphi).
Qed.

(* SOUNDNESS + COMPLETENESS: provability coincides with validity. *)
Corollary prov_iff_valid :
  forall G phi,
    Prov G phi <->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi).
Proof.
  intros G phi. split.
  - intros H Dom m v Hg. exact (soundness Dom m (v 0) G phi H v Hg).
  - apply completeness.
Qed.
