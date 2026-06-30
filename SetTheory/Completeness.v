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
