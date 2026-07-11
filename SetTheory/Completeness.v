(* ===================================================================== *)
(*  Completeness.v                                                        *)
(*                                                                       *)
(*  GENERIC Goedel/Henkin completeness for the calculus of Calculus.v     *)
(*  w.r.t. the Tarski semantics of Fol.v -- for ANY theory over this      *)
(*  language, with no set-theoretic content whatsoever:                   *)
(*                                                                       *)
(*   - the quotient term model of an abstract maximal-consistent Henkin   *)
(*     theory, and the TRUTH LEMMA (`model_exists`);                      *)
(*   - the B-relative Lindenbaum/Henkin chain over a sentence theory B    *)
(*     plus a finite context: `BProv`, `model_of_BCon`;                   *)
(*   - COMPLETENESS `completeness` and `prov_iff_valid`                   *)
(*     (Prov G phi <-> G |= phi) -- obtained from `model_of_BCon` at the  *)
(*     EMPTY base theory B = emptyset (`model_of_con` is that instance);  *)
(*   - infinite-theory completeness for sentence theories                 *)
(*     (`completeness_inf`), one-way semantic proof transfer              *)
(*     (`theory_transfer`), and DEDUCTIVE EQUIVALENCE `theory_equiv`:     *)
(*     two sentence theories with the same models prove the same          *)
(*     sentences -- the abstract engine for proving any two               *)
(*     axiomatizations deductively equivalent.                            *)
(*                                                                       *)
(*  - Created (UTC): 2026-07-01T21:20:00Z                                 *)
(*  - Repository HEAD: c73d98802cf8385db7100480fdc5019105812718           *)
(* ===================================================================== *)

From SetTheory Require Import Fol Calculus.
From Stdlib Require Import List PeanoNat Classical Lia Setoid.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
Import ListNotations.

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

  Local Lemma canonical_scons :
    forall (d : D) k (s : nat -> nat), d = mkD k -> forall n,
      scons D d (fun i => mkD (s i)) n =
      (fun i => mkD (scons_nat k s i)) n.
  Proof. intros d k s Hd [| n]; cbn; [ exact Hd | reflexivity ]. Qed.

  (* The truth lemma, by structural induction on the formula with the        *)
  (* substitution generalized (the quantifier cases recurse on the body at a *)
  (* consed substitution, via rename_inst_up): under the canonical variable  *)
  (* assignment i |-> [s i], satisfaction matches membership in T.           *)
  Lemma truth :
    forall a (s : nat -> nat),
      Sat D memD (fun i => mkD (s i)) a <-> T (rename s a).
  Proof.
    intro a.
    induction a as [i j | i j | | a1 IH1 a2 IH2 | a1 IH1 a2 IH2
                   | a1 IH1 a2 IH2 | a1 IH | a1 IH ]; intro s.
    - (* fMem *) simpl. unfold memD. simpl. split; intro Hm.
      + apply (cmem_cong (rep (s i)) (s i) (rep (s j)) (s j));
          [ apply ceq_sym; apply rep_ceq | apply ceq_sym; apply rep_ceq | exact Hm ].
      + apply (cmem_cong (s i) (rep (s i)) (s j) (rep (s j)));
          [ apply rep_ceq | apply rep_ceq | exact Hm ].
    - (* fEq *) simpl. split; intro He.
      + assert (Hr : rep (s i) = rep (s j)).
        { change (proj1_sig (mkD (s i)) = proj1_sig (mkD (s j))). rewrite He. reflexivity. }
        apply (ceq_trans (s i) (rep (s j)) (s j)).
        * rewrite <- Hr. apply rep_ceq.
        * apply ceq_sym. apply rep_ceq.
      + apply D_eq. simpl. apply rep_respects. exact He.
    - (* fBot *) simpl. split; [ intro H; destruct H | intro H; exfalso; exact (T_cons H) ].
    - (* fImp *) simpl.
      rewrite (IH1 s), (IH2 s).
      symmetry. apply T_imp_iff.
    - (* fAnd *) simpl.
      rewrite (IH1 s), (IH2 s).
      symmetry. apply T_and_iff.
    - (* fOr *) simpl.
      rewrite (IH1 s), (IH2 s).
      symmetry. apply T_or_iff.
    - (* fAll *) simpl. split.
      + intros HSat. apply (proj2 (T_all_iff (rename (up s) a1))). intro k.
        rewrite (rename_inst_up a1 k s).
        apply (proj1 (IH (scons_nat k s))).
        exact (proj1 (Sat_ext D memD a1 _ _ (canonical_scons (mkD k) k s eq_refl))
                 (HSat (mkD k))).
      + intros HT d.
        pose proof (proj1 (T_all_iff (rename (up s) a1)) HT (proj1_sig d)) as Hk.
        rewrite (rename_inst_up a1 (proj1_sig d) s) in Hk.
        apply (proj2 (IH (scons_nat (proj1_sig d) s))) in Hk.
        exact (proj2 (Sat_ext D memD a1 _ _
                 (canonical_scons d (proj1_sig d) s (eq_sym (mkD_proj d)))) Hk).
    - (* fEx *) simpl. split.
      + intros [d HSat]. apply (proj2 (T_ex_iff (rename (up s) a1))).
        exists (proj1_sig d). rewrite (rename_inst_up a1 (proj1_sig d) s).
        apply (proj1 (IH (scons_nat (proj1_sig d) s))).
        exact (proj1 (Sat_ext D memD a1 _ _
                 (canonical_scons d (proj1_sig d) s (eq_sym (mkD_proj d)))) HSat).
      + intro HT. destruct (proj1 (T_ex_iff (rename (up s) a1)) HT) as [k Hk].
        rewrite (rename_inst_up a1 k s) in Hk.
        apply (proj2 (IH (scons_nat k s))) in Hk.
        exists (mkD k).
        exact (proj2 (Sat_ext D memD a1 _ _ (canonical_scons (mkD k) k s eq_refl)) Hk).
  Qed.

  (* canonical assignment: satisfaction matches T outright *)
  Corollary truth_id : forall a, Sat D memD (fun i => mkD i) a <-> T a.
  Proof.
    intro a. pose proof (truth a (fun i => i)) as H.
    rewrite rename_id in H. exact H.
  Qed.

  (* MODEL EXISTENCE: every maximal-consistent Henkin theory is satisfiable. *)
  Theorem model_exists :
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      forall a, Sat Dom m v a <-> T a.
  Proof. exists D, memD, (fun i => mkD i). exact truth_id. Qed.

End CanonicalModel.
(* ===================================================================== *)
(*  The Lindenbaum/Henkin chain, relative to a SENTENCE base theory B.    *)
(*  A sentence has no free variables, so any variable is fresh w.r.t. the  *)
(*  (possibly infinite) base theory B -- which is what lets the Henkin     *)
(*  witnesses work over an infinite theory.  Ordinary finite-context       *)
(*  completeness is the B = emptyset instance (BProv_empty / model_of_con  *)
(*  below).                                                                *)
(* ===================================================================== *)

(* robust membership solver for list app/cons rearrangements *)
Ltac mem := rewrite ?in_app_iff in *; cbn [In] in *;
            rewrite ?in_app_iff in *; cbn [In] in *; tauto.
(* "B together with the finite list G proves phi" *)
Definition BProv (B : form -> Prop) (G : list form) (phi : form) : Prop :=
  exists Gb, (forall x, In x Gb -> B x) /\ Prov (Gb ++ G) phi.
Definition BCon (B : form -> Prop) (G : list form) : Prop := ~ BProv B G fBot.

(* A finite-context assumption is available in relative provability. *)
Lemma BProv_ass : forall B G phi,
  In phi G -> BProv B G phi.
Proof.
  intros B G phi hphi.
  exists nil. split; [ intros x hx; contradiction | ].
  simpl. apply P_ass. exact hphi.
Qed.

Lemma BProv_mono :
  forall B G G' phi, (forall x, In x G -> In x G') -> BProv B G phi -> BProv B G' phi.
Proof.
  intros B G G' phi Hsub [Gb [HGb Hp]]. exists Gb. split; [ exact HGb | ].
  apply (Prov_weaken (Gb ++ G) phi Hp). intros x Hx.
  apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx | Hx];
    [ left; exact Hx | right; apply Hsub; exact Hx ].
Qed.

(* A base-theory axiom and a bare finite-context derivation are the two
   primitive ways to enter relative provability. *)
Lemma BProv_ax : forall (B : form -> Prop) G phi,
  B phi -> BProv B G phi.
Proof.
  intros B G phi hphi.
  exists (phi :: nil). split.
  - intros x [hx | []]. subst x. exact hphi.
  - apply P_ass. apply in_app_iff. left. left. reflexivity.
Qed.

Lemma BProv_of_Prov : forall (B : form -> Prop) G phi,
  Prov G phi -> BProv B G phi.
Proof.
  intros B G phi hp.
  exists nil. split; [ intros x hx; contradiction | exact hp ].
Qed.

(* Finitely many relative proofs can share one finite list of background
   axioms. *)
Lemma BProv_bound_list : forall B D L,
  (forall x, In x L -> BProv B D x) ->
  exists Lb,
    (forall x, In x Lb -> B x) /\
    (forall x, In x L -> Prov (Lb ++ D) x).
Proof.
  intros B D L. induction L as [|a L IH]; intro hL.
  - exists nil. split; intros x hx; contradiction.
  - destruct (hL a (or_introl eq_refl)) as [La [hLa hpa]].
    destruct (IH (fun x hx => hL x (or_intror hx))) as [Lb [hLb hpL]].
    exists (La ++ Lb). split.
    + intros x hx. apply in_app_iff in hx. destruct hx as [hx | hx].
      * exact (hLa x hx).
      * exact (hLb x hx).
    + intros x hx. destruct hx as [hx | hx].
      * subst x. apply (Prov_weaken (La ++ D) a hpa). intros y hy; mem.
      * apply (Prov_weaken (Lb ++ D) x (hpL x hx)). intros y hy; mem.
Qed.

(* Lift any finite natural-deduction derivation into relative provability by
   supplying relative proofs of all its assumptions.  This hides the finite
   list of used background axioms from every derived proof rule. *)
Lemma BProv_derive : forall B G Delta phi,
  Prov Delta phi ->
  (forall d, In d Delta -> BProv B G d) ->
  BProv B G phi.
Proof.
  intros B G Delta phi hp hDelta.
  destruct (BProv_bound_list B G Delta hDelta) as [Lb [hLb hpDelta]].
  exists Lb. split; [ exact hLb | ].
  exact (Prov_cut Delta phi hp (Lb ++ G) hpDelta).
Qed.

(* Lift unary and binary proof rules uniformly over relative provability. *)
Lemma BProv_rule1 : forall (B : form -> Prop) G a b,
  (forall Delta, Prov Delta a -> Prov Delta b) ->
  BProv B G a -> BProv B G b.
Proof.
  intros B G a b Hrule [L [HL Hp]].
  exists L. split; [ exact HL | exact (Hrule (L ++ G) Hp) ].
Qed.

Lemma BProv_rule2 : forall (B : form -> Prop) G a b c,
  (forall Delta, Prov Delta a -> Prov Delta b -> Prov Delta c) ->
  BProv B G a -> BProv B G b -> BProv B G c.
Proof.
  intros B G a b c Hrule Ha Hb.
  apply (BProv_derive B G (a :: b :: nil) c).
  - apply Hrule; apply P_ass; simpl; tauto.
  - intros d [<- | [<- | []]]; assumption.
Qed.

(* Transport a relative proof once every used source axiom and every finite
   context assumption has been proved in the target. *)
Lemma BProv_lift : forall (B C : form -> Prop) G D phi,
  BProv B G phi ->
  (forall b, B b -> BProv C D b) ->
  (forall g, In g G -> BProv C D g) ->
  BProv C D phi.
Proof.
  intros B C G D phi [Lb [hLb hp]] hB hG.
  assert (hctx : forall x, In x (Lb ++ G) -> BProv C D x).
  {
    intros x hx. apply in_app_iff in hx. destruct hx as [hx | hx].
    - exact (hB x (hLb x hx)).
    - exact (hG x hx).
  }
  destruct (BProv_bound_list C D (Lb ++ G) hctx) as [Lc [hLc hpctx]].
  exists Lc. split; [ exact hLc | ].
  exact (Prov_cut (Lb ++ G) phi hp (Lc ++ D) hpctx).
Qed.

Lemma BProv_cut : forall (B : form -> Prop) G D phi,
  BProv B G phi ->
  (forall g, In g G -> BProv B D g) ->
  BProv B D phi.
Proof.
  intros B G D phi hp hG.
  apply (BProv_lift B B G D phi hp).
  - intros b hb. apply BProv_ax. exact hb.
  - exact hG.
Qed.

Lemma BProv_theory_mono : forall (B C : form -> Prop) G phi,
  (forall b, B b -> C b) -> BProv B G phi -> BProv C G phi.
Proof.
  intros B C G phi hBC [L [hL hp]].
  exists L. split; [ intros x hx; exact (hBC x (hL x hx)) | exact hp ].
Qed.

(* Soundness for relative provability from a base theory and finite context. *)
Lemma soundness_BProv :
  forall (Dom : Type) (m : Dom -> Dom -> Prop) B G phi,
    BProv B G phi ->
    forall v,
      (forall b, B b -> Sat Dom m v b) ->
      (forall g, In g G -> Sat Dom m v g) ->
      Sat Dom m v phi.
Proof.
  intros Dom m B G phi [L [hL hp]] v hB hG.
  apply (soundness Dom m (L ++ G) phi hp v).
  intros x hx. apply in_app_iff in hx. destruct hx as [hx | hx].
  - exact (hB x (hL x hx)).
  - exact (hG x hx).
Qed.

Lemma BCon_cons_or :
  forall B L phi, BCon B L -> BCon B (phi :: L) \/ BCon B (fImp phi fBot :: L).
Proof.
  intros B L phi HL. destruct (classic (BCon B (phi :: L))) as [H | H];
    [ left; exact H | right ].
  apply NNPP in H. destruct H as [Gb1 [HGb1 Hbad1]].
  intros [Gb2 [HGb2 Hbad2]]. apply HL. exists (Gb1 ++ Gb2). split.
  - intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx | Hx];
      [ apply HGb1; exact Hx | apply HGb2; exact Hx ].
  - apply (P_impE ((Gb1 ++ Gb2) ++ L) (fImp phi fBot) fBot).
    + apply P_impI. apply (Prov_weaken (fImp phi fBot :: (Gb2 ++ L))).
      * apply (Prov_exch (Gb2 ++ fImp phi fBot :: L)); [ intro x; mem | exact Hbad2 ].
      * intros x Hx; mem.
    + apply P_impI. apply (Prov_weaken (phi :: (Gb1 ++ L))).
      * apply (Prov_exch (Gb1 ++ phi :: L)); [ intro x; mem | exact Hbad1 ].
      * intros x Hx; mem.
Qed.

Lemma BCon_henkin_ex :
  forall B L a, Sentences B -> BCon B (fEx a :: L) ->
    BCon B (rename (inst (freshFor (fEx a :: L))) a :: fEx a :: L).
Proof.
  intros B L a HB Hcon [Gb [HGb Hbad]]. apply Hcon. exists Gb. split; [ exact HGb | ].
  set (w := freshFor (fEx a :: L)) in *.
  apply (Prov_exch (fEx a :: (Gb ++ L))); [ intro x; mem | ].
  apply (henkin_ex_core (Gb ++ L) a w).
  - exact (freshFor_not_free (fEx a :: L) (fEx a) (or_introl eq_refl)).
  - intros g Hg. apply in_app_iff in Hg. destruct Hg as [Hg | Hg].
    + exact (HB g (HGb g Hg) w).
    + apply (freshFor_not_free (fEx a :: L) g). right. exact Hg.
  - apply (Prov_exch (Gb ++ rename (inst w) a :: fEx a :: L)); [ intro x; mem | exact Hbad ].
Qed.

Lemma BCon_henkin_all :
  forall B L a, Sentences B -> BCon B (fImp (fAll a) fBot :: L) ->
    BCon B (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
            :: fImp (fAll a) fBot :: L).
Proof.
  intros B L a HB Hcon [Gb [HGb Hbad]]. apply Hcon. exists Gb. split; [ exact HGb | ].
  set (w := freshFor (fImp (fAll a) fBot :: L)) in *.
  apply (Prov_exch (fImp (fAll a) fBot :: (Gb ++ L))); [ intro x; mem | ].
  apply (henkin_all_core (Gb ++ L) a w).
  - intro Hf. apply (freshFor_not_free (fImp (fAll a) fBot :: L) (fImp (fAll a) fBot)
                      (or_introl eq_refl)). simpl. left. exact Hf.
  - intros g Hg. apply in_app_iff in Hg. destruct Hg as [Hg | Hg].
    + exact (HB g (HGb g Hg) w).
    + apply (freshFor_not_free (fImp (fAll a) fBot :: L) g). right. exact Hg.
  - apply (Prov_exch (Gb ++ fImp (rename (inst w) a) fBot :: fImp (fAll a) fBot :: L));
      [ intro x; mem | exact Hbad ].
Qed.

(* ---- the B-relative Lindenbaum chain ---- *)

Definition stepB (B : form -> Prop) (L : list form) (phi : form) : list form :=
  match excluded_middle_informative (BCon B (phi :: L)) with
  | left _ =>
      match phi with
      | fEx a => rename (inst (freshFor (fEx a :: L))) a :: fEx a :: L
      | _ => phi :: L
      end
  | right _ =>
      match phi with
      | fAll a => fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot
                  :: fImp (fAll a) fBot :: L
      | _ => fImp phi fBot :: L
      end
  end.

Lemma stepB_con : forall B L phi, Sentences B -> BCon B L -> BCon B (stepB B L phi).
Proof.
  intros B L phi HB HL. unfold stepB.
  destruct (excluded_middle_informative (BCon B (phi :: L))) as [Hc | Hnc].
  - destruct phi; try exact Hc; apply BCon_henkin_ex; [ exact HB | exact Hc ].
  - destruct (BCon_cons_or B L phi HL) as [Hbad | Hcn]; [ contradiction | ].
    destruct phi; try exact Hcn; apply BCon_henkin_all; [ exact HB | exact Hcn ].
Qed.

Lemma stepB_incl : forall B L phi x, In x L -> In x (stepB B L phi).
Proof.
  intros B L phi x Hx. unfold stepB.
  destruct (excluded_middle_informative (BCon B (phi :: L)));
    destruct phi; cbn [In]; tauto.
Qed.

Lemma stepB_decides :
  forall B L phi, In phi (stepB B L phi) \/ In (fImp phi fBot) (stepB B L phi).
Proof.
  intros B L phi. unfold stepB.
  destruct (excluded_middle_informative (BCon B (phi :: L)));
    [ left | right ]; destruct phi; cbn [In]; tauto.
Qed.

Fixpoint chainB (B : form -> Prop) (L0 : list form) (n : nat) : list form :=
  match n with O => L0 | S m => stepB B (chainB B L0 m) (Enum m) end.

Lemma chainB_incl : forall B L0 m x, In x (chainB B L0 m) -> In x (chainB B L0 (S m)).
Proof. intros B L0 m x Hx. cbn [chainB]. apply stepB_incl. exact Hx. Qed.

Lemma chainB_mono :
  forall B L0 n m, m <= n -> forall x, In x (chainB B L0 m) -> In x (chainB B L0 n).
Proof.
  intros B L0 n. induction n as [| n IHn]; intros m Hle x Hx.
  - assert (m = 0) by lia. subst m. exact Hx.
  - apply Nat.le_succ_r in Hle. destruct Hle as [Hle | Heq].
    + apply chainB_incl. exact (IHn m Hle x Hx).
    + subst m. exact Hx.
Qed.

Lemma chainB_con :
  forall B L0, Sentences B -> BCon B L0 -> forall n, BCon B (chainB B L0 n).
Proof.
  intros B L0 HB H0. induction n as [| n IHn].
  - exact H0.
  - cbn [chainB]. apply stepB_con; [ exact HB | exact IHn ].
Qed.

(* ---- the maximal-consistent Henkin theory over (B, L0), and completeness ---- *)

Definition Tinf (B : form -> Prop) (L0 : list form) (phi : form) : Prop :=
  exists n, BProv B (chainB B L0 n) phi.

Lemma BProv_weaken_chain :
  forall B L0 n n' phi, n <= n' ->
    BProv B (chainB B L0 n) phi -> BProv B (chainB B L0 n') phi.
Proof.
  intros B L0 n n' phi Hle H. apply (BProv_mono B (chainB B L0 n)); [ | exact H ].
  intros x Hx. apply (chainB_mono B L0 n' n Hle x Hx).
Qed.

Lemma BProv_mp : forall B L a b, BProv B L (fImp a b) -> BProv B L a -> BProv B L b.
Proof. intros B L a b hImp ha; exact (BProv_rule2 B L (fImp a b) a b (fun D => P_impE D a b) hImp ha). Qed.

Lemma BProv_eqElim : forall B G i j a,
  BProv B G (fEq i j) ->
  BProv B G (rename (inst i) a) ->
  BProv B G (rename (inst j) a).
Proof. intros B G i j a heq ha; exact (BProv_rule2 B G (fEq i j) (rename (inst i) a) (rename (inst j) a) (fun D => P_eqElim D i j a) heq ha). Qed.

Lemma BProv_eqSym : forall B G i j,
  BProv B G (fEq i j) -> BProv B G (fEq j i).
Proof. intros B G i j heq; exact (BProv_rule1 B G (fEq i j) (fEq j i) (fun D => Prov_eq_sym D i j) heq). Qed.

Lemma BProv_eqTrans : forall B G i j k,
  BProv B G (fEq i j) ->
  BProv B G (fEq j k) ->
  BProv B G (fEq i k).
Proof. intros B G i j k hij hjk; exact (BProv_rule2 B G (fEq i j) (fEq j k) (fEq i k) (fun D => Prov_eq_trans D i j k) hij hjk). Qed.

(* ---- natural-deduction rules lifted to relative provability ----

   These rules are independent of the base theory.  Keeping them beside
   [BProv] prevents each interpretation from duplicating the finite-axiom
   list bookkeeping. *)

Lemma BProv_context_cons : forall (B : form -> Prop) G a b,
  BProv B G b -> BProv B (a :: G) b.
Proof.
  intros B G a b h.
  apply (BProv_mono B G (a :: G) b); [ intros x hx; right; exact hx | exact h ].
Qed.

Lemma BProv_impI : forall (B : form -> Prop) G a b,
  BProv B (a :: G) b -> BProv B G (fImp a b).
Proof.
  intros B G a b [L [hL hp]].
  exists L. split; [ exact hL | ].
  apply P_impI.
  apply (Prov_weaken (L ++ a :: G) b hp).
  intros x hx; mem.
Qed.

Lemma BProv_impI_after_prefix : forall (B : form -> Prop) Gamma Delta a b,
  BProv B (Gamma ++ a :: Delta) b ->
  BProv B (Gamma ++ Delta) (fImp a b).
Proof.
  intros B Gamma Delta a b [L [hL hp]].
  exists L. split; [ exact hL | ].
  apply P_impI.
  apply (Prov_weaken (L ++ Gamma ++ a :: Delta) b hp).
  intros x hx; mem.
Qed.

Lemma BProv_andI : forall (B : form -> Prop) G a b,
  BProv B G a -> BProv B G b -> BProv B G (fAnd a b).
Proof. intros B G a b ha hb; exact (BProv_rule2 B G a b (fAnd a b) (fun D => P_andI D a b) ha hb). Qed.

Lemma BProv_botE : forall (B : form -> Prop) G a,
  BProv B G fBot -> BProv B G a.
Proof. intros B G a hbot; exact (BProv_rule1 B G fBot a (fun D => P_botE D a) hbot). Qed.

Lemma BProv_andE1 : forall (B : form -> Prop) G a b,
  BProv B G (fAnd a b) -> BProv B G a.
Proof. intros B G a b hand; exact (BProv_rule1 B G (fAnd a b) a (fun D => P_andE1 D a b) hand). Qed.

Lemma BProv_andE2 : forall (B : form -> Prop) G a b,
  BProv B G (fAnd a b) -> BProv B G b.
Proof. intros B G a b hand; exact (BProv_rule1 B G (fAnd a b) b (fun D => P_andE2 D a b) hand). Qed.

Lemma BProv_orI1 : forall (B : form -> Prop) G a b,
  BProv B G a -> BProv B G (fOr a b).
Proof. intros B G a b ha; exact (BProv_rule1 B G a (fOr a b) (fun D => P_orI1 D a b) ha). Qed.

Lemma BProv_orI2 : forall (B : form -> Prop) G a b,
  BProv B G b -> BProv B G (fOr a b).
Proof. intros B G a b hb; exact (BProv_rule1 B G b (fOr a b) (fun D => P_orI2 D a b) hb). Qed.

Lemma BProv_orE_imp : forall (B : form -> Prop) G a b c,
  BProv B G (fOr a b) ->
  BProv B G (fImp a c) ->
  BProv B G (fImp b c) ->
  BProv B G c.
Proof.
  intros B G a b c hor ha hb.
  apply (BProv_derive B G
    (fOr a b :: fImp a c :: fImp b c :: nil) c).
  - apply (Prov_orE_imp
      (fOr a b :: fImp a c :: fImp b c :: nil) a b c);
      apply P_ass; simpl; tauto.
  - intros d [<- | [<- | [<- | []]]]; assumption.
Qed.

Lemma BProv_orE : forall (B : form -> Prop) G a b c,
  BProv B G (fOr a b) ->
  BProv B (a :: G) c ->
  BProv B (b :: G) c ->
  BProv B G c.
Proof.
  intros B G a b c hor ha hb.
  apply (BProv_orE_imp B G a b c hor).
  - apply BProv_impI. exact ha.
  - apply BProv_impI. exact hb.
Qed.

Lemma BProv_orE_after_prefix : forall (B : form -> Prop) Gamma Delta a b c,
  BProv B (Gamma ++ Delta) (fOr a b) ->
  BProv B (Gamma ++ a :: Delta) c ->
  BProv B (Gamma ++ b :: Delta) c ->
  BProv B (Gamma ++ Delta) c.
Proof.
  intros B Gamma Delta a b c hor ha hb.
  apply (BProv_orE_imp B (Gamma ++ Delta) a b c hor).
  - apply BProv_impI_after_prefix. exact ha.
  - apply BProv_impI_after_prefix. exact hb.
Qed.

Lemma BProv_allE : forall (B : form -> Prop) G a k,
  BProv B G (fAll a) -> BProv B G (rename (inst k) a).
Proof. intros B G a k hall; exact (BProv_rule1 B G (fAll a) (rename (inst k) a) (fun D => P_allE D a k) hall). Qed.

Lemma BProv_exI : forall (B : form -> Prop) G a k,
  BProv B G (rename (inst k) a) -> BProv B G (fEx a).
Proof. intros B G a k hex; exact (BProv_rule1 B G (rename (inst k) a) (fEx a) (fun D => P_exI D a k) hex). Qed.

Lemma map_rename_eq_of_sentences : forall (B : form -> Prop) L,
  Sentences B ->
  (forall x, In x L -> B x) ->
  forall r, map (rename r) L = L.
Proof.
  intros B L. induction L as [|x xs IH]; intros hB hL r; simpl.
  - reflexivity.
  - rewrite (rename_eq_of_sentence x (hB x (hL x (or_introl eq_refl))) r).
    rewrite (IH hB (fun y hy => hL y (or_intror hy)) r).
    reflexivity.
Qed.

Lemma BProv_allI_of_sentences : forall (B : form -> Prop) G a,
  Sentences B ->
  BProv B (map (rename S) G) a ->
  BProv B G (fAll a).
Proof.
  intros B G a hB [L [hL hp]].
  pose proof (map_rename_eq_of_sentences B L hB hL S) as hLmap.
  exists L. split; [ exact hL | ].
  apply P_allI.
  apply (Prov_weaken (L ++ map (rename S) G) a hp).
  intros x hx. rewrite map_app, hLmap. exact hx.
Qed.

Lemma BProv_exE_of_sentences : forall (B : form -> Prop) G a c,
  Sentences B ->
  BProv B G (fEx a) ->
  BProv B (a :: map (rename S) G) (rename S c) ->
  BProv B G c.
Proof.
  intros B G a c hB [Le [hLe hpe]] [Lb [hLb hpb]].
  pose proof (map_rename_eq_of_sentences B Lb hB hLb S) as hLbmap.
  exists (Le ++ Lb). split.
  - intros x hx. apply in_app_iff in hx. destruct hx as [hx | hx].
    + exact (hLe x hx).
    + exact (hLb x hx).
  - apply (P_exE ((Le ++ Lb) ++ G) a c).
    + apply (Prov_weaken (Le ++ G) (fEx a) hpe).
      intros x hx.
      apply in_app_iff in hx.
      apply in_app_iff.
      destruct hx as [hx | hx].
      * left. apply in_app_iff. left. exact hx.
      * right. exact hx.
    + apply (Prov_weaken (Lb ++ a :: map (rename S) G) (rename S c) hpb).
      intros x hx.
      apply in_app_iff in hx.
      simpl in hx.
      simpl.
      destruct hx as [hx | [hx | hx]].
      * right.
        rewrite map_app.
        apply in_app_iff. left.
        rewrite map_app.
        apply in_app_iff. right.
        rewrite hLbmap.
        exact hx.
      * left. exact hx.
      * right.
        rewrite map_app.
        apply in_app_iff. right.
        exact hx.
Qed.

(* ---- directed connective and equivalence calculus ---- *)

(* Implication is contravariant in its premise and covariant in its result. *)
Lemma BProv_imp_mono : forall (B : form -> Prop) G a a' b b',
  BProv B G (fImp a' a) ->
  BProv B G (fImp b b') ->
  BProv B G (fImp (fImp a b) (fImp a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply (BProv_impI B G (fImp a b) (fImp a' b')).
  apply (BProv_impI B (fImp a b :: G) a' b').
  set (C := a' :: fImp a b :: G).
  assert (ha'C : BProv B C a').
  { apply BProv_ass. unfold C. simpl. tauto. }
  assert (haC : BProv B C a).
  { apply (BProv_mp B C a' a).
    - apply BProv_context_cons. apply BProv_context_cons. exact ha.
    - exact ha'C. }
  assert (habC : BProv B C (fImp a b)).
  { apply BProv_ass. unfold C. simpl. tauto. }
  assert (hbC : BProv B C b).
  { exact (BProv_mp B C a b habC haC). }
  apply (BProv_mp B C b b').
  - apply BProv_context_cons. apply BProv_context_cons. exact hb.
  - exact hbC.
Qed.

(* Conjunction is covariant in both components. *)
Lemma BProv_and_mono : forall (B : form -> Prop) G a a' b b',
  BProv B G (fImp a a') ->
  BProv B G (fImp b b') ->
  BProv B G (fImp (fAnd a b) (fAnd a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply (BProv_impI B G (fAnd a b) (fAnd a' b')).
  set (C := fAnd a b :: G).
  assert (habC : BProv B C (fAnd a b)).
  { apply BProv_ass. unfold C. simpl. tauto. }
  apply (BProv_andI B C a' b').
  - apply (BProv_mp B C a a').
    + apply BProv_context_cons. exact ha.
    + exact (BProv_andE1 B C a b habC).
  - apply (BProv_mp B C b b').
    + apply BProv_context_cons. exact hb.
    + exact (BProv_andE2 B C a b habC).
Qed.

(* Disjunction is covariant in both components. *)
Lemma BProv_or_mono : forall (B : form -> Prop) G a a' b b',
  BProv B G (fImp a a') ->
  BProv B G (fImp b b') ->
  BProv B G (fImp (fOr a b) (fOr a' b')).
Proof.
  intros B G a a' b b' ha hb.
  apply (BProv_impI B G (fOr a b) (fOr a' b')).
  set (C := fOr a b :: G).
  assert (horC : BProv B C (fOr a b)).
  { apply BProv_ass. unfold C. simpl. tauto. }
  apply (BProv_orE B C a b (fOr a' b') horC).
  - apply (BProv_orI1 B (a :: C) a' b').
    apply (BProv_mp B (a :: C) a a').
    + apply BProv_context_cons. apply BProv_context_cons. exact ha.
    + apply BProv_ass. simpl. tauto.
  - apply (BProv_orI2 B (b :: C) a' b').
    apply (BProv_mp B (b :: C) b b').
    + apply BProv_context_cons. apply BProv_context_cons. exact hb.
    + apply BProv_ass. simpl. tauto.
Qed.

Lemma BProv_fIff_intro : forall (B : form -> Prop) G a b,
  BProv B G (fImp a b) ->
  BProv B G (fImp b a) ->
  BProv B G (fIff a b).
Proof.
  intros B G a b hab hba. unfold fIff.
  exact (BProv_andI B G (fImp a b) (fImp b a) hab hba).
Qed.

Lemma BProv_fIff_forward : forall (B : form -> Prop) G a b,
  BProv B G (fIff a b) -> BProv B G (fImp a b).
Proof.
  intros B G a b h. unfold fIff in h.
  exact (BProv_andE1 B G (fImp a b) (fImp b a) h).
Qed.

Lemma BProv_fIff_reverse : forall (B : form -> Prop) G a b,
  BProv B G (fIff a b) -> BProv B G (fImp b a).
Proof.
  intros B G a b h. unfold fIff in h.
  exact (BProv_andE2 B G (fImp a b) (fImp b a) h).
Qed.

Lemma BProv_fIff_refl : forall (B : form -> Prop) G a,
  BProv B G (fIff a a).
Proof.
  intros B G a. apply BProv_fIff_intro.
  - apply BProv_impI. apply BProv_ass. simpl. tauto.
  - apply BProv_impI. apply BProv_ass. simpl. tauto.
Qed.

Lemma BProv_fIff_imp_congr : forall (B : form -> Prop) G a a' b b',
  BProv B G (fIff a a') ->
  BProv B G (fIff b b') ->
  BProv B G (fIff (fImp a b) (fImp a' b')).
Proof.
  intros B G a a' b b' ha hb. apply BProv_fIff_intro.
  - apply BProv_imp_mono.
    + exact (BProv_fIff_reverse B G a a' ha).
    + exact (BProv_fIff_forward B G b b' hb).
  - apply BProv_imp_mono.
    + exact (BProv_fIff_forward B G a a' ha).
    + exact (BProv_fIff_reverse B G b b' hb).
Qed.

Lemma BProv_fIff_and_congr : forall (B : form -> Prop) G a a' b b',
  BProv B G (fIff a a') ->
  BProv B G (fIff b b') ->
  BProv B G (fIff (fAnd a b) (fAnd a' b')).
Proof.
  intros B G a a' b b' ha hb. apply BProv_fIff_intro.
  - apply BProv_and_mono.
    + exact (BProv_fIff_forward B G a a' ha).
    + exact (BProv_fIff_forward B G b b' hb).
  - apply BProv_and_mono.
    + exact (BProv_fIff_reverse B G a a' ha).
    + exact (BProv_fIff_reverse B G b b' hb).
Qed.

Lemma BProv_fIff_or_congr : forall (B : form -> Prop) G a a' b b',
  BProv B G (fIff a a') ->
  BProv B G (fIff b b') ->
  BProv B G (fIff (fOr a b) (fOr a' b')).
Proof.
  intros B G a a' b b' ha hb. apply BProv_fIff_intro.
  - apply BProv_or_mono.
    + exact (BProv_fIff_forward B G a a' ha).
    + exact (BProv_fIff_forward B G b b' hb).
  - apply BProv_or_mono.
    + exact (BProv_fIff_reverse B G a a' ha).
    + exact (BProv_fIff_reverse B G b b' hb).
Qed.

Lemma stepB_pos_in : forall B L phi, BCon B (phi :: L) -> In phi (stepB B L phi).
Proof.
  intros B L phi Hc. unfold stepB.
  destruct (excluded_middle_informative (BCon B (phi :: L))) as [H | H];
    [ destruct phi; cbn [In]; tauto | contradiction ].
Qed.

Lemma stepB_neg_in : forall B L phi, ~ BCon B (phi :: L) -> In (fImp phi fBot) (stepB B L phi).
Proof.
  intros B L phi Hnc. unfold stepB.
  destruct (excluded_middle_informative (BCon B (phi :: L))) as [H | H];
    [ contradiction | destruct phi; cbn [In]; tauto ].
Qed.

Lemma stepB_ex_pos :
  forall B L a, BCon B (fEx a :: L) ->
    In (rename (inst (freshFor (fEx a :: L))) a) (stepB B L (fEx a)).
Proof.
  intros B L a Hc. unfold stepB.
  destruct (excluded_middle_informative (BCon B (fEx a :: L))) as [H | H];
    [ cbn [In]; tauto | contradiction ].
Qed.

Lemma stepB_all_neg :
  forall B L a, ~ BCon B (fAll a :: L) ->
    In (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: L))) a) fBot) (stepB B L (fAll a)).
Proof.
  intros B L a Hnc. unfold stepB.
  destruct (excluded_middle_informative (BCon B (fAll a :: L))) as [H | H];
    [ contradiction | cbn [In]; tauto ].
Qed.

Lemma Tinf_cons : forall B L0, Sentences B -> BCon B L0 -> ~ Tinf B L0 fBot.
Proof. intros B L0 HB H0 [n Hn]. exact (chainB_con B L0 HB H0 n Hn). Qed.

Lemma Tinf_compl : forall B L0 phi, Tinf B L0 phi \/ Tinf B L0 (fImp phi fBot).
Proof.
  intros B L0 phi. destruct (Enum_surj phi) as [n Hn]. subst phi.
  destruct (stepB_decides B (chainB B L0 n) (Enum n)) as [Hin | Hin].
  - left. exists (S n). exists nil. split; [ intros x [] | ].
    cbn [chainB app]. apply P_ass. exact Hin.
  - right. exists (S n). exists nil. split; [ intros x [] | ].
    cbn [chainB app]. apply P_ass. exact Hin.
Qed.

Lemma Tinf_bound :
  forall B L0 G, (forall x, In x G -> Tinf B L0 x) ->
    exists n Gb, (forall x, In x Gb -> B x) /\
                 (forall x, In x G -> Prov (Gb ++ chainB B L0 n) x).
Proof.
  intros B L0 G. induction G as [| g G' IHG]; intro Hall.
  - exists 0, nil. split; [ intros x [] | intros x [] ].
  - destruct (Hall g (or_introl eq_refl)) as [ng [Gbg [HGbg Hpg]]].
    destruct IHG as [N' [Gb' [HGb' HG']]]; [ intros x Hx; apply Hall; right; exact Hx | ].
    exists (Nat.max ng N'), (Gbg ++ Gb'). split.
    + intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx | Hx];
        [ apply HGbg; exact Hx | apply HGb'; exact Hx ].
    + intros x [Heq | Hx].
      * subst x. apply (Prov_weaken (Gbg ++ chainB B L0 ng) g Hpg).
        intros y Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy | Hy].
        -- left. apply in_app_iff. left. exact Hy.
        -- right. apply (chainB_mono B L0 (Nat.max ng N') ng); [ lia | exact Hy ].
      * apply (Prov_weaken (Gb' ++ chainB B L0 N') x (HG' x Hx)).
        intros y Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy | Hy].
        -- left. apply in_app_iff. right. exact Hy.
        -- right. apply (chainB_mono B L0 (Nat.max ng N') N'); [ lia | exact Hy ].
Qed.

Lemma Tinf_closed :
  forall B L0 G phi, (forall x, In x G -> Tinf B L0 x) -> Prov G phi -> Tinf B L0 phi.
Proof.
  intros B L0 G phi Hall Hp. destruct (Tinf_bound B L0 G Hall) as [N [Gb [HGb HN]]].
  exists N. exists Gb. split; [ exact HGb | ].
  exact (Prov_cut G phi Hp (Gb ++ chainB B L0 N) HN).
Qed.

Lemma Tinf_mp : forall B L0 a b,
  Tinf B L0 (fImp a b) -> Tinf B L0 a -> Tinf B L0 b.
Proof.
  intros B L0 a b Himp Ha.
  apply (Tinf_closed B L0 (fImp a b :: a :: nil) b).
  - intros x [<- | [<- | []]]; assumption.
  - apply (P_impE (fImp a b :: a :: nil) a b); apply P_ass; simpl; tauto.
Qed.

Lemma Tinf_henkin_ex :
  forall B L0, Sentences B -> BCon B L0 -> forall a,
    Tinf B L0 (fEx a) -> exists k, Tinf B L0 (rename (inst k) a).
Proof.
  intros B L0 HB H0 a HEx. destruct (Enum_surj (fEx a)) as [m Hm].
  destruct (classic (BCon B (fEx a :: chainB B L0 m))) as [Hpos | Hnc].
  - exists (freshFor (fEx a :: chainB B L0 m)). exists (S m). exists nil. split;
      [ intros x [] | ].
    cbn [chainB app]. rewrite Hm. apply P_ass. apply stepB_ex_pos. exact Hpos.
  - exfalso.
    assert (Hneg : Tinf B L0 (fImp (fEx a) fBot)).
    { exists (S m). exists nil. split; [ intros x [] | ]. cbn [chainB app]. rewrite Hm.
      apply P_ass. apply stepB_neg_in. exact Hnc. }
    apply (Tinf_cons B L0 HB H0).
    exact (Tinf_mp B L0 (fEx a) fBot Hneg HEx).
Qed.

Lemma Tinf_henkin_all :
  forall B L0, Sentences B -> BCon B L0 -> forall a,
    (forall k, Tinf B L0 (rename (inst k) a)) -> Tinf B L0 (fAll a).
Proof.
  intros B L0 HB H0 a Hall.
  destruct (Tinf_compl B L0 (fAll a)) as [Hpos | Hneg]; [ exact Hpos | ].
  exfalso. destruct (Enum_surj (fAll a)) as [m Hm].
  destruct (classic (BCon B (fAll a :: chainB B L0 m))) as [Hc | Hnc].
  - assert (Hposfa : Tinf B L0 (fAll a)).
    { exists (S m). exists nil. split; [ intros x [] | ].
      cbn [chainB app]. rewrite Hm. apply P_ass. apply stepB_pos_in. exact Hc. }
    apply (Tinf_cons B L0 HB H0).
    exact (Tinf_mp B L0 (fAll a) fBot Hneg Hposfa).
  - assert (Hnegw : Tinf B L0
                      (fImp (rename (inst (freshFor (fImp (fAll a) fBot :: chainB B L0 m))) a) fBot)).
    { exists (S m). exists nil. split; [ intros x [] | ]. cbn [chainB app]. rewrite Hm.
      apply P_ass. apply stepB_all_neg. exact Hnc. }
    set (w := freshFor (fImp (fAll a) fBot :: chainB B L0 m)) in *.
    apply (Tinf_cons B L0 HB H0).
    exact (Tinf_mp B L0 (rename (inst w) a) fBot Hnegw (Hall w)).
Qed.

(* MODEL EXISTENCE for a consistent sentence theory with a finite extra list. *)
Theorem model_of_BCon :
  forall B L0, Sentences B -> BCon B L0 ->
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      (forall g, B g -> Sat Dom m v g) /\ (forall g, In g L0 -> Sat Dom m v g).
Proof.
  intros B L0 HB H0.
  destruct (model_exists (Tinf B L0)
              (Tinf_cons B L0 HB H0) (Tinf_compl B L0) (Tinf_closed B L0)
              (Tinf_henkin_ex B L0 HB H0) (Tinf_henkin_all B L0 HB H0)) as [Dom [m [v Hsat]]].
  exists Dom, m, v. split.
  - intros g Hg. apply (proj2 (Hsat g)). exists 0. exists (g :: nil). split.
    + intros x [Heq | []]. subst x. exact Hg.
    + cbn [chainB app]. apply P_ass. left. reflexivity.
  - intros g Hg. apply (proj2 (Hsat g)). exists 0. exists nil. split.
    + intros x [].
    + cbn [chainB app]. apply P_ass. exact Hg.
Qed.

(* ===================================================================== *)
(*  Finite-context completeness, as the B = emptyset instance.            *)
(* ===================================================================== *)

(* Provability from the empty base theory is plain provability. *)
Lemma BProv_empty :
  forall G phi, BProv (fun _ => False) G phi <-> Prov G phi.
Proof.
  intros G phi. split.
  - intros [Gb [HGb Hp]]. destruct Gb as [| x Gb'].
    + exact Hp.
    + exfalso. apply (HGb x). left. reflexivity.
  - intro H. exists nil. split; [ intros x [] | exact H ].
Qed.

(* Every consistent finite context has a model (the B = emptyset instance
   of model_of_BCon). *)
Theorem model_of_con :
  forall G0, Con G0 ->
    exists (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
      forall g, In g G0 -> Sat Dom m v g.
Proof.
  intros G0 HG0.
  assert (HB : Sentences (fun _ : form => False)) by (intros f Hf; destruct Hf).
  assert (H0 : BCon (fun _ => False) G0).
  { intro Hbad. apply HG0. apply (proj1 (BProv_empty G0 fBot)). exact Hbad. }
  destruct (model_of_BCon (fun _ => False) G0 HB H0) as [Dom [m [v [_ HsatL]]]].
  exists Dom, m, v. exact HsatL.
Qed.

(* Shared countermodel kernel for finite and sentence-theory completeness. *)
Local Lemma completeness_inf_context_core :
  forall B G psi, Sentences B ->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, B g -> Sat Dom m v g) ->
       (forall g, In g G -> Sat Dom m v g) ->
       Sat Dom m v psi) ->
    BProv B G psi.
Proof.
  intros B G psi HB Hval.
  apply NNPP. intro Hnp.
  assert (HBcon : BCon B (fImp psi fBot :: G)).
  { intros [Gb [HGb Hbad]]. apply Hnp. exists Gb. split; [ exact HGb | ].
    apply Prov_byContra.
    apply (Prov_exch (Gb ++ fImp psi fBot :: G)); [ intro x; mem | exact Hbad ]. }
  destruct (model_of_BCon B (fImp psi fBot :: G) HB HBcon)
    as [Dom [m [v [HsatB HsatL]]]].
  exact (HsatL _ (or_introl eq_refl)
           (Hval Dom m v HsatB (fun g hg => HsatL g (or_intror hg)))).
Qed.

(* COMPLETENESS: validity in all models implies provability. *)
Theorem completeness :
  forall G phi,
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi) ->
    Prov G phi.
Proof.
  intros G phi Hval.
  apply (proj1 (BProv_empty G phi)).
  apply (completeness_inf_context_core (fun _ => False) G phi).
  - intros f Hf. destruct Hf.
  - intros Dom m v _ HG. exact (Hval Dom m v HG).
Qed.

(* SOUNDNESS + COMPLETENESS: provability coincides with validity. *)
Corollary prov_iff_valid :
  forall G phi,
    Prov G phi <->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi).
Proof.
  intros G phi. split.
  - intros H Dom m v Hg. exact (soundness Dom m G phi H v Hg).
  - apply completeness.
Qed.

(* Relative infinite completeness needs the base theory to consist of
   sentences, but imposes no sentence restriction on either the finite
   context G or the target psi. *)
Theorem completeness_inf_context :
  forall B G psi, Sentences B ->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, B g -> Sat Dom m v g) ->
       (forall g, In g G -> Sat Dom m v g) ->
       Sat Dom m v psi) ->
    BProv B G psi.
Proof. exact completeness_inf_context_core. Qed.

(* INFINITE COMPLETENESS: the historical empty-context interface.  The target
   sentence premise is retained for compatibility, although the stronger
   finite-context theorem above does not need it. *)
Theorem completeness_inf :
  forall B psi, Sentences B -> Sentence psi ->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, B g -> Sat Dom m v g) -> Sat Dom m v psi) ->
    BProv B nil psi.
Proof.
  intros B psi HB _ Hval.
  apply (completeness_inf_context B nil psi HB).
  intros Dom m v HsatB _.
  exact (Hval Dom m v HsatB).
Qed.

(* SEMANTIC THEORY TRANSFER: if every model of B2 is a model of B1, proofs
   over B1 transfer to B2.  The finite context and target formula are
   unrestricted; only the destination base theory must consist of sentences. *)
Theorem theory_transfer :
  forall B1 B2 G psi, Sentences B2 ->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, B2 g -> Sat Dom m v g) ->
       forall g, B1 g -> Sat Dom m v g) ->
    BProv B1 G psi -> BProv B2 G psi.
Proof.
  intros B1 B2 G psi HB2 Hmodels Hp.
  apply (completeness_inf_context B2 G psi HB2).
  intros Dom m v HB2sat HGsat.
  exact (soundness_BProv Dom m B1 G psi Hp v
           (Hmodels Dom m v HB2sat) HGsat).
Qed.

(* DEDUCTIVE EQUIVALENCE: two sentence theories with the same models prove
   the same sentences. *)
Theorem theory_equiv :
  forall B1 B2, Sentences B1 -> Sentences B2 ->
    (forall (Dom : Type) (m : Dom -> Dom -> Prop) (v : nat -> Dom),
       (forall g, B1 g -> Sat Dom m v g) <-> (forall g, B2 g -> Sat Dom m v g)) ->
    forall psi, Sentence psi -> (BProv B1 nil psi <-> BProv B2 nil psi).
Proof.
  intros B1 B2 HB1 HB2 Hsame psi _. split.
  - apply (theory_transfer B1 B2 nil psi HB2).
    intros Dom m v HB2sat. exact (proj2 (Hsame Dom m v) HB2sat).
  - apply (theory_transfer B2 B1 nil psi HB1).
    intros Dom m v HB1sat. exact (proj1 (Hsame Dom m v) HB1sat).
Qed.

Check model_exists.
Check completeness.
Check prov_iff_valid.
Check completeness_inf.
Check theory_transfer.
Check theory_equiv.
