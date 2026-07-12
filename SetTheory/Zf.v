(* ===================================================================== *)
(*  Zf.v                                                                  *)
(*                                                                       *)
(*  FIRST-ORDER ZF, independent of the Closure axiomatization T:          *)
(*                                                                       *)
(*   - the ZF axioms as formulas (Ext_form ... Reg_form, with the         *)
(*     Separation and Replacement schemas over `form`), the axiom set     *)
(*     `ZFax` and provability `ZFprov`, and the SENTENCE theory `ZFax_s`  *)
(*     (every axiom universally closed by `seal`);                        *)
(*   - extraction bridges: satisfaction of each (open) axiom formula in   *)
(*     a structure (V, mem) is equivalent to the abstract semantic axiom  *)
(*     (`bridge_Ext` ... `bridge_Repl`, with legacy `_fwd` projections);  *)
(*   - INTERNAL MATHEMATICS of an arbitrary first-order model of          *)
(*     {Ext, Sep, Pair, Union, Inf, Repl} (note: no Powerset, no          *)
(*     Regularity): internal set algebra, Kuratowski pairs with           *)
(*     injectivity, an internal omega with the definable-induction        *)
(*     schema `omega_ind`, a formula-macro library with satisfaction      *)
(*     specs, and the FINITE RECURSION THEOREM (approximations `Approx`,  *)
(*     existence + agreement, functional stage relation Theta), giving    *)
(*                                                                       *)
(*       ClosureFO_of_ZF : every definable set-like relation admits a     *)
(*       closure superset of any seed -- inside every such model.         *)
(*                                                                       *)
(*  These are reusable tools for interpreting or proving ANY schema in    *)
(*  first-order ZF models, not just the Closure schema of Equivalence.v.  *)
(*                                                                       *)
(*  - Created (UTC): 2026-07-01T21:20:00Z                                 *)
(*  - Repository HEAD: c73d98802cf8385db7100480fdc5019105812718           *)
(* ===================================================================== *)

From SetTheory Require Import Fol Calculus.
From Stdlib Require Import List Setoid ClassicalEpsilon.
Import ListNotations.

(* ================= the ZF axioms as first-order formulas ============== *)


(* renamings used to place a schema's formula under fresh binders *)
Definition rsep : nat -> nat := fun n => match n with O => O | S i => S (S (S i)) end.
Definition rf1  : nat -> nat := fun n => match n with O => 1 | 1 => 2 | S (S j) => S (S (S j)) end.
Definition rf2  : nat -> nat := fun n => match n with O => O | 1 => 2 | S (S j) => S (S (S j)) end.
Definition ri   : nat -> nat := fun n => match n with O => 1 | 1 => O | S (S j) => S (S (S (S j))) end.

(* environment lemmas for the schema renamings *)
Section EnvLemmas.

Variable V : Type.
Local Notation scons := (Fol.scons V).

Lemma rsep_env : forall dx s da (e : nat -> V) n,
  scons dx (scons s (scons da e)) (rsep n) = scons dx e n.
Proof. intros. destruct n; reflexivity. Qed.

Lemma rf1_env : forall y2 y1 x (e : nat -> V) n,
  scons y2 (scons y1 (scons x e)) (rf1 n) = scons y1 (scons x e) n.
Proof. intros. destruct n as [| [| j]]; reflexivity. Qed.

Lemma rf2_env : forall y2 y1 x (e : nat -> V) n,
  scons y2 (scons y1 (scons x e)) (rf2 n) = scons y2 (scons x e) n.
Proof. intros. destruct n as [| [| j]]; reflexivity. Qed.

Lemma ri_env : forall x y r a (e : nat -> V) n,
  scons x (scons y (scons r (scons a e))) (ri n) = scons y (scons x e) n.
Proof. intros. destruct n as [| [| j]]; reflexivity. Qed.

End EnvLemmas.

(* --- the ZF axioms as closed formulas --- *)

(* --- the ZF axioms as closed formulas --- *)

Definition Ext_form : form :=
  fAll (fAll (fImp (fAll (fIff (fMem 0 2) (fMem 0 1))) (fEq 1 0))).
Definition Pair_form : form :=
  fAll (fAll (fEx (fAll (fIff (fMem 0 1) (fOr (fEq 0 3) (fEq 0 2)))))).
Definition Union_form : form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fEx (fAnd (fMem 1 0) (fMem 0 3)))))).
Definition Pow_form : form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 3)))))).
Definition Inf_form : form :=
  fEx (fAnd
        (fEx (fAnd (fMem 0 1) (fAll (fImp (fMem 0 1) fBot))))
        (fAll (fImp (fMem 0 1)
                 (fEx (fAnd (fMem 0 2)
                         (fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2))))))))).
Definition Reg_form : form :=
  fAll (fImp (fEx (fMem 0 1))
          (fEx (fAnd (fMem 0 1)
                  (fImp (fEx (fAnd (fMem 0 1) (fMem 0 2))) fBot)))).
Definition Sep_form (phi : form) : form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fAnd (fMem 0 2) (rename rsep phi))))).
Definition Func_form (psi : form) : form :=
  fAll (fAll (fAll (fImp (fAnd (rename rf1 psi) (rename rf2 psi)) (fEq 1 0)))).
Definition Image_form (psi : form) : form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fEx (fAnd (fMem 0 3) (rename ri psi)))))).
Definition Repl_form (psi : form) : form := fImp (Func_form psi) (Image_form psi).

(* --- the ZF axiom set: list-context provability, and as a sentence theory --- *)

(* --- the ZF axiom set, ZF-provability, and the corollary --- *)

Definition ZFax (f : form) : Prop :=
  f = Ext_form \/ f = Pair_form \/ f = Union_form \/ f = Pow_form \/
  f = Inf_form \/ f = Reg_form \/
  (exists phi, f = Sep_form phi) \/ (exists psi, f = Repl_form psi).
Definition ZFprov (phi : form) : Prop :=
  exists G, (forall x, In x G -> ZFax x) /\ Prov G phi.
Definition ZFax_s (f : form) : Prop :=
  f = seal Ext_form \/ f = seal Reg_form \/ f = seal Pow_form \/
  f = seal Pair_form \/ f = seal Union_form \/ f = seal Inf_form \/
  (exists phi, f = seal (Sep_form phi)) \/ (exists psi, f = seal (Repl_form psi)).
Lemma Sentences_ZF : Sentences ZFax_s.
Proof.
  intros f Hf.
  destruct Hf as [->|[->|[->|[->|[->|[->|[[phi ->]|[psi ->]]]]]]]]; apply Sentence_seal.
Qed.

(* ===== extraction bridges: open-axiom satisfaction <-> semantic axioms ==== *)

(* --- bridges: model satisfaction of the (open) axioms <-> abstract axioms --- *)

Lemma bridge_Ext :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Ext_form) <->
    (forall a b, (forall x, mem x a <-> mem x b) -> a = b).
Proof.
  intros V mem. split.
  - intros H a b Hab. exact (H (fun _ => a) a b Hab).
  - intros H e a b Hab. exact (H a b Hab).
Qed.

Lemma bridge_Ext_fwd :
  forall (V : Type) (mem : V -> V -> Prop), (forall e, Sat V mem e Ext_form) ->
    (forall a b, (forall x, mem x a <-> mem x b) -> a = b).
Proof. intros V mem H. exact (proj1 (bridge_Ext V mem) H). Qed.

Lemma bridge_Pow :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Pow_form) <->
    (forall a, exists p, forall x, mem x p <-> Sub V mem x a).
Proof.
  intros V mem. split.
  - intros H a. exact (H (fun _ => a) a).
  - intros H e a. exact (H a).
Qed.

Lemma bridge_Pow_fwd :
  forall (V : Type) (mem : V -> V -> Prop), (forall e, Sat V mem e Pow_form) ->
    (forall a, exists p, forall x, mem x p <-> Sub V mem x a).
Proof. intros V mem H. exact (proj1 (bridge_Pow V mem) H). Qed.

Lemma bridge_Reg :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Reg_form) <->
    (forall a, (exists x, mem x a) ->
      exists m, mem m a /\ ~ (exists z, mem z m /\ mem z a)).
Proof.
  intros V mem. split.
  - intros H a. exact (H (fun _ => a) a).
  - intros H e a. exact (H a).
Qed.

Lemma bridge_Reg_fwd :
  forall (V : Type) (mem : V -> V -> Prop), (forall e, Sat V mem e Reg_form) ->
    (forall a, (exists x, mem x a) -> exists m, mem m a /\ ~ (exists z, mem z m /\ mem z a)).
Proof. intros V mem H. exact (proj1 (bridge_Reg V mem) H). Qed.

Lemma rsep_rel :
  forall (V : Type) (mem : V -> V -> Prop) phi x s da e,
    Sat V mem (scons V x (scons V s (scons V da e))) (rename rsep phi)
    <-> Sat V mem (scons V x e) phi.
Proof.
  intros V mem phi x s da e.
  apply (Sat_rename_ext V mem phi rsep
           (scons V x (scons V s (scons V da e)))
           (scons V x e) (rsep_env V x s da e)).
Qed.

Lemma bridge_Sep :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall phi e, Sat V mem e (Sep_form phi)) <->
    (forall phi e a, exists s, forall x,
      mem x s <-> (mem x a /\ Sat V mem (scons V x e) phi)).
Proof.
  intros V mem.
  assert (Hbody : forall phi e a s x,
      (mem x a /\
       Sat V mem (scons V x (scons V s (scons V a e))) (rename rsep phi)) <->
      (mem x a /\ Sat V mem (scons V x e) phi)).
  { intros phi e a s x.
    pose proof (rsep_rel V mem phi x s a e). tauto. }
  split.
  - intros H phi e a.
    pose proof (H phi e) as He. unfold Sep_form, fIff in He. cbn [Sat] in He.
    destruct (He a) as [s Hs]. exists s. intro x.
    exact (iff_trans (Hs x) (Hbody phi e a s x)).
  - intros H phi e. unfold Sep_form, fIff. cbn [Sat]. intro a.
    destruct (H phi e a) as [s Hs]. exists s. intro x.
    exact (iff_trans (Hs x) (iff_sym (Hbody phi e a s x))).
Qed.

Lemma bridge_Sep_fwd :
  forall (V : Type) (mem : V -> V -> Prop), (forall phi e, Sat V mem e (Sep_form phi)) ->
    (forall phi e a, exists s, forall x, mem x s <-> (mem x a /\ Sat V mem (scons V x e) phi)).
Proof. intros V mem H. exact (proj1 (bridge_Sep V mem) H). Qed.
(* --- bridges for the four generative axioms --- *)

Lemma bridge_Pair :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Pair_form) <->
    (forall a b, exists p, forall x, mem x p <-> (x = a \/ x = b)).
Proof.
  intros V mem. split.
  - intros H a b. destruct (H (fun _ => a) a b) as [p Hp].
    exists p. intro x. specialize (Hp x). cbn in Hp. tauto.
  - intros H e a b. destruct (H a b) as [p Hp].
    exists p. intro x. specialize (Hp x). cbn. tauto.
Qed.

Lemma bridge_Pair_fwd :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Pair_form) ->
    forall a b, exists p, forall x, mem x p <-> (x = a \/ x = b).
Proof. intros V mem H. exact (proj1 (bridge_Pair V mem) H). Qed.

Lemma bridge_Union :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Union_form) <->
    (forall u, exists w, forall x,
      mem x w <-> exists v, mem x v /\ mem v u).
Proof.
  intros V mem. split.
  - intros H u. destruct (H (fun _ => u) u) as [w Hw].
    exists w. intro x. specialize (Hw x). cbn in Hw.
    split.
    + intro Hx. destruct (proj1 Hw Hx) as [v [Hv1 Hv2]]. exists v. tauto.
    + intros [v [Hv1 Hv2]]. apply (proj2 Hw). exists v. tauto.
  - intros H e u. destruct (H u) as [w Hw].
    exists w. intro x. specialize (Hw x). cbn.
    split.
    + intro Hx. destruct (proj1 Hw Hx) as [v [Hv1 Hv2]]. exists v. tauto.
    + intros [v [Hv1 Hv2]]. apply (proj2 Hw). exists v. tauto.
Qed.

Lemma bridge_Union_fwd :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall e, Sat V mem e Union_form) ->
    forall u, exists w, forall x, mem x w <-> exists v, mem x v /\ mem v u.
Proof. intros V mem H. exact (proj1 (bridge_Union V mem) H). Qed.

(** [Inf_form] is closed, but the pointwise environment is retained so the
    legacy extraction theorem remains a literal projection. *)
Lemma bridge_Inf :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
    Sat V mem v Inf_form <->
    exists I,
      (exists e0, mem e0 I /\ forall z, ~ mem z e0) /\
      (forall x, mem x I ->
         exists sx, mem sx I /\ forall t, mem t sx <-> (mem t x \/ t = x)).
Proof.
  intros V mem v. split.
  - intro H. cbn in H. destruct H as [I [[e0 [He0 Hemp]] Hsucc]].
    exists I. split.
    + exists e0. split; [ exact He0 | ]. intros z Hz. exact (Hemp z Hz).
    + intros x Hx. destruct (Hsucc x Hx) as [sx [Hsx Hspec]].
      exists sx. split; [ exact Hsx | ]. intro t. specialize (Hspec t). tauto.
  - intros [I [[e0 [He0 Hemp]] Hsucc]]. cbn [Sat].
    exists I. split.
    + exists e0. split; [ exact He0 | ]. intros z Hz. exact (Hemp z Hz).
    + intros x Hx. destruct (Hsucc x Hx) as [sx [Hsx Hspec]].
      exists sx. split; [ exact Hsx | ]. intro t. exact (Hspec t).
Qed.

Lemma bridge_Inf_fwd :
  forall (V : Type) (mem : V -> V -> Prop) (v : nat -> V),
    Sat V mem v Inf_form ->
    exists I,
      (exists e0, mem e0 I /\ forall z, ~ mem z e0) /\
      (forall x, mem x I ->
         exists sx, mem sx I /\ forall t, mem t sx <-> (mem t x \/ t = x)).
Proof. intros V mem v H. exact (proj1 (bridge_Inf V mem v) H). Qed.

(* Canonical semantic readings of the two components of Replacement. *)
Lemma bridge_Func :
  forall (V : Type) (mem : V -> V -> Prop) psi e,
    Sat V mem e (Func_form psi) <-> Functional V (relOf V mem psi e).
Proof.
  intros V mem psi e. unfold Func_form, Functional. cbn [Sat].
  assert (H1 : forall x y1 y2,
      Sat V mem (scons V y2 (scons V y1 (scons V x e))) (rename rf1 psi) <->
      relOf V mem psi e y1 x).
  { intros x y1 y2. exact (Sat_rename_relOf V mem psi rf1
      (scons V y2 (scons V y1 (scons V x e))) e y1 x
      (rf1_env V y2 y1 x e)). }
  assert (H2 : forall x y1 y2,
      Sat V mem (scons V y2 (scons V y1 (scons V x e))) (rename rf2 psi) <->
      relOf V mem psi e y2 x).
  { intros x y1 y2. exact (Sat_rename_relOf V mem psi rf2
      (scons V y2 (scons V y1 (scons V x e))) e y2 x
      (rf2_env V y2 y1 x e)). }
  split; intros H x y1 y2; specialize (H x y1 y2);
    pose proof (H1 x y1 y2); pose proof (H2 x y1 y2); tauto.
Qed.

Lemma bridge_Image :
  forall (V : Type) (mem : V -> V -> Prop) psi e,
    Sat V mem e (Image_form psi) <->
    (forall a, exists r, forall y,
       mem y r <-> exists x, mem x a /\ relOf V mem psi e y x).
Proof.
  intros V mem psi e. unfold Image_form. cbn [Sat].
  assert (Hrel : forall a r y x,
      Sat V mem (scons V x (scons V y (scons V r (scons V a e))))
        (rename ri psi) <-> relOf V mem psi e y x).
  { intros a r y x. exact (Sat_rename_relOf V mem psi ri
      (scons V x (scons V y (scons V r (scons V a e)))) e y x
      (ri_env V x y r a e)). }
  assert (Hbody : forall a r y,
      (exists x, mem x a /\
        Sat V mem (scons V x (scons V y (scons V r (scons V a e))))
          (rename ri psi)) <->
      (exists x, mem x a /\ relOf V mem psi e y x)).
  { intros a r y. split; intros [x [Hxa Hpsi]]; exists x; split;
      [ exact Hxa | exact (proj1 (Hrel a r y x) Hpsi)
      | exact Hxa | exact (proj2 (Hrel a r y x) Hpsi) ]. }
  split; intros H a; destruct (H a) as [r Hr]; exists r; intro y.
  - exact (iff_trans (Hr y) (Hbody a r y)).
  - exact (iff_trans (Hr y) (iff_sym (Hbody a r y))).
Qed.

Lemma bridge_Repl :
  forall (V : Type) (mem : V -> V -> Prop) psi e,
    Sat V mem e (Repl_form psi) <->
    (Functional V (relOf V mem psi e) ->
     forall a, exists r, forall y,
       mem y r <-> exists x, mem x a /\ relOf V mem psi e y x).
Proof.
  intros V mem psi e. unfold Repl_form. cbn [Sat].
  rewrite (bridge_Func V mem psi e), (bridge_Image V mem psi e). tauto.
Qed.

Lemma bridge_Repl_fwd :
  forall (V : Type) (mem : V -> V -> Prop),
    (forall psi e, Sat V mem e (Repl_form psi)) ->
    forall psi (e : nat -> V),
      Functional V (relOf V mem psi e) ->
      forall a, exists r, forall y,
        mem y r <-> exists x, mem x a /\ relOf V mem psi e y x.
Proof.
  intros V mem H psi e Hfun.
  exact (proj1 (bridge_Repl V mem psi e) (H psi e) Hfun).
Qed.

(* ===================================================================== *)
(*  Inside an arbitrary first-order ZF model (no Powerset, no             *)
(*  Regularity): the internal finite recursion theorem, and closure of    *)
(*  any seed under any definable set-like relation.                       *)
(* ===================================================================== *)
Section ZfModel.

Variable V : Type.
Variable mem : V -> V -> Prop.
Local Infix "∈" := mem (at level 70, no associativity).
Local Notation SAT := (Sat V mem).
Local Notation SC := (scons V).

(* -------- the model-side ZF axioms (no Powerset, no Regularity) ------- *)

Hypothesis AxExt :
  forall a b, (forall x, x ∈ a <-> x ∈ b) -> a = b.

Hypothesis AxSep :
  forall (phi : form) (e : nat -> V) (a : V),
    exists s, forall x, x ∈ s <-> (x ∈ a /\ SAT (SC x e) phi).

Hypothesis AxPair :
  forall a b, exists p, forall x, x ∈ p <-> (x = a \/ x = b).

Hypothesis AxUnion :
  forall u, exists w, forall x, x ∈ w <-> exists v, x ∈ v /\ v ∈ u.

Hypothesis AxInf :
  exists I,
    (exists e0, e0 ∈ I /\ forall z, ~ z ∈ e0) /\
    (forall x, x ∈ I ->
       exists sx, sx ∈ I /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).

Hypothesis AxRepl :
  forall (psi : form) (e : nat -> V),
    Functional V (relOf V mem psi e) ->
    forall a, exists r, forall y,
      y ∈ r <-> exists x, x ∈ a /\ relOf V mem psi e y x.

(* --------------------- internal set operators ------------------------- *)

Definition sepD (phi : form) (e : nat -> V) (a : V) : V :=
  proj1_sig (constructive_indefinite_description _ (AxSep phi e a)).
Lemma sepD_spec :
  forall phi e a x, x ∈ sepD phi e a <-> (x ∈ a /\ SAT (SC x e) phi).
Proof.
  intros phi e a.
  exact (proj2_sig (constructive_indefinite_description _ (AxSep phi e a))).
Qed.

Definition vpair (a b : V) : V :=
  proj1_sig (constructive_indefinite_description _ (AxPair a b)).
Lemma vpair_spec : forall a b x, x ∈ vpair a b <-> (x = a \/ x = b).
Proof.
  intros a b.
  exact (proj2_sig (constructive_indefinite_description _ (AxPair a b))).
Qed.

Definition vsingle (a : V) : V := vpair a a.
Lemma vsingle_spec : forall a x, x ∈ vsingle a <-> x = a.
Proof.
  intros a x. unfold vsingle. rewrite (vpair_spec a a x). tauto.
Qed.

Definition vunion (u : V) : V :=
  proj1_sig (constructive_indefinite_description _ (AxUnion u)).
Lemma vunion_spec : forall u x, x ∈ vunion u <-> exists v, x ∈ v /\ v ∈ u.
Proof.
  intro u.
  exact (proj2_sig (constructive_indefinite_description _ (AxUnion u))).
Qed.

Definition vcup (a b : V) : V := vunion (vpair a b).
Lemma vcup_spec : forall a b x, x ∈ vcup a b <-> (x ∈ a \/ x ∈ b).
Proof.
  intros a b x. unfold vcup. rewrite (vunion_spec (vpair a b) x). split.
  - intros [v [Hxv Hv]]. apply (proj1 (vpair_spec a b v)) in Hv.
    destruct Hv as [-> | ->]; [ left | right ]; exact Hxv.
  - intros [Ha | Hb].
    + exists a. split; [ exact Ha | apply (proj2 (vpair_spec a b a)); left; reflexivity ].
    + exists b. split; [ exact Hb | apply (proj2 (vpair_spec a b b)); right; reflexivity ].
Qed.

Definition vsucc (a : V) : V := vcup a (vsingle a).
Lemma vsucc_spec : forall a x, x ∈ vsucc a <-> (x ∈ a \/ x = a).
Proof.
  intros a x. unfold vsucc. rewrite (vcup_spec a (vsingle a) x).
  rewrite (vsingle_spec a x). tauto.
Qed.

Lemma vsucc_self : forall a, a ∈ vsucc a.
Proof. intro a. apply (proj2 (vsucc_spec a a)). right. reflexivity. Qed.

Definition InfSet : V :=
  proj1_sig (constructive_indefinite_description _ AxInf).
Lemma InfSet_spec :
  (exists e0, e0 ∈ InfSet /\ forall z, ~ z ∈ e0) /\
  (forall x, x ∈ InfSet ->
     exists sx, sx ∈ InfSet /\ forall t, t ∈ sx <-> (t ∈ x \/ t = x)).
Proof. exact (proj2_sig (constructive_indefinite_description _ AxInf)). Qed.

Definition vempty : V := sepD fBot (fun _ => InfSet) InfSet.
Lemma vempty_spec : forall x, ~ x ∈ vempty.
Proof.
  intros x H. apply (proj1 (sepD_spec fBot (fun _ => InfSet) InfSet x)) in H.
  destruct H as [_ HF]. cbn in HF. exact HF.
Qed.

Lemma empty_in_InfSet : vempty ∈ InfSet.
Proof.
  destruct InfSet_spec as [[e0 [He0 Hemp]] _].
  assert (e0 = vempty).
  { apply AxExt. intro t. split; intro Ht.
    - exfalso. exact (Hemp t Ht).
    - exfalso. exact (vempty_spec t Ht). }
  subst e0. exact He0.
Qed.

Lemma vsucc_in_InfSet : forall x, x ∈ InfSet -> vsucc x ∈ InfSet.
Proof.
  intros x Hx. destruct InfSet_spec as [_ Hsucc].
  destruct (Hsucc x Hx) as [sx [Hsx Hspec]].
  assert (sx = vsucc x).
  { apply AxExt. intro t. split; intro Ht.
    - apply (proj2 (vsucc_spec x t)). exact (proj1 (Hspec t) Ht).
    - apply (proj2 (Hspec t)).        exact (proj1 (vsucc_spec x t) Ht). }
  subst sx. exact Hsx.
Qed.

(* ------------------ Kuratowski pairs and injectivity ------------------ *)

Definition kpair (a b : V) : V := vpair (vsingle a) (vpair a b).
Lemma kpair_mem :
  forall a b q, q ∈ kpair a b <-> (q = vsingle a \/ q = vpair a b).
Proof. intros a b q. unfold kpair. apply vpair_spec. Qed.

Lemma vsingle_inj : forall a b, vsingle a = vsingle b -> a = b.
Proof.
  intros a b H.
  assert (Ha : a ∈ vsingle a) by (apply (proj2 (vsingle_spec a a)); reflexivity).
  rewrite H in Ha. exact (proj1 (vsingle_spec b a) Ha).
Qed.

Lemma vpair_single : forall a b c, vpair a b = vsingle c -> a = c /\ b = c.
Proof.
  intros a b c H. split.
  - assert (Ha : a ∈ vpair a b) by (apply (proj2 (vpair_spec a b a)); left; reflexivity).
    rewrite H in Ha. exact (proj1 (vsingle_spec c a) Ha).
  - assert (Hb : b ∈ vpair a b) by (apply (proj2 (vpair_spec a b b)); right; reflexivity).
    rewrite H in Hb. exact (proj1 (vsingle_spec c b) Hb).
Qed.

Lemma kpair_inj : forall a b c d, kpair a b = kpair c d -> a = c /\ b = d.
Proof.
  intros a b c d H.
  assert (Hac : a = c).
  { assert (Hs : vsingle a ∈ kpair a b)
      by (apply (proj2 (kpair_mem a b (vsingle a))); left; reflexivity).
    rewrite H in Hs. apply (proj1 (kpair_mem c d (vsingle a))) in Hs.
    destruct Hs as [Hs | Hs].
    - exact (vsingle_inj a c Hs).
    - symmetry in Hs. destruct (vpair_single c d a Hs) as [Hc _]. symmetry. exact Hc. }
  split; [ exact Hac | ].
  subst c. rename H into E.  (* E : kpair a b = kpair a d *)
  assert (H1 : vpair a b ∈ kpair a b)
    by (apply (proj2 (kpair_mem a b (vpair a b))); right; reflexivity).
  rewrite E in H1. apply (proj1 (kpair_mem a d (vpair a b))) in H1.
  destruct H1 as [H1 | H1].
  - (* vpair a b = vsingle a, so b = a *)
    destruct (vpair_single a b a H1) as [_ Hba].
    assert (H2 : vpair a d ∈ kpair a d)
      by (apply (proj2 (kpair_mem a d (vpair a d))); right; reflexivity).
    rewrite <- E in H2. apply (proj1 (kpair_mem a b (vpair a d))) in H2.
    destruct H2 as [H2 | H2].
    + destruct (vpair_single a d a H2) as [_ Hda].
      rewrite Hba, Hda. reflexivity.
    + assert (Hd : d ∈ vpair a d)
        by (apply (proj2 (vpair_spec a d d)); right; reflexivity).
      rewrite H2 in Hd. apply (proj1 (vpair_spec a b d)) in Hd.
      destruct Hd as [Hd | Hd].
      * rewrite Hba, Hd. reflexivity.
      * symmetry. exact Hd.
  - (* vpair a b = vpair a d *)
    assert (Hb : b ∈ vpair a b)
      by (apply (proj2 (vpair_spec a b b)); right; reflexivity).
    rewrite H1 in Hb. apply (proj1 (vpair_spec a d b)) in Hb.
    destruct Hb as [Hb | Hb]; [ | exact Hb ].
    (* b = a *)
    assert (Hd : d ∈ vpair a d)
      by (apply (proj2 (vpair_spec a d d)); right; reflexivity).
    rewrite <- H1 in Hd. apply (proj1 (vpair_spec a b d)) in Hd.
    destruct Hd as [Hd | Hd].
    + rewrite Hb, Hd. reflexivity.
    + symmetry. exact Hd.
Qed.

(* ------------- formula macros with satisfaction specs ----------------- *)
(*  Each macro is a genuine `form`; its spec lemma says exactly what its  *)
(*  satisfaction means.  Arguments are ABSOLUTE de Bruijn slots in the    *)
(*  environment at the use site; under an extra binder every slot shifts  *)
(*  by one, which the call sites account for explicitly.  After its spec  *)
(*  is proved a macro is made locally opaque, so `cbn` in later proofs    *)
(*  reduces `Sat` through the surrounding connectives but leaves the      *)
(*  macro folded, ready for its spec lemma.                               *)

(* "slot i is the empty set" *)
Definition fEmptyF (i : nat) : form := fAll (fImp (fMem 0 (S i)) fBot).

Lemma fEmptyF_spec : forall ee i, SAT ee (fEmptyF i) <-> ee i = vempty.
Proof.
  intros ee i. unfold fEmptyF. cbn. split.
  - intro H. apply AxExt. intro x. split.
    + intro Hx. exfalso. exact (H x Hx).
    + intro Hx. exfalso. exact (vempty_spec x Hx).
  - intros Heq d Hd. rewrite Heq in Hd. exact (vempty_spec d Hd).
Qed.
Local Opaque fEmptyF.

(* "slot i contains exactly the objects satisfying phi"; phi is read under
   the newly bound slot 0. *)
Definition fSetByF (i : nat) (phi : form) : form :=
  fAll (fIff (fMem 0 (S i)) phi).

Lemma fSetByF_sat :
  forall ee i phi,
    SAT ee (fSetByF i phi) <->
    forall x, x ∈ ee i <-> SAT (SC x ee) phi.
Proof.
  intros ee i phi. unfold fSetByF, fIff. cbn. tauto.
Qed.

(* Extensionality turns a semantic specification of the element formula
   into the equality asserted by fSetByF. *)
Lemma fSetByF_spec :
  forall ee i phi b,
    (forall x, SAT (SC x ee) phi <-> x ∈ b) ->
    (SAT ee (fSetByF i phi) <-> ee i = b).
Proof.
  intros ee i phi b Hphi. rewrite fSetByF_sat. split.
  - intro H. apply AxExt. intro x.
    specialize (H x). specialize (Hphi x). tauto.
  - intros Heq x. rewrite Heq. specialize (Hphi x). tauto.
Qed.
Local Opaque fSetByF.

(* "slot i = {slot j}" *)
Definition fSingF (i j : nat) : form :=
  fSetByF i (fEq 0 (S j)).

Lemma fSingF_spec : forall ee i j, SAT ee (fSingF i j) <-> ee i = vsingle (ee j).
Proof.
  intros ee i j. unfold fSingF. apply fSetByF_spec. intro x. cbn.
  symmetry. apply vsingle_spec.
Qed.
Local Opaque fSingF.

(* "slot i = {slot j, slot k}" *)
Definition fUPairF (i j k : nat) : form :=
  fSetByF i (fOr (fEq 0 (S j)) (fEq 0 (S k))).

Lemma fUPairF_spec :
  forall ee i j k, SAT ee (fUPairF i j k) <-> ee i = vpair (ee j) (ee k).
Proof.
  intros ee i j k. unfold fUPairF. apply fSetByF_spec. intro x. cbn.
  symmetry. apply vpair_spec.
Qed.
Local Opaque fUPairF.

(* "slot i = <slot j, slot k>"  (Kuratowski) *)
Definition fKPairF (i j k : nat) : form :=
  fSetByF i (fOr (fSingF 0 (S j)) (fUPairF 0 (S j) (S k))).

Lemma fKPairF_spec :
  forall ee i j k, SAT ee (fKPairF i j k) <-> ee i = kpair (ee j) (ee k).
Proof.
  intros ee i j k. unfold fKPairF. apply fSetByF_spec. intro q. cbn [Sat].
  rewrite (fSingF_spec (SC q ee) 0 (S j)).
  rewrite (fUPairF_spec (SC q ee) 0 (S j) (S k)). cbn.
  symmetry. apply kpair_mem.
Qed.
Local Opaque fKPairF.

(* "<slot i, slot j> ∈ slot k" *)
Definition fPairMemF (i j k : nat) : form :=
  fEx (fAnd (fKPairF 0 (S i) (S j)) (fMem 0 (S k))).

Lemma fPairMemF_spec :
  forall ee i j k, SAT ee (fPairMemF i j k) <-> kpair (ee i) (ee j) ∈ ee k.
Proof.
  intros ee i j k. unfold fPairMemF. cbn. split.
  - intros [d [Hd Hmem]].
    apply (proj1 (fKPairF_spec (SC d ee) 0 (S i) (S j))) in Hd.
    cbn in Hd. rewrite Hd in Hmem. exact Hmem.
  - intro H. exists (kpair (ee i) (ee j)). split.
    + apply (proj2 (fKPairF_spec (SC (kpair (ee i) (ee j)) ee) 0 (S i) (S j))).
      reflexivity.
    + exact H.
Qed.
Local Opaque fPairMemF.

(* "slot i = successor of slot j" *)
Definition fSuccF (i j : nat) : form :=
  fSetByF i (fOr (fMem 0 (S j)) (fEq 0 (S j))).

Lemma fSuccF_spec :
  forall ee i j, SAT ee (fSuccF i j) <-> ee i = vsucc (ee j).
Proof.
  intros ee i j. unfold fSuccF. apply fSetByF_spec. intro x. cbn.
  symmetry. apply vsucc_spec.
Qed.
Local Opaque fSuccF.

(* ----------------------- the internal omega --------------------------- *)

Definition inductiveV (c : V) : Prop :=
  vempty ∈ c /\ forall y, y ∈ c -> vsucc y ∈ c.

(* "slot i is an inductive set" *)
Definition fInd (i : nat) : form :=
  fAnd (fEx (fAnd (fEmptyF 0) (fMem 0 (S i))))
       (fAll (fImp (fMem 0 (S i)) (fEx (fAnd (fSuccF 0 1) (fMem 0 (S (S i))))))).

Lemma fInd_spec : forall ee i, SAT ee (fInd i) <-> inductiveV (ee i).
Proof.
  intros ee i. unfold fInd, inductiveV. cbn. split.
  - intros [[z [Hz Hzi]] Hsucc]. split.
    + apply (proj1 (fEmptyF_spec (SC z ee) 0)) in Hz. cbn in Hz.
      rewrite Hz in Hzi. exact Hzi.
    + intros y Hy. destruct (Hsucc y Hy) as [t [Ht Hti]].
      apply (proj1 (fSuccF_spec (SC t (SC y ee)) 0 1)) in Ht. cbn in Ht.
      rewrite Ht in Hti. exact Hti.
  - intros [He Hsucc]. split.
    + exists vempty. split.
      * apply (proj2 (fEmptyF_spec (SC vempty ee) 0)). reflexivity.
      * exact He.
    + intros y Hy. exists (vsucc y). split.
      * apply (proj2 (fSuccF_spec (SC (vsucc y) (SC y ee)) 0 1)). reflexivity.
      * exact (Hsucc y Hy).
Qed.
Local Opaque fInd.

Definition omega : V :=
  sepD (fAll (fImp (fInd 0) (fMem 1 0))) (fun _ => vempty) InfSet.

Lemma omega_spec :
  forall n, n ∈ omega <-> (n ∈ InfSet /\ forall c, inductiveV c -> n ∈ c).
Proof.
  intro n. unfold omega.
  rewrite (sepD_spec (fAll (fImp (fInd 0) (fMem 1 0))) (fun _ => vempty) InfSet n).
  cbn. split.
  - intros [HI H]. split; [ exact HI | ]. intros c Hc. apply (H c).
    apply (proj2 (fInd_spec (SC c (SC n (fun _ => vempty))) 0)). exact Hc.
  - intros [HI H]. split; [ exact HI | ]. intros c Hc. apply (H c).
    apply (proj1 (fInd_spec (SC c (SC n (fun _ => vempty))) 0)) in Hc. exact Hc.
Qed.

Lemma vempty_in_omega : vempty ∈ omega.
Proof.
  apply (proj2 (omega_spec vempty)). split.
  - exact empty_in_InfSet.
  - intros c [Hc _]. exact Hc.
Qed.

Lemma omega_succ : forall n, n ∈ omega -> vsucc n ∈ omega.
Proof.
  intros n Hn. apply (proj1 (omega_spec n)) in Hn. destruct Hn as [HI H].
  apply (proj2 (omega_spec (vsucc n))). split.
  - exact (vsucc_in_InfSet n HI).
  - intros c Hc. destruct Hc as [Hce Hcs]. apply Hcs. apply (H c). split; assumption.
Qed.

(* THE DEFINABLE-INDUCTION SCHEMA: internal induction over omega for any  *)
(* property given by a formula phi with parameters in the environment e.  *)
Lemma omega_ind :
  forall (phi : form) (e : nat -> V),
    SAT (SC vempty e) phi ->
    (forall n, n ∈ omega -> SAT (SC n e) phi -> SAT (SC (vsucc n) e) phi) ->
    forall n, n ∈ omega -> SAT (SC n e) phi.
Proof.
  intros phi e Hbase Hstep n Hn.
  pose (A := sepD phi e omega).
  assert (HA : forall x, x ∈ A <-> (x ∈ omega /\ SAT (SC x e) phi))
    by (intro x; exact (sepD_spec phi e omega x)).
  assert (HAind : inductiveV A).
  { split.
    - apply (proj2 (HA vempty)). split; [ exact vempty_in_omega | exact Hbase ].
    - intros y Hy. apply (proj1 (HA y)) in Hy. destruct Hy as [Hyo Hyp].
      apply (proj2 (HA (vsucc y))). split.
      + exact (omega_succ y Hyo).
      + exact (Hstep y Hyo Hyp). }
  destruct (proj1 (omega_spec n) Hn) as [_ Hleast].
  exact (proj2 (proj1 (HA n) (Hleast A HAind))).
Qed.

(* -------------------- arithmetic of internal naturals ----------------- *)

Lemma nat_transitive :
  forall n, n ∈ omega -> forall y, y ∈ n -> forall x, x ∈ y -> x ∈ n.
Proof.
  assert (H : forall n, n ∈ omega ->
              SAT (SC n (fun _ => omega))
                  (fAll (fImp (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 2)))))).
  { apply omega_ind.
    - cbn. intros y Hy. exfalso. exact (vempty_spec y Hy).
    - intros n Hn IH. cbn in IH |- *. intros y Hy x Hx.
      apply (proj1 (vsucc_spec n y)) in Hy.
      apply (proj2 (vsucc_spec n x)). left.
      destruct Hy as [Hy | Hy].
      + exact (IH y Hy x Hx).
      + rewrite Hy in Hx. exact Hx. }
  intros n Hn y Hy x Hx. specialize (H n Hn). cbn in H. exact (H y Hy x Hx).
Qed.

Lemma nat_no_self : forall n, n ∈ omega -> ~ n ∈ n.
Proof.
  assert (H : forall n, n ∈ omega ->
              SAT (SC n (fun _ => omega)) (fImp (fMem 0 0) fBot)).
  { apply omega_ind.
    - cbn. intro Hd. exact (vempty_spec vempty Hd).
    - intros n Hn IH. cbn in IH |- *. intro Hd.
      apply (proj1 (vsucc_spec n (vsucc n))) in Hd. destruct Hd as [Hd | Heq].
      + apply IH. exact (nat_transitive n Hn (vsucc n) Hd n (vsucc_self n)).
      + apply IH. pose proof (vsucc_self n) as Hs. rewrite Heq in Hs. exact Hs. }
  intros n Hn. specialize (H n Hn). cbn in H. exact H.
Qed.

Lemma succ_le_lt :
  forall m, m ∈ omega -> forall k, (vsucc k ∈ m \/ vsucc k = m) -> k ∈ m.
Proof.
  intros m Hm k [Hin | Heq].
  - exact (nat_transitive m Hm (vsucc k) Hin k (vsucc_self k)).
  - pose proof (vsucc_self k) as Hs. rewrite Heq in Hs. exact Hs.
Qed.

Lemma succ_not_le : forall m, m ∈ omega -> ~ (vsucc m ∈ m \/ vsucc m = m).
Proof.
  intros m Hm H. exact (nat_no_self m Hm (succ_le_lt m Hm m H)).
Qed.

Lemma succ_not_in_self : forall m, m ∈ omega -> ~ vsucc m ∈ vsucc m.
Proof. intros m Hm. exact (nat_no_self (vsucc m) (omega_succ m Hm)). Qed.

Lemma succ_inj_nat :
  forall m, m ∈ omega -> forall k, (k ∈ m \/ k = m) -> vsucc k = vsucc m -> k = m.
Proof.
  intros m Hm k Hkm Heq. destruct Hkm as [Hk | Hk]; [ | exact Hk ].
  exfalso.
  pose proof (vsucc_self m) as Hs. rewrite <- Heq in Hs.
  apply (proj1 (vsucc_spec k m)) in Hs. destruct Hs as [Hmk | Hme].
  - exact (nat_no_self m Hm (nat_transitive m Hm k Hk m Hmk)).
  - rewrite Hme in Hk. rewrite Hme in Hm. exact (nat_no_self k Hm Hk).
Qed.

(* ===================================================================== *)
(*  The closure construction for a fixed definable relation.              *)
(*  psiC is the formula defining the relation (argument slots 0, 1;       *)
(*  parameters in eC from slot 2 up), RC its semantic reading.            *)
(* ===================================================================== *)

Section FixedRelation.

Variable psiC : form.
Variable eC : nat -> V.
Local Notation RC := (relOf V mem psiC eC).
Hypothesis HSL : SetLike V mem RC.

(* -------- the canonical one-step operator gstep, via FO Replacement --- *)

Definition bnd (x : V) : V :=
  proj1_sig (constructive_indefinite_description _ (HSL x)).
Lemma bnd_spec : forall x z, RC z x -> z ∈ bnd x.
Proof.
  intros x z H.
  exact (proj2_sig (constructive_indefinite_description _ (HSL x)) z H).
Qed.

(* the CANONICAL set of RC-predecessors of v (canonical by Extensionality,
   even though the bound used to carve it is chosen by Hilbert epsilon) *)
Definition predSet (v : V) : V := sepD psiC (SC v eC) (bnd v).
Lemma predSet_spec : forall v z, z ∈ predSet v <-> RC z v.
Proof.
  intros v z. unfold predSet.
  rewrite (sepD_spec psiC (SC v eC) (bnd v) z). split.
  - intros [_ H]. exact H.
  - intro H. split; [ exact (bnd_spec v z H) | exact H ].
Qed.

(* the graph formula "slot 0 = the set of RC-predecessors of slot 1"      *)
Definition rPS : nat -> nat :=
  fun n => match n with 0 => 0 | 1 => 2 | S (S k) => S (S (S k)) end.
Definition psiPS : form := fSetByF 0 (rename rPS psiC).

Lemma psiPS_rel :
  forall y x, relOf V mem psiPS eC y x <-> (forall u, u ∈ y <-> RC u x).
Proof.
  intros y x. unfold relOf at 1. unfold psiPS.
  rewrite fSetByF_sat. cbn.
  assert (Hin : forall u,
      Sat V mem (SC u (SC y (SC x eC))) (rename rPS psiC) <-> RC u x).
  { intro u.
    apply (Sat_rename_relOf V mem psiC rPS
             (SC u (SC y (SC x eC))) eC u x).
    intro n. destruct n as [| [| k]]; reflexivity. }
  split.
  - intros H u. specialize (H u). specialize (Hin u). tauto.
  - intros H u. specialize (H u). specialize (Hin u). tauto.
Qed.

Lemma psiPS_functional : Functional V (relOf V mem psiPS eC).
Proof.
  intros x y1 y2 H1 H2.
  pose proof (proj1 (psiPS_rel y1 x) H1) as G1.
  pose proof (proj1 (psiPS_rel y2 x) H2) as G2.
  apply AxExt. intro u. rewrite (G1 u), (G2 u). tauto.
Qed.

Definition predImg (t : V) : V :=
  proj1_sig (constructive_indefinite_description _
               (AxRepl psiPS eC psiPS_functional t)).
Lemma predImg_spec :
  forall t y, y ∈ predImg t <-> exists x, x ∈ t /\ relOf V mem psiPS eC y x.
Proof.
  intro t.
  exact (proj2_sig (constructive_indefinite_description _
                      (AxRepl psiPS eC psiPS_functional t))).
Qed.

(*  g(t) = t ∪ { u : exists v ∈ t, RC u v } — the textbook one-step
    closure operator, built canonically (no choice of bounds leaks in).  *)
Definition gstep (t : V) : V := vcup t (vunion (predImg t)).

Lemma gstep_spec :
  forall t u, u ∈ gstep t <-> (u ∈ t \/ exists v, v ∈ t /\ RC u v).
Proof.
  intros t u. unfold gstep.
  rewrite (vcup_spec t (vunion (predImg t)) u).
  rewrite (vunion_spec (predImg t) u).
  split.
  - intros [Hl | [y [Huy Hy]]]; [ left; exact Hl | right ].
    apply (proj1 (predImg_spec t y)) in Hy. destruct Hy as [x [Hxt Hrel]].
    pose proof (proj1 (psiPS_rel y x) Hrel) as Hrel'.
    exists x. split; [ exact Hxt | ]. apply (proj1 (Hrel' u)). exact Huy.
  - intros [Hl | [v [Hvt Hrc]]]; [ left; exact Hl | right ].
    exists (predSet v). split.
    + apply (proj2 (predSet_spec v u)). exact Hrc.
    + apply (proj2 (predImg_spec t (predSet v))).
      exists v. split; [ exact Hvt | ].
      apply (proj2 (psiPS_rel (predSet v) v)).
      intro w. exact (predSet_spec v w).
Qed.

(* --------- relation- and step-macros, with the parameter block --------- *)
(*  Formulas below mention psiC, so their specs carry the side condition   *)
(*  that the environment holds eC's values from slot `off` upward.         *)

Definition rRF (i j off : nat) : nat -> nat :=
  fun n => match n with 0 => i | 1 => j | S (S k) => off + k end.

(* "RC (slot i) (slot j)" *)
Definition fRF (i j off : nat) : form := rename (rRF i j off) psiC.

Lemma fRF_spec :
  forall ee i j off,
    (forall k, ee (off + k) = eC k) ->
    (SAT ee (fRF i j off) <-> RC (ee i) (ee j)).
Proof.
  intros ee i j off Hoff. unfold fRF.
  apply (Sat_rename_relOf V mem psiC (rRF i j off) ee eC (ee i) (ee j)).
  intro n. destruct n as [| [| k]]; cbn.
  - reflexivity.
  - reflexivity.
  - exact (Hoff k).
Qed.
Local Opaque fRF.

(* "slot i = gstep (slot j)" *)
Definition fStepF (i j off : nat) : form :=
  fSetByF i
    (fOr (fMem 0 (S j))
      (fEx (fAnd (fMem 0 (S (S j))) (fRF 1 0 (S (S off)))))).

Lemma fStepF_spec :
  forall ee i j off,
    (forall k, ee (off + k) = eC k) ->
    (SAT ee (fStepF i j off) <-> ee i = gstep (ee j)).
Proof.
  intros ee i j off Hoff. unfold fStepF.
  assert (Hin : forall u v,
      Sat V mem (SC v (SC u ee)) (fRF 1 0 (S (S off))) <-> RC u v).
  { intros u v.
    apply (fRF_spec (SC v (SC u ee)) 1 0 (S (S off))).
    intro k. exact (Hoff k). }
  apply fSetByF_spec. intro u. cbn [Sat]. rewrite (gstep_spec (ee j) u).
  split; intros [Hl | [v [Hv HR]]].
  - left. exact Hl.
  - right. exists v. split; [ exact Hv | ]. apply (proj1 (Hin u v)). exact HR.
  - left. exact Hl.
  - right. exists v. split; [ exact Hv | ]. apply (proj2 (Hin u v)). exact HR.
Qed.
Local Opaque fStepF.

(* ------------------- the approximation predicate ---------------------- *)

Variable s : V.   (* the seed whose closure we are building *)

(*  Approx f m: f is (the graph of) a function with domain {0,...,m}      *)
(*  recording the iteration s, g(s), g(g(s)), ...                         *)
Definition Approx (f m : V) : Prop :=
  (forall k y y', kpair k y ∈ f -> kpair k y' ∈ f -> y = y') /\
  (forall k y, kpair k y ∈ f -> (k ∈ m \/ k = m)) /\
  kpair vempty s ∈ f /\
  (forall k, (k ∈ m \/ k = m) -> exists y, kpair k y ∈ f) /\
  (forall k t y, k ∈ m -> kpair k t ∈ f -> kpair (vsucc k) y ∈ f ->
                 y = gstep t).

(* clause 1: functionality *)
Definition fAppC1 (f_i : nat) : form :=
  fAll (fAll (fAll (fImp (fAnd (fPairMemF 2 1 (3 + f_i))
                               (fPairMemF 2 0 (3 + f_i)))
                         (fEq 1 0)))).

Lemma fAppC1_spec :
  forall ee f_i,
    SAT ee (fAppC1 f_i) <->
    (forall k y y', kpair k y ∈ ee f_i -> kpair k y' ∈ ee f_i -> y = y').
Proof.
  intros ee f_i. unfold fAppC1. cbn. split.
  - intros H k y y' H1 H2.
    apply (H k y y'). split.
    + apply (proj2 (fPairMemF_spec (SC y' (SC y (SC k ee))) 2 1 (3 + f_i))).
      exact H1.
    + apply (proj2 (fPairMemF_spec (SC y' (SC y (SC k ee))) 2 0 (3 + f_i))).
      exact H2.
  - intros H k y y' [H1 H2].
    apply (proj1 (fPairMemF_spec (SC y' (SC y (SC k ee))) 2 1 (3 + f_i))) in H1.
    apply (proj1 (fPairMemF_spec (SC y' (SC y (SC k ee))) 2 0 (3 + f_i))) in H2.
    exact (H k y y' H1 H2).
Qed.
Local Opaque fAppC1.

(* clause 2: the domain is bounded by {0,...,m} *)
Definition fAppC2 (f_i m_i : nat) : form :=
  fAll (fAll (fImp (fPairMemF 1 0 (2 + f_i))
                   (fOr (fMem 1 (2 + m_i)) (fEq 1 (2 + m_i))))).

Lemma fAppC2_spec :
  forall ee f_i m_i,
    SAT ee (fAppC2 f_i m_i) <->
    (forall k y, kpair k y ∈ ee f_i -> (k ∈ ee m_i \/ k = ee m_i)).
Proof.
  intros ee f_i m_i. unfold fAppC2. cbn. split.
  - intros H k y Hp.
    apply (H k y).
    apply (proj2 (fPairMemF_spec (SC y (SC k ee)) 1 0 (2 + f_i))). exact Hp.
  - intros H k y Hp.
    apply (proj1 (fPairMemF_spec (SC y (SC k ee)) 1 0 (2 + f_i))) in Hp.
    exact (H k y Hp).
Qed.
Local Opaque fAppC2.

(* clause 3: the base pair <0, s> is recorded *)
Definition fAppC3 (f_i s_i : nat) : form :=
  fEx (fAnd (fEmptyF 0) (fPairMemF 0 (S s_i) (S f_i))).

Lemma fAppC3_spec :
  forall ee f_i s_i,
    SAT ee (fAppC3 f_i s_i) <-> kpair vempty (ee s_i) ∈ ee f_i.
Proof.
  intros ee f_i s_i. unfold fAppC3. cbn. split.
  - intros [z [Hz Hp]].
    apply (proj1 (fEmptyF_spec (SC z ee) 0)) in Hz. cbn in Hz.
    apply (proj1 (fPairMemF_spec (SC z ee) 0 (S s_i) (S f_i))) in Hp.
    cbn in Hp. rewrite Hz in Hp. exact Hp.
  - intro H. exists vempty. split.
    + apply (proj2 (fEmptyF_spec (SC vempty ee) 0)). reflexivity.
    + apply (proj2 (fPairMemF_spec (SC vempty ee) 0 (S s_i) (S f_i))). exact H.
Qed.
Local Opaque fAppC3.

(* clause 4: the domain covers {0,...,m} *)
Definition fAppC4 (f_i m_i : nat) : form :=
  fAll (fImp (fOr (fMem 0 (S m_i)) (fEq 0 (S m_i)))
             (fEx (fPairMemF 1 0 (2 + f_i)))).

Lemma fAppC4_spec :
  forall ee f_i m_i,
    SAT ee (fAppC4 f_i m_i) <->
    (forall k, (k ∈ ee m_i \/ k = ee m_i) -> exists y, kpair k y ∈ ee f_i).
Proof.
  intros ee f_i m_i. unfold fAppC4. cbn. split.
  - intros H k Hk. destruct (H k Hk) as [y Hy].
    exists y.
    apply (proj1 (fPairMemF_spec (SC y (SC k ee)) 1 0 (2 + f_i))) in Hy. exact Hy.
  - intros H k Hk. destruct (H k Hk) as [y Hy].
    exists y.
    apply (proj2 (fPairMemF_spec (SC y (SC k ee)) 1 0 (2 + f_i))). exact Hy.
Qed.
Local Opaque fAppC4.

(* clause 5: the recurrence f(k+1) = gstep (f k) *)
Definition fAppC5 (f_i m_i off : nat) : form :=
  fAll (fAll (fAll (fAll
    (fImp (fAnd (fAnd (fAnd (fMem 3 (4 + m_i)) (fSuccF 2 3))
                      (fPairMemF 3 1 (4 + f_i)))
                (fPairMemF 2 0 (4 + f_i)))
          (fStepF 0 1 (4 + off)))))).

Lemma fAppC5_spec :
  forall ee f_i m_i off,
    (forall k, ee (off + k) = eC k) ->
    (SAT ee (fAppC5 f_i m_i off) <->
     (forall k t y, k ∈ ee m_i -> kpair k t ∈ ee f_i ->
                    kpair (vsucc k) y ∈ ee f_i -> y = gstep t)).
Proof.
  intros ee f_i m_i off Hoff. unfold fAppC5. cbn. split.
  - intros H k t y Hk H1 H2.
    assert (Hc : Sat V mem (SC y (SC t (SC (vsucc k) (SC k ee))))
                     (fStepF 0 1 (4 + off))).
    { apply (H k (vsucc k) t y). split; [ split; [ split | ] | ].
      - exact Hk.
      - apply (proj2 (fSuccF_spec (SC y (SC t (SC (vsucc k) (SC k ee)))) 2 3)).
        reflexivity.
      - apply (proj2 (fPairMemF_spec (SC y (SC t (SC (vsucc k) (SC k ee)))) 3 1 (4 + f_i))).
        exact H1.
      - apply (proj2 (fPairMemF_spec (SC y (SC t (SC (vsucc k) (SC k ee)))) 2 0 (4 + f_i))).
        exact H2. }
    apply (proj1 (fStepF_spec (SC y (SC t (SC (vsucc k) (SC k ee)))) 0 1 (4 + off)
                    (fun k0 => Hoff k0))) in Hc.
    exact Hc.
  - intros H d d0 d1 d2 [[[Hk Hsucc] HP1] HP2].
    apply (proj1 (fSuccF_spec (SC d2 (SC d1 (SC d0 (SC d ee)))) 2 3)) in Hsucc.
    cbn in Hsucc.
    apply (proj1 (fPairMemF_spec (SC d2 (SC d1 (SC d0 (SC d ee)))) 3 1 (4 + f_i))) in HP1.
    apply (proj1 (fPairMemF_spec (SC d2 (SC d1 (SC d0 (SC d ee)))) 2 0 (4 + f_i))) in HP2.
    cbn in HP1, HP2.
    apply (proj2 (fStepF_spec (SC d2 (SC d1 (SC d0 (SC d ee)))) 0 1 (4 + off)
                    (fun k0 => Hoff k0))).
    cbn. rewrite Hsucc in HP2. exact (H d d1 d2 Hk HP1 HP2).
Qed.
Local Opaque fAppC5.

(* the full approximation formula *)
Definition fApproxF (f_i m_i s_i off : nat) : form :=
  fAnd (fAppC1 f_i)
       (fAnd (fAppC2 f_i m_i)
             (fAnd (fAppC3 f_i s_i)
                   (fAnd (fAppC4 f_i m_i) (fAppC5 f_i m_i off)))).

Lemma fApproxF_spec :
  forall ee f_i m_i s_i off,
    (forall k, ee (off + k) = eC k) -> ee s_i = s ->
    (SAT ee (fApproxF f_i m_i s_i off) <-> Approx (ee f_i) (ee m_i)).
Proof.
  intros ee f_i m_i s_i off Hoff Hs. unfold fApproxF. cbn.
  rewrite (fAppC1_spec ee f_i).
  rewrite (fAppC2_spec ee f_i m_i).
  rewrite (fAppC3_spec ee f_i s_i).
  rewrite (fAppC4_spec ee f_i m_i).
  rewrite (fAppC5_spec ee f_i m_i off Hoff).
  rewrite Hs. unfold Approx. tauto.
Qed.
Local Opaque fApproxF.

(* ---------------- the stage relation Theta and its formula ------------- *)

Definition Theta (y m : V) : Prop :=
  m ∈ omega /\ exists f, Approx f m /\ kpair m y ∈ f.

Definition fThetaF (y_i m_i s_i om_i off : nat) : form :=
  fAnd (fMem m_i om_i)
       (fEx (fAnd (fApproxF 0 (S m_i) (S s_i) (S off))
                  (fPairMemF (S m_i) (S y_i) 0))).

Lemma fThetaF_spec :
  forall ee y_i m_i s_i om_i off,
    (forall k, ee (off + k) = eC k) -> ee s_i = s -> ee om_i = omega ->
    (SAT ee (fThetaF y_i m_i s_i om_i off) <-> Theta (ee y_i) (ee m_i)).
Proof.
  intros ee y_i m_i s_i om_i off Hoff Hs Hom.
  unfold fThetaF, Theta. cbn. rewrite Hom. split.
  - intros [Hm [f [HA HP]]]. split; [ exact Hm | ]. exists f. split.
    + apply (proj1 (fApproxF_spec (SC f ee) 0 (S m_i) (S s_i) (S off)
                      (fun k => Hoff k) Hs)) in HA.
      exact HA.
    + apply (proj1 (fPairMemF_spec (SC f ee) (S m_i) (S y_i) 0)) in HP.
      exact HP.
  - intros [Hm [f [HA HP]]]. split; [ exact Hm | ]. exists f. split.
    + apply (proj2 (fApproxF_spec (SC f ee) 0 (S m_i) (S s_i) (S off)
                      (fun k => Hoff k) Hs)).
      exact HA.
    + apply (proj2 (fPairMemF_spec (SC f ee) (S m_i) (S y_i) 0)).
      exact HP.
Qed.
Local Opaque fThetaF.

Definition psiTheta : form := fThetaF 0 1 2 3 4.
Definition eTheta : nat -> V := SC s (SC omega eC).

Lemma theta_rel :
  forall y m, relOf V mem psiTheta eTheta y m <-> Theta y m.
Proof.
  intros y m. unfold relOf, psiTheta, eTheta.
  exact (fThetaF_spec (SC y (SC m (SC s (SC omega eC)))) 0 1 2 3 4
           (fun k => eq_refl) eq_refl eq_refl).
Qed.

(* ------------------- existence of approximations ---------------------- *)

Lemma Approx_base : Approx (vsingle (kpair vempty s)) vempty.
Proof.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros k y y' H1 H2.
    apply (proj1 (vsingle_spec (kpair vempty s) (kpair k y))) in H1.
    apply (proj1 (vsingle_spec (kpair vempty s) (kpair k y'))) in H2.
    destruct (kpair_inj k y vempty s H1) as [_ Hy].
    destruct (kpair_inj k y' vempty s H2) as [_ Hy'].
    rewrite Hy, Hy'. reflexivity.
  - intros k y H.
    apply (proj1 (vsingle_spec (kpair vempty s) (kpair k y))) in H.
    destruct (kpair_inj k y vempty s H) as [Hk _]. right. exact Hk.
  - apply (proj2 (vsingle_spec (kpair vempty s) (kpair vempty s))). reflexivity.
  - intros k [Hk | Hk].
    + exfalso. exact (vempty_spec k Hk).
    + exists s. rewrite Hk.
      apply (proj2 (vsingle_spec (kpair vempty s) (kpair vempty s))). reflexivity.
  - intros k t y Hk _ _. exfalso. exact (vempty_spec k Hk).
Qed.

Lemma Approx_extend :
  forall m f t, m ∈ omega -> Approx f m -> kpair m t ∈ f ->
    Approx (vcup f (vsingle (kpair (vsucc m) (gstep t)))) (vsucc m).
Proof.
  intros m f t Hm HA Hmt.
  pose proof HA as [C1 [C2 [C3 [C4 C5]]]].
  set (newp := kpair (vsucc m) (gstep t)).
  assert (Hf' : forall x, x ∈ vcup f (vsingle newp) <-> (x ∈ f \/ x = newp)).
  { intro x. rewrite (vcup_spec f (vsingle newp) x).
    rewrite (vsingle_spec newp x). tauto. }
  split; [ | split; [ | split; [ | split ] ] ].
  - (* functionality *)
    intros k y y' H1 H2.
    apply (proj1 (Hf' (kpair k y))) in H1. apply (proj1 (Hf' (kpair k y'))) in H2.
    destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
    + exact (C1 k y y' H1 H2).
    + destruct (kpair_inj k y' (vsucc m) (gstep t) H2) as [Hk _].
      exfalso. rewrite Hk in H1.
      exact (succ_not_le m Hm (C2 (vsucc m) y H1)).
    + destruct (kpair_inj k y (vsucc m) (gstep t) H1) as [Hk _].
      exfalso. rewrite Hk in H2.
      exact (succ_not_le m Hm (C2 (vsucc m) y' H2)).
    + destruct (kpair_inj k y (vsucc m) (gstep t) H1) as [_ Hy].
      destruct (kpair_inj k y' (vsucc m) (gstep t) H2) as [_ Hy'].
      rewrite Hy, Hy'. reflexivity.
  - (* domain bound *)
    intros k y H. apply (proj1 (Hf' (kpair k y))) in H. destruct H as [H | H].
    + destruct (C2 k y H) as [Hk | Hk]; left; apply (proj2 (vsucc_spec m k));
        [ left; exact Hk | right; exact Hk ].
    + destruct (kpair_inj k y (vsucc m) (gstep t) H) as [Hk _]. right. exact Hk.
  - (* base pair *)
    apply (proj2 (Hf' (kpair vempty s))). left. exact C3.
  - (* domain coverage *)
    intros k [Hk | Hk].
    + apply (proj1 (vsucc_spec m k)) in Hk. destruct (C4 k Hk) as [y Hy].
      exists y. apply (proj2 (Hf' (kpair k y))). left. exact Hy.
    + exists (gstep t). apply (proj2 (Hf' (kpair k (gstep t)))). right.
      rewrite Hk. reflexivity.
  - (* recurrence *)
    intros k t' y Hk H1 H2.
    apply (proj1 (Hf' (kpair k t'))) in H1.
    apply (proj1 (Hf' (kpair (vsucc k) y))) in H2.
    apply (proj1 (vsucc_spec m k)) in Hk.
    destruct H1 as [H1 | H1].
    + destruct H2 as [H2 | H2].
      * (* both pairs in the old f *)
        destruct Hk as [Hk | Hk].
        -- exact (C5 k t' y Hk H1 H2).
        -- exfalso. rewrite Hk in H2.
           exact (succ_not_le m Hm (C2 (vsucc m) y H2)).
      * (* the successor pair is the new one *)
        destruct (kpair_inj (vsucc k) y (vsucc m) (gstep t) H2) as [Hsk Hy].
        assert (Hkm : k = m) by exact (succ_inj_nat m Hm k Hk Hsk).
        rewrite Hkm in H1.
        assert (Htt : t' = t) by exact (C1 m t' t H1 Hmt).
        rewrite Hy, Htt. reflexivity.
    + (* the k-pair is the new one: impossible, vsucc m is not below itself *)
      destruct (kpair_inj k t' (vsucc m) (gstep t) H1) as [Hk' _].
      exfalso. rewrite Hk' in Hk. exact (succ_not_le m Hm Hk).
Qed.

Lemma Approx_exists : forall m, m ∈ omega -> exists f, Approx f m.
Proof.
  assert (Hbr : forall n,
      SAT (SC n (SC s eC)) (fEx (fApproxF 0 1 2 3)) <-> exists f, Approx f n).
  { intro n. cbn. split.
    - intros [f Hf]. exists f.
      apply (proj1 (fApproxF_spec (SC f (SC n (SC s eC))) 0 1 2 3
                      (fun k => eq_refl) eq_refl)) in Hf.
      exact Hf.
    - intros [f Hf]. exists f.
      apply (proj2 (fApproxF_spec (SC f (SC n (SC s eC))) 0 1 2 3
                      (fun k => eq_refl) eq_refl)).
      exact Hf. }
  intros m Hm. apply (proj1 (Hbr m)).
  apply (omega_ind (fEx (fApproxF 0 1 2 3)) (SC s eC)); [ | | exact Hm ].
  - apply (proj2 (Hbr vempty)).
    exists (vsingle (kpair vempty s)). exact Approx_base.
  - intros n Hn IH. apply (proj2 (Hbr (vsucc n))).
    apply (proj1 (Hbr n)) in IH. destruct IH as [f Hf].
    pose proof Hf as [_ [_ [_ [C4 _]]]].
    destruct (C4 n (or_intror eq_refl)) as [t Ht].
    exists (vcup f (vsingle (kpair (vsucc n) (gstep t)))).
    exact (Approx_extend n f t Hn Hf Ht).
Qed.

(* -------------------- uniqueness (agreement) --------------------------- *)

Lemma Approx_agree :
  forall m, m ∈ omega -> forall f f', Approx f m -> Approx f' m ->
  forall k, k ∈ omega ->
  forall y y', (k ∈ m \/ k = m) ->
    kpair k y ∈ f -> kpair k y' ∈ f' -> y = y'.
Proof.
  intros m Hm f f' Hf Hf'.
  pose (eUq := SC f (SC f' (SC m (fun _ => vempty)))).
  pose (phiUq := fAll (fAll (fImp
                   (fAnd (fAnd (fOr (fMem 2 5) (fEq 2 5)) (fPairMemF 2 1 3))
                         (fPairMemF 2 0 4))
                   (fEq 1 0)))).
  assert (Hbr : forall k,
      SAT (SC k eUq) phiUq <->
      (forall y y', (k ∈ m \/ k = m) ->
         kpair k y ∈ f -> kpair k y' ∈ f' -> y = y')).
  { intro k. unfold phiUq, eUq. cbn. split.
    - intros H y y' Hkm H1 H2.
      apply (H y y'). split; [ split; [ exact Hkm | ] | ].
      + apply (proj2 (fPairMemF_spec
                        (SC y' (SC y (SC k (SC f (SC f' (SC m (fun _ => vempty))))))) 2 1 3)).
        exact H1.
      + apply (proj2 (fPairMemF_spec
                        (SC y' (SC y (SC k (SC f (SC f' (SC m (fun _ => vempty))))))) 2 0 4)).
        exact H2.
    - intros H y y' [[Hkm HP1] HP2].
      apply (proj1 (fPairMemF_spec
                      (SC y' (SC y (SC k (SC f (SC f' (SC m (fun _ => vempty))))))) 2 1 3)) in HP1.
      apply (proj1 (fPairMemF_spec
                      (SC y' (SC y (SC k (SC f (SC f' (SC m (fun _ => vempty))))))) 2 0 4)) in HP2.
      exact (H y y' Hkm HP1 HP2). }
  intros k Hk. apply (proj1 (Hbr k)).
  apply (omega_ind phiUq eUq); [ | | exact Hk ].
  - (* base: both functions record s at 0 *)
    apply (proj2 (Hbr vempty)). intros y y' _ H1 H2.
    pose proof Hf  as [C1  [_ [C3  _]]].
    pose proof Hf' as [C1' [_ [C3' _]]].
    transitivity s.
    + exact (C1 vempty y s H1 C3).
    + symmetry. exact (C1' vempty y' s H2 C3').
  - (* step *)
    intros n Hn IH. apply (proj2 (Hbr (vsucc n))).
    pose proof (proj1 (Hbr n) IH) as IH'. clear IH. rename IH' into IH.
    intros y y' Hsm H1 H2.
    assert (Hnm : n ∈ m) by exact (succ_le_lt m Hm n Hsm).
    pose proof Hf  as [C1  [C2  [C3  [C4  C5 ]]]].
    pose proof Hf' as [C1' [C2' [C3' [C4' C5']]]].
    destruct (C4  n (or_introl Hnm)) as [t  Ht ].
    destruct (C4' n (or_introl Hnm)) as [t' Ht'].
    assert (Htt : t = t') by exact (IH t t' (or_introl Hnm) Ht Ht').
    rewrite (C5 n t y Hnm Ht H1). rewrite (C5' n t' y' Hnm Ht' H2).
    rewrite Htt. reflexivity.
Qed.

Lemma theta_functional : Functional V (relOf V mem psiTheta eTheta).
Proof.
  intros m y1 y2 H1 H2.
  apply (proj1 (theta_rel y1 m)) in H1. apply (proj1 (theta_rel y2 m)) in H2.
  destruct H1 as [Hm [f [Hf Hp]]]. destruct H2 as [_ [f' [Hf' Hp']]].
  exact (Approx_agree m Hm f f' Hf Hf' m Hm y1 y2 (or_intror eq_refl) Hp Hp').
Qed.

(* --------- collect the stages with FO Replacement, take the union ------ *)

Definition Wimg : V :=
  proj1_sig (constructive_indefinite_description _
               (AxRepl psiTheta eTheta theta_functional omega)).
Lemma Wimg_spec :
  forall y, y ∈ Wimg <-> exists mm, mm ∈ omega /\ relOf V mem psiTheta eTheta y mm.
Proof.
  exact (proj2_sig (constructive_indefinite_description _
                      (AxRepl psiTheta eTheta theta_functional omega))).
Qed.

Theorem ClosureFO_of_ZF :
  exists w, Sub V mem s w /\ (forall u v, RC u v -> v ∈ w -> u ∈ w).
Proof.
  exists (vunion Wimg). split.
  - (* s is contained: s itself is stage 0 *)
    intros x Hx. apply (proj2 (vunion_spec Wimg x)). exists s. split; [ exact Hx | ].
    apply (proj2 (Wimg_spec s)). exists vempty. split; [ exact vempty_in_omega | ].
    apply (proj2 (theta_rel s vempty)). split; [ exact vempty_in_omega | ].
    exists (vsingle (kpair vempty s)). split; [ exact Approx_base | ].
    apply (proj2 (vsingle_spec (kpair vempty s) (kpair vempty s))). reflexivity.
  - (* closed under RC-predecessors: step to the next stage *)
    intros u v HR Hv.
    apply (proj1 (vunion_spec Wimg v)) in Hv. destruct Hv as [y [Hvy HyW]].
    apply (proj1 (Wimg_spec y)) in HyW. destruct HyW as [mm [Hmm HT]].
    apply (proj1 (theta_rel y mm)) in HT. destruct HT as [_ [f [Hf Hp]]].
    apply (proj2 (vunion_spec Wimg u)). exists (gstep y). split.
    + apply (proj2 (gstep_spec y u)). right. exists v. split; [ exact Hvy | exact HR ].
    + apply (proj2 (Wimg_spec (gstep y))).
      exists (vsucc mm). split; [ exact (omega_succ mm Hmm) | ].
      apply (proj2 (theta_rel (gstep y) (vsucc mm))).
      split; [ exact (omega_succ mm Hmm) | ].
      exists (vcup f (vsingle (kpair (vsucc mm) (gstep y)))). split.
      * exact (Approx_extend mm f y Hmm Hf Hp).
      * apply (proj2 (vcup_spec f (vsingle (kpair (vsucc mm) (gstep y)))
                        (kpair (vsucc mm) (gstep y)))).
        right.
        apply (proj2 (vsingle_spec (kpair (vsucc mm) (gstep y))
                        (kpair (vsucc mm) (gstep y)))).
        reflexivity.
Qed.

End FixedRelation.

End ZfModel.

Check ClosureFO_of_ZF.
