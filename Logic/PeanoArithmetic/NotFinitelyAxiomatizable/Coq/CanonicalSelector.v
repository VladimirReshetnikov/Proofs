(**
  A definably functional selector for finite Skolem programs.

  The semantic hull construction only needs an arbitrary witness selector,
  but the later program-evaluator argument needs a PA formula whose output is
  unique.  We therefore select the least witness in the arithmetic order,
  and select zero when no witness exists.  This file isolates exactly the two
  ambient arithmetic principles needed by that construction: definable
  least-number and trichotomy of the strict order.
*)

From Stdlib Require Import List Arith Lia Classical ClassicalEpsilon.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction FiniteSkolemHull.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.

Module PACanonicalSelector.

Definition rawLt (M : RawPAModel) (x y : M) : Prop :=
  exists d : M, raw_add M x (raw_succ M d) = y.

Definition rawCanonicalSelectorGraph (M : RawPAModel)
    (body : PA.formula) (env : nat -> M) (x : M) : Prop :=
  (raw_formula_sat M (scons M x env) body /\
   forall y, rawLt M y x ->
     ~ raw_formula_sat M (scons M y env) body) \/
  ((~ exists y, raw_formula_sat M (scons M y env) body) /\
   x = raw_zero M).

Definition RawDefinableLeastNumber (M : RawPAModel) : Prop :=
  forall (body : PA.formula) (env : nat -> M),
    (exists x, raw_formula_sat M (scons M x env) body) ->
    exists x,
      raw_formula_sat M (scons M x env) body /\
      forall y, rawLt M y x ->
        ~ raw_formula_sat M (scons M y env) body.

Definition RawLtTrichotomy (M : RawPAModel) : Prop :=
  forall x y : M, x = y \/ rawLt M x y \/ rawLt M y x.

Lemma rawCanonicalSelectorGraph_total : forall M,
  RawDefinableLeastNumber M ->
  forall body env, exists x, rawCanonicalSelectorGraph M body env x.
Proof.
  intros M hleast body env.
  destruct (classic (exists x,
      raw_formula_sat M (scons M x env) body)) as [hex | hnone].
  - destruct (hleast body env hex) as [x [hx hmin]].
    exists x. left. split; assumption.
  - exists (raw_zero M). right. split; [exact hnone | reflexivity].
Qed.

Lemma rawCanonicalSelectorGraph_functional : forall M,
  RawLtTrichotomy M ->
  forall body env x y,
    rawCanonicalSelectorGraph M body env x ->
    rawCanonicalSelectorGraph M body env y ->
    x = y.
Proof.
  intros M htri body env x y hx hy.
  destruct hx as [[hxb hxmin] | [hnone hx0]];
    destruct hy as [[hyb hymin] | [hnone' hy0]].
  - destruct (htri x y) as [hxy | [hlt | hgt]].
    + exact hxy.
    + exfalso. exact (hymin x hlt hxb).
    + exfalso. exact (hxmin y hgt hyb).
  - exfalso. exact (hnone' (ex_intro _ x hxb)).
  - exfalso. exact (hnone (ex_intro _ y hyb)).
  - now rewrite hx0, hy0.
Qed.

Definition rawCanonicalSelector (M : RawPAModel)
    (body : PA.formula) (env : nat -> M) : M :=
  epsilon (inhabits (raw_zero M))
    (rawCanonicalSelectorGraph M body env).

Lemma rawCanonicalSelector_graph : forall M,
  RawDefinableLeastNumber M ->
  forall body env,
    rawCanonicalSelectorGraph M body env
      (rawCanonicalSelector M body env).
Proof.
  intros M hleast body env.
  unfold rawCanonicalSelector.
  apply epsilon_spec.
  exact (rawCanonicalSelectorGraph_total M hleast body env).
Qed.

Lemma rawCanonicalSelector_witnesses : forall M,
  RawDefinableLeastNumber M ->
  SelectorWitnesses M (rawCanonicalSelector M).
Proof.
  intros M hleast body env hex.
  pose proof (rawCanonicalSelector_graph M hleast body env) as hg.
  destruct hg as [[hsat _] | [hnone _]].
  - exact hsat.
  - exfalso. exact (hnone hex).
Qed.

Lemma rawCanonicalSelector_graph_unique : forall M,
  RawDefinableLeastNumber M ->
  RawLtTrichotomy M ->
  forall body env x,
    rawCanonicalSelectorGraph M body env x <->
    x = rawCanonicalSelector M body env.
Proof.
  intros M hleast htri body env x.
  split.
  - intro hx.
    apply (rawCanonicalSelectorGraph_functional M htri body env x
      (rawCanonicalSelector M body env) hx).
    apply rawCanonicalSelector_graph. exact hleast.
  - intro hx. subst x.
    apply rawCanonicalSelector_graph. exact hleast.
Qed.

(** Under a newly bound probe variable, variable 0 remains the probe while
    every old parameter is shifted past the selected output at variable 1. *)
Definition skipSelectedOutput (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (S k)
  end.

Definition selectorProbeBody (body : PA.formula) : PA.formula :=
  PA.Formula.rename skipSelectedOutput body.

Lemma raw_selectorProbeBody : forall M body env x y,
  raw_formula_sat M (scons M y (scons M x env))
      (selectorProbeBody body) <->
  raw_formula_sat M (scons M y env) body.
Proof.
  intros M body env x y.
  unfold selectorProbeBody.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext.
  intros [|n]; reflexivity.
Qed.

(** Formula with free variable 0 as output and the original parameters from
    variable 1 onward. *)
Definition canonicalSelectorFormula (body : PA.formula) : PA.formula :=
  PA.pOr
    (PA.pAnd body
      (PA.pAll (PA.pImp
        (PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 1))
        (PA.pImp (selectorProbeBody body) PA.pBot))))
    (PA.pAnd (PA.pEq (PA.tVar 0) PA.tZero)
      (PA.pAll (PA.pImp (selectorProbeBody body) PA.pBot))).

Lemma raw_ltTermAt_vars : forall M env x y,
  raw_formula_sat M (scons M y (scons M x env))
      (PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 1)) <->
  rawLt M y x.
Proof.
  intros M env x y.
  unfold PA.Formula.ltTermAt, rawLt.
  simpl.
  reflexivity.
Qed.

Theorem raw_canonicalSelectorFormula : forall M body env x,
  raw_formula_sat M (scons M x env)
      (canonicalSelectorFormula body) <->
  rawCanonicalSelectorGraph M body env x.
Proof.
  intros M body env x.
  unfold canonicalSelectorFormula, rawCanonicalSelectorGraph.
  cbn [raw_formula_sat].
  split.
  - intros [[hbody hminimal] | [hx0 hnone]].
    + left. split; [exact hbody |].
      intros y hy hbodyY.
      apply (hminimal y).
      * apply (proj2 (raw_ltTermAt_vars M env x y)). exact hy.
      * apply (proj2 (raw_selectorProbeBody M body env x y)).
        exact hbodyY.
    + right. split.
      * intros [y hy].
        apply (hnone y).
        apply (proj2 (raw_selectorProbeBody M body env x y)).
        exact hy.
      * exact hx0.
  - intros [[hbody hminimal] | [hnone hx0]].
    + left. split; [exact hbody |].
      intros y hlt hbodyY.
      apply (hminimal y).
      * apply (proj1 (raw_ltTermAt_vars M env x y)). exact hlt.
      * apply (proj1 (raw_selectorProbeBody M body env x y)).
        exact hbodyY.
    + right. split; [exact hx0 |].
      intros y hy.
      apply hnone. exists y.
      apply (proj1 (raw_selectorProbeBody M body env x y)).
      exact hy.
Qed.

Theorem raw_canonicalSelectorFormula_unique : forall M,
  RawDefinableLeastNumber M ->
  RawLtTrichotomy M ->
  forall body env x,
    raw_formula_sat M (scons M x env)
        (canonicalSelectorFormula body) <->
    x = rawCanonicalSelector M body env.
Proof.
  intros M hleast htri body env x.
  rewrite raw_canonicalSelectorFormula.
  apply rawCanonicalSelector_graph_unique; assumption.
Qed.

Corollary raw_canonicalSelectorFormula_exists_unique : forall M,
  RawDefinableLeastNumber M ->
  RawLtTrichotomy M ->
  forall body env,
    exists! x,
      raw_formula_sat M (scons M x env)
        (canonicalSelectorFormula body).
Proof.
  intros M hleast htri body env.
  exists (rawCanonicalSelector M body env).
  split.
  - apply (proj2 (raw_canonicalSelectorFormula_unique M hleast htri
      body env (rawCanonicalSelector M body env))).
    reflexivity.
  - intros x hx.
    symmetry.
    apply (proj1 (raw_canonicalSelectorFormula_unique M hleast htri
      body env x)).
    exact hx.
Qed.

(** The canonical least/default selector is now a valid instance of the
    fragment-transfer theorem. *)
Corollary canonicalSkolemHull_satisfies_rank_fragment :
  forall (M : RawPAModel) (seed : M) n,
    RawDefinableLeastNumber M ->
    RawModelSatisfies M PA.Formula.Ax_s ->
    RawModelSatisfies
      (skolemHullRawModel M seed (S (rankFragmentSyntaxRank n))
        (rawCanonicalSelector M))
      (PARankFragment n).
Proof.
  intros M seed n hleast hPA.
  apply skolemHull_satisfies_rank_fragment.
  - apply rawCanonicalSelector_witnesses. exact hleast.
  - exact hPA.
Qed.

End PACanonicalSelector.
