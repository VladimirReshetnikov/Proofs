(**
  Peano arithmetic has two non-isomorphic first-order models.

  The models below are raw arithmetic structures satisfying every sealed PA
  axiom, including every first-order induction instance.  We deliberately do
  not use the stronger [PA.Model] record, whose induction field ranges over
  all Coq predicates and therefore makes that interface categorical.
*)

From Stdlib Require Import Arith Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  CanonicalSelector CanonicalSelectorPA FiniteBetaCoding NonstandardHFFin.

Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.

Module PATwoNonisomorphicModels.

(** A genuine first-order PA model at the raw semantic boundary. *)
Record FirstOrderPAModel : Type := {
  first_order_raw : RawPAModel;
  first_order_satisfies_pa : RawPASatisfies first_order_raw
}.

(** Isomorphism of raw arithmetic structures. *)
Record RawPAIso (M N : RawPAModel) : Type := {
  iso_to : M -> N;
  iso_inv : N -> M;
  iso_left_inv : forall x, iso_inv (iso_to x) = x;
  iso_right_inv : forall y, iso_to (iso_inv y) = y;
  iso_map_zero : iso_to (raw_zero M) = raw_zero N;
  iso_map_succ : forall x,
    iso_to (raw_succ M x) = raw_succ N (iso_to x);
  iso_map_add : forall x y,
    iso_to (raw_add M x y) = raw_add N (iso_to x) (iso_to y);
  iso_map_mul : forall x y,
    iso_to (raw_mul M x y) = raw_mul N (iso_to x) (iso_to y)
}.

Lemma iso_map_rawNumeralValue : forall (M N : RawPAModel)
    (i : RawPAIso M N) n,
  iso_to M N i (rawNumeralValue M n) = rawNumeralValue N n.
Proof.
  intros M N i n. induction n as [|n ih].
  - exact (iso_map_zero M N i).
  - simpl. rewrite iso_map_succ. now rewrite ih.
Qed.

Definition NumeralGenerated (M : RawPAModel) : Prop :=
  forall x : M, exists n, x = rawNumeralValue M n.

Lemma numeralGenerated_of_iso : forall (M N : RawPAModel),
  RawPAIso M N -> NumeralGenerated M -> NumeralGenerated N.
Proof.
  intros M N i hM y.
  destruct (hM (iso_inv M N i y)) as [n hn].
  exists n.
  rewrite <- (iso_right_inv M N i y).
  rewrite hn.
  apply iso_map_rawNumeralValue.
Qed.

(** The raw presentation of the usual natural-number structure. *)
Definition natRawPAModel : RawPAModel :=
  {| raw_carrier := nat;
     raw_zero := 0;
     raw_succ := S;
     raw_add := Nat.add;
     raw_mul := Nat.mul |}.

Lemma nat_raw_term_eval : forall (e : nat -> nat) t,
  raw_term_eval natRawPAModel e t = PA.Term.eval PA.natModel e t.
Proof.
  intros e t. induction t; simpl; congruence.
Qed.

Lemma nat_raw_formula_sat : forall (e : nat -> nat) phi,
  raw_formula_sat natRawPAModel e phi <->
  PA.Formula.Sat PA.natModel e phi.
Proof.
  intros e phi. revert e.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; intro e; simpl.
  - rewrite !nat_raw_term_eval. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros h x.
    + apply (proj1 (IHa (scons _ x e))). exact (h x).
    + apply (proj2 (IHa (scons _ x e))). exact (h x).
  - split; intros [x hx]; exists x.
    + apply (proj1 (IHa (scons _ x e))). exact hx.
    + apply (proj2 (IHa (scons _ x e))). exact hx.
Qed.

Lemma nat_raw_satisfies_pa : RawPASatisfies natRawPAModel.
Proof.
  intros phi hphi e.
  apply (proj2 (nat_raw_formula_sat e phi)).
  exact (PA.Formula.sat_axiom_s PA.natModel e phi hphi).
Qed.

Definition standardPAModel : FirstOrderPAModel :=
  {| first_order_raw := natRawPAModel;
     first_order_satisfies_pa := nat_raw_satisfies_pa |}.

Lemma nat_rawNumeralValue : forall n,
  rawNumeralValue natRawPAModel n = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma standardPAModel_numeralGenerated :
  NumeralGenerated (first_order_raw standardPAModel).
Proof.
  intro n. exists n. symmetry. apply nat_rawNumeralValue.
Qed.

(** Compactness supplies a PA model with an element above every standard
    numeral, hence a model which is not numeral-generated. *)
Theorem nonstandardPAModel_exists :
  exists (M : FirstOrderPAModel) (star : first_order_raw M),
    (forall n,
      rawLt (first_order_raw M)
        (rawNumeralValue (first_order_raw M) n) star) /\
    ~ NumeralGenerated (first_order_raw M).
Proof.
  destruct nonstandardHFFin_raw_bounds_exists as [V [H [star hstar]]].
  pose (R := fofamRawPAModel H).
  assert (hPA : RawPASatisfies R).
  { unfold R. apply fofam_raw_pa_satisfies. }
  assert (habove : forall n, rawLt R (rawNumeralValue R n) star).
  {
    intro n.
    assert (hsat : raw_formula_sat R (fun _ => star)
        (PA.Formula.ltTermAt (PA.Term.numeral n) (PA.tVar 0))).
    {
      unfold R.
      apply (proj2 (raw_formula_sat_fofam V H (fun _ => star) _)).
      exact (hstar n).
    }
    pose proof (proj1 (raw_sat_ltTermAt_iff R
      (PA.Term.numeral n) (PA.tVar 0) (fun _ => star)) hsat) as hlt.
    rewrite raw_term_eval_numeral in hlt.
    cbn [raw_term_eval] in hlt.
    exact hlt.
  }
  exists {| first_order_raw := R; first_order_satisfies_pa := hPA |}, star.
  split.
  - exact habove.
  - intro hgenerated.
    destruct (hgenerated star) as [n hn].
    change (star = rawNumeralValue R n) in hn.
    pose proof (habove n) as hlt.
    rewrite <- hn in hlt.
    exact (raw_not_lt_self R hPA star hlt).
Qed.

(** Headline theorem: first-order Peano arithmetic has at least two
    non-isomorphic models. *)
Theorem peano_arithmetic_has_two_nonisomorphic_models :
  exists M N : FirstOrderPAModel,
    ~ inhabited (RawPAIso (first_order_raw M) (first_order_raw N)).
Proof.
  destruct nonstandardPAModel_exists as [N [star [habove hnotGenerated]]].
  exists standardPAModel, N.
  intros [i].
  apply hnotGenerated.
  exact (numeralGenerated_of_iso _ _ i
    standardPAModel_numeralGenerated).
Qed.

End PATwoNonisomorphicModels.
