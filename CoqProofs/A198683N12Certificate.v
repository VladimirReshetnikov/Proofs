(*
  Coq port of the generic core of LeanProofs/A198683N12Certificate.lean.

  # The `A198683(12)` endgame, generic core: the witness and the decision tree

  The Lean module packages the entire remaining uncertainty about the disputed
  OEIS value `A198683(12)` into

  1. one wide hypothesis -- the partition witness `N12PartitionWitness`, the
     mechanically-checkable-in-principle certificate that the
     interval-arithmetic pipeline of the research corpus is designed to
     produce -- and
  2. two narrow hypotheses -- the near-`1` split (`v25 <> v1404`) and
     `OverflowIsolated` -- each a single concrete separation question about
     explicit closed-form complex numbers,

  and proves the complete decision tree relating them to the count of
  distinct parenthesization values.  This Coq module is that development
  PARAMETERIZED over the value domain: a value type `V`, an evaluation
  function `evalV : Expr -> V` on the shared lexical power-tower syntax of
  `CoqProofs/PowTower.v`, and three distinguished values `v25`, `v1404`,
  `vOverflow`.  The complex-number instantiation (Coquelicot `C`, with
  principal-power evaluation and the concrete tower constants `nearOne25`,
  `nearOne1404`, `overflowCandidate12`) arrives in a companion module; nothing
  here depends on which instance is supplied.

  Because the intended value domain has no decidable equality, the Lean
  `Set.ncard` count is replaced by a RELATIONAL distinct-count specification
  over lists:

    DistinctCount l n  :=  exists d, NoDup d /\ SameElements d l /\ length d = n

  and its basic theory (existence, uniqueness, congruence, and the two bound
  transfer principles) is proved classically at the head of the module.

  ## The decision tree

  Writing `S` for the near-`1` split (`v25 <> v1404`) and `O` for
  `OverflowIsolated w`, and letting `n` satisfy `A198683Count n` (the
  distinct count of `map evalV (parenthesizations 12)`):

  | `S`?  | `O`?  | conclusion                       | theorem                                     |
  |-------|-------|----------------------------------|---------------------------------------------|
  | --    | --    | `n = 2924 \/ n = 2925 \/ n = 2926` | `a198683_twelve_mem`                        |
  | yes   | --    | `n = 2925 \/ n = 2926`             | `a198683_twelve_mem_of_split`               |
  | --    | yes   | `n = 2925 \/ n = 2926`             | `a198683_twelve_mem_of_overflowIsolated`    |
  | yes   | yes   | `n = 2926`                         | `a198683_twelve_eq_2926`                    |
  | yes   | no    | `n = 2925`                         | `a198683_twelve_eq_2925_of_overflowCollision` |
  | no    | yes   | `n = 2925`                         | `a198683_twelve_eq_2925_of_merge`           |
  | no    | no    | `n = 2924`                         | `a198683_twelve_eq_2924`                    |

  The community-expected value is `2926`; the table shows exactly which two
  separation facts that expectation rests on.

  Proof architecture, mirroring the Lean module with explicit lists in place
  of `Finset` images:

  * the rep-value list `map classValue (seq 0 2926)` has the same elements as
    the full evaluation list (fields `covers` + `reps_mem`), so both bounds
    transfer to the 2926-representative list;
  * upper bounds drop duplicated indices from the rep list by exhibiting an
    explicit smaller covering list (`removeIdx`), mirroring Lean's
    `image_univ_subset_diff` argument;
  * lower bounds exhibit an explicit `NoDup` value sublist -- the
    representatives outside the structurally uncertain indices are
    pairwise-distinct-valued by the `separated` field -- and compare lengths
    with `NoDup_incl_length`.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import Classical.
From LeanProofsCoq Require Import PowTower.

Import ListNotations.

Module LeanProofs.
Module A198683N12Certificate.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.

(* ======================================================================
   Part 1 -- the relational distinct-count specification and its theory

   `DistinctCount l n` says that `n` is the number of distinct elements of
   `l`, witnessed by an explicit duplicate-free list with the same elements.
   No decidable equality on the element type is assumed; existence of the
   dedup witness is classical (`classic` decides membership of the head in
   the tail), and uniqueness is `NoDup_incl_length` both ways.
   ====================================================================== *)

Definition SameElements {V : Type} (l l' : list V) : Prop :=
  incl l l' /\ incl l' l.

Definition DistinctCount {V : Type} (l : list V) (n : nat) : Prop :=
  exists d, NoDup d /\ SameElements d l /\ length d = n.

Theorem distinctCount_exists {V : Type} (l : list V) :
    exists n, DistinctCount l n.
Proof.
  induction l as [|a l IH].
  - exists 0. exists (@nil V).
    split; [constructor|].
    split; [split; apply incl_refl|reflexivity].
  - destruct IH as [n [d [Hnd [[Hdl Hld] Hlen]]]].
    destruct (classic (In a l)) as [Hin|Hnin].
    + (* the head is already in the tail: the same witness deduplicates *)
      exists n. exists d.
      split; [exact Hnd|].
      split; [split|exact Hlen].
      * intros x Hx. right. apply Hdl. exact Hx.
      * intros x [He|Hx]; [rewrite <- He; apply Hld; exact Hin|].
        apply Hld. exact Hx.
    + (* fresh head: cons it onto the witness *)
      exists (S n). exists (a :: d).
      split.
      { constructor; [|exact Hnd].
        intro Hain. apply Hnin. apply Hdl. exact Hain. }
      split; [split|].
      * intros x [He|Hx]; [rewrite <- He; left; reflexivity|].
        right. apply Hdl. exact Hx.
      * intros x [He|Hx]; [rewrite <- He; left; reflexivity|].
        right. apply Hld. exact Hx.
      * simpl. rewrite Hlen. reflexivity.
Qed.

Theorem distinctCount_unique {V : Type} (l : list V) (n m : nat) :
    DistinctCount l n -> DistinctCount l m -> n = m.
Proof.
  intros [d [Hnd [[Hdl Hld] Hlen]]] [d' [Hnd' [[Hdl' Hld'] Hlen']]].
  subst n m.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length; [exact Hnd|].
    eapply incl_tran; [exact Hdl|exact Hld'].
  - apply NoDup_incl_length; [exact Hnd'|].
    eapply incl_tran; [exact Hdl'|exact Hld].
Qed.

Theorem distinctCount_congr {V : Type} (l l' : list V) (n : nat) :
    SameElements l l' -> DistinctCount l n -> DistinctCount l' n.
Proof.
  intros [Hll' Hl'l] [d [Hnd [[Hdl Hld] Hlen]]].
  exists d.
  split; [exact Hnd|].
  split; [split|exact Hlen].
  - eapply incl_tran; [exact Hdl|exact Hll'].
  - eapply incl_tran; [exact Hl'l|exact Hld].
Qed.

(* Lower-bound transfer: any duplicate-free list drawn from `l` is no longer
   than the distinct count of `l`. *)
Theorem distinctCount_ge_witness {V : Type} (l d : list V) (n : nat) :
    NoDup d -> incl d l -> DistinctCount l n -> length d <= n.
Proof.
  intros Hnd Hincl [d0 [Hnd0 [[Hd0l Hld0] Hlen]]].
  subst n.
  apply NoDup_incl_length; [exact Hnd|].
  eapply incl_tran; [exact Hincl|exact Hld0].
Qed.

(* Upper-bound transfer: any list covering `l` is at least as long as the
   distinct count of `l` (no `NoDup` needed on the cover). *)
Theorem distinctCount_le_cover {V : Type} (l c : list V) (n : nat) :
    incl l c -> DistinctCount l n -> n <= length c.
Proof.
  intros Hincl [d [Hnd [[Hdl Hld] Hlen]]].
  subst n.
  apply NoDup_incl_length; [exact Hnd|].
  eapply incl_tran; [exact Hdl|exact Hincl].
Qed.

(* ======================================================================
   Part 2 -- index-list helpers

   `removeIdx i l` deletes every occurrence of the index `i` from a list of
   natural numbers; on `NoDup` lists it removes exactly one element.  These
   are the explicit-list counterparts of Lean's `Set.univ \ s` index
   exclusions.
   ====================================================================== *)

Definition removeIdx (i : nat) (l : list nat) : list nat :=
  filter (fun k => negb (Nat.eqb k i)) l.

Lemma removeIdx_cons (i a : nat) (l : list nat) :
    removeIdx i (a :: l) =
      if Nat.eqb a i then removeIdx i l else a :: removeIdx i l.
Proof.
  unfold removeIdx. simpl. destruct (Nat.eqb a i); reflexivity.
Qed.

Lemma removeIdx_In (i : nat) (l : list nat) (k : nat) :
    In k (removeIdx i l) <-> In k l /\ k <> i.
Proof.
  unfold removeIdx.
  rewrite filter_In, Bool.negb_true_iff, Nat.eqb_neq.
  reflexivity.
Qed.

Lemma removeIdx_NoDup (i : nat) (l : list nat) :
    NoDup l -> NoDup (removeIdx i l).
Proof.
  apply NoDup_filter.
Qed.

Lemma removeIdx_not_In (i : nat) (l : list nat) :
    ~ In i l -> removeIdx i l = l.
Proof.
  induction l as [|a l IH]; intros H.
  - reflexivity.
  - rewrite removeIdx_cons.
    destruct (Nat.eqb a i) eqn:E.
    + apply Nat.eqb_eq in E. subst a.
      exfalso. apply H. left. reflexivity.
    + f_equal. apply IH. intro Hin. apply H. right. exact Hin.
Qed.

Lemma In_length_pos {A : Type} (x : A) (l : list A) :
    In x l -> 1 <= length l.
Proof.
  destruct l; simpl; [tauto|lia].
Qed.

Lemma removeIdx_length (i : nat) (l : list nat) :
    NoDup l -> In i l -> length (removeIdx i l) = length l - 1.
Proof.
  induction l as [|a l IH]; intros Hnd Hin; [destruct Hin|].
  inversion Hnd as [|? ? Hnin Hnd']; subst.
  rewrite removeIdx_cons.
  destruct (Nat.eqb a i) eqn:E.
  - apply Nat.eqb_eq in E. subst a.
    rewrite removeIdx_not_In by exact Hnin.
    simpl. lia.
  - apply Nat.eqb_neq in E.
    destruct Hin as [Ha|Hin]; [congruence|].
    simpl. rewrite IH by assumption.
    pose proof (In_length_pos i l Hin).
    lia.
Qed.

(* ======================================================================
   Part 3 -- the witness and the decision tree, parameterized over the
   value domain
   ====================================================================== *)

Section Certificate.

Variable V : Type.
(* Will be instantiated by principal-power evaluation on Coquelicot's C. *)
Variable evalV : PT.Expr -> V.
(* The three distinguished class values: the two near-`1` towers and the
   overflow candidate. *)
Variables v25 v1404 vOverflow : V.

(*
  The wide certificate: a claimed system of 2926 class representatives for
  the n = 12 principal-power values, with

  * `reps_mem`/`covers` -- every representative is a genuine lexical
    parenthesization of twelve atoms, and every parenthesization takes the
    same value as some representative (this is where all within-class
    equalities of the probe-refined partition live);
  * `separated` -- representatives of distinct classes take distinct values,
    EXCEPT that nothing is claimed about the two structurally uncertain
    comparisons: any pair involving the overflow class, and the near-`1`
    pair `{idx25, idx1404}`;
  * the three distinguished indices are pinned to the distinguished values,
    so that the narrow hypotheses of this module are statements about
    explicit values of the instance domain.

  Indices are plain `nat`s bounded by 2926 (Coq's stand-in for Lean's
  `Fin 2926`); every field carrying an index also carries its bound.
*)
Record N12PartitionWitness : Type := {
  (* One lexical representative expression per claimed class,
     indices 0..2925. *)
  reps : nat -> PT.Expr;
  (* Every representative is a parenthesization of twelve atoms. *)
  reps_mem : forall k, k < 2926 -> In (reps k) (PT.parenthesizations 12);
  (* Every parenthesization of twelve atoms takes the value of some
     representative. *)
  covers : forall e, In e (PT.parenthesizations 12) ->
    exists k, k < 2926 /\ evalV e = evalV (reps k);
  (* The class of the near-`1` representative 25. *)
  idx25 : nat;
  (* The class of the near-`1` representatives {1404, 4239}. *)
  idx1404 : nat;
  (* The overflow class {57}. *)
  idxOverflow : nat;
  idx25_lt : idx25 < 2926;
  idx1404_lt : idx1404 < 2926;
  idxOverflow_lt : idxOverflow < 2926;
  idx25_ne_idx1404 : idx25 <> idx1404;
  idx25_ne_idxOverflow : idx25 <> idxOverflow;
  idx1404_ne_idxOverflow : idx1404 <> idxOverflow;
  (* The three distinguished classes evaluate to the distinguished values. *)
  eval_idx25 : evalV (reps idx25) = v25;
  eval_idx1404 : evalV (reps idx1404) = v1404;
  eval_idxOverflow : evalV (reps idxOverflow) = vOverflow;
  (* Cross-class separation, claimed for every pair EXCEPT the two
     structurally uncertain comparisons. *)
  separated : forall j k, j < 2926 -> k < 2926 -> j <> k ->
    j <> idxOverflow -> k <> idxOverflow ->
    ~(j = idx25 /\ k = idx1404) -> ~(j = idx1404 /\ k = idx25) ->
    evalV (reps j) <> evalV (reps k)
}.

(*
  Narrow hypothesis 2 (no miracles for the overflow class): the value of the
  overflow candidate differs from the value of every other class of the
  witness.  (Narrow hypothesis 1, the near-`1` split, is simply
  `v25 <> v1404` and needs no wrapper.)
*)
Definition OverflowIsolated (w : N12PartitionWitness) : Prop :=
  forall k, k < 2926 -> k <> idxOverflow w -> evalV (reps w k) <> vOverflow.

(* The full lexical evaluation list at n = 12. *)
Definition valueList12 : list V := map evalV (PT.parenthesizations 12).

(* `A198683Count n` -- the abstract statement "the distinct count of the
   n = 12 value list is `n`"; the instance-level `a198683 12 = n`. *)
Definition A198683Count (n : nat) : Prop := DistinctCount valueList12 n.

Theorem a198683Count_exists : exists n, A198683Count n.
Proof.
  exact (distinctCount_exists valueList12).
Qed.

Theorem a198683Count_unique (n m : nat) :
    A198683Count n -> A198683Count m -> n = m.
Proof.
  exact (distinctCount_unique valueList12 n m).
Qed.

Theorem a198683Count_exists_unique : exists! n, A198683Count n.
Proof.
  destruct a198683Count_exists as [n Hn].
  exists n. split; [exact Hn|].
  intros m Hm. exact (a198683Count_unique n m Hn Hm).
Qed.

Section WithWitness.

Variable w : N12PartitionWitness.

(* The class-value map induced by the witness (Lean's `w.value`). *)
Definition classValue (k : nat) : V := evalV (reps w k).

Lemma classValue_in_valueList (k : nat) :
    k < 2926 -> In (classValue k) valueList12.
Proof.
  intro Hk.
  unfold classValue, valueList12.
  apply in_map.
  apply (reps_mem w). exact Hk.
Qed.

(* --- The counting core: the value list has the same elements as the
       2926-representative value list, so both bounds transfer to it. --- *)

Lemma valueList12_incl_repValues :
    incl valueList12 (map classValue (seq 0 2926)).
Proof.
  intros v Hv.
  unfold valueList12 in Hv.
  apply in_map_iff in Hv. destruct Hv as [e [He Hein]].
  destruct (covers w e Hein) as [k [Hk Heq]].
  subst v.
  replace (evalV e) with (classValue k)
    by (unfold classValue; symmetry; exact Heq).
  apply in_map. apply in_seq. lia.
Qed.

Lemma repValues_incl_valueList12 :
    incl (map classValue (seq 0 2926)) valueList12.
Proof.
  intros v Hv.
  apply in_map_iff in Hv. destruct Hv as [k [Hk Hkin]].
  apply in_seq in Hkin.
  subst v.
  apply classValue_in_valueList. lia.
Qed.

Theorem valueList12_sameElements_repValues :
    SameElements valueList12 (map classValue (seq 0 2926)).
Proof.
  split; [apply valueList12_incl_repValues|apply repValues_incl_valueList12].
Qed.

(* --- Generic bound principles at the witness level --- *)

(* Upper: any index list whose values cover the value list bounds the
   count by its length. *)
Lemma count_le_of_cover (idxs : list nat) (n : nat) :
    incl valueList12 (map classValue idxs) ->
    A198683Count n -> n <= length idxs.
Proof.
  intros Hcov Hc.
  pose proof (distinctCount_le_cover _ _ _ Hcov Hc) as H.
  rewrite length_map in H. exact H.
Qed.

(* An index list with pairwise-distinct values maps to a NoDup value list. *)
Lemma NoDup_map_classValue (idxs : list nat) :
    NoDup idxs ->
    (forall j k, In j idxs -> In k idxs -> j <> k ->
      classValue j <> classValue k) ->
    NoDup (map classValue idxs).
Proof.
  induction idxs as [|a l IH]; intros Hnd Hsep.
  - constructor.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    simpl. constructor.
    + intro Hin.
      apply in_map_iff in Hin. destruct Hin as [k [Hk Hkin]].
      assert (Hak : a <> k) by (intro He; subst; contradiction).
      exact (Hsep a k (or_introl eq_refl) (or_intror Hkin) Hak (eq_sym Hk)).
    + apply IH; [exact Hnd'|].
      intros j k Hj Hk Hjk.
      apply Hsep; [right; exact Hj|right; exact Hk|exact Hjk].
Qed.

(* Lower: any duplicate-free index list of in-range indices with
   pairwise-distinct values bounds the count from below by its length. *)
Lemma count_ge_of_pairwise (idxs : list nat) (n : nat) :
    NoDup idxs ->
    (forall k, In k idxs -> k < 2926) ->
    (forall j k, In j idxs -> In k idxs -> j <> k ->
      classValue j <> classValue k) ->
    A198683Count n -> length idxs <= n.
Proof.
  intros Hnd Hlt Hsep Hc.
  rewrite <- (length_map classValue idxs).
  apply (distinctCount_ge_witness valueList12 (map classValue idxs) n).
  - apply NoDup_map_classValue; assumption.
  - intros v Hv.
    apply in_map_iff in Hv. destruct Hv as [k [Hk Hkin]].
    subst v.
    apply classValue_in_valueList.
    apply Hlt. exact Hkin.
  - exact Hc.
Qed.

(* --- Pairwise-separation lemmas: the four regimes of the decision tree --- *)

(* The raw `separated` field, phrased on `classValue`. *)
Lemma classValue_ne (j k : nat) :
    j < 2926 -> k < 2926 -> j <> k ->
    j <> idxOverflow w -> k <> idxOverflow w ->
    ~(j = idx25 w /\ k = idx1404 w) -> ~(j = idx1404 w /\ k = idx25 w) ->
    classValue j <> classValue k.
Proof.
  intros. unfold classValue. apply (separated w); assumption.
Qed.

(* With the near-`1` split, only the overflow index needs excluding. *)
Lemma classValue_ne_of_split (hsplit : v25 <> v1404) (j k : nat) :
    j < 2926 -> k < 2926 -> j <> k ->
    j <> idxOverflow w -> k <> idxOverflow w ->
    classValue j <> classValue k.
Proof.
  intros Hj Hk Hjk Hjo Hko.
  pose proof (idx25_ne_idx1404 w) as Hd.
  destruct (Nat.eq_dec j (idx25 w)) as [ej|nj].
  - destruct (Nat.eq_dec k (idx1404 w)) as [ek|nk].
    + subst. unfold classValue.
      rewrite (eval_idx25 w), (eval_idx1404 w).
      exact hsplit.
    + apply classValue_ne; try assumption; intros [H1 H2]; congruence.
  - destruct (Nat.eq_dec j (idx1404 w)) as [ej14|nj14].
    + destruct (Nat.eq_dec k (idx25 w)) as [ek25|nk25].
      * subst. unfold classValue.
        rewrite (eval_idx1404 w), (eval_idx25 w).
        intro He. apply hsplit. symmetry. exact He.
      * apply classValue_ne; try assumption; intros [H1 H2]; congruence.
    + apply classValue_ne; try assumption; intros [H1 H2]; congruence.
Qed.

(* With overflow isolation, only the near-`1` index 25 needs excluding. *)
Lemma classValue_ne_of_isolated (hiso : OverflowIsolated w) (j k : nat) :
    j < 2926 -> k < 2926 -> j <> k ->
    j <> idx25 w -> k <> idx25 w ->
    classValue j <> classValue k.
Proof.
  intros Hj Hk Hjk Hj25 Hk25.
  destruct (Nat.eq_dec j (idxOverflow w)) as [ejo|njo].
  - subst j. intro He.
    assert (Hne : k <> idxOverflow w) by congruence.
    apply (hiso k Hk Hne).
    unfold classValue in He.
    rewrite <- He. apply (eval_idxOverflow w).
  - destruct (Nat.eq_dec k (idxOverflow w)) as [eko|nko].
    + subst k. intro He.
      apply (hiso j Hj njo).
      unfold classValue in He.
      rewrite He. apply (eval_idxOverflow w).
    + apply classValue_ne; try assumption; intros [H1 H2]; congruence.
Qed.

(* With both narrow hypotheses, the value map is injective on all indices. *)
Lemma classValue_ne_full (hsplit : v25 <> v1404) (hiso : OverflowIsolated w)
    (j k : nat) :
    j < 2926 -> k < 2926 -> j <> k ->
    classValue j <> classValue k.
Proof.
  intros Hj Hk Hjk.
  destruct (Nat.eq_dec j (idxOverflow w)) as [ejo|njo].
  - subst j. intro He.
    assert (Hne : k <> idxOverflow w) by congruence.
    apply (hiso k Hk Hne).
    unfold classValue in He.
    rewrite <- He. apply (eval_idxOverflow w).
  - destruct (Nat.eq_dec k (idxOverflow w)) as [eko|nko].
    + subst k. intro He.
      apply (hiso j Hj njo).
      unfold classValue in He.
      rewrite He. apply (eval_idxOverflow w).
    + apply classValue_ne_of_split; assumption.
Qed.

(* --- The classical extraction from a failed no-miracles hypothesis --- *)

Lemma overflowCollision_witness (hcol : ~ OverflowIsolated w) :
    exists k0, k0 < 2926 /\ k0 <> idxOverflow w /\
      evalV (reps w k0) = vOverflow.
Proof.
  apply NNPP. intro Hn.
  apply hcol.
  intros k Hk Hne Heq.
  apply Hn. exists k. repeat split; assumption.
Qed.

(* --- Covering lists for the upper bounds (Lean's
       `image_univ_subset_diff` argument, with explicit rerouting) --- *)

(* Merge: the class of index 25 re-routes through `idx1404`. *)
Lemma valueList12_incl_cover_merge (hm : v25 = v1404) :
    incl valueList12 (map classValue (removeIdx (idx25 w) (seq 0 2926))).
Proof.
  intros v Hv.
  apply valueList12_incl_repValues in Hv.
  apply in_map_iff in Hv. destruct Hv as [k [Hk Hkin]].
  apply in_seq in Hkin.
  destruct (Nat.eq_dec k (idx25 w)) as [ek|nk].
  - subst k v.
    replace (classValue (idx25 w)) with (classValue (idx1404 w)).
    + apply in_map. apply removeIdx_In. split.
      * apply in_seq. pose proof (idx1404_lt w). lia.
      * intro He. apply (idx25_ne_idx1404 w). symmetry. exact He.
    + unfold classValue.
      rewrite (eval_idx25 w), (eval_idx1404 w).
      symmetry. exact hm.
  - subst v. apply in_map. apply removeIdx_In.
    split; [apply in_seq; lia|exact nk].
Qed.

(* Collision: the overflow class re-routes through its collision partner. *)
Lemma valueList12_incl_cover_collision (hcol : ~ OverflowIsolated w) :
    incl valueList12
      (map classValue (removeIdx (idxOverflow w) (seq 0 2926))).
Proof.
  destruct (overflowCollision_witness hcol) as [k0 [Hk0 [Hk0ne Hk0v]]].
  intros v Hv.
  apply valueList12_incl_repValues in Hv.
  apply in_map_iff in Hv. destruct Hv as [k [Hk Hkin]].
  apply in_seq in Hkin.
  destruct (Nat.eq_dec k (idxOverflow w)) as [ek|nk].
  - subst k v.
    replace (classValue (idxOverflow w)) with (classValue k0).
    + apply in_map. apply removeIdx_In.
      split; [apply in_seq; lia|exact Hk0ne].
    + unfold classValue.
      rewrite (eval_idxOverflow w).
      exact Hk0v.
  - subst v. apply in_map. apply removeIdx_In.
    split; [apply in_seq; lia|exact nk].
Qed.

(* Merge + collision: the class of index 25 re-routes through `idx1404`,
   and the overflow class re-routes through its collision partner --
   unless that partner is the merged class 25, in which case it re-routes
   all the way to `idx1404`. *)
Lemma valueList12_incl_cover_merge_collision
    (hm : v25 = v1404) (hcol : ~ OverflowIsolated w) :
    incl valueList12
      (map classValue
        (removeIdx (idxOverflow w) (removeIdx (idx25 w) (seq 0 2926)))).
Proof.
  destruct (overflowCollision_witness hcol) as [k0 [Hk0 [Hk0ne Hk0v]]].
  assert (Hin1404 : In (idx1404 w)
      (removeIdx (idxOverflow w) (removeIdx (idx25 w) (seq 0 2926)))).
  { apply removeIdx_In. split; [apply removeIdx_In; split|].
    - apply in_seq. pose proof (idx1404_lt w). lia.
    - intro He. apply (idx25_ne_idx1404 w). symmetry. exact He.
    - exact (idx1404_ne_idxOverflow w). }
  assert (Hval1404_25 : classValue (idx1404 w) = classValue (idx25 w)).
  { unfold classValue.
    rewrite (eval_idx25 w), (eval_idx1404 w).
    symmetry. exact hm. }
  intros v Hv.
  apply valueList12_incl_repValues in Hv.
  apply in_map_iff in Hv. destruct Hv as [k [Hk Hkin]].
  apply in_seq in Hkin.
  destruct (Nat.eq_dec k (idx25 w)) as [e25|n25].
  - subst k v.
    rewrite <- Hval1404_25.
    apply in_map. exact Hin1404.
  - destruct (Nat.eq_dec k (idxOverflow w)) as [eo|no].
    + subst k v.
      assert (Hov : classValue (idxOverflow w) = classValue k0).
      { unfold classValue.
        rewrite (eval_idxOverflow w).
        symmetry. exact Hk0v. }
      rewrite Hov.
      destruct (Nat.eq_dec k0 (idx25 w)) as [ek0|nk0].
      * subst k0.
        rewrite <- Hval1404_25.
        apply in_map. exact Hin1404.
      * apply in_map. apply removeIdx_In.
        split; [apply removeIdx_In; split|].
        -- apply in_seq. lia.
        -- exact nk0.
        -- exact Hk0ne.
    + subst v. apply in_map. apply removeIdx_In.
      split; [apply removeIdx_In; split|].
      * apply in_seq. lia.
      * exact n25.
      * exact no.
Qed.

(* --- Upper bounds --- *)

Theorem a198683Count_le_2926 (n : nat) : A198683Count n -> n <= 2926.
Proof.
  intros Hc.
  pose proof (count_le_of_cover _ _ valueList12_incl_repValues Hc) as H.
  rewrite length_seq in H.
  exact H.
Qed.

Theorem a198683Count_le_2925_of_merge (hm : v25 = v1404) (n : nat) :
    A198683Count n -> n <= 2925.
Proof.
  intros Hc.
  pose proof (count_le_of_cover _ _ (valueList12_incl_cover_merge hm) Hc)
    as H.
  rewrite removeIdx_length in H;
    [ rewrite length_seq in H; lia
    | apply seq_NoDup
    | apply in_seq; pose proof (idx25_lt w); lia ].
Qed.

Theorem a198683Count_le_2925_of_overflowCollision
    (hcol : ~ OverflowIsolated w) (n : nat) :
    A198683Count n -> n <= 2925.
Proof.
  intros Hc.
  pose proof
    (count_le_of_cover _ _ (valueList12_incl_cover_collision hcol) Hc) as H.
  rewrite removeIdx_length in H;
    [ rewrite length_seq in H; lia
    | apply seq_NoDup
    | apply in_seq; pose proof (idxOverflow_lt w); lia ].
Qed.

Theorem a198683Count_le_2924_of_merge_of_overflowCollision
    (hm : v25 = v1404) (hcol : ~ OverflowIsolated w) (n : nat) :
    A198683Count n -> n <= 2924.
Proof.
  intros Hc.
  pose proof
    (count_le_of_cover _ _ (valueList12_incl_cover_merge_collision hm hcol)
      Hc) as H.
  rewrite removeIdx_length in H;
    [ rewrite removeIdx_length in H;
        [ rewrite length_seq in H; lia
        | apply seq_NoDup
        | apply in_seq; pose proof (idx25_lt w); lia ]
    | apply removeIdx_NoDup; apply seq_NoDup
    | apply removeIdx_In; split;
        [ apply in_seq; pose proof (idxOverflow_lt w); lia
        | apply not_eq_sym; exact (idx25_ne_idxOverflow w) ] ].
Qed.

(* --- Lower bounds --- *)

Theorem a198683Count_ge_2924 (n : nat) : A198683Count n -> 2924 <= n.
Proof.
  intros Hc.
  set (idxs := removeIdx (idx25 w) (removeIdx (idxOverflow w) (seq 0 2926))).
  assert (Hchar : forall k, In k idxs <->
      (k < 2926 /\ k <> idxOverflow w /\ k <> idx25 w)).
  { intro k. unfold idxs.
    rewrite !removeIdx_In, in_seq. lia. }
  assert (Hge : length idxs <= n).
  { apply count_ge_of_pairwise; [| | |exact Hc].
    - unfold idxs.
      apply removeIdx_NoDup. apply removeIdx_NoDup. apply seq_NoDup.
    - intros k Hk. apply Hchar in Hk. tauto.
    - intros j k Hj Hk Hjk.
      apply Hchar in Hj. apply Hchar in Hk.
      destruct Hj as [Hj1 [Hj2 Hj3]]. destruct Hk as [Hk1 [Hk2 Hk3]].
      apply classValue_ne; try assumption; intros [H1 H2]; congruence. }
  assert (Hlen : length idxs = 2924).
  { unfold idxs.
    rewrite removeIdx_length;
      [ rewrite removeIdx_length;
          [ rewrite length_seq; reflexivity
          | apply seq_NoDup
          | apply in_seq; pose proof (idxOverflow_lt w); lia ]
      | apply removeIdx_NoDup; apply seq_NoDup
      | apply removeIdx_In; split;
          [ apply in_seq; pose proof (idx25_lt w); lia
          | exact (idx25_ne_idxOverflow w) ] ]. }
  lia.
Qed.

Theorem a198683Count_ge_2925_of_split (hsplit : v25 <> v1404) (n : nat) :
    A198683Count n -> 2925 <= n.
Proof.
  intros Hc.
  set (idxs := removeIdx (idxOverflow w) (seq 0 2926)).
  assert (Hchar : forall k, In k idxs <->
      (k < 2926 /\ k <> idxOverflow w)).
  { intro k. unfold idxs.
    rewrite removeIdx_In, in_seq. lia. }
  assert (Hge : length idxs <= n).
  { apply count_ge_of_pairwise; [| | |exact Hc].
    - unfold idxs. apply removeIdx_NoDup. apply seq_NoDup.
    - intros k Hk. apply Hchar in Hk. tauto.
    - intros j k Hj Hk Hjk.
      apply Hchar in Hj. apply Hchar in Hk.
      destruct Hj as [Hj1 Hj2]. destruct Hk as [Hk1 Hk2].
      apply classValue_ne_of_split; assumption. }
  assert (Hlen : length idxs = 2925).
  { unfold idxs.
    rewrite removeIdx_length;
      [ rewrite length_seq; reflexivity
      | apply seq_NoDup
      | apply in_seq; pose proof (idxOverflow_lt w); lia ]. }
  lia.
Qed.

Theorem a198683Count_ge_2925_of_overflowIsolated
    (hiso : OverflowIsolated w) (n : nat) :
    A198683Count n -> 2925 <= n.
Proof.
  intros Hc.
  set (idxs := removeIdx (idx25 w) (seq 0 2926)).
  assert (Hchar : forall k, In k idxs <->
      (k < 2926 /\ k <> idx25 w)).
  { intro k. unfold idxs.
    rewrite removeIdx_In, in_seq. lia. }
  assert (Hge : length idxs <= n).
  { apply count_ge_of_pairwise; [| | |exact Hc].
    - unfold idxs. apply removeIdx_NoDup. apply seq_NoDup.
    - intros k Hk. apply Hchar in Hk. tauto.
    - intros j k Hj Hk Hjk.
      apply Hchar in Hj. apply Hchar in Hk.
      destruct Hj as [Hj1 Hj2]. destruct Hk as [Hk1 Hk2].
      apply classValue_ne_of_isolated; assumption. }
  assert (Hlen : length idxs = 2925).
  { unfold idxs.
    rewrite removeIdx_length;
      [ rewrite length_seq; reflexivity
      | apply seq_NoDup
      | apply in_seq; pose proof (idx25_lt w); lia ]. }
  lia.
Qed.

Theorem a198683Count_ge_2926_of_split_of_overflowIsolated
    (hsplit : v25 <> v1404) (hiso : OverflowIsolated w) (n : nat) :
    A198683Count n -> 2926 <= n.
Proof.
  intros Hc.
  assert (Hge : length (seq 0 2926) <= n).
  { apply count_ge_of_pairwise; [| | |exact Hc].
    - apply seq_NoDup.
    - intros k Hk. apply in_seq in Hk. lia.
    - intros j k Hj Hk Hjk.
      apply in_seq in Hj. apply in_seq in Hk.
      apply classValue_ne_full; try assumption; lia. }
  rewrite length_seq in Hge.
  exact Hge.
Qed.

(* --- The decision tree ---

   The seven theorems mirroring the Lean module; `n` is the distinct count,
   i.e. the hypothesis is `A198683Count n`.  The unconditional membership
   theorem needs no case analysis at all: the two-sided bounds
   `2924 <= n <= 2926` already absorb both dichotomies. *)

(* Given any partition witness, the twelfth term is one of three values --
   with NO hypothesis about the near-`1` split or the overflow class. *)
Theorem a198683_twelve_mem (n : nat) (Hc : A198683Count n) :
    n = 2924 \/ n = 2925 \/ n = 2926.
Proof.
  pose proof (a198683Count_ge_2924 n Hc).
  pose proof (a198683Count_le_2926 n Hc).
  lia.
Qed.

(* The near-`1` split rules out 2924. *)
Theorem a198683_twelve_mem_of_split (hsplit : v25 <> v1404)
    (n : nat) (Hc : A198683Count n) :
    n = 2925 \/ n = 2926.
Proof.
  pose proof (a198683Count_ge_2925_of_split hsplit n Hc).
  pose proof (a198683Count_le_2926 n Hc).
  lia.
Qed.

(* The no-miracles hypothesis rules out 2924. *)
Theorem a198683_twelve_mem_of_overflowIsolated (hiso : OverflowIsolated w)
    (n : nat) (Hc : A198683Count n) :
    n = 2925 \/ n = 2926.
Proof.
  pose proof (a198683Count_ge_2925_of_overflowIsolated hiso n Hc).
  pose proof (a198683Count_le_2926 n Hc).
  lia.
Qed.

(* THE EXPECTED ANSWER: both narrow hypotheses pin the value at 2926. *)
Theorem a198683_twelve_eq_2926 (hsplit : v25 <> v1404)
    (hiso : OverflowIsolated w) (n : nat) (Hc : A198683Count n) :
    n = 2926.
Proof.
  pose proof
    (a198683Count_ge_2926_of_split_of_overflowIsolated hsplit hiso n Hc).
  pose proof (a198683Count_le_2926 n Hc).
  lia.
Qed.

(* If the near-`1` split holds but the overflow value collides, the count
   is 2925. *)
Theorem a198683_twelve_eq_2925_of_overflowCollision (hsplit : v25 <> v1404)
    (hcol : ~ OverflowIsolated w) (n : nat) (Hc : A198683Count n) :
    n = 2925.
Proof.
  pose proof (a198683Count_ge_2925_of_split hsplit n Hc).
  pose proof (a198683Count_le_2925_of_overflowCollision hcol n Hc).
  lia.
Qed.

(* If the overflow value is isolated but the near-`1` towers coincide, the
   count is 2925. *)
Theorem a198683_twelve_eq_2925_of_merge (hm : v25 = v1404)
    (hiso : OverflowIsolated w) (n : nat) (Hc : A198683Count n) :
    n = 2925.
Proof.
  pose proof (a198683Count_ge_2925_of_overflowIsolated hiso n Hc).
  pose proof (a198683Count_le_2925_of_merge hm n Hc).
  lia.
Qed.

(* If both narrow hypotheses fail, the count is 2924. *)
Theorem a198683_twelve_eq_2924 (hm : v25 = v1404)
    (hcol : ~ OverflowIsolated w) (n : nat) (Hc : A198683Count n) :
    n = 2924.
Proof.
  pose proof (a198683Count_ge_2924 n Hc).
  pose proof (a198683Count_le_2924_of_merge_of_overflowCollision hm hcol n Hc).
  lia.
Qed.

End WithWitness.

End Certificate.

End A198683N12Certificate.
End LeanProofs.
