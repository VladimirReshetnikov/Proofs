(**
  Canonical natural-number codes for finite lists of natural numbers.

  The constructor code is

      code []        = 0
      code (x :: xs) = 1 + ((x + code xs)^2 + x).

  The polynomial pairing function is injective and dominates both of its
  coordinates.  Consequently the tail code is strictly smaller than every
  nonempty list code.  [decodeFuel] follows these decreasing tail codes;
  [decode] gives it enough fuel for every genuine code and rejects malformed
  positive numbers.

  The second half of the file fixes the intended metalevel meanings of the
  list predicates represented by PA formulae in the companion development.
  Every predicate is guarded by successful decoding.  Indices are zero based.
*)

From Stdlib Require Import
  List Arith Lia Bool PeanoNat
  Sorting.Permutation Sorting.Sorted.

Import ListNotations.

Module PAListCode.

(** * Polynomial pairing and its executable partial inverse *)

Definition polynomialPair (a b : nat) : nat :=
  (a + b) * (a + b) + a.

Lemma polynomialPair_left_le : forall a b,
  a <= polynomialPair a b.
Proof.
  intros a b. unfold polynomialPair. nia.
Qed.

Lemma polynomialPair_right_le : forall a b,
  b <= polynomialPair a b.
Proof.
  intros a b. unfold polynomialPair. nia.
Qed.

Lemma polynomialPair_diagonal_bounds : forall a b,
  let s := a + b in
  s * s <= polynomialPair a b < S s * S s.
Proof.
  intros a b s. unfold polynomialPair, s. nia.
Qed.

Theorem polynomialPair_injective : forall a b c d,
  polynomialPair a b = polynomialPair c d ->
  a = c /\ b = d.
Proof.
  intros a b c d heq.
  pose proof (polynomialPair_diagonal_bounds a b) as hab.
  pose proof (polynomialPair_diagonal_bounds c d) as hcd.
  set (s := a + b) in *.
  set (t := c + d) in *.
  cbn in hab, hcd.
  assert (hst : s = t).
  {
    destruct (Nat.lt_trichotomy s t) as [hlt | [he | hgt]].
    - assert (S s <= t) by lia.
      assert (S s * S s <= t * t).
      { apply Nat.mul_le_mono; assumption. }
      lia.
    - exact he.
    - assert (S t <= s) by lia.
      assert (S t * S t <= s * s).
      { apply Nat.mul_le_mono; assumption. }
      lia.
  }
  unfold polynomialPair in heq.
  fold s in heq. fold t in heq.
  assert (hac : a = c) by nia.
  split; [exact hac |].
  unfold s, t in hst. lia.
Qed.

Definition polynomialPairCandidates (n : nat) : list (nat * nat) :=
  list_prod (seq 0 (S n)) (seq 0 (S n)).

Definition polynomialUnpair (n : nat) : nat * nat :=
  match find
      (fun ab => Nat.eqb (polynomialPair (fst ab) (snd ab)) n)
      (polynomialPairCandidates n) with
  | Some ab => ab
  | None => (0, 0)
  end.

Lemma find_some_of_In_true : forall (A : Type) (f : A -> bool) xs x,
  In x xs -> f x = true -> exists y, find f xs = Some y.
Proof.
  intros A f xs.
  induction xs as [|a xs IH]; simpl; intros x hx hfx.
  - contradiction.
  - destruct hx as [hx | hx].
    + subst x. rewrite hfx. exists a. reflexivity.
    + destruct (f a) eqn:hfa.
      * exists a. reflexivity.
      * apply (IH x); assumption.
Qed.

Lemma polynomialPair_in_candidates : forall a b,
  In (a, b) (polynomialPairCandidates (polynomialPair a b)).
Proof.
  intros a b. unfold polynomialPairCandidates.
  apply in_prod_iff. split; apply in_seq; simpl; split; try lia.
  - pose proof (polynomialPair_left_le a b). lia.
  - pose proof (polynomialPair_right_le a b). lia.
Qed.

Lemma polynomialUnpair_sound : forall n,
  (exists a b, polynomialPair a b = n) ->
  polynomialPair (fst (polynomialUnpair n))
    (snd (polynomialUnpair n)) = n.
Proof.
  intros n [a [b hab]].
  unfold polynomialUnpair.
  remember (find
    (fun ab0 : nat * nat =>
      Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
    (polynomialPairCandidates n)) as found eqn:hfound.
  destruct found as [[x y] |].
  - pose proof (find_some
      (fun ab0 : nat * nat =>
        Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
      (polynomialPairCandidates n) (eq_sym hfound)) as [_ htest].
    simpl. apply Nat.eqb_eq. exact htest.
  - exfalso.
    assert (hin : In (a, b) (polynomialPairCandidates n)).
    { subst n. apply polynomialPair_in_candidates. }
    pose proof (find_none
      (fun ab0 : nat * nat =>
        Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
      (polynomialPairCandidates n) (eq_sym hfound) (a, b) hin) as hfalse.
    simpl in hfalse. apply Nat.eqb_neq in hfalse. contradiction.
Qed.

Theorem polynomialUnpair_pair : forall a b,
  polynomialUnpair (polynomialPair a b) = (a, b).
Proof.
  intros a b.
  pose proof (polynomialUnpair_sound (polynomialPair a b)
    (ex_intro _ a (ex_intro _ b eq_refl))) as hsound.
  destruct (polynomialUnpair (polynomialPair a b)) as [x y] eqn:hu.
  simpl in hsound.
  destruct (polynomialPair_injective x y a b hsound) as [hx hy].
  subst x. subst y. reflexivity.
Qed.

Definition polynomialSplit (n : nat) : option (nat * nat) :=
  let ab := polynomialUnpair n in
  if Nat.eqb (polynomialPair (fst ab) (snd ab)) n
  then Some ab
  else None.

Lemma polynomialSplit_pair : forall a b,
  polynomialSplit (polynomialPair a b) = Some (a, b).
Proof.
  intros a b. unfold polynomialSplit.
  rewrite polynomialUnpair_pair. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma polynomialSplit_sound : forall n a b,
  polynomialSplit n = Some (a, b) ->
  polynomialPair a b = n.
Proof.
  intros n a b. unfold polynomialSplit.
  destruct (polynomialUnpair n) as [x y]. simpl.
  destruct (Nat.eqb (polynomialPair x y) n) eqn:heq;
    intro h; inversion h; subst.
  apply Nat.eqb_eq. exact heq.
Qed.

(** * Canonical codes and decoding *)

Fixpoint listCode (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => S (polynomialPair x (listCode rest))
  end.

Lemma listCode_cons_formula : forall x xs,
  listCode (x :: xs) =
    S (((x + listCode xs) * (x + listCode xs)) + x).
Proof.
  reflexivity.
Qed.

Lemma listCode_positive_iff_nonempty : forall xs,
  0 < listCode xs <-> xs <> [].
Proof.
  intros [|x xs]; simpl; split; intros h; try lia; try contradiction.
  discriminate.
Qed.

Lemma listCode_tail_lt : forall x xs,
  listCode xs < listCode (x :: xs).
Proof.
  intros x xs. simpl.
  pose proof (polynomialPair_right_le x (listCode xs)). lia.
Qed.

Lemma listCode_length_le : forall xs,
  length xs <= listCode xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lia |].
  pose proof (polynomialPair_right_le x (listCode xs)). lia.
Qed.

Fixpoint decodeFuel (fuel p : nat) : option (list nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match p with
      | 0 => Some []
      | S q =>
          match polynomialSplit q with
          | None => None
          | Some (x, tail) =>
              match decodeFuel fuel' tail with
              | None => None
              | Some xs => Some (x :: xs)
              end
          end
      end
  end.

Definition decode (p : nat) : option (list nat) :=
  decodeFuel (S p) p.

Lemma decodeFuel_listCode : forall xs fuel,
  length xs < fuel ->
  decodeFuel fuel (listCode xs) = Some xs.
Proof.
  induction xs as [|x xs IH]; intros [|fuel] h; simpl in *; try lia.
  - reflexivity.
  - rewrite polynomialSplit_pair.
    rewrite IH by lia. reflexivity.
Qed.

Lemma decodeFuel_sound : forall fuel p xs,
  decodeFuel fuel p = Some xs ->
  listCode xs = p.
Proof.
  induction fuel as [|fuel IH]; intros p xs h; simpl in h.
  - discriminate.
  - destruct p as [|q].
    + inversion h. reflexivity.
    + destruct (polynomialSplit q) as [[x tail]|] eqn:hsplit;
        try discriminate.
      destruct (decodeFuel fuel tail) as [rest|] eqn:hrest;
        try discriminate.
      inversion h; subst xs.
      pose proof (IH tail rest hrest) as htail.
      pose proof (polynomialSplit_sound q x tail hsplit) as hpair.
      simpl. rewrite htail, hpair. reflexivity.
Qed.

Theorem decode_listCode : forall xs,
  decode (listCode xs) = Some xs.
Proof.
  intro xs. unfold decode.
  apply decodeFuel_listCode.
  pose proof (listCode_length_le xs). lia.
Qed.

Theorem listCode_decode : forall p xs,
  decode p = Some xs ->
  listCode xs = p.
Proof.
  intros p xs h. unfold decode in h.
  exact (decodeFuel_sound (S p) p xs h).
Qed.

Theorem decode_some_iff_listCode : forall p xs,
  decode p = Some xs <-> listCode xs = p.
Proof.
  intros p xs. split.
  - apply listCode_decode.
  - intro h. subst p. apply decode_listCode.
Qed.

Theorem listCode_injective : forall xs ys,
  listCode xs = listCode ys -> xs = ys.
Proof.
  intros xs ys h.
  pose proof (decode_listCode xs) as hx.
  pose proof (decode_listCode ys) as hy.
  rewrite h in hx. rewrite hx in hy. inversion hy. reflexivity.
Qed.

Theorem decode_functional : forall p xs ys,
  decode p = Some xs -> decode p = Some ys -> xs = ys.
Proof.
  intros p xs ys hx hy. rewrite hx in hy. inversion hy. reflexivity.
Qed.

Definition ValidCode (p : nat) : Prop :=
  exists xs, decode p = Some xs.

Definition validCodeb (p : nat) : bool :=
  match decode p with
  | Some _ => true
  | None => false
  end.

Lemma validCodeb_spec : forall p,
  validCodeb p = true <-> ValidCode p.
Proof.
  intro p. unfold validCodeb, ValidCode.
  destruct (decode p) as [xs|] eqn:hdecode; split; intro h.
  - exists xs. reflexivity.
  - reflexivity.
  - discriminate.
  - destruct h as [xs h]. discriminate.
Qed.

Lemma ValidCode_listCode : forall xs,
  ValidCode (listCode xs).
Proof.
  intro xs. exists xs. apply decode_listCode.
Qed.

Lemma ValidCode_iff_exists_listCode : forall p,
  ValidCode p <-> exists xs, listCode xs = p.
Proof.
  intro p. split.
  - intros [xs h]. exists xs. now apply listCode_decode.
  - intros [xs h]. exists xs. apply decode_some_iff_listCode. exact h.
Qed.

Lemma ValidCode_unique_list : forall p,
  ValidCode p -> exists! xs, listCode xs = p.
Proof.
  intros p [xs hdecode].
  exists xs. split.
  - now apply listCode_decode.
  - intros ys hy. apply listCode_injective.
    rewrite hy. now apply listCode_decode in hdecode.
Qed.

(** Decode an outer list whose entries are themselves list codes. *)
Fixpoint decodeCodes (codes : list nat) : option (list (list nat)) :=
  match codes with
  | [] => Some []
  | c :: rest =>
      match decode c, decodeCodes rest with
      | Some xs, Some xss => Some (xs :: xss)
      | _, _ => None
      end
  end.

Lemma decodeCodes_map_listCode : forall xss,
  decodeCodes (map listCode xss) = Some xss.
Proof.
  induction xss as [|xs xss IH]; simpl.
  - reflexivity.
  - rewrite decode_listCode, IH. reflexivity.
Qed.

Lemma decodeCodes_sound : forall codes xss,
  decodeCodes codes = Some xss ->
  map listCode xss = codes.
Proof.
  induction codes as [|c codes IH]; intros xss h; simpl in h.
  - inversion h. reflexivity.
  - destruct (decode c) as [xs|] eqn:hc; try discriminate.
    destruct (decodeCodes codes) as [rest|] eqn:hr; try discriminate.
    inversion h; subst xss.
    simpl. f_equal.
    + now apply listCode_decode in hc.
    + exact (IH rest eq_refl).
Qed.

Lemma decodeCodes_entries_valid : forall codes xss,
  decodeCodes codes = Some xss ->
  Forall ValidCode codes.
Proof.
  induction codes as [|c codes IH]; intros xss h; simpl in h.
  - constructor.
  - destruct (decode c) as [xs|] eqn:hc; try discriminate.
    destruct (decodeCodes codes) as [rest|] eqn:hr; try discriminate.
    inversion h; subst xss.
    constructor.
    + exists xs. exact hc.
    + exact (IH rest eq_refl).
Qed.

(** * Metalevel meanings of the represented list predicates *)

Definition HasLength (v n : nat) : Prop :=
  exists xs, decode v = Some xs /\ length xs = n.

(** [k] is zero based. *)
Definition NthElement (v k m : nat) : Prop :=
  exists xs, decode v = Some xs /\ nth_error xs k = Some m.

Definition SingletonCode (v m : nat) : Prop :=
  decode v = Some [m].

Definition ConcatenationCode (v t u : nat) : Prop :=
  exists xs ys zs,
    decode v = Some xs /\
    decode t = Some ys /\
    decode u = Some zs /\
    xs = ys ++ zs.

Definition FlattenCode (v w : nat) : Prop :=
  exists flat codes xss,
    decode v = Some flat /\
    decode w = Some codes /\
    decodeCodes codes = Some xss /\
    flat = concat xss.

(** [OccurrencesCode v n m] means that [v] contains exactly [n]
    occurrences of [m]. *)
Definition OccurrencesCode (v n m : nat) : Prop :=
  exists xs,
    decode v = Some xs /\
    count_occ Nat.eq_dec xs m = n.

Definition PermutationCode (v w : nat) : Prop :=
  exists xs ys,
    decode v = Some xs /\
    decode w = Some ys /\
    Permutation xs ys.

Definition ContiguousSubstring (needle haystack : list nat) : Prop :=
  exists prefix suffix,
    haystack = prefix ++ needle ++ suffix.

Definition ContiguousSubstringCode (v w : nat) : Prop :=
  exists xs ys,
    decode v = Some xs /\
    decode w = Some ys /\
    ContiguousSubstring xs ys.

Inductive Subsequence : list nat -> list nat -> Prop :=
| subsequence_nil : forall ys, Subsequence [] ys
| subsequence_keep : forall x xs ys,
    Subsequence xs ys -> Subsequence (x :: xs) (x :: ys)
| subsequence_skip : forall y xs ys,
    Subsequence xs ys -> Subsequence xs (y :: ys).

Definition SubsequenceCode (v w : nat) : Prop :=
  exists xs ys,
    decode v = Some xs /\
    decode w = Some ys /\
    Subsequence xs ys.

Definition NoDuplicatesCode (v : nat) : Prop :=
  exists xs, decode v = Some xs /\ NoDup xs.

Definition Nondecreasing (xs : list nat) : Prop :=
  Sorted le xs.

Definition SortedCode (v : nat) : Prop :=
  exists xs, decode v = Some xs /\ Nondecreasing xs.

(** Non-strict lexicographic order.  In particular, every list is
    [LexLe]-related to itself and the empty list is below every list. *)
Inductive LexLe : list nat -> list nat -> Prop :=
| lexLe_nil : forall ys, LexLe [] ys
| lexLe_head_lt : forall x y xs ys,
    x < y -> LexLe (x :: xs) (y :: ys)
| lexLe_head_eq : forall x xs ys,
    LexLe xs ys -> LexLe (x :: xs) (x :: ys).

Lemma LexLe_refl : forall xs, LexLe xs xs.
Proof.
  induction xs as [|x xs IH].
  - constructor.
  - apply lexLe_head_eq. exact IH.
Qed.

Definition LexSortedLists (xss : list (list nat)) : Prop :=
  Sorted LexLe xss.

Definition LexSortedCode (v : nat) : Prop :=
  exists codes xss,
    decode v = Some codes /\
    decodeCodes codes = Some xss /\
    LexSortedLists xss.

(** The unique intended enumeration convention for permutations: the outer
    list contains every *distinct list value* permutation exactly once, and
    those values occur in non-strict lexicographic order.  Thus repeated
    elements of [base] do not cause duplicate permutation entries. *)
Definition CanonicalPermutations
    (xss : list (list nat)) (base : list nat) : Prop :=
  LexSortedLists xss /\
  NoDup xss /\
  (forall ys, In ys xss <-> Permutation ys base).

Definition AllPermutationsCode (v w : nat) : Prop :=
  exists codes xss base,
    decode v = Some codes /\
    decodeCodes codes = Some xss /\
    decode w = Some base /\
    CanonicalPermutations xss base.

(** * Guard and projection lemmas *)

Lemma HasLength_valid : forall v n,
  HasLength v n -> ValidCode v.
Proof. intros v n [xs [h _]]. now exists xs. Qed.

Lemma NthElement_valid : forall v k m,
  NthElement v k m -> ValidCode v.
Proof. intros v k m [xs [h _]]. now exists xs. Qed.

Lemma SingletonCode_valid : forall v m,
  SingletonCode v m -> ValidCode v.
Proof. intros v m h. now exists [m]. Qed.

Lemma ConcatenationCode_valid : forall v t u,
  ConcatenationCode v t u ->
  ValidCode v /\ ValidCode t /\ ValidCode u.
Proof.
  intros v t u [xs [ys [zs [hv [ht [hu _]]]]]].
  split.
  - now exists xs.
  - split; [now exists ys | now exists zs].
Qed.

Lemma FlattenCode_valid : forall v w,
  FlattenCode v w -> ValidCode v /\ ValidCode w.
Proof.
  intros v w [flat [codes [xss [hv [hw [_ _]]]]]].
  split; [now exists flat | now exists codes].
Qed.

Lemma FlattenCode_inner_valid : forall v w flat codes xss,
  decode v = Some flat ->
  decode w = Some codes ->
  decodeCodes codes = Some xss ->
  flat = concat xss ->
  Forall ValidCode codes.
Proof.
  intros. eapply decodeCodes_entries_valid. exact H1.
Qed.

Lemma OccurrencesCode_valid : forall v n m,
  OccurrencesCode v n m -> ValidCode v.
Proof. intros v n m [xs [h _]]. now exists xs. Qed.

Lemma PermutationCode_valid : forall v w,
  PermutationCode v w -> ValidCode v /\ ValidCode w.
Proof.
  intros v w [xs [ys [hv [hw _]]]].
  split; [now exists xs | now exists ys].
Qed.

Lemma ContiguousSubstringCode_valid : forall v w,
  ContiguousSubstringCode v w -> ValidCode v /\ ValidCode w.
Proof.
  intros v w [xs [ys [hv [hw _]]]].
  split; [now exists xs | now exists ys].
Qed.

Lemma SubsequenceCode_valid : forall v w,
  SubsequenceCode v w -> ValidCode v /\ ValidCode w.
Proof.
  intros v w [xs [ys [hv [hw _]]]].
  split; [now exists xs | now exists ys].
Qed.

Lemma NoDuplicatesCode_valid : forall v,
  NoDuplicatesCode v -> ValidCode v.
Proof. intros v [xs [h _]]. now exists xs. Qed.

Lemma SortedCode_valid : forall v,
  SortedCode v -> ValidCode v.
Proof. intros v [xs [h _]]. now exists xs. Qed.

Lemma LexSortedCode_valid : forall v,
  LexSortedCode v -> ValidCode v.
Proof. intros v [codes [xss [h _]]]. now exists codes. Qed.

Lemma LexSortedCode_inner_valid : forall v codes xss,
  decode v = Some codes ->
  decodeCodes codes = Some xss ->
  LexSortedLists xss ->
  Forall ValidCode codes.
Proof.
  intros. eapply decodeCodes_entries_valid. exact H0.
Qed.

Lemma AllPermutationsCode_valid : forall v w,
  AllPermutationsCode v w -> ValidCode v /\ ValidCode w.
Proof.
  intros v w [codes [xss [base [hv [_ [hw _]]]]]].
  split; [now exists codes | now exists base].
Qed.

Lemma AllPermutationsCode_inner_valid : forall v w codes xss base,
  decode v = Some codes ->
  decodeCodes codes = Some xss ->
  decode w = Some base ->
  CanonicalPermutations xss base ->
  Forall ValidCode codes.
Proof.
  intros. eapply decodeCodes_entries_valid. exact H0.
Qed.

Lemma CanonicalPermutations_lex_sorted : forall xss base,
  CanonicalPermutations xss base -> LexSortedLists xss.
Proof. intros xss base [h _]. exact h. Qed.

Lemma CanonicalPermutations_no_duplicates : forall xss base,
  CanonicalPermutations xss base -> NoDup xss.
Proof. intros xss base [_ [h _]]. exact h. Qed.

Lemma CanonicalPermutations_sound : forall xss base ys,
  CanonicalPermutations xss base ->
  In ys xss -> Permutation ys base.
Proof.
  intros xss base ys [_ [_ hspec]] hin.
  now apply (proj1 (hspec ys)).
Qed.

Lemma CanonicalPermutations_complete : forall xss base ys,
  CanonicalPermutations xss base ->
  Permutation ys base -> In ys xss.
Proof.
  intros xss base ys [_ [_ hspec]] hperm.
  now apply (proj2 (hspec ys)).
Qed.

Lemma HasLength_listCode : forall xs n,
  HasLength (listCode xs) n <-> length xs = n.
Proof.
  intros xs n. split.
  - intros [ys [hdecode hlen]].
    rewrite decode_listCode in hdecode. inversion hdecode. exact hlen.
  - intro hlen. exists xs. split; [apply decode_listCode | exact hlen].
Qed.

Lemma NthElement_listCode : forall xs k m,
  NthElement (listCode xs) k m <-> nth_error xs k = Some m.
Proof.
  intros xs k m. split.
  - intros [ys [hdecode hnth]].
    rewrite decode_listCode in hdecode. inversion hdecode. exact hnth.
  - intro hnth. exists xs. split; [apply decode_listCode | exact hnth].
Qed.

Lemma SingletonCode_listCode : forall xs m,
  SingletonCode (listCode xs) m <-> xs = [m].
Proof.
  intros xs m. unfold SingletonCode.
  rewrite decode_listCode. split; intro h; inversion h; reflexivity.
Qed.

Lemma ConcatenationCode_listCode : forall ys zs,
  ConcatenationCode (listCode (ys ++ zs)) (listCode ys) (listCode zs).
Proof.
  intros ys zs.
  exists (ys ++ zs), ys, zs.
  repeat split; try apply decode_listCode; reflexivity.
Qed.

Lemma FlattenCode_listCode : forall xss,
  FlattenCode (listCode (concat xss))
    (listCode (map listCode xss)).
Proof.
  intro xss.
  exists (concat xss), (map listCode xss), xss.
  repeat split; try apply decode_listCode;
    try apply decodeCodes_map_listCode; reflexivity.
Qed.

End PAListCode.
