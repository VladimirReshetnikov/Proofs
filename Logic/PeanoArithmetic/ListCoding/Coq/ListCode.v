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
  Sorting.Permutation Sorting.Sorted Sorting.Mergesort.

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

(** * Aggregate and order-statistic predicates

    The scalar result is the first argument.  It is an ordinary natural
    number, not another list code.  Every predicate still guards its list
    argument by successful decoding of the same canonical code used above. *)

Fixpoint natListProduct (xs : list nat) : nat :=
  match xs with
  | [] => 1
  | x :: xs' => x * natListProduct xs'
  end.

Definition SumElementsCode (p v : nat) : Prop :=
  exists xs, decode v = Some xs /\ list_sum xs = p.

Definition ProductElementsCode (p v : nat) : Prop :=
  exists xs, decode v = Some xs /\ natListProduct xs = p.

Definition GreatestCode (m v : nat) : Prop :=
  exists xs,
    decode v = Some xs /\
    In m xs /\ Forall (fun x => x <= m) xs.

Definition LeastCode (m v : nat) : Prop :=
  exists xs,
    decode v = Some xs /\
    In m xs /\ Forall (fun x => m <= x) xs.

(** [TwiceMedianList m xs] avoids division.  Its witness is a sorted
    permutation.  At odd length [2*k+1] the result is twice entry [k]; at
    even positive length [2*(k+1)] it is the sum of entries [k] and [k+1]. *)
Definition TwiceMedianList (m : nat) (xs : list nat) : Prop :=
  exists sorted,
    Permutation sorted xs /\
    Nondecreasing sorted /\
    ((exists k a,
        length xs = k + k + 1 /\
        nth_error sorted k = Some a /\
        m = a + a) \/
     exists k a b,
        length xs = S k + S k /\
        nth_error sorted k = Some a /\
        nth_error sorted (S k) = Some b /\
        m = a + b).

Definition TwiceMedianCode (m v : nat) : Prop :=
  exists xs, decode v = Some xs /\ TwiceMedianList m xs.

(** A unique mode must occur, and every different value that occurs has a
    strictly smaller multiplicity.  Restricting rivals to values in the list
    is equivalent to quantifying over all naturals, since absent values have
    multiplicity zero. *)
Definition UniqueMostFrequent (m : nat) (xs : list nat) : Prop :=
  In m xs /\
  forall x, In x xs -> x <> m ->
    count_occ Nat.eq_dec xs x < count_occ Nat.eq_dec xs m.

Definition UniqueModeCode (m v : nat) : Prop :=
  exists xs, decode v = Some xs /\ UniqueMostFrequent m xs.

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

Lemma SumElementsCode_valid : forall p v,
  SumElementsCode p v -> ValidCode v.
Proof. intros p v [xs [h _]]. now exists xs. Qed.

Lemma ProductElementsCode_valid : forall p v,
  ProductElementsCode p v -> ValidCode v.
Proof. intros p v [xs [h _]]. now exists xs. Qed.

Lemma GreatestCode_valid : forall m v,
  GreatestCode m v -> ValidCode v.
Proof. intros m v [xs [h _]]. now exists xs. Qed.

Lemma LeastCode_valid : forall m v,
  LeastCode m v -> ValidCode v.
Proof. intros m v [xs [h _]]. now exists xs. Qed.

Lemma TwiceMedianCode_valid : forall m v,
  TwiceMedianCode m v -> ValidCode v.
Proof. intros m v [xs [h _]]. now exists xs. Qed.

Lemma UniqueModeCode_valid : forall m v,
  UniqueModeCode m v -> ValidCode v.
Proof. intros m v [xs [h _]]. now exists xs. Qed.

Lemma SumElementsCode_functional : forall p q v,
  SumElementsCode p v -> SumElementsCode q v -> p = q.
Proof.
  intros p q v [xs [hv hp]] [ys [hv' hq]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  now rewrite <- hp, <- hq.
Qed.

Lemma ProductElementsCode_functional : forall p q v,
  ProductElementsCode p v -> ProductElementsCode q v -> p = q.
Proof.
  intros p q v [xs [hv hp]] [ys [hv' hq]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  now rewrite <- hp, <- hq.
Qed.

Lemma SumElementsCode_exists : forall v,
  ValidCode v -> exists p, SumElementsCode p v.
Proof. intros v [xs hv]. exists (list_sum xs), xs. now split. Qed.

Lemma ProductElementsCode_exists : forall v,
  ValidCode v -> exists p, ProductElementsCode p v.
Proof. intros v [xs hv]. exists (natListProduct xs), xs. now split. Qed.

Lemma GreatestCode_functional : forall m n v,
  GreatestCode m v -> GreatestCode n v -> m = n.
Proof.
  intros m n v [xs [hv [hm hboundm]]] [ys [hv' [hn hboundn]]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  apply Forall_forall with (x := n) in hboundm; [|exact hn].
  apply Forall_forall with (x := m) in hboundn; [|exact hm]. lia.
Qed.

Lemma LeastCode_functional : forall m n v,
  LeastCode m v -> LeastCode n v -> m = n.
Proof.
  intros m n v [xs [hv [hm hboundm]]] [ys [hv' [hn hboundn]]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  apply Forall_forall with (x := n) in hboundm; [|exact hn].
  apply Forall_forall with (x := m) in hboundn; [|exact hm]. lia.
Qed.

Lemma UniqueModeCode_functional : forall m n v,
  UniqueModeCode m v -> UniqueModeCode n v -> m = n.
Proof.
  intros m n v [xs [hv [hm hdomm]]] [ys [hv' [hn hdomn]]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  destruct (Nat.eq_dec m n) as [heq | hneq]; [exact heq |].
  pose proof (hdomm n hn ltac:(congruence)) as hnm.
  pose proof (hdomn m hm hneq) as hmn. lia.
Qed.

Lemma sorted_permutation_unique : forall xs ys,
  Sorted le xs -> Sorted le ys -> Permutation xs ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys hsx hsy hp.
  - apply Permutation_length in hp. destruct ys; simpl in hp; try lia.
    reflexivity.
  - destruct ys as [|y ys].
    + apply Permutation_length in hp. simpl in hp. lia.
    + assert (hxin : In x (y :: ys)).
      { eapply Permutation_in; [exact hp | now left]. }
      assert (hyin : In y (x :: xs)).
      { eapply Permutation_in; [apply Permutation_sym; exact hp | now left]. }
      assert (hxy : x <= y).
      {
        destruct hyin as [heq | hyin]; [lia |].
        pose proof (Sorted_extends Nat.le_trans hsx) as hall.
        apply Forall_forall with (x := y) in hall; assumption.
      }
      assert (hyx : y <= x).
      {
        destruct hxin as [heq | hxin]; [lia |].
        pose proof (Sorted_extends Nat.le_trans hsy) as hall.
        apply Forall_forall with (x := x) in hall; assumption.
      }
      assert (hhead : x = y) by lia. subst y. f_equal.
      apply IH.
      * inversion hsx. assumption.
      * inversion hsy. assumption.
      * now apply Permutation_cons_inv in hp.
Qed.

Lemma TwiceMedianList_functional : forall m n xs,
  TwiceMedianList m xs -> TwiceMedianList n xs -> m = n.
Proof.
  intros m n xs [ss [hps [hss hcaseM]]] [tt [hpt [htt hcaseN]]].
  assert (hst : ss = tt).
  {
    apply sorted_permutation_unique; try assumption.
    exact (Permutation_trans hps (Permutation_sym hpt)).
  }
  subst tt.
  destruct hcaseM as
      [[k [a [hlenM [ha hm]]]] |
       [k [a [b [hlenM [ha [hb hm]]]]]]];
    destruct hcaseN as
      [[q [c [hlenN [hc hn]]]] |
       [q [c [d [hlenN [hc [hd hn]]]]]]].
  - assert (hkq : k = q) by lia. subst q.
    rewrite ha in hc. inversion hc. lia.
  - lia.
  - lia.
  - assert (hkq : k = q) by lia. subst q.
    rewrite ha in hc. inversion hc. rewrite hb in hd. inversion hd. lia.
Qed.

Lemma TwiceMedianCode_functional : forall m n v,
  TwiceMedianCode m v -> TwiceMedianCode n v -> m = n.
Proof.
  intros m n v [xs [hv hm]] [ys [hv' hn]].
  pose proof (decode_functional v xs ys hv hv') as hxy. subst ys.
  now apply (TwiceMedianList_functional m n xs).
Qed.

Lemma list_greatest_exists : forall x xs,
  exists m, In m (x :: xs) /\ Forall (fun z => z <= m) (x :: xs).
Proof.
  intros x xs. revert x. induction xs as [|y ys IH]; intro x.
  - exists x. split; [now left |]. repeat constructor.
  - destruct (IH y) as [m [hmin hmBound]].
    destruct (le_dec x m) as [hxm | hmx].
    + exists m. split; [now right |]. constructor; assumption.
    + exists x. split; [now left |]. constructor; [lia |].
      apply Forall_forall. intros z hz.
      apply Forall_forall with (x := z) in hmBound; [lia | exact hz].
Qed.

Lemma list_least_exists : forall x xs,
  exists m, In m (x :: xs) /\ Forall (fun z => m <= z) (x :: xs).
Proof.
  intros x xs. revert x. induction xs as [|y ys IH]; intro x.
  - exists x. split; [now left |]. repeat constructor.
  - destruct (IH y) as [m [hmin hmBound]].
    destruct (le_dec m x) as [hmx | hxm].
    + exists m. split; [now right |]. constructor; assumption.
    + exists x. split; [now left |]. constructor; [lia |].
      apply Forall_forall. intros z hz.
      apply Forall_forall with (x := z) in hmBound; [lia | exact hz].
Qed.

Lemma GreatestCode_exists_nonempty : forall v x xs,
  decode v = Some (x :: xs) -> exists m, GreatestCode m v.
Proof.
  intros v x xs hv. destruct (list_greatest_exists x xs) as [m hspec].
  exists m, (x :: xs). now split.
Qed.

Lemma LeastCode_exists_nonempty : forall v x xs,
  decode v = Some (x :: xs) -> exists m, LeastCode m v.
Proof.
  intros v x xs hv. destruct (list_least_exists x xs) as [m hspec].
  exists m, (x :: xs). now split.
Qed.

Lemma NatSort_sorted_le : forall xs,
  Sorted le (NatSort.sort xs).
Proof.
  intro xs. pose proof (NatSort.Sorted_sort xs) as hsort.
  induction hsort as [|a l hsorted IH hhead].
  - constructor.
  - constructor; [exact IH |].
    inversion hhead as [|b l' hab]; subst.
    + constructor.
    + constructor. apply Nat.leb_le. exact hab.
Qed.

Lemma TwiceMedianCode_exists_nonempty : forall v x xs,
  decode v = Some (x :: xs) -> exists m, TwiceMedianCode m v.
Proof.
  intros v x xs hv.
  set (sorted := NatSort.sort (x :: xs)).
  assert (hperm : Permutation sorted (x :: xs)).
  { unfold sorted. apply Permutation_sym. apply NatSort.Permuted_sort. }
  assert (hsorted : Nondecreasing sorted).
  { unfold Nondecreasing, sorted. apply NatSort_sorted_le. }
  assert (hlen : length sorted = length (x :: xs)).
  { apply Permutation_length. exact hperm. }
  destruct (Nat.Even_or_Odd (length (x :: xs))) as
      [[q hq] | [q hq]].
  - assert (hqpos : 0 < q) by (simpl in hq; nia).
    destruct q as [|k]; [lia |].
    assert (hk : k < length sorted) by (rewrite hlen; nia).
    assert (hsk : S k < length sorted) by (rewrite hlen; nia).
    assert (hak : nth_error sorted k <> None).
    { apply (proj2 (nth_error_Some sorted k)). exact hk. }
    destruct (nth_error sorted k) as [a|] eqn:ha; [|contradiction].
    assert (hbk : nth_error sorted (S k) <> None).
    { apply (proj2 (nth_error_Some sorted (S k))). exact hsk. }
    destruct (nth_error sorted (S k)) as [b|] eqn:hb; [|contradiction].
    exists (a + b), (x :: xs). split; [exact hv |].
    exists sorted. split; [exact hperm |]. split; [exact hsorted |].
    right. exists k, a, b. repeat split; try assumption; nia.
  - assert (hk : q < length sorted) by (rewrite hlen; nia).
    assert (haq : nth_error sorted q <> None).
    { apply (proj2 (nth_error_Some sorted q)). exact hk. }
    destruct (nth_error sorted q) as [a|] eqn:ha; [|contradiction].
    exists (a + a), (x :: xs). split; [exact hv |].
    exists sorted. split; [exact hperm |]. split; [exact hsorted |].
    left. exists q, a. repeat split; try assumption; nia.
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

Lemma SumElementsCode_listCode : forall p xs,
  SumElementsCode p (listCode xs) <-> list_sum xs = p.
Proof.
  intros p xs. split.
  - intros [ys [h hsum]]. rewrite decode_listCode in h.
    inversion h. exact hsum.
  - intro hsum. exists xs. split; [apply decode_listCode | exact hsum].
Qed.

Lemma ProductElementsCode_listCode : forall p xs,
  ProductElementsCode p (listCode xs) <-> natListProduct xs = p.
Proof.
  intros p xs. split.
  - intros [ys [h hprod]]. rewrite decode_listCode in h.
    inversion h. exact hprod.
  - intro hprod. exists xs. split; [apply decode_listCode | exact hprod].
Qed.

Lemma GreatestCode_listCode : forall m xs,
  GreatestCode m (listCode xs) <->
  In m xs /\ Forall (fun x => x <= m) xs.
Proof.
  intros m xs. split.
  - intros [ys [h hspec]]. rewrite decode_listCode in h.
    inversion h. exact hspec.
  - intros hspec. exists xs. split; [apply decode_listCode | exact hspec].
Qed.

Lemma LeastCode_listCode : forall m xs,
  LeastCode m (listCode xs) <->
  In m xs /\ Forall (fun x => m <= x) xs.
Proof.
  intros m xs. split.
  - intros [ys [h hspec]]. rewrite decode_listCode in h.
    inversion h. exact hspec.
  - intros hspec. exists xs. split; [apply decode_listCode | exact hspec].
Qed.

Lemma TwiceMedianCode_listCode : forall m xs,
  TwiceMedianCode m (listCode xs) <-> TwiceMedianList m xs.
Proof.
  intros m xs. split.
  - intros [ys [h hmedian]]. rewrite decode_listCode in h.
    inversion h. exact hmedian.
  - intro hmedian. exists xs. split; [apply decode_listCode | exact hmedian].
Qed.

Lemma UniqueModeCode_listCode : forall m xs,
  UniqueModeCode m (listCode xs) <-> UniqueMostFrequent m xs.
Proof.
  intros m xs. split.
  - intros [ys [h hmode]]. rewrite decode_listCode in h.
    inversion h. exact hmode.
  - intro hmode. exists xs. split; [apply decode_listCode | exact hmode].
Qed.

(** Named edge regressions make the empty-list and tie conventions visible
    to the kernel audit rather than leaving them only implicit in the general
    specifications. *)
Lemma SumElementsCode_empty : SumElementsCode 0 (listCode []).
Proof. apply (proj2 (SumElementsCode_listCode 0 [])). reflexivity. Qed.

Lemma ProductElementsCode_empty : ProductElementsCode 1 (listCode []).
Proof. apply (proj2 (ProductElementsCode_listCode 1 [])). reflexivity. Qed.

Lemma GreatestCode_empty_false : forall m,
  ~ GreatestCode m (listCode []).
Proof.
  intros m h. apply GreatestCode_listCode in h. destruct h as [h _].
  contradiction.
Qed.

Lemma LeastCode_empty_false : forall m,
  ~ LeastCode m (listCode []).
Proof.
  intros m h. apply LeastCode_listCode in h. destruct h as [h _].
  contradiction.
Qed.

Lemma TwiceMedianCode_empty_false : forall m,
  ~ TwiceMedianCode m (listCode []).
Proof.
  intros m h. apply TwiceMedianCode_listCode in h.
  destruct h as [sorted [hp [hs
    [[k [a [hlen _]]] | [k [a [b [hlen _]]]]]]]].
  all: simpl in hlen; lia.
Qed.

Lemma UniqueModeCode_empty_false : forall m,
  ~ UniqueModeCode m (listCode []).
Proof.
  intros m h. apply UniqueModeCode_listCode in h. destruct h as [h _].
  contradiction.
Qed.

Lemma UniqueModeCode_tie_1_2_false : forall m,
  ~ UniqueModeCode m (listCode [1; 2]).
Proof.
  intros m h. apply UniqueModeCode_listCode in h.
  destruct h as [hin hdom]. simpl in hin.
  destruct hin as [hm | [hm | []]]; subst m.
  - specialize (hdom 2 ltac:(simpl; auto) ltac:(lia)). simpl in hdom. lia.
  - specialize (hdom 1 ltac:(simpl; auto) ltac:(lia)). simpl in hdom. lia.
Qed.

Lemma TwiceMedianCode_odd_example :
  TwiceMedianCode 2 (listCode [1]).
Proof.
  apply (proj2 (TwiceMedianCode_listCode 2 [1])).
  exists [1]. split; [apply Permutation_refl |]. split.
  - unfold Nondecreasing. repeat constructor.
  - left. exists 0, 1. repeat split; reflexivity.
Qed.

Lemma TwiceMedianCode_even_example :
  TwiceMedianCode 4 (listCode [1; 3]).
Proof.
  apply (proj2 (TwiceMedianCode_listCode 4 [1; 3])).
  exists [1; 3]. split; [apply Permutation_refl |]. split.
  - unfold Nondecreasing. repeat constructor; lia.
  - right. exists 0, 1, 3. repeat split; reflexivity.
Qed.

End PAListCode.
