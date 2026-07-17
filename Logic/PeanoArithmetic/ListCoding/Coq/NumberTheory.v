(**
  Number-theoretic relations built on the canonical list code.

  The definitions in this file are deliberately certificate-oriented.  A
  bounded finite computation is witnessed by one or more canonical list
  codes; [NumberTheoryFormulas] gives the corresponding first-order PA
  formulae and proves their standard-model correctness.

  Prime indices are ONE BASED: [NthPrime 2 1] holds and index zero is empty.
*)

From Stdlib Require Import
  List Arith Lia Bool PeanoNat
  Sorting.Permutation Sorting.Sorted Sorting.Mergesort.
From PAListCoding Require Import ListCode ListFormulas.

Import ListNotations.

Module PAListNumberTheory.

Import PAListCode.
Import PAListFormulas.

(** * Divisibility and primality *)

Definition Divides (d n : nat) : Prop := Nat.divide d n.

Definition PrimeNat (p : nat) : Prop :=
  1 < p /\
  forall d, Divides d p -> d = 1 \/ d = p.

Lemma primeNat_gt_one : forall p, PrimeNat p -> 1 < p.
Proof. intros p [h _]. exact h. Qed.

Lemma primeNat_two : PrimeNat 2.
Proof.
  split; [lia |].
  intros d hd. assert (d <= 2).
  { apply Nat.divide_pos_le; [lia | exact hd]. }
  destruct d as [|[|d]]; [destruct hd as [q hq]; simpl in hq; nia | |];
    [left; reflexivity | right; lia].
Qed.

Lemma primeNat_three : PrimeNat 3.
Proof.
  split; [lia |].
  intros d hd. assert (d <= 3).
  { apply Nat.divide_pos_le; [lia | exact hd]. }
  destruct d as [|[|[|d]]].
  - destruct hd as [q hq]. simpl in hq. nia.
  - left. reflexivity.
  - destruct hd as [q hq]. simpl in hq. nia.
  - assert (d = 0) by lia. subst d. right. reflexivity.
Qed.

(** Adjacent strict increase.  This positional presentation is exactly what
    a first-order formula needs and is equivalent to [Sorted lt]. *)
Definition StrictlyIncreasing (xs : list nat) : Prop :=
  forall i a b,
    nth_error xs i = Some a ->
    nth_error xs (S i) = Some b ->
    a < b.

Definition StrictlyIncreasingCode (v : nat) : Prop :=
  exists len,
    HasLength v len /\
    forall i a b,
      S i < len ->
      NthElement v i a ->
      NthElement v (S i) b ->
      a < b.

Lemma StrictlyIncreasingCode_decode : forall v xs,
  decode v = Some xs ->
  (StrictlyIncreasingCode v <-> StrictlyIncreasing xs).
Proof.
  intros v xs hv. split.
  - intros [len [[ys [hy hlen]] h]].
    rewrite hv in hy. inversion hy; subst ys.
    intros i a b hia hib.
    assert (hi : S i < length xs).
    { apply nth_error_Some. rewrite hib. discriminate. }
    rewrite hlen in hi. apply (h i a b hi).
    + exists xs. now split.
    + exists xs. now split.
  - intros h. exists (length xs). split.
    + exists xs. now split.
    + intros i a b _ hia hib.
      apply (NthElement_decode v i a xs hv) in hia.
      apply (NthElement_decode v (S i) b xs hv) in hib.
      exact (h i a b hia hib).
Qed.

Lemma StrictlyIncreasingCode_listCode : forall xs,
  StrictlyIncreasingCode (listCode xs) <-> StrictlyIncreasing xs.
Proof.
  intro xs. apply StrictlyIncreasingCode_decode. apply decode_listCode.
Qed.

(** A one-based prime-index certificate lists exactly the smaller primes in
    strictly increasing order.  Its length [k] satisfies [n = S k]. *)
Definition NthPrime (p n : nat) : Prop :=
  PrimeNat p /\
  exists k below,
    n = S k /\
    HasLength below k /\
    StrictlyIncreasingCode below /\
    (forall i q, NthElement below i q -> PrimeNat q /\ q < p) /\
    (forall q, PrimeNat q /\ q < p -> exists i, NthElement below i q).

Lemma nthPrime_index_zero_false : forall p, ~ NthPrime p 0.
Proof.
  intros p [_ [k [below [hindex _]]]]. discriminate.
Qed.

Lemma nthPrime_two_one : NthPrime 2 1.
Proof.
  split; [apply primeNat_two |].
  exists 0, (listCode []). split; [reflexivity |].
  split.
  - exists []. split; [apply decode_listCode | reflexivity].
  - split.
    + apply StrictlyIncreasingCode_listCode.
      intros i; destruct i; discriminate.
    + split.
      * intros i q hq. destruct hq as [xs [hdec hnth]].
        rewrite decode_listCode in hdec. inversion hdec; subst xs.
        destruct i; discriminate.
      * intros q [[hqprime hqdiv] hq2]. exfalso.
        pose proof (primeNat_gt_one q (conj hqprime hqdiv)). lia.
Qed.

(** * Exponentiation by a multiplication trace *)

Definition PowerNat (m n k : nat) : Prop := m = Nat.pow n k.

Definition PowerPosition (m n k : nat) : Prop :=
  exists trace,
    HasLength trace (S k) /\
    NthElement trace 0 1 /\
    NthElement trace k m /\
    forall i cur next,
      i < k ->
      NthElement trace i cur ->
      NthElement trace (S i) next ->
      next = cur * n.

Definition powerTrace (n k : nat) : list nat :=
  map (fun i => Nat.pow n i) (seq 0 (S k)).

Lemma powerTrace_length : forall n k,
  length (powerTrace n k) = S k.
Proof. intros. unfold powerTrace. now rewrite map_length, seq_length. Qed.

Lemma powerTrace_nth : forall n k i,
  i <= k -> nth_error (powerTrace n k) i = Some (Nat.pow n i).
Proof.
  intros n k i hi. unfold powerTrace.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S k) eqn:hlt.
  - simpl. replace (0 + i) with i by lia. reflexivity.
  - apply Nat.ltb_ge in hlt. lia.
Qed.

Lemma PowerPosition_iff : forall m n k,
  PowerPosition m n k <-> PowerNat m n k.
Proof.
  intros m n k. split.
  - intros [trace [[xs [hdecode hlen]] [hbase [hfinal hstep]]]].
    assert (hinv : forall i, i <= k -> nth_error xs i = Some (Nat.pow n i)).
    {
      intros i hi. induction i as [|i IH].
      - apply (NthElement_decode trace 0 1 xs hdecode) in hbase.
        simpl. exact hbase.
      - assert (hil : i < k) by lia.
        specialize (IH ltac:(lia)).
        destruct (nth_error_exists_of_lt xs (S i) ltac:(lia)) as [next hn].
        assert (hcur : NthElement trace i (Nat.pow n i)).
        { apply (NthElement_decode trace i _ xs hdecode). exact IH. }
        assert (hnext : NthElement trace (S i) next).
        { apply (NthElement_decode trace (S i) next xs hdecode). exact hn. }
        pose proof (hstep i (Nat.pow n i) next hil hcur hnext) as hs.
        rewrite hn, hs. f_equal. rewrite Nat.pow_succ_r'. nia.
    }
    apply (NthElement_decode trace k m xs hdecode) in hfinal.
    specialize (hinv k ltac:(lia)). unfold PowerNat.
    rewrite hfinal in hinv. inversion hinv. reflexivity.
  - intro hpow. unfold PowerNat in hpow.
    set (xs := powerTrace n k).
    set (trace := listCode xs).
    exists trace. repeat split.
    + exists xs. split; [unfold trace; apply decode_listCode |].
      unfold xs. apply powerTrace_length.
    + exists xs. split; [unfold trace; apply decode_listCode |].
      unfold xs. rewrite powerTrace_nth by lia. reflexivity.
    + exists xs. split; [unfold trace; apply decode_listCode |].
      unfold xs. rewrite powerTrace_nth by lia. now rewrite hpow.
    + intros i cur next hi hcur hnext.
      apply (NthElement_decode trace i cur xs
        ltac:(unfold trace; apply decode_listCode)) in hcur.
      apply (NthElement_decode trace (S i) next xs
        ltac:(unfold trace; apply decode_listCode)) in hnext.
      unfold xs in hcur, hnext.
      rewrite powerTrace_nth in hcur by lia.
      rewrite powerTrace_nth in hnext by lia.
      inversion hcur; inversion hnext; subst cur next.
      nia.
Qed.

Lemma power_exists_unique : forall n k, exists! m, PowerNat m n k.
Proof.
  intros n k. exists (Nat.pow n k). split; [reflexivity |].
  intros y hy. symmetry. exact hy.
Qed.

(** * Canonical prime-factorization certificates *)

Definition FactorPair (c p e : nat) : Prop := decode c = Some [p; e].

(** The public value [v] is only the outer code.  The aligned prime,
    exponent, and power codes below are existential certificates.  Equal
    lengths and total indexing ensure that every outer entry is exactly the
    two-element code [[p;e]]. *)
Definition PrimeFactorizationCode (v n : nat) : Prop :=
  exists len primes exponents powers,
    0 < n /\
    HasLength v len /\
    HasLength primes len /\
    HasLength exponents len /\
    HasLength powers len /\
    StrictlyIncreasingCode primes /\
    ProductElementsCode n powers /\
    (forall i c p e w,
      i < len ->
      NthElement v i c ->
      NthElement primes i p ->
      NthElement exponents i e ->
      NthElement powers i w ->
      FactorPair c p e /\ PrimeNat p /\ 0 < e /\ PowerNat w p e).

Definition PrimeFactorizationList (cs : list nat) (n : nat) : Prop :=
  PrimeFactorizationCode (listCode cs) n.

Lemma primeFactorizationCode_valid : forall v n,
  PrimeFactorizationCode v n -> ValidCode v.
Proof.
  intros v n [len [ps [es [ws [_ [hv _]]]]]].
  exact (HasLength_valid v len hv).
Qed.

Lemma primeFactorizationCode_listCode : forall cs n,
  PrimeFactorizationCode (listCode cs) n <-> PrimeFactorizationList cs n.
Proof. reflexivity. Qed.

Lemma primeFactorization_zero_false : forall v,
  ~ PrimeFactorizationCode v 0.
Proof. intros v [len [ps [es [ws [h _]]]]]. lia. Qed.

Lemma primeFactorization_one_empty :
  PrimeFactorizationCode (listCode []) 1.
Proof.
  exists 0, (listCode []), (listCode []), (listCode []).
  split; [lia |]. split.
  - exists []; split; [apply decode_listCode | reflexivity].
  - split.
    + exists []; split; [apply decode_listCode | reflexivity].
    + split.
      * exists []; split; [apply decode_listCode | reflexivity].
      * split.
        -- exists []; split; [apply decode_listCode | reflexivity].
        -- split.
           ++ apply StrictlyIncreasingCode_listCode.
              intros i; destruct i; discriminate.
           ++ split.
              ** exists []; split; [apply decode_listCode | reflexivity].
              ** intros i c p e w hi. lia.
Qed.

(** * Canonical most-significant-digit-first base expansions *)

Definition digitStep (b acc d : nat) : nat := acc * b + d.

Definition evalDigits (b : nat) (ds : list nat) : nat :=
  fold_left (digitStep b) ds 0.

Definition DigitEvaluationPosition (v n b : nat) : Prop :=
  AggregatePosition (digitStep b) 0 n v.

Lemma DigitEvaluationPosition_iff : forall v n b,
  DigitEvaluationPosition v n b <->
  exists ds, decode v = Some ds /\ evalDigits b ds = n.
Proof.
  intros v n b. unfold DigitEvaluationPosition, evalDigits.
  apply AggregatePosition_iff.
Qed.

Definition BaseDigitsCode (v n b : nat) : Prop :=
  2 <= b /\
  DigitEvaluationPosition v n b /\
  (forall i d, NthElement v i d -> d < b) /\
  ((n = 0 /\ SingletonCode v 0) \/
   (0 < n /\ exists d, NthElement v 0 d /\ 0 < d)).

Definition CanonicalDigits (ds : list nat) (n b : nat) : Prop :=
  2 <= b /\
  evalDigits b ds = n /\
  Forall (fun d => d < b) ds /\
  ((n = 0 /\ ds = [0]) \/
   (0 < n /\ exists d rest, ds = d :: rest /\ 0 < d)).

Lemma nthElements_forall_iff : forall v xs (P : nat -> Prop),
  decode v = Some xs ->
  ((forall i d, NthElement v i d -> P d) <-> Forall P xs).
Proof.
  intros v xs P hv. split.
  - intro h. apply Forall_forall. intros d hd.
    apply In_nth_error in hd. destruct hd as [i hi].
    apply (h i d). exists xs. now split.
  - intros h i d hnth.
    apply (NthElement_decode v i d xs hv) in hnth.
    apply Forall_forall with (x := d) in h.
    + exact h.
    + apply nth_error_In with (n := i). exact hnth.
Qed.

Lemma baseDigitsCode_listCode : forall ds n b,
  BaseDigitsCode (listCode ds) n b <-> CanonicalDigits ds n b.
Proof.
  intros ds n b. unfold BaseDigitsCode, CanonicalDigits.
  rewrite DigitEvaluationPosition_iff.
  split.
  - intros [hb [[xs [hx heval]] [hbound hcanon]]].
    rewrite decode_listCode in hx. inversion hx; subst xs.
    repeat split; try assumption.
    + apply (proj1 (nthElements_forall_iff (listCode ds) ds _
        (decode_listCode ds))). exact hbound.
    + destruct hcanon as [[hn hs] | [hn [d [hd hdp]]]].
      * left. split; [exact hn |].
        unfold SingletonCode in hs. rewrite decode_listCode in hs.
        inversion hs. reflexivity.
      * right. split; [exact hn |].
        apply (NthElement_decode (listCode ds) 0 d ds
          (decode_listCode ds)) in hd.
        destruct ds as [|x rest]; [discriminate |].
        simpl in hd. inversion hd; subst x.
        exists d, rest. now split.
  - intros [hb [heval [hbound hcanon]]]. repeat split.
    + exact hb.
    + exists ds. split; [apply decode_listCode | exact heval].
    + apply (proj2 (nthElements_forall_iff (listCode ds) ds _
        (decode_listCode ds))). exact hbound.
    + destruct hcanon as [[hn hds] | [hn [d [rest [hds hd]]]]].
      * left. split; [exact hn |]. subst ds.
        unfold SingletonCode. apply decode_listCode.
      * right. split; [exact hn |]. exists d. split.
        -- subst ds. exists (d :: rest). split; [apply decode_listCode | reflexivity].
        -- exact hd.
Qed.

Lemma baseDigitsCode_valid : forall v n b,
  BaseDigitsCode v n b -> ValidCode v.
Proof.
  intros v n b [_ [heval _]].
  unfold DigitEvaluationPosition, AggregatePosition in heval.
  destruct heval as [len [trace [hv _]]]. exact (HasLength_valid v len hv).
Qed.

Lemma baseDigits_invalid_base_zero : forall v n,
  ~ BaseDigitsCode v n 0.
Proof. intros v n [h _]. lia. Qed.

Lemma baseDigits_invalid_base_one : forall v n,
  ~ BaseDigitsCode v n 1.
Proof. intros v n [h _]. lia. Qed.

Lemma baseDigits_zero : forall b,
  2 <= b -> BaseDigitsCode (listCode [0]) 0 b.
Proof.
  intros b hb. apply baseDigitsCode_listCode. unfold CanonicalDigits, evalDigits.
  repeat split; try assumption; simpl; try constructor; try lia.
  left. now split.
Qed.

(** * Canonical divisor lists *)

Definition DivisorListCode (v n : nat) : Prop :=
  0 < n /\
  ValidCode v /\
  StrictlyIncreasingCode v /\
  (forall i d, NthElement v i d -> 0 < d /\ Divides d n) /\
  (forall d, 0 < d -> d <= n -> Divides d n ->
    exists i, NthElement v i d).

(** Public vocabulary alias: the list contains exactly the positive
    divisors, so [PositiveDivisorsCode] and [DivisorListCode] coincide. *)
Definition PositiveDivisorsCode := DivisorListCode.

Definition CanonicalDivisors (ds : list nat) (n : nat) : Prop :=
  0 < n /\
  StrictlyIncreasing ds /\
  (forall d, In d ds <-> 0 < d /\ Divides d n).

Lemma divisorListCode_valid : forall v n,
  DivisorListCode v n -> ValidCode v.
Proof. intros v n [_ [h _]]. exact h. Qed.

Lemma divisorListCode_listCode : forall ds n,
  DivisorListCode (listCode ds) n <-> CanonicalDivisors ds n.
Proof.
  intros ds n. unfold DivisorListCode, CanonicalDivisors.
  rewrite StrictlyIncreasingCode_listCode.
  split.
  - intros [hn [_ [hs [hsound hcomplete]]]].
    split; [exact hn |]. split; [exact hs |]. intro d. split.
    + intro hd. apply In_nth_error in hd. destruct hd as [i hi].
      apply (hsound i d). exists ds. split; [apply decode_listCode | exact hi].
    + intros [hd hdiv].
      assert (hdle : d <= n).
      {
        destruct hdiv as [q hq].
        destruct q; simpl in hq; [lia |]. nia.
      }
      assert (hdiv' : Divides d n).
      { unfold Divides in *. destruct hdiv as [q hq]. now exists q. }
      destruct (hcomplete d hd hdle hdiv') as [i hi].
      apply (NthElement_decode (listCode ds) i d ds
        (decode_listCode ds)) in hi.
      now apply nth_error_In in hi.
  - intros [hn [hs hexact]].
    split; [exact hn |]. split; [apply ValidCode_listCode |].
    split; [exact hs |]. split.
    + intros i d hi.
      apply (NthElement_decode (listCode ds) i d ds
        (decode_listCode ds)) in hi.
      apply hexact. now apply nth_error_In in hi.
    + intros d hd hdle hdiv.
      assert (hin : In d ds).
      { apply hexact. now split. }
      apply In_nth_error in hin. destruct hin as [i hi].
      exists i, ds. split; [apply decode_listCode | exact hi].
Qed.

Lemma divisorList_zero_false : forall v, ~ DivisorListCode v 0.
Proof. intros v [h _]. lia. Qed.

Lemma divisorList_one : DivisorListCode (listCode [1]) 1.
Proof.
  apply divisorListCode_listCode. unfold CanonicalDivisors, StrictlyIncreasing.
  split; [lia |]. split.
  - intros i; destruct i; simpl; discriminate.
  - intro d. simpl. split.
    + intros [hd | []]. subst d. split; [lia | exists 1; reflexivity].
    + intros [hd hdiv]. left.
      assert (d <= 1) by (apply Nat.divide_pos_le; [lia | exact hdiv]). lia.
Qed.

Lemma positiveDivisorsCode_listCode : forall ds n,
  PositiveDivisorsCode (listCode ds) n <-> CanonicalDivisors ds n.
Proof. exact divisorListCode_listCode. Qed.

Lemma baseDigits_decimal_123 :
  BaseDigitsCode (listCode [1; 2; 3]) 123 10.
Proof.
  apply baseDigitsCode_listCode. unfold CanonicalDigits, evalDigits.
  split; [lia |]. split; [reflexivity |]. split.
  - repeat constructor; lia.
  - right. split; [lia |]. exists 1, [2; 3]. split; [reflexivity | lia].
Qed.

Lemma power_zero_zero : PowerNat 1 0 0.
Proof. reflexivity. Qed.

(** * Existence and uniqueness of the positive-divisor list *)

Lemma locallySorted_nth_error_lt : forall xs,
  LocallySorted lt xs <->
  forall i a b,
    nth_error xs i = Some a ->
    nth_error xs (S i) = Some b -> a < b.
Proof.
  induction xs as [|x xs IH].
  - split.
    + intros _ i a b h. destruct i; discriminate.
    + intros _. constructor.
  - destruct xs as [|y ys].
    + split.
      * intros _ i a b h1 h2. destruct i; discriminate.
      * intros _. constructor.
    + split.
      * intros h i a b h1 h2.
        inversion h as [| |a0 b0 l htail hxy]; subst.
        destruct i as [|i].
        -- simpl in h1, h2. inversion h1; inversion h2; subst. exact hxy.
        -- simpl in h1, h2. apply (proj1 IH htail i a b h1 h2).
      * intro h. constructor.
        -- apply (proj2 IH). intros i a b h1 h2.
           apply (h (S i) a b); simpl; assumption.
        -- exact (h 0 x y eq_refl eq_refl).
Qed.

Lemma StrictlyIncreasing_sorted_lt : forall xs,
  StrictlyIncreasing xs <-> Sorted lt xs.
Proof.
  intro xs. unfold StrictlyIncreasing.
  rewrite Sorted_LocallySorted_iff.
  symmetry. apply locallySorted_nth_error_lt.
Qed.

Lemma sorted_lt_sorted_le : forall xs,
  Sorted lt xs -> Sorted le xs.
Proof.
  intros xs h. induction h as [|x xs hs IH hhead].
  - constructor.
  - constructor; [exact IH |].
    inversion hhead; subst; constructor; lia.
Qed.

Lemma sorted_lt_nodup : forall xs,
  Sorted lt xs -> NoDup xs.
Proof.
  intros xs hsorted. induction hsorted as [|x xs hs IH hhead].
  - constructor.
  - constructor.
    + intro hin.
      pose proof (Sorted_extends Nat.lt_trans
        (Sorted_cons hs hhead)) as hall.
      apply Forall_forall with (x := x) in hall; [lia | exact hin].
    + exact IH.
Qed.

Lemma sorted_le_nodup_strict : forall xs,
  Sorted le xs -> NoDup xs -> StrictlyIncreasing xs.
Proof.
  intros xs hsorted hnodup. unfold StrictlyIncreasing.
  intros i a b hia hib.
  pose proof (proj1 (Sorted_LocallySorted_iff le xs) hsorted) as hlocal.
  pose proof (proj1 (locallySorted_nth_error xs) hlocal i a b hia hib) as hab.
  assert (a <> b).
  {
    intro heq. subst b.
    assert (hi : i < length xs).
    { apply nth_error_Some. rewrite hia. discriminate. }
    pose proof (proj1 (NoDup_nth_error xs) hnodup i (S i) hi) as hindex.
    assert (i = S i) by (apply hindex; now rewrite hia, hib).
    lia.
  }
  lia.
Qed.

Definition divisorCandidates (n : nat) : list nat :=
  filter (fun d => Nat.eqb (n mod d) 0) (seq 1 n).

Definition canonicalDivisorList (n : nat) : list nat :=
  NatSort.sort (divisorCandidates n).

Lemma divisorCandidates_spec : forall n d,
  In d (divisorCandidates n) <->
  0 < d /\ d <= n /\ Divides d n.
Proof.
  intros n d. unfold divisorCandidates.
  rewrite filter_In, in_seq. split.
  - intros [[hlo hhi] hmod].
    apply Nat.eqb_eq in hmod. repeat split; try lia.
    unfold Divides. apply (proj1 (Nat.mod_divide n d ltac:(lia))). exact hmod.
  - intros [hd [hdn hdiv]]. split.
    + split; lia.
    + apply Nat.eqb_eq.
      apply (proj2 (Nat.mod_divide n d ltac:(lia))). exact hdiv.
Qed.

Lemma canonicalDivisorList_permutation : forall n,
  Permutation (divisorCandidates n) (canonicalDivisorList n).
Proof. intro n. unfold canonicalDivisorList. apply NatSort.Permuted_sort. Qed.

Lemma canonicalDivisorList_strict : forall n,
  StrictlyIncreasing (canonicalDivisorList n).
Proof.
  intro n. apply sorted_le_nodup_strict.
  - unfold canonicalDivisorList. apply NatSort_sorted_le.
  - apply (Permutation_NoDup (canonicalDivisorList_permutation n)).
    apply NoDup_filter. apply seq_NoDup.
Qed.

Lemma canonicalDivisorList_spec : forall n,
  0 < n -> CanonicalDivisors (canonicalDivisorList n) n.
Proof.
  intros n hn. unfold CanonicalDivisors.
  split; [exact hn |]. split; [apply canonicalDivisorList_strict |].
  intro d.
  assert (hperm : In d (canonicalDivisorList n) <->
      In d (divisorCandidates n)).
  {
    split; intro hin.
    - eapply Permutation_in; [apply Permutation_sym;
        apply canonicalDivisorList_permutation | exact hin].
    - eapply Permutation_in; [apply canonicalDivisorList_permutation | exact hin].
  }
  rewrite hperm.
  rewrite divisorCandidates_spec. split.
  - intros [hd [_ hdiv]]. now split.
  - intros [hd hdiv]. repeat split; try assumption.
    apply Nat.divide_pos_le; assumption.
Qed.

Theorem divisorListCode_exists : forall n,
  0 < n -> exists v, DivisorListCode v n.
Proof.
  intros n hn. exists (listCode (canonicalDivisorList n)).
  apply divisorListCode_listCode. apply canonicalDivisorList_spec. exact hn.
Qed.

Lemma CanonicalDivisors_unique : forall xs ys n,
  CanonicalDivisors xs n -> CanonicalDivisors ys n -> xs = ys.
Proof.
  intros xs ys n [_ [hxs hspecx]] [_ [hys hspecy]].
  apply sorted_permutation_unique.
  - apply sorted_lt_sorted_le. apply StrictlyIncreasing_sorted_lt. exact hxs.
  - apply sorted_lt_sorted_le. apply StrictlyIncreasing_sorted_lt. exact hys.
  - apply NoDup_Permutation.
    + apply sorted_lt_nodup. apply StrictlyIncreasing_sorted_lt. exact hxs.
    + apply sorted_lt_nodup. apply StrictlyIncreasing_sorted_lt. exact hys.
    + intro d. rewrite hspecx, hspecy. reflexivity.
Qed.

Theorem divisorListCode_functional : forall v w n,
  DivisorListCode v n -> DivisorListCode w n -> v = w.
Proof.
  intros v w n hv hw.
  destruct (divisorListCode_valid v n hv) as [xs hdx].
  destruct (divisorListCode_valid w n hw) as [ys hdy].
  assert (hcv : listCode xs = v) by now apply listCode_decode.
  assert (hcw : listCode ys = w) by now apply listCode_decode.
  rewrite <- hcv in hv. rewrite <- hcw in hw.
  apply divisorListCode_listCode in hv.
  apply divisorListCode_listCode in hw.
  subst v w. f_equal. exact (CanonicalDivisors_unique xs ys n hv hw).
Qed.

Theorem positiveDivisorsCode_exists : forall n,
  0 < n -> exists v, PositiveDivisorsCode v n.
Proof. exact divisorListCode_exists. Qed.

Theorem positiveDivisorsCode_functional : forall v w n,
  PositiveDivisorsCode v n -> PositiveDivisorsCode w n -> v = w.
Proof. exact divisorListCode_functional. Qed.

(** * Existence and uniqueness of canonical base digits *)

Lemma fold_left_digitStep_decompose : forall b ds acc,
  fold_left (digitStep b) ds acc =
  acc * Nat.pow b (length ds) + evalDigits b ds.
Proof.
  intros b ds. induction ds as [|d ds IH]; intro acc.
  - simpl. unfold evalDigits. simpl. lia.
  - change (fold_left (digitStep b) ds (acc * b + d) =
      acc * b ^ S (length ds) +
      fold_left (digitStep b) ds d).
    rewrite (IH (acc * b + d)), (IH d), Nat.pow_succ_r by lia.
    nia.
Qed.

Lemma evalDigits_cons : forall b d ds,
  evalDigits b (d :: ds) =
  d * Nat.pow b (length ds) + evalDigits b ds.
Proof.
  intros b d ds. unfold evalDigits at 1. simpl.
  unfold digitStep. simpl.
  apply fold_left_digitStep_decompose.
Qed.

Lemma evalDigits_app_singleton : forall b ds d,
  evalDigits b (ds ++ [d]) = evalDigits b ds * b + d.
Proof.
  intros b ds d. unfold evalDigits. rewrite fold_left_app. simpl.
  unfold digitStep. reflexivity.
Qed.

Lemma evalDigits_upper_bound : forall b ds,
  0 < b -> Forall (fun d => d < b) ds ->
  evalDigits b ds < Nat.pow b (length ds).
Proof.
  intros b ds hb hdigits. induction hdigits as [|d ds hd hds IH].
  - simpl. unfold evalDigits. simpl. lia.
  - rewrite evalDigits_cons. simpl length.
    rewrite Nat.pow_succ_r by lia.
    assert (0 < b ^ length ds).
    { pose proof (Nat.pow_nonzero b (length ds) ltac:(lia)). lia. }
    nia.
Qed.

Lemma evalDigits_lower_head : forall b d ds,
  0 < b -> 0 < d ->
  Nat.pow b (length ds) <= evalDigits b (d :: ds).
Proof.
  intros b d ds hb hd. rewrite evalDigits_cons.
  assert (0 < b ^ length ds).
  { pose proof (Nat.pow_nonzero b (length ds) ltac:(lia)). lia. }
  nia.
Qed.

Lemma evalDigits_injective_same_length : forall b xs ys,
  0 < b ->
  length xs = length ys ->
  Forall (fun d => d < b) xs ->
  Forall (fun d => d < b) ys ->
  evalDigits b xs = evalDigits b ys -> xs = ys.
Proof.
  intros b xs. induction xs as [|x xs IH];
    intros ys hb hlen hxs hys heval.
  - destruct ys; [reflexivity | discriminate].
  - destruct ys as [|y ys]; [discriminate |].
    inversion hxs as [|? ? hx hxt]; subst.
    inversion hys as [|? ? hy hyt]; subst.
    simpl in hlen. injection hlen as htail.
    rewrite !evalDigits_cons in heval.
    rewrite <- htail in heval.
    assert (hrx : evalDigits b xs < b ^ length xs).
    { apply evalDigits_upper_bound; assumption. }
    assert (hry : evalDigits b ys < b ^ length xs).
    { rewrite htail. apply evalDigits_upper_bound; assumption. }
    assert (hq : 0 < b ^ length xs).
    { pose proof (Nat.pow_nonzero b (length xs) ltac:(lia)). lia. }
    assert (hxy : x = y) by nia. subst y. f_equal.
    apply (IH ys hb htail hxt hyt). nia.
Qed.

Lemma CanonicalDigits_unique : forall xs ys n b,
  CanonicalDigits xs n b -> CanonicalDigits ys n b -> xs = ys.
Proof.
  intros xs ys n b
    [hb [hevalx [hboundx hcanonx]]]
    [_ [hevaly [hboundy hcanony]]].
  destruct hcanonx as [[hn hx] | [hn [x [xt [hx hxp]]]]];
    destruct hcanony as [[hn' hy] | [hn' [y [yt [hy hyp]]]]].
  - now rewrite hx, hy.
  - lia.
  - lia.
  - subst xs ys.
    assert (hlen : length (x :: xt) = length (y :: yt)).
    {
      destruct (Nat.lt_trichotomy (length xt) (length yt))
        as [hlt | [heq | hgt]].
      - assert (hupper : evalDigits b (x :: xt) < b ^ S (length xt)).
        { apply evalDigits_upper_bound; [lia | exact hboundx]. }
        assert (hlower : b ^ length yt <= evalDigits b (y :: yt)).
        { apply evalDigits_lower_head; [lia | exact hyp]. }
        assert (hpow : b ^ S (length xt) <= b ^ length yt).
        { apply Nat.pow_le_mono_r; lia. }
        lia.
      - simpl. lia.
      - assert (hupper : evalDigits b (y :: yt) < b ^ S (length yt)).
        { apply evalDigits_upper_bound; [lia | exact hboundy]. }
        assert (hlower : b ^ length xt <= evalDigits b (x :: xt)).
        { apply evalDigits_lower_head; [lia | exact hxp]. }
        assert (hpow : b ^ S (length yt) <= b ^ length xt).
        { apply Nat.pow_le_mono_r; lia. }
        lia.
    }
    apply (evalDigits_injective_same_length b (x :: xt) (y :: yt));
      try assumption; lia.
Qed.

Theorem canonicalDigits_exists : forall b n,
  2 <= b -> exists ds, CanonicalDigits ds n b.
Proof.
  intros b n hb. pattern n. apply lt_wf_ind.
  intros x IH. destruct x as [|x].
  - exists [0]. unfold CanonicalDigits, evalDigits.
    split; [exact hb |]. split; [reflexivity |]. split.
    + repeat constructor; lia.
    + left. now split.
  - set (q := S x / b).
    destruct (Nat.eq_dec q 0) as [hq0 | hqpos].
    + assert (hsmall : S x < b).
      { apply (proj1 (Nat.div_small_iff (S x) b ltac:(lia))). exact hq0. }
      exists [S x]. unfold CanonicalDigits, evalDigits.
      split; [exact hb |]. split; [reflexivity |]. split.
      * repeat constructor; lia.
      * right. split; [lia |]. exists (S x), [].
        split; [reflexivity | lia].
    + assert (hq_lt : q < S x).
      { unfold q. apply Nat.div_lt; lia. }
      destruct (IH q hq_lt) as [ds
        [hb' [heval [hbound hcanon]]]].
      assert (hq : 0 < q) by lia.
      destruct hcanon as [[hqzero hds] |
          [hqpositive [d [rest [hds hd]]]]]; [lia |].
      exists (ds ++ [S x mod b]). unfold CanonicalDigits.
      split; [exact hb |]. split.
      * rewrite evalDigits_app_singleton, heval.
        pose proof (Nat.div_mod (S x) b ltac:(lia)). unfold q in *. nia.
      * split.
        -- apply Forall_app. split; [exact hbound |]. constructor.
           ++ apply Nat.mod_upper_bound. lia.
           ++ constructor.
        -- right. split; [lia |]. exists d, (rest ++ [S x mod b]).
           subst ds. rewrite <- app_comm_cons. now split.
Qed.

Theorem baseDigitsCode_exists : forall n b,
  2 <= b -> exists v, BaseDigitsCode v n b.
Proof.
  intros n b hb. destruct (canonicalDigits_exists b n hb) as [ds hds].
  exists (listCode ds). apply baseDigitsCode_listCode. exact hds.
Qed.

Theorem baseDigitsCode_functional : forall v w n b,
  BaseDigitsCode v n b -> BaseDigitsCode w n b -> v = w.
Proof.
  intros v w n b hv hw.
  destruct (baseDigitsCode_valid v n b hv) as [xs hdx].
  destruct (baseDigitsCode_valid w n b hw) as [ys hdy].
  assert (hcv : listCode xs = v) by now apply listCode_decode.
  assert (hcw : listCode ys = w) by now apply listCode_decode.
  rewrite <- hcv in hv. rewrite <- hcw in hw.
  apply baseDigitsCode_listCode in hv.
  apply baseDigitsCode_listCode in hw.
  subst v w. f_equal. exact (CanonicalDigits_unique xs ys n b hv hw).
Qed.

(** * Functionality of the one-based prime enumeration *)

Definition PrimeBelowList (p : nat) (xs : list nat) : Prop :=
  StrictlyIncreasing xs /\
  forall q, In q xs <-> PrimeNat q /\ q < p.

Lemma NthPrime_list_certificate : forall p n,
  NthPrime p n <->
  PrimeNat p /\
  exists xs,
    n = S (length xs) /\ PrimeBelowList p xs.
Proof.
  intros p n. split.
  - intros [hp [k [below
      [hindex [hlen [hstrict [hsound hcomplete]]]]]]].
    destruct hlen as [xs [hdecode hlength]].
    split; [exact hp |]. exists xs. split.
    + now rewrite hlength.
    + split.
      * apply (proj1 (StrictlyIncreasingCode_decode below xs hdecode)).
        exact hstrict.
      * intro q. split.
        -- intro hin. apply In_nth_error in hin. destruct hin as [i hi].
           apply (hsound i q). exists xs. now split.
        -- intro hq. destruct (hcomplete q hq) as [i hi].
           apply (NthElement_decode below i q xs hdecode) in hi.
           now apply nth_error_In in hi.
  - intros [hp [xs [hindex [hstrict hexact]]]].
    split; [exact hp |]. exists (length xs), (listCode xs).
    split; [exact hindex |]. split.
    + exists xs. split; [apply decode_listCode | reflexivity].
    + split.
      * apply StrictlyIncreasingCode_listCode. exact hstrict.
      * split.
        -- intros i q hi. apply hexact.
           apply (NthElement_decode (listCode xs) i q xs
             (decode_listCode xs)) in hi.
           now apply nth_error_In in hi.
        -- intros q hq. apply hexact in hq.
           apply In_nth_error in hq. destruct hq as [i hi].
           exists i, xs. split; [apply decode_listCode | exact hi].
Qed.

Lemma PrimeBelowList_nodup : forall p xs,
  PrimeBelowList p xs -> NoDup xs.
Proof.
  intros p xs [hstrict _].
  apply sorted_lt_nodup. apply StrictlyIncreasing_sorted_lt. exact hstrict.
Qed.

Theorem nthPrime_index_functional : forall p n m,
  NthPrime p n -> NthPrime p m -> n = m.
Proof.
  intros p n m hn hm.
  apply NthPrime_list_certificate in hn.
  apply NthPrime_list_certificate in hm.
  destruct hn as [_ [xs [hn hxs]]].
  destruct hm as [_ [ys [hm hys]]].
  assert (hxy : incl xs ys).
  {
    intros q hq. apply (proj2 (proj2 hys q)).
    apply (proj1 (proj2 hxs q)). exact hq.
  }
  assert (hyx : incl ys xs).
  {
    intros q hq. apply (proj2 (proj2 hxs q)).
    apply (proj1 (proj2 hys q)). exact hq.
  }
  pose proof (NoDup_incl_length (PrimeBelowList_nodup p xs hxs)
    hxy) as hle.
  pose proof (NoDup_incl_length (PrimeBelowList_nodup p ys hys)
    hyx) as hge.
  lia.
Qed.

Theorem nthPrime_prime_functional : forall p q n,
  NthPrime p n -> NthPrime q n -> p = q.
Proof.
  intros p q n hp hq.
  apply NthPrime_list_certificate in hp.
  apply NthPrime_list_certificate in hq.
  destruct hp as [hpp [xs [hindexp hxs]]].
  destruct hq as [hqp [ys [hindexq hys]]].
  destruct (Nat.lt_trichotomy p q) as [hpq | [hpq | hqp']];
    [|exact hpq|].
  - assert (hxy : incl xs ys).
    {
      intros r hr. apply (proj2 (proj2 hys r)).
      apply (proj1 (proj2 hxs r)) in hr. destruct hr as [hpr hr].
      split; [exact hpr | lia].
    }
    assert (hyx : incl ys xs).
    {
      apply (NoDup_length_incl (PrimeBelowList_nodup p xs hxs));
        [lia | exact hxy].
    }
    assert (hpin : In p ys).
    { apply (proj2 (proj2 hys p)). now split. }
    apply hyx in hpin. apply (proj1 (proj2 hxs p)) in hpin. lia.
  - assert (hyx : incl ys xs).
    {
      intros r hr. apply (proj2 (proj2 hxs r)).
      apply (proj1 (proj2 hys r)) in hr. destruct hr as [hpr hr].
      split; [exact hpr | lia].
    }
    assert (hxy : incl xs ys).
    {
      apply (NoDup_length_incl (PrimeBelowList_nodup q ys hys));
        [lia | exact hyx].
    }
    assert (hqin : In q xs).
    { apply (proj2 (proj2 hxs q)). now split. }
    apply hxy in hqin. apply (proj1 (proj2 hys q)) in hqin. lia.
Qed.

End PAListNumberTheory.
