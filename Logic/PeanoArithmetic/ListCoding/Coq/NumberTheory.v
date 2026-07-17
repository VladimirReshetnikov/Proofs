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
  Sorting.Permutation Sorting.Sorted.
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

End PAListNumberTheory.
