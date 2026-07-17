(**
  Natural existence and uniqueness for one-based prime indices and canonical
  prime-factorization certificates, using MathComp's verified unbounded-prime
  and [prime_decomp] results.  This integration is deliberately isolated from
  the PA syntax development.
*)

From Stdlib Require Import List Arith Lia Sorting.Sorted.
From PAListCoding Require Import ListCode ListFormulas NumberTheory.
From mathcomp.boot Require Import all_boot prime.

Import ListNotations.

Module PAListNumberTheoryFactorization.

Import PAListCode.
Import PAListFormulas.
Import PAListNumberTheory.
Import Monoid.Theory.
Local Open Scope big_scope.

Lemma mathcomp_prime_iff : forall p,
  prime p <-> PrimeNat p.
Proof.
  intro p. split.
  - move/primeP=> [hp hdiv]. split.
    + exact (elimT ltP hp).
    + intros d [k hk].
      have hdvd : d %| p by apply/dvdnP; exists k.
      move: (hdiv d hdvd)=> /orP[/eqP hd1 | /eqP hdp].
      * now left.
      * now right.
  - intros [hp hdiv]. apply/primeP. split.
    + exact (introT ltP hp).
    + move=> d /dvdnP [k hk]. apply/orP.
      destruct (hdiv d (ex_intro _ k hk)) as [hd | hd].
      * left. exact (introT eqP hd).
      * right. exact (introT eqP hd).
Qed.

Lemma nth_error_mathcomp_nth : forall (A : Type) (x0 x : A) xs i,
  nth_error xs i = Some x -> nth x0 xs i = x.
Proof.
  intros A x0 x xs. induction xs as [|y ys IH]; intros i hi.
  - destruct i; discriminate.
  - destruct i as [|i].
    + simpl in hi. inversion hi. reflexivity.
    + simpl in hi |- *. exact (IH i hi).
Qed.

Lemma nth_error_mathcomp_nth_some : forall (A : Type) (x0 : A) xs i,
  (i < List.length xs)%coq_nat ->
  nth_error xs i = Some (nth x0 xs i).
Proof.
  intros A x0 xs. induction xs as [|x xs IH]; intros i hi.
  - simpl in hi. lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl in hi |- *. apply IH. lia.
Qed.

Lemma mathcomp_sorted_strict : forall xs,
  sorted ltn xs -> StrictlyIncreasing xs.
Proof.
  intros xs hs i a b hia hib.
  have hsP := elimT (@sortedP nat ltn xs 0) hs.
  assert (hi : (i.+1 < size xs)%coq_nat).
  { apply nth_error_Some. rewrite hib. discriminate. }
  have hibound : i.+1 < size xs := introT ltP hi.
  have hab := hsP i hibound.
  assert (hni : nth 0 xs i = a).
  { exact (nth_error_mathcomp_nth nat 0 a xs i hia). }
  assert (hnsi : nth 0 xs i.+1 = b).
  { exact (nth_error_mathcomp_nth nat 0 b xs i.+1 hib). }
  rewrite hni hnsi in hab. exact (elimT ltP hab).
Qed.

Lemma strict_mathcomp_sorted : forall xs,
  StrictlyIncreasing xs -> sorted ltn xs.
Proof.
  intros xs hs. apply/(sortedP 0).
  move=> i hi. apply/ltP.
  apply (hs i (nth 0 xs i) (nth 0 xs i.+1)).
  - apply nth_error_mathcomp_nth_some.
    exact (elimT ltP (ltn_trans (ltnSn i) hi)).
  - apply nth_error_mathcomp_nth_some. exact (elimT ltP hi).
Qed.

Lemma mem_seq_In : forall (x : nat) (xs : list nat),
  x \in xs <-> In x xs.
Proof.
  intros x xs. induction xs as [|y ys IH].
  - simpl. split; [discriminate | contradiction].
  - rewrite inE. split.
    + move/orP=> [/eqP -> | h].
      * now left.
      * right. apply (proj1 IH). exact h.
    + intros [-> | h].
      * apply/orP. left. apply/eqP. reflexivity.
      * apply/orP. right. apply (proj2 IH). exact h.
Qed.

Lemma seq_map_List_map : forall (A B : Type) (f : A -> B) xs,
  [seq f x | x <- xs] = List.map f xs.
Proof.
  intros A B f xs. induction xs as [|x xs IH]; simpl; now f_equal.
Qed.

(** MathComp supplies unbounded primes.  Boolean minimization turns that
    result into the least prime strictly above any given number. *)
Lemma least_prime_above : forall p,
  exists q,
    PrimeNat q /\
    (p < q)%coq_nat /\
    forall r, PrimeNat r -> (p < r)%coq_nat -> (q <= r)%coq_nat.
Proof.
  intro p.
  set (P := fun q : nat => (p < q) && prime q).
  assert (hex : exists q, P q).
  {
    destruct (prime_above p) as [q hpq hprime].
    exists q. unfold P. apply/andP. now split.
  }
  pose (q := ex_minn hex).
  have hspec := ex_minnP hex.
  destruct hspec as [m hP hmin].
  unfold P in hP. move: hP=> /andP [hpq hprime].
  exists q. split.
  - apply mathcomp_prime_iff. exact hprime.
  - split.
    + exact (elimT ltP hpq).
    + intros r hr hpr. apply (elimT leP).
      apply hmin. unfold P. apply/andP. split.
      * exact (introT ltP hpr).
      * apply mathcomp_prime_iff in hr. exact hr.
Qed.

Lemma sorted_lt_snoc : forall xs p,
  Sorted lt xs ->
  (forall x, In x xs -> (x < p)%coq_nat) ->
  Sorted lt (xs ++ [p]).
Proof.
  intros xs p hsorted. induction hsorted as [|x xs hsorted IH hhead];
    intro hall.
  - simpl. constructor; constructor.
  - simpl. constructor.
    + apply IH. intros y hy. apply hall. now right.
    + destruct xs as [|y ys].
      * constructor. apply hall. now left.
      * inversion hhead; subst. now constructor.
Qed.

Lemma strictlyIncreasing_snoc : forall xs p,
  StrictlyIncreasing xs ->
  (forall x, In x xs -> (x < p)%coq_nat) ->
  StrictlyIncreasing (xs ++ [p]).
Proof.
  intros xs p hstrict hall.
  apply (proj2 (StrictlyIncreasing_sorted_lt (xs ++ [p]))).
  apply sorted_lt_snoc.
  - apply (proj1 (StrictlyIncreasing_sorted_lt xs)). exact hstrict.
  - exact hall.
Qed.

Lemma PrimeBelowList_snoc_next : forall p q xs,
  PrimeNat p ->
  PrimeBelowList p xs ->
  PrimeNat q ->
  (p < q)%coq_nat ->
  (forall r, PrimeNat r -> (p < r)%coq_nat -> (q <= r)%coq_nat) ->
  PrimeBelowList q (xs ++ [p]).
Proof.
  intros p q xs hp [hstrict hexact] hq hpq hleast.
  split.
  - apply strictlyIncreasing_snoc; [exact hstrict |].
    intros x hx. apply hexact in hx. exact (proj2 hx).
  - intro r. rewrite in_app_iff. simpl. split.
    + intros [hr | [hr | hr]].
      * apply hexact in hr. destruct hr as [hprime hrp].
        split; [exact hprime | lia].
      * subst r. now split.
      * contradiction.
    + intros [hprime hrq].
      destruct (Nat.lt_trichotomy r p) as [hrp | [hrp | hpr]].
      * left. apply hexact. now split.
      * right. now left.
      * pose proof (hleast r hprime hpr) as hqr. lia.
Qed.

Lemma nthPrime_successor_exists : forall p n,
  NthPrime p n -> exists q, NthPrime q (S n).
Proof.
  intros p n hp.
  apply NthPrime_list_certificate in hp.
  destruct hp as [hp [xs [hn hbelow]]].
  destruct (least_prime_above p) as [q [hq [hpq hleast]]].
  exists q. apply NthPrime_list_certificate. split; [exact hq |].
  exists (xs ++ [p]). split.
  - rewrite length_app. simpl. lia.
  - now apply PrimeBelowList_snoc_next.
Qed.

Lemma nthPrime_positive_exists : forall n,
  (0 < n)%coq_nat -> exists p, NthPrime p n.
Proof.
  intros [|k] hn; [lia |]. clear hn.
  induction k as [|k IH].
  - exists 2. exact nthPrime_two_one.
  - destruct IH as [p hp].
    destruct (nthPrime_successor_exists p (S k) hp) as [q hq].
    now exists q.
Qed.

Theorem nthPrime_exists_unique : forall n,
  (0 < n)%coq_nat -> exists! p, NthPrime p n.
Proof.
  intros n hn. destruct (nthPrime_positive_exists n hn) as [p hp].
  exists p. split; [exact hp |].
  intros q hq. exact (nthPrime_prime_functional p q n hp hq).
Qed.

Theorem nthPrime_index_exists_unique : forall p,
  PrimeNat p -> exists! n, NthPrime p n.
Proof.
  intros p hp.
  set (xs := [seq q <- iota 0 p | prime q]).
  assert (hbelow : PrimeBelowList p xs).
  {
    split.
    - apply mathcomp_sorted_strict. unfold xs.
      apply sorted_filter; [exact ltn_trans | apply iota_ltn_sorted].
    - intro q. split.
      + intro hin.
        assert (hmem : q \in xs).
        { apply (proj2 (mem_seq_In q xs)). exact hin. }
        unfold xs in hmem. rewrite mem_filter mem_iota in hmem.
        move: hmem=> /andP [hprime /andP [_ hqp]].
        split.
        * apply mathcomp_prime_iff. exact hprime.
        * rewrite add0n in hqp. exact (elimT ltP hqp).
      + intros [hprime hqp].
        apply (proj1 (mem_seq_In q xs)). unfold xs.
        rewrite mem_filter mem_iota. apply/andP. split.
        * apply mathcomp_prime_iff in hprime. exact hprime.
        * apply/andP. split; [apply leq0n |].
          rewrite add0n. exact (introT ltP hqp).
  }
  assert (hnth : NthPrime p (S (length xs))).
  {
    apply NthPrime_list_certificate. split; [exact hp |].
    exists xs. now split.
  }
  exists (S (length xs)). split; [exact hnth |].
  intros n hn. exact (nthPrime_index_functional p (S (length xs)) n hnth hn).
Qed.

Definition factorCodes (pd : list (nat * nat)) : list nat :=
  List.map (fun pe => listCode [fst pe; snd pe]) pd.

Definition factorPrimes (pd : list (nat * nat)) : list nat :=
  List.map fst pd.

Definition factorExponents (pd : list (nat * nat)) : list nat :=
  List.map snd pd.

Definition factorPowers (pd : list (nat * nat)) : list nat :=
  List.map (fun pe => Nat.pow (fst pe) (snd pe)) pd.

Definition TypedPrimeFactorization (pd : list (nat * nat)) (n : nat) : Prop :=
  StrictlyIncreasing (factorPrimes pd) /\
  Forall (fun pe => PrimeNat (fst pe) /\ (0 < snd pe)%coq_nat) pd /\
  natListProduct (factorPowers pd) = n.

Lemma aligned_lists_to_pairs : forall len cs ps es ws,
  List.length cs = len ->
  List.length ps = len ->
  List.length es = len ->
  List.length ws = len ->
  (forall i c p e w,
    (i < len)%coq_nat ->
    nth_error cs i = Some c ->
    nth_error ps i = Some p ->
    nth_error es i = Some e ->
    nth_error ws i = Some w ->
    FactorPair c p e /\ PrimeNat p /\ (0 < e)%coq_nat /\ PowerNat w p e) ->
  exists pd,
    cs = factorCodes pd /\
    ps = factorPrimes pd /\
    es = factorExponents pd /\
    ws = factorPowers pd /\
    Forall (fun pe => PrimeNat (fst pe) /\ (0 < snd pe)%coq_nat) pd.
Proof.
  induction len as [|len IH]; intros cs ps es ws hcs hps hes hws halign.
  - apply length_zero_iff_nil in hcs, hps, hes, hws. subst.
    exists []. repeat split; constructor.
  - destruct cs as [|c cs]; [discriminate |].
    destruct ps as [|p ps]; [discriminate |].
    destruct es as [|e es]; [discriminate |].
    destruct ws as [|w ws]; [discriminate |].
    simpl in hcs, hps, hes, hws. injection hcs as hcs.
    injection hps as hps. injection hes as hes. injection hws as hws.
    destruct (halign 0 c p e w ltac:(lia)
      ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity) ltac:(reflexivity))
      as [hpair [hprime [hepos hpower]]].
    destruct (IH cs ps es ws hcs hps hes hws) as
      [pd [hcst [hpst [hest [hwst hall]]]]].
    {
      intros i c' p' e' w' hi hc hp he hw.
      apply (halign (S i) c' p' e' w'); simpl; try assumption; lia.
    }
    exists ((p, e) :: pd). split.
    + unfold FactorPair in hpair.
      pose proof (listCode_decode c [p; e] hpair) as hc.
      subst c. unfold factorCodes in hcst |- *. simpl. now f_equal.
    + split; [simpl; now f_equal |].
      split; [simpl; now f_equal |]. split.
      * simpl. f_equal; [exact hpower | exact hwst].
      * constructor; [now split | exact hall].
Qed.

(** Every public certificate can be recovered as a typed, aligned list of
    prime/exponent pairs.  This direction is useful both for auditing the
    positional encoding and for reducing functionality to ordinary unique
    factorization. *)
Lemma primeFactorizationCode_typed : forall v n,
  PrimeFactorizationCode v n ->
  exists pd,
    decode v = Some (factorCodes pd) /\
    TypedPrimeFactorization pd n.
Proof.
  intros v n
    [len [primes [exponents [powers
      [hn [hv [hprimes [hexponents [hpowers
        [hincreasing [hproduct halign]]]]]]]]]]].
  destruct hv as [cs [hv hcs]].
  destruct hprimes as [ps [hprimes hps]].
  destruct hexponents as [es [hexponents hes]].
  destruct hpowers as [ws [hpowers hws]].
  destruct hproduct as [ws' [hpowers' hproduct]].
  pose proof (decode_functional powers ws ws' hpowers hpowers') as hws'.
  subst ws'.
  assert (hincreasing' : StrictlyIncreasing ps).
  {
    apply (proj1 (StrictlyIncreasingCode_decode primes ps hprimes)).
    exact hincreasing.
  }
  destruct (aligned_lists_to_pairs len cs ps es ws
    hcs hps hes hws) as
    [pd [hcs' [hps' [hes' [hws' hall]]]]].
  {
    intros i c p e w hi hc hp he hw.
    apply (halign i c p e w hi).
    - exists cs. now split.
    - exists ps. now split.
    - exists es. now split.
    - exists ws. now split.
  }
  subst cs ps es ws.
  exists pd. split; [exact hv |].
  unfold TypedPrimeFactorization.
  repeat split; assumption.
Qed.

Lemma expn_eq_pow : forall p e, p ^ e = Nat.pow p e.
Proof.
  intros p e. induction e as [|e IH].
  - rewrite expn0. reflexivity.
  - rewrite expnS IH mulnE. reflexivity.
Qed.

Lemma natListProduct_factorPowers : forall pd,
  natListProduct (factorPowers pd) =
  \prod_(pe <- pd) (fst pe) ^ (snd pe).
Proof.
  induction pd as [|[p e] pd IH]; simpl.
  - rewrite big_nil. reflexivity.
  - rewrite big_cons mulnE expn_eq_pow IH. reflexivity.
Qed.

Lemma factorPowers_product_positive : forall pd,
  Forall (fun pe => PrimeNat (fst pe) /\ (0 < snd pe)%coq_nat) pd ->
  (0 < natListProduct (factorPowers pd))%coq_nat.
Proof.
  intros pd hall. induction hall as [|[p e] pd [hprime hepos] hall IH].
  - simpl. lia.
  - simpl. apply Nat.mul_pos_pos.
    + apply (proj1 (Nat.neq_0_lt_0 (Nat.pow p e))).
      apply Nat.pow_nonzero.
      destruct hprime as [hp _]. intro hp0. subst p. inversion hp.
    + exact IH.
Qed.

Lemma logn_factorPowers_absent : forall q pd,
  Forall (fun pe => PrimeNat (fst pe) /\ (0 < snd pe)%coq_nat) pd ->
  ~ In q (factorPrimes pd) ->
  logn q (natListProduct (factorPowers pd)) = 0.
Proof.
  intros q pd. induction pd as [|[p e] pd IH]; intros hall habsent.
  - simpl. apply logn1.
  - inversion hall as [|? ? [hprime hepos] hall']; subst.
    assert (hqp : q <> p).
    { intro h. apply habsent. subst q. simpl. now left. }
    assert (habsent' : ~ In q (factorPrimes pd)).
    { intro h. apply habsent. simpl. now right. }
    cbn [factorPowers natListProduct].
    rewrite lognM.
    + change (logn q (Nat.pow p e) +
        logn q (natListProduct (factorPowers pd)) = 0).
      rewrite <- (expn_eq_pow p e), lognX.
      apply mathcomp_prime_iff in hprime.
      change (is_true (prime p)) in hprime.
      rewrite (@logn_prime q p hprime).
      have hneqb : (q == p) = false := introF eqP hqp.
      rewrite hneqb muln0 (IH hall' habsent'). reflexivity.
    + apply/ltP. change (0 < Nat.pow p e)%coq_nat.
      apply (proj1 (Nat.neq_0_lt_0 (Nat.pow p e))).
      apply Nat.pow_nonzero.
      apply mathcomp_prime_iff in hprime.
      change (is_true (prime p)) in hprime.
      intro hp0. subst p. move: (prime_gt0 hprime). discriminate.
    + apply/ltP. exact (factorPowers_product_positive pd hall').
Qed.

Lemma logn_factorPowers_member : forall pd p e,
  Forall (fun pe => PrimeNat (fst pe) /\ (0 < snd pe)%coq_nat) pd ->
  NoDup (factorPrimes pd) ->
  In (p, e) pd ->
  logn p (natListProduct (factorPowers pd)) = e.
Proof.
  intros pd. induction pd as [|[q f] pd IH]; intros p e hall hnodup hin.
  - contradiction.
  - inversion hall as [|? ? [hprime hepos] hall']; subst.
    inversion hnodup as [|? ? hqabsent hnodup']; subst.
    simpl in hin. destruct hin as [hhead | hin].
    + inversion hhead; subst q f.
      change (~ In p (factorPrimes pd)) in hqabsent.
      cbn [factorPowers natListProduct]. rewrite lognM.
      * change (logn p (Nat.pow p e) +
          logn p (natListProduct (factorPowers pd)) = e).
        rewrite <- (expn_eq_pow p e), lognX.
        apply mathcomp_prime_iff in hprime.
        change (is_true (prime p)) in hprime.
        rewrite (@logn_prime p p hprime) eq_refl muln1.
        rewrite (logn_factorPowers_absent p pd hall' hqabsent) addn0.
        reflexivity.
      * apply/ltP. change (0 < Nat.pow p e)%coq_nat.
        apply (proj1 (Nat.neq_0_lt_0 (Nat.pow p e))).
        apply Nat.pow_nonzero. intro hp0. subst p.
        destruct hprime as [hgt _]. inversion hgt.
      * apply/ltP. exact (factorPowers_product_positive pd hall').
    + assert (hpin : In p (factorPrimes pd)).
      { unfold factorPrimes. apply in_map with (f := fst) in hin.
        exact hin. }
      assert (hpq : p <> q).
      { intro hpq. subst p. exact (hqabsent hpin). }
      cbn [factorPowers natListProduct]. rewrite lognM.
      * change (logn p (Nat.pow q f) +
          logn p (natListProduct (factorPowers pd)) = e).
        rewrite <- (expn_eq_pow q f), lognX.
        apply mathcomp_prime_iff in hprime.
        change (is_true (prime q)) in hprime.
        rewrite (@logn_prime p q hprime).
        have hneqb : (p == q) = false := introF eqP hpq.
        rewrite hneqb muln0 add0n. exact (IH p e hall' hnodup' hin).
      * apply/ltP. change (0 < Nat.pow q f)%coq_nat.
        apply (proj1 (Nat.neq_0_lt_0 (Nat.pow q f))).
        apply Nat.pow_nonzero. intro hq0. subst q.
        destruct hprime as [hgt _]. inversion hgt.
      * apply/ltP. exact (factorPowers_product_positive pd hall').
Qed.

Lemma typed_factorPrimes_eq_primes : forall pd n,
  TypedPrimeFactorization pd n ->
  factorPrimes pd = primes n.
Proof.
  intros pd n [hstrict [hall hproduct]].
  assert (hnodup : NoDup (factorPrimes pd)).
  {
    apply sorted_lt_nodup.
    apply (proj1 (StrictlyIncreasing_sorted_lt (factorPrimes pd))).
    exact hstrict.
  }
  apply (irr_sorted_eq ltn_trans ltnn).
  - exact (strict_mathcomp_sorted (factorPrimes pd) hstrict).
  - exact (sorted_primes n).
  - move=> p. apply/idP/idP.
    + move=> hmem.
      assert (hin : In p (factorPrimes pd)).
      { apply (proj1 (mem_seq_In p (factorPrimes pd))). exact hmem. }
      unfold factorPrimes in hin.
      apply in_map_iff in hin.
      destruct hin as [[q e] [hq hin]]. simpl in hq. subst q.
      pose proof hall as hentry.
      apply Forall_forall with (x := (p, e)) in hentry; [|exact hin].
      destruct hentry as [_ hepos].
      pose proof (logn_factorPowers_member pd p e hall hnodup hin) as hlog.
      rewrite hproduct in hlog.
      rewrite -logn_gt0. apply/ltP. rewrite hlog. exact hepos.
    + move=> hmem.
      rewrite -logn_gt0 in hmem.
      assert (hlogpos : (0 < logn p n)%coq_nat).
      { exact (elimT ltP hmem). }
      apply (proj2 (mem_seq_In p (factorPrimes pd))).
      destruct (in_dec Nat.eq_dec p (factorPrimes pd)) as [hin | habsent].
      * exact hin.
      * pose proof (logn_factorPowers_absent p pd hall habsent) as hlog.
        rewrite hproduct in hlog. lia.
Qed.

Lemma typedPrimeFactorization_eq_prime_decomp : forall pd n,
  TypedPrimeFactorization pd n ->
  pd = prime_decomp n.
Proof.
  intros pd n htyped.
  pose proof (typed_factorPrimes_eq_primes pd n htyped) as hprimes.
  destruct htyped as [hstrict [hall hproduct]].
  assert (hnodup : NoDup (factorPrimes pd)).
  {
    apply sorted_lt_nodup.
    apply (proj1 (StrictlyIncreasing_sorted_lt (factorPrimes pd))).
    exact hstrict.
  }
  rewrite prime_decompE. rewrite <- hprimes.
  unfold factorPrimes. rewrite seq_map_List_map List.map_map.
  rewrite <- (List.map_id pd) at 1.
  apply List.map_ext_in. intros [p e] hin. simpl. f_equal.
  symmetry.
  pose proof (logn_factorPowers_member pd p e hall hnodup hin) as hlog.
  now rewrite hproduct in hlog.
Qed.

Theorem primeFactorizationCode_functional : forall v w n,
  PrimeFactorizationCode v n ->
  PrimeFactorizationCode w n ->
  v = w.
Proof.
  intros v w n hv hw.
  destruct (primeFactorizationCode_typed v n hv) as [pd [hdecodev htypedv]].
  destruct (primeFactorizationCode_typed w n hw) as [qd [hdecodew htypedw]].
  pose proof (typedPrimeFactorization_eq_prime_decomp pd n htypedv) as hpd.
  pose proof (typedPrimeFactorization_eq_prime_decomp qd n htypedw) as hqd.
  pose proof (listCode_decode v (factorCodes pd) hdecodev) as hcodev.
  pose proof (listCode_decode w (factorCodes qd) hdecodew) as hcodew.
  rewrite <- hcodev. rewrite <- hcodew. rewrite hpd hqd. reflexivity.
Qed.

Lemma prime_decomp_member_from_nth : forall n i p e,
  nth_error (prime_decomp n) i = Some (p, e) ->
  [/\ prime p, 0 < e & p ^ e %| n].
Proof.
  intros n i p e hnth.
  assert (hi : (i < size (prime_decomp n))%coq_nat).
  { apply nth_error_Some. rewrite hnth. discriminate. }
  have hibound : i < size (prime_decomp n) := introT ltP hi.
  have hmem := mem_nth (0, 0) hibound.
  assert (hvalue : nth (0, 0) (prime_decomp n) i = (p, e)).
  { exact (nth_error_mathcomp_nth (nat * nat) (0, 0) (p, e)
      (prime_decomp n) i hnth). }
  rewrite hvalue in hmem.
  exact (mem_prime_decomp hmem).
Qed.

Theorem primeFactorizationCode_exists : forall n,
  (0 < n)%coq_nat -> exists v, PrimeFactorizationCode v n.
Proof.
  intros n hn.
  set (pd := prime_decomp n).
  exists (listCode (factorCodes pd)).
  exists (length pd),
    (listCode (factorPrimes pd)),
    (listCode (factorExponents pd)),
    (listCode (factorPowers pd)).
  split; [exact hn |]. split.
  - apply HasLength_listCode. unfold factorCodes. apply length_map.
  - split.
    + apply HasLength_listCode. unfold factorPrimes. apply length_map.
    + split.
      * apply HasLength_listCode. unfold factorExponents. apply length_map.
      * split.
        -- apply HasLength_listCode. unfold factorPowers. apply length_map.
        -- split.
           ++ apply StrictlyIncreasingCode_listCode.
              unfold factorPrimes, pd.
              change (StrictlyIncreasing (primes n)).
              apply mathcomp_sorted_strict. apply sorted_primes.
           ++ split.
              ** apply ProductElementsCode_listCode.
                 rewrite natListProduct_factorPowers.
                 symmetry. unfold pd. apply prod_prime_decomp.
                 exact (introT ltP hn).
              ** intros i c p e w hi hc hp he hw.
                 apply NthElement_listCode in hc.
                 apply NthElement_listCode in hp.
                 apply NthElement_listCode in he.
                 apply NthElement_listCode in hw.
                 unfold factorCodes, factorPrimes,
                   factorExponents, factorPowers in hc, hp, he, hw.
                 repeat rewrite nth_error_map in hc, hp, he, hw.
                 destruct (nth_error pd i) as [[p0 e0]|] eqn:hpe;
                   simpl in hc, hp, he, hw; try discriminate.
                 inversion hc; inversion hp; inversion he; inversion hw;
                   subst c p e w.
                 destruct (prime_decomp_member_from_nth n i p0 e0
                   ltac:(unfold pd in hpe; exact hpe)) as [hprime hepos _].
                 split.
                 --- unfold FactorPair.
                     change (decode (listCode [p0; e0]) = Some [p0; e0]).
                     apply decode_listCode.
                 --- split.
                     ++++ apply mathcomp_prime_iff. exact hprime.
                     ++++ split; [exact (elimT ltP hepos) | reflexivity].
Qed.

Theorem primeFactorizationCode_exists_unique : forall n,
  (0 < n)%coq_nat -> exists! v, PrimeFactorizationCode v n.
Proof.
  intros n hn.
  destruct (primeFactorizationCode_exists n hn) as [v hv].
  exists v. split; [exact hv |].
  intros w hw. exact (primeFactorizationCode_functional v w n hv hw).
Qed.

End PAListNumberTheoryFactorization.
