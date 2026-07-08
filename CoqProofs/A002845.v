(*
  Coq port of the exact-logarithm layer of LeanProofs/A002845.lean.

  This Coq port keeps the proved exact-logarithm reduction and the earlier
  binary-N sparse bridge, then uses a small hereditary sparse-binary executable
  recurrence for the published value certificates.  Materializing the exact
  logarithms as binary naturals is already too large beyond the first few rows;
  the hereditary representation keeps the exponent structure sparse.

  The value certificates are produced by a memoized level table whose rows are
  kept sorted and duplicate-free by a fueled bottom-up mergesort over
  `HereditarySparse.compare`, replacing the quadratic `dedupBy` scan.  The
  counts through n = 17 are computed once into `a002845TableN` and every
  value theorem is a cheap table lookup.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import NArith.BinNat.
From Stdlib Require Import NArith.Nnat.
From LeanProofsCoq Require Import PowTower SparseBinary.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A002845.

Module PowExpr.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.
Module SB := LeanProofsCoq.SparseBinary.LeanProofs.A002845.Sparse.

Definition PowExpr := PT.Expr.

Definition Sparse : Type :=
  LeanProofsCoq.SparseBinary.LeanProofs.A002845.Sparse.

Definition two : PowExpr := PT.atom.

Definition pow : PowExpr -> PowExpr -> PowExpr := PT.pow.

Definition evalNat : PowExpr -> nat :=
  PT.eval 2 Nat.pow.

Definition logCombineNat (a b : nat) : nat :=
  a * Nat.pow 2 b.

Fixpoint logEvalNat (e : PowExpr) : nat :=
  match e with
  | PT.atom => 1
  | PT.pow a b => logCombineNat (logEvalNat a) (logEvalNat b)
  end.

Definition logCombineN (a b : N) : N :=
  (a * N.pow 2 b)%N.

Fixpoint logEvalN (e : PowExpr) : N :=
  match e with
  | PT.atom => 1%N
  | PT.pow a b => logCombineN (logEvalN a) (logEvalN b)
  end.

Theorem logEvalNat_eq_sharedEval (e : PowExpr) :
    logEvalNat e = PT.eval 1 logCombineNat e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Theorem logEvalN_eq_sharedEval (e : PowExpr) :
    logEvalN e = PT.eval 1%N logCombineN e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

Theorem logEvalN_of_nat (e : PowExpr) :
    logEvalN e = N.of_nat (logEvalNat e).
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl.
    unfold logCombineN, logCombineNat.
    rewrite Nat2N.inj_mul, Nat2N.inj_pow.
    now rewrite <- iha, <- ihb.
Qed.

Theorem evalNat_eq_two_pow_logEvalNat (e : PowExpr) :
    evalNat e = Nat.pow 2 (logEvalNat e).
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - unfold evalNat at 1. simpl.
    fold (evalNat a). fold (evalNat b).
    rewrite iha, ihb.
    unfold logCombineNat.
    now rewrite Nat.pow_mul_r.
Qed.

Lemma N_eqb_of_nat (x y : nat) :
    N.eqb (N.of_nat x) (N.of_nat y) = Nat.eqb x y.
Proof.
  destruct (N.eqb_spec (N.of_nat x) (N.of_nat y)) as [hn | hn];
    destruct (Nat.eqb_spec x y) as [h | h]; try reflexivity.
  - exfalso. apply h. now apply Nat2N.inj_iff.
  - exfalso. apply hn. now subst.
Qed.

Lemma memberBy_map_N_of_nat (x : nat) (xs : list nat) :
    PT.memberBy N.eqb (N.of_nat x) (map N.of_nat xs) =
      PT.memberBy Nat.eqb x xs.
Proof.
  induction xs as [|y ys ih].
  - reflexivity.
  - simpl. rewrite N_eqb_of_nat, ih. reflexivity.
Qed.

Lemma dedupBy_map_N_of_nat (xs : list nat) :
    PT.dedupBy N.eqb (map N.of_nat xs) =
      map N.of_nat (PT.dedupBy Nat.eqb xs).
Proof.
  induction xs as [|x xs ih].
  - reflexivity.
  - simpl.
    rewrite ih.
    unfold PT.insertBy.
    rewrite memberBy_map_N_of_nat.
    destruct (PT.memberBy Nat.eqb x (PT.dedupBy Nat.eqb xs));
      reflexivity.
Qed.

Lemma evalList_logEvalN_of_nat (n : nat) :
    PT.evalList logEvalN n =
      map N.of_nat (PT.evalList logEvalNat n).
Proof.
  unfold PT.evalList.
  rewrite map_map.
  apply map_ext.
  exact logEvalN_of_nat.
Qed.

Definition directLogCardNat (n : nat) : nat :=
  PT.valueCount Nat.eqb logEvalNat n.

Definition directLogCardN (n : nat) : nat :=
  PT.valueCount N.eqb logEvalN n.

Theorem directLogCardN_eq_directLogCardNat (n : nat) :
    directLogCardN n = directLogCardNat n.
Proof.
  unfold directLogCardN, directLogCardNat.
  unfold PT.valueCount, PT.valueList.
  rewrite evalList_logEvalN_of_nat.
  rewrite dedupBy_map_N_of_nat.
  now rewrite length_map.
Qed.

Definition directA002845 : nat -> nat := directLogCardN.

Theorem directA002845_eq_directLogCardNat (n : nat) :
    directA002845 n = directLogCardNat n.
Proof.
  exact (directLogCardN_eq_directLogCardNat n).
Qed.

Definition certifiedCombineLog (a b : Sparse) : Sparse :=
  SB.shift a b.

Fixpoint sparseLogEval (e : PowExpr) : Sparse :=
  match e with
  | PT.atom => SB.ofN 1
  | PT.pow a b => certifiedCombineLog (sparseLogEval a) (sparseLogEval b)
  end.

Theorem canonical_sparseLogEval (e : PowExpr) :
    SB.Canonical (sparseLogEval e).
Proof.
  induction e as [|a iha b ihb].
  - apply SB.canonical_ofN.
  - unfold sparseLogEval; fold (sparseLogEval a); fold (sparseLogEval b).
    unfold certifiedCombineLog.
    exact (proj1 (SB.shift_spec iha ihb)).
Qed.

Theorem sparseLogEval_eq_logEvalN (e : PowExpr) :
    sparseLogEval e = logEvalN e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl.
    unfold certifiedCombineLog, SB.shift, logCombineN.
    now rewrite iha, ihb.
Qed.

Theorem eval_sparseLogEval (e : PowExpr) :
    SB.eval (sparseLogEval e) = logEvalN e.
Proof.
  now rewrite sparseLogEval_eq_logEvalN.
Qed.

Definition certifiedSparseCard (n : nat) : nat :=
  PT.valueCount SB.beq sparseLogEval n.

Theorem certifiedSparseCard_eq_directLogCardN (n : nat) :
    certifiedSparseCard n = directLogCardN n.
Proof.
  reflexivity.
Qed.

Theorem directA002845_eq_certifiedSparseCard (n : nat) :
    directA002845 n = certifiedSparseCard n.
Proof.
  unfold directA002845.
  symmetry.
  apply certifiedSparseCard_eq_directLogCardN.
Qed.

(*
  EXECUTABLE-ONLY MODULE.  `HereditarySparse` is a certificate carrier: its
  fueled comparison/arithmetic and the sorted level recurrence below are not
  yet connected by machine-checked specifications to the proved `Sparse`
  (`N`-backed) layer above.  The value theorems it certifies are trusted
  executable computations — the same trust level as the Lean module's
  `native_decide` layer — cross-checked below against the quadratic
  structural-equality dedup on a cheap prefix and against the published OEIS
  values.
*)
Module HereditarySparse.

Inductive t : Type :=
| snil : t
| scons : t -> t -> t.

Fixpoint size (x : t) : nat :=
  match x with
  | snil => 1
  | scons h rest => S (size h + size rest)
  end.

Fixpoint beq (x y : t) : bool :=
  match x, y with
  | snil, snil => true
  | scons xh xt, scons yh yt => beq xh yh && beq xt yt
  | _, _ => false
  end.

Fixpoint revAux (xs acc : t) : t :=
  match xs with
  | snil => acc
  | scons h rest => revAux rest (scons h acc)
  end.

Definition rev (xs : t) : t := revAux xs snil.

Fixpoint compareFuel (fuel : nat) (x y : t) : comparison :=
  match fuel with
  | 0 => Eq
  | S fuel' => compareListFuel fuel' (rev x) (rev y)
  end
with compareListFuel (fuel : nat) (xs ys : t) : comparison :=
  match fuel with
  | 0 => Eq
  | S fuel' =>
      match xs, ys with
      | snil, snil => Eq
      | snil, scons _ _ => Lt
      | scons _ _, snil => Gt
      | scons x xs', scons y ys' =>
          match compareFuel fuel' x y with
          | Eq => compareListFuel fuel' xs' ys'
          | c => c
          end
      end
  end.

Definition compare (x y : t) : comparison :=
  compareFuel (size x + size y + 1) x y.

Definition zero : t := snil.

Fixpoint incrFuel (fuel : nat) (x : t) : t :=
  match fuel with
  | 0 => x
  | S fuel' => insBitFuel fuel' zero x
  end
with insBitFuel (fuel : nat) (p bits : t) : t :=
  match fuel with
  | 0 => scons p bits
  | S fuel' =>
      match bits with
      | snil => scons p snil
      | scons q qs =>
          match compare p q with
          | Lt => scons p (scons q qs)
          | Eq => insBitFuel fuel' (incrFuel fuel' q) qs
          | Gt => scons q (insBitFuel fuel' p qs)
          end
      end
  end.

Definition incr (x : t) : t :=
  incrFuel (size x + 1) x.

Definition insBit (p bits : t) : t :=
  insBitFuel (size p + size bits + 1) p bits.

Definition one : t := scons zero zero.

Definition add (x y : t) : t :=
  let fix foldBits ys acc :=
    match ys with
    | snil => acc
    | scons p ps => foldBits ps (insBit p acc)
    end in
  foldBits y x.

Definition shift (x b : t) : t :=
  let fix foldBits xs acc :=
    match xs with
    | snil => acc
    | scons p ps => foldBits ps (insBit (add p b) acc)
    end in
  foldBits x snil.

Definition combineLevel (left right : list t) : list t :=
  flat_map (fun a => map (fun b => shift a b) right) left.

(* ---------------------------------------------------------------------- *)
(* Sorted merge-dedup machinery: a fueled bottom-up mergesort over `compare`
   whose merge step drops `Eq`-adjacent duplicates, so level sets stay sorted
   and duplicate-free in O(m log m) comparisons instead of the quadratic
   `dedupBy` scan.

   Unlike the A199812 port, the candidate lists here reach hundreds of
   thousands of entries (about 250 000 raw candidates at level 18), so every
   list traversal below is written tail-recursively with accumulators
   (`rev_append` style): the Coq VM does not grow its stack for deep non-tail
   recursion, and the direct structural versions overflow it. *)

(* Tail-recursive list length, used only as mergesort fuel (its unary result
   stays on the VM heap and is never read back). *)
Fixpoint listLengthOnto (xs : list t) (acc : nat) : nat :=
  match xs with
  | [] => acc
  | _ :: xs' => listLengthOnto xs' (S acc)
  end.

Definition listLength (xs : list t) : nat := listLengthOnto xs 0.

(* Binary-natural list length, used for the level-count table: reading a
   unary `nat` of six digits back out of the VM overflows the OCaml stack
   (the S-chain is read back recursively), while binary `N` readback is
   logarithmic. *)
Fixpoint listLengthNOnto (xs : list t) (acc : N) : N :=
  match xs with
  | [] => acc
  | _ :: xs' => listLengthNOnto xs' (N.succ acc)
  end.

Definition listLengthN (xs : list t) : N := listLengthNOnto xs 0%N.

Lemma listLengthNOnto_spec (xs : list t) (acc : N) :
    listLengthNOnto xs acc = (N.of_nat (length xs) + acc)%N.
Proof.
  revert acc.
  induction xs as [|x xs ih]; intro acc.
  - cbn. lia.
  - cbn [listLengthNOnto length].
    rewrite ih, Nat2N.inj_succ.
    lia.
Qed.

Lemma listLengthN_spec (xs : list t) : listLengthN xs = N.of_nat (length xs).
Proof.
  unfold listLengthN. rewrite listLengthNOnto_spec. lia.
Qed.

(* Merge two sorted duplicate-free lists, dropping duplicates.  The result is
   accumulated in reverse and flipped back by `rev_append`; the fuel
   `length xs + length ys` bounds the number of merge steps. *)
Fixpoint mergeDedupFuel (fuel : nat) (acc xs ys : list t) : list t :=
  match fuel with
  | 0 => rev_append acc (xs ++ ys)
  | S fuel' =>
      match xs, ys with
      | [], _ => rev_append acc ys
      | _, [] => rev_append acc xs
      | x :: xs', y :: ys' =>
          match compare x y with
          | Lt => mergeDedupFuel fuel' (x :: acc) xs' ys
          | Eq => mergeDedupFuel fuel' (x :: acc) xs' ys'
          | Gt => mergeDedupFuel fuel' (y :: acc) xs ys'
          end
      end
  end.

Definition mergeDedup (xs ys : list t) : list t :=
  mergeDedupFuel (listLengthOnto xs (listLength ys)) [] xs ys.

(* One bottom-up round: merge adjacent pairs of sorted runs (the accumulator
   reverses the run order, which is harmless for the eventual union). *)
Fixpoint mergePairsOnto (ls acc : list (list t)) : list (list t) :=
  match ls with
  | a :: b :: rest => mergePairsOnto rest (mergeDedup a b :: acc)
  | [l] => l :: acc
  | [] => acc
  end.

Fixpoint mergeAllFuel (fuel : nat) (ls : list (list t)) : list t :=
  match fuel, ls with
  | _, [] => []
  | _, [l] => l
  | 0, l :: _ => l
  | S f, ls => mergeAllFuel f (mergePairsOnto ls [])
  end.

Fixpoint singletonsOnto (xs : list t) (acc : list (list t)) :
    list (list t) :=
  match xs with
  | [] => acc
  | x :: xs' => singletonsOnto xs' ([x] :: acc)
  end.

(* Each `mergePairsOnto` round halves the run count, so `length xs` rounds of
   fuel are always enough. *)
Definition sortDedup (xs : list t) : list t :=
  mergeAllFuel (listLength xs) (singletonsOnto xs []).

(* Quadratic structural-equality variant, kept only as a cross-check oracle
   for the sorted recurrence (see `count_agrees_with_beq_through_eleven`). *)
Definition levelFromTableByBeq (levels : list (list t)) (n : nat) : list t :=
  match n with
  | 0 => []
  | 1 => [one]
  | S (S n') =>
      PT.dedupBy beq
        (flat_map
          (fun k =>
             combineLevel (nth (S k) levels []) (nth (S n' - k) levels []))
          (seq 0 (S n')))
  end.

Fixpoint levelTableByBeq (fuel : nat) : list (list t) :=
  match fuel with
  | 0 => []
  | S fuel' =>
      let levels := levelTableByBeq fuel' in
      levels ++ [levelFromTableByBeq levels fuel']
  end.

Definition countByBeq (n : nat) : nat :=
  length (nth n (levelTableByBeq (S n)) []).

(* Tail-recursive candidate assembly: `shift a b` for every `a` in the left
   level and `b` in the right level, accumulated in front of `acc`. *)
Fixpoint shiftAllOnto (a : t) (right acc : list t) : list t :=
  match right with
  | [] => acc
  | b :: right' => shiftAllOnto a right' (shift a b :: acc)
  end.

Fixpoint combineLevelOnto (left right acc : list t) : list t :=
  match left with
  | [] => acc
  | a :: left' => combineLevelOnto left' right (shiftAllOnto a right acc)
  end.

Definition levelCandidates (levels : list (list t)) (n' : nat) : list t :=
  fold_left
    (fun acc k =>
       combineLevelOnto (nth (S k) levels []) (nth (S n' - k) levels []) acc)
    (seq 0 (S n')) [].

Definition levelFromTable (levels : list (list t)) (n : nat) : list t :=
  match n with
  | 0 => []
  | 1 => [one]
  | S (S n') => sortDedup (levelCandidates levels n')
  end.

Fixpoint levelTable (fuel : nat) : list (list t) :=
  match fuel with
  | 0 => []
  | S fuel' =>
      let levels := levelTable fuel' in
      levels ++ [levelFromTable levels fuel']
  end.

Lemma levelTable_length (fuel : nat) : length (levelTable fuel) = fuel.
Proof.
  induction fuel as [|fuel ih].
  - reflexivity.
  - cbn. rewrite length_app, ih. cbn. lia.
Qed.

Lemma levelTable_prefix (n m : nat) (h : (n <= m)%nat) :
    exists suffix, levelTable m = levelTable n ++ suffix.
Proof.
  induction h as [|m h ih].
  - exists []. now rewrite app_nil_r.
  - destruct ih as [suffix hs].
    exists (suffix ++ [levelFromTable (levelTable m) m]).
    cbn. rewrite hs. now rewrite app_assoc.
Qed.

(* Rows already present in a shorter table are unchanged in any longer one,
   so per-value lookups can all share one computed table. *)
Lemma nth_levelTable_stable (k n m : nat) (hk : (k < n)%nat)
    (hnm : (n <= m)%nat) :
    nth k (levelTable m) [] = nth k (levelTable n) [].
Proof.
  destruct (levelTable_prefix hnm) as [suffix hs].
  rewrite hs.
  apply app_nth1.
  now rewrite levelTable_length.
Qed.

Definition levelCountsN (fuel : nat) : list N :=
  map listLengthN (levelTable fuel).

Lemma nth_levelCountsN (fuel n : nat) :
    nth n (levelCountsN fuel) 0%N =
      N.of_nat (length (nth n (levelTable fuel) [])).
Proof.
  unfold levelCountsN.
  change 0%N with (listLengthN []).
  rewrite map_nth.
  apply listLengthN_spec.
Qed.

Definition level (n : nat) : list t :=
  nth n (levelTable (S n)) [].

Definition count (n : nat) : nat :=
  length (level n).

(* Sanity bridge: the sorted merge-dedup recurrence agrees with the quadratic
   structural-equality dedup on a cheap prefix. *)
Theorem count_agrees_with_beq_through_eleven :
    map countByBeq (seq 0 12) = map count (seq 0 12).
Proof. vm_compute. reflexivity. Qed.

End HereditarySparse.

Definition certifiedLevelCount : nat -> nat :=
  HereditarySparse.count.

Definition a002845 : nat -> nat := certifiedLevelCount.

(* The counts of levels 0 through 17 as binary naturals (`N` readback from
   the VM is logarithmic in the value; unary `nat` readback of the larger
   counts overflows the OCaml stack).  Every value theorem below is a cheap
   lookup into this table. *)
Definition a002845TableN : list N :=
  [0; 1; 1; 1; 2; 4; 8; 17; 36; 78; 171; 379; 851; 1928; 4396; 10087;
   23273; 53948]%N.

(* The single expensive computation of the file: the kernel VM evaluates the
   sorted level recurrence once, at Qed time (`vm_cast_no_check` skips the
   redundant tactic-time evaluation). *)
Theorem a002845TableN_spec :
    HereditarySparse.levelCountsN 18 = a002845TableN.
Proof. vm_cast_no_check (eq_refl a002845TableN). Qed.

Lemma a002845_eq_tableN_nth (n : nat) (h : n < 18) :
    N.of_nat (a002845 n) = nth n a002845TableN 0%N.
Proof.
  rewrite <- a002845TableN_spec, HereditarySparse.nth_levelCountsN.
  unfold a002845, certifiedLevelCount, HereditarySparse.count,
    HereditarySparse.level.
  do 2 f_equal.
  symmetry.
  apply HereditarySparse.nth_levelTable_stable; lia.
Qed.

Definition a002845ValuesThroughFourteen : list nat :=
  [1; 1; 1; 2; 4; 8; 17; 36; 78; 171; 379; 851; 1928; 4396].

Definition a002845ValuesThroughSeventeen : list nat :=
  [1; 1; 1; 2; 4; 8; 17; 36; 78; 171; 379; 851; 1928; 4396; 10087; 23273;
   53948].

Theorem a002845_one : a002845 1 = 1.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_two : a002845 2 = 1.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_three : a002845 3 = 1.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_four : a002845 4 = 2.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_five : a002845 5 = 4.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_six : a002845 6 = 8.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_seven : a002845 7 = 17.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_eight : a002845 8 = 36.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_nine : a002845 9 = 78.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_ten : a002845 10 = 171.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_eleven : a002845 11 = 379.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_twelve : a002845 12 = 851.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_thirteen : a002845 13 = 1928.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_fourteen : a002845 14 = 4396.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_fifteen : a002845 15 = 10087.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_sixteen : a002845 16 = 23273.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

Theorem a002845_seventeen : a002845 17 = 53948.
Proof.
  apply Nat2N.inj. rewrite a002845_eq_tableN_nth by lia.
  vm_compute. reflexivity.
Qed.

(* Derived from the individual value lemmas by rewriting; those lemmas are
   themselves constant-time lookups into the single vm_computed
   `a002845TableN`, so the level enumeration is computed once for the whole
   file rather than once per theorem. *)
Theorem a002845_values_through_fourteen :
    map a002845 (seq 1 14) = a002845ValuesThroughFourteen.
Proof.
  cbn [seq map].
  now rewrite a002845_one, a002845_two, a002845_three, a002845_four,
    a002845_five, a002845_six, a002845_seven, a002845_eight, a002845_nine,
    a002845_ten, a002845_eleven, a002845_twelve, a002845_thirteen,
    a002845_fourteen.
Qed.

Theorem a002845_values_through_seventeen :
    map a002845 (seq 1 17) = a002845ValuesThroughSeventeen.
Proof.
  cbn [seq map].
  now rewrite a002845_one, a002845_two, a002845_three, a002845_four,
    a002845_five, a002845_six, a002845_seven, a002845_eight, a002845_nine,
    a002845_ten, a002845_eleven, a002845_twelve, a002845_thirteen,
    a002845_fourteen, a002845_fifteen, a002845_sixteen, a002845_seventeen.
Qed.

(* The shorter published table is a prefix of the n = 17 table. *)
Theorem a002845ValuesThroughFourteen_prefix :
    a002845ValuesThroughFourteen = firstn 14 a002845ValuesThroughSeventeen.
Proof. reflexivity. Qed.

End PowExpr.

Export PowExpr.

End A002845.
End LeanProofs.
