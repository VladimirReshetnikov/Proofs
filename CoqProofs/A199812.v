(*
  Coq port of the executable ordinal-note layer from
  LeanProofs/A199812.lean.

  The Lean module connects this normal-form computation to mathlib's ordinal
  semantics.  This Coq module ports the discrete Cantor-normal-form recurrence
  used for computation: inner exponents below epsilon_0 are represented by
  ordinal notes, and the tower split recurrence combines notes by
  a, b |-> a + omega^b.

  The value certificates are produced by a memoized level table whose rows are
  kept sorted and duplicate-free by a fueled bottom-up mergesort over
  `onoteCompare`.  This replaces the quadratic `memberBy`/`dedupBy` scan of the
  direct port (kept below for spec parity) and brings the whole file's compile
  time from minutes down to seconds.  The counts through n = 13 are computed
  once into `a199812Table` and every value theorem is a cheap table lookup.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From LeanProofsCoq Require Import PowTower.

Import ListNotations.
Set Implicit Arguments.
Open Scope nat_scope.

Module LeanProofs.
Module A199812.

Module TowerExpr.

Module PT := LeanProofsCoq.PowTower.LeanProofs.PowTower.

Definition PowExpr := PT.Expr.

Inductive ONote : Type :=
| ozero : ONote
| oadd : ONote -> nat -> ONote -> ONote.

Fixpoint onoteEqb (a b : ONote) : bool :=
  match a, b with
  | ozero, ozero => true
  | oadd ae an ar, oadd be bn br =>
      onoteEqb ae be && Nat.eqb an bn && onoteEqb ar br
  | _, _ => false
  end.

Fixpoint onoteCompare (a b : ONote) : comparison :=
  match a, b with
  | ozero, ozero => Eq
  | ozero, oadd _ _ _ => Lt
  | oadd _ _ _, ozero => Gt
  | oadd ae an ar, oadd be bn br =>
      match onoteCompare ae be with
      | Eq =>
          match Nat.compare an bn with
          | Eq => onoteCompare ar br
          | c => c
          end
      | c => c
      end
  end.

Theorem onoteCompare_refl (a : ONote) : onoteCompare a a = Eq.
Proof.
  induction a as [|e ihe n r ihr].
  - reflexivity.
  - simpl. now rewrite ihe, Nat.compare_refl.
Qed.

Theorem onoteCompare_eq (a b : ONote) : onoteCompare a b = Eq -> a = b.
Proof.
  revert b.
  induction a as [|ae ihe an ar ihr]; intros [|be bn br] h; simpl in h;
    try discriminate.
  - reflexivity.
  - destruct (onoteCompare ae be) eqn:hae; try discriminate.
    destruct (Nat.compare an bn) eqn:hn; try discriminate.
    apply ihe in hae.
    apply Nat.compare_eq in hn.
    apply ihr in h.
    now subst.
Qed.

(* Soundness of the mergesort dedup key: dropping `Eq`-adjacent entries drops
   exactly the structural duplicates. *)
Theorem onoteCompare_eq_iff (a b : ONote) : onoteCompare a b = Eq <-> a = b.
Proof.
  split.
  - apply onoteCompare_eq.
  - intro h. subst. apply onoteCompare_refl.
Qed.

Definition principalPower (e : ONote) : ONote :=
  oadd e 1 ozero.

Fixpoint addPrincipalPower (a b : ONote) : ONote :=
  match a with
  | ozero => principalPower b
  | oadd e n rest =>
      match onoteCompare e b with
      | Lt => principalPower b
      | Eq => oadd e (S n) ozero
      | Gt => oadd e n (addPrincipalPower rest b)
      end
  end.

Definition combineDegree (a b : ONote) : ONote :=
  addPrincipalPower a b.

Fixpoint degreeNote (e : PowExpr) : ONote :=
  match e with
  | PT.atom => ozero
  | PT.pow a b => combineDegree (degreeNote a) (degreeNote b)
  end.

Theorem degreeNote_eq_sharedCombineEval (e : PowExpr) :
    degreeNote e = PT.eval ozero combineDegree e.
Proof.
  induction e as [|a iha b ihb].
  - reflexivity.
  - simpl. now rewrite iha, ihb.
Qed.

(* Direct port of the shared-evaluator recursion, kept for spec parity with
   `PowTower.recursiveValueList`.  Its `dedupBy` deduplication is quadratic
   with expensive structural equality, so the value certificates below use the
   sorted level table instead; `computedDegreeCount_agrees_through_eight`
   cross-checks the two on a cheap prefix. *)
Definition computedDegreeValues (n : nat) : list ONote :=
  PT.recursiveValueList onoteEqb ozero combineDegree n.

Definition computedDegreeCount (n : nat) : nat :=
  length (computedDegreeValues n).

(* ---------------------------------------------------------------------- *)
(* Sorted merge-dedup machinery: a fueled bottom-up mergesort over
   `onoteCompare` whose merge step drops `Eq`-adjacent duplicates, so level
   sets stay sorted and duplicate-free in O(m log m) comparisons. *)

(* Merge two sorted duplicate-free lists, dropping duplicates. *)
Fixpoint mergeDedup (xs : list ONote) : list ONote -> list ONote :=
  match xs with
  | [] => fun ys => ys
  | x :: xs' =>
      fix inner (ys : list ONote) : list ONote :=
        match ys with
        | [] => x :: xs'
        | y :: ys' =>
            match onoteCompare x y with
            | Lt => x :: mergeDedup xs' (y :: ys')
            | Eq => x :: mergeDedup xs' ys'
            | Gt => y :: inner ys'
            end
        end
  end.

Fixpoint mergePairs (ls : list (list ONote)) : list (list ONote) :=
  match ls with
  | a :: b :: rest => mergeDedup a b :: mergePairs rest
  | _ => ls
  end.

Fixpoint mergeAllFuel (fuel : nat) (ls : list (list ONote)) : list ONote :=
  match fuel, ls with
  | _, [] => []
  | _, [l] => l
  | 0, l :: _ => l
  | S f, ls => mergeAllFuel f (mergePairs ls)
  end.

(* Each `mergePairs` round halves the list, so `length xs` rounds of fuel are
   always enough. *)
Definition sortDedup (xs : list ONote) : list ONote :=
  mergeAllFuel (length xs) (map (fun x => [x]) xs).

(* ---------------------------------------------------------------------- *)
(* Memoized level table: row n holds the sorted duplicate-free degree notes
   of the n-atom towers, and each new row is built from the already-computed
   rows instead of re-running the recursion. *)

Definition levelFromTable (levels : list (list ONote)) (n : nat) :
    list ONote :=
  match n with
  | 0 => []
  | 1 => [ozero]
  | S (S n') =>
      sortDedup
        (flat_map
          (fun k =>
             PT.combineLevel combineDegree
               (nth (S k) levels []) (nth (S n' - k) levels []))
          (seq 0 (S n')))
  end.

Fixpoint levelTable (fuel : nat) : list (list ONote) :=
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

Lemma levelTable_prefix (n m : nat) (h : n <= m) :
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
Lemma nth_levelTable_stable (k n m : nat) (hk : k < n) (hnm : n <= m) :
    nth k (levelTable m) [] = nth k (levelTable n) [].
Proof.
  destruct (levelTable_prefix hnm) as [suffix hs].
  rewrite hs.
  apply app_nth1.
  now rewrite levelTable_length.
Qed.

Definition levelCounts (fuel : nat) : list nat :=
  map (@length ONote) (levelTable fuel).

Lemma nth_levelCounts (fuel n : nat) :
    nth n (levelCounts fuel) 0 = length (nth n (levelTable fuel) []).
Proof.
  unfold levelCounts.
  change 0 with (@length ONote []).
  apply map_nth.
Qed.

Definition degreeLevel (n : nat) : list ONote :=
  nth n (levelTable (S n)) [].

Definition degreeLevelCount (n : nat) : nat :=
  length (degreeLevel n).

Definition a199812 : nat -> nat := degreeLevelCount.

(* Sanity bridge: the sorted level recurrence agrees with the direct
   shared-evaluator dedup recursion on a cheap prefix. *)
Theorem computedDegreeCount_agrees_through_eight :
    map computedDegreeCount (seq 1 8) = map a199812 (seq 1 8).
Proof. vm_compute. reflexivity. Qed.

(* The counts of levels 0 through 13, computed once by the kernel VM.  Every
   value theorem below is a cheap lookup into this table. *)
Definition a199812Table : list nat :=
  Eval vm_compute in levelCounts 14.

Lemma a199812Table_spec : levelCounts 14 = a199812Table.
Proof. vm_compute. reflexivity. Qed.

Lemma a199812_eq_table_nth (n : nat) (h : n < 14) :
    a199812 n = nth n a199812Table 0.
Proof.
  rewrite <- a199812Table_spec, nth_levelCounts.
  unfold a199812, degreeLevelCount, degreeLevel.
  f_equal.
  symmetry.
  apply nth_levelTable_stable; lia.
Qed.

Definition a199812ValuesThroughEleven : list nat :=
  [1; 1; 2; 5; 13; 32; 79; 193; 478; 1196; 3037].

Definition a199812ValuesThroughTwelve : list nat :=
  [1; 1; 2; 5; 13; 32; 79; 193; 478; 1196; 3037; 7802].

Definition a199812ValuesThroughThirteen : list nat :=
  [1; 1; 2; 5; 13; 32; 79; 193; 478; 1196; 3037; 7802; 20287].

Theorem a199812_one : a199812 1 = 1.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_two : a199812 2 = 1.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_three : a199812 3 = 2.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_four : a199812 4 = 5.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_five : a199812 5 = 13.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_six : a199812 6 = 32.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_seven : a199812 7 = 79.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_eight : a199812 8 = 193.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_nine : a199812 9 = 478.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_ten : a199812 10 = 1196.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_eleven : a199812 11 = 3037.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_twelve : a199812 12 = 7802.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

Theorem a199812_thirteen : a199812 13 = 20287.
Proof. rewrite a199812_eq_table_nth by lia. reflexivity. Qed.

(* Derived from the individual value lemmas by rewriting; those lemmas are
   themselves constant-time lookups into the single vm_computed
   `a199812Table`, so the level enumeration is computed once for the whole
   file rather than once per theorem. *)
Theorem a199812_values_through_eleven :
    map a199812 (seq 1 11) = a199812ValuesThroughEleven.
Proof.
  cbn [seq map].
  now rewrite a199812_one, a199812_two, a199812_three, a199812_four,
    a199812_five, a199812_six, a199812_seven, a199812_eight,
    a199812_nine, a199812_ten, a199812_eleven.
Qed.

Theorem a199812_values_through_twelve :
    map a199812 (seq 1 12) = a199812ValuesThroughTwelve.
Proof.
  cbn [seq map].
  now rewrite a199812_one, a199812_two, a199812_three, a199812_four,
    a199812_five, a199812_six, a199812_seven, a199812_eight,
    a199812_nine, a199812_ten, a199812_eleven, a199812_twelve.
Qed.

Theorem a199812_values_through_thirteen :
    map a199812 (seq 1 13) = a199812ValuesThroughThirteen.
Proof.
  cbn [seq map].
  now rewrite a199812_one, a199812_two, a199812_three, a199812_four,
    a199812_five, a199812_six, a199812_seven, a199812_eight,
    a199812_nine, a199812_ten, a199812_eleven, a199812_twelve,
    a199812_thirteen.
Qed.

(* The shorter published tables are prefixes of the n = 13 table. *)
Theorem a199812ValuesThroughEleven_prefix :
    a199812ValuesThroughEleven = firstn 11 a199812ValuesThroughThirteen.
Proof. reflexivity. Qed.

Theorem a199812ValuesThroughTwelve_prefix :
    a199812ValuesThroughTwelve = firstn 12 a199812ValuesThroughThirteen.
Proof. reflexivity. Qed.

End TowerExpr.

Export TowerExpr.

End A199812.
End LeanProofs.
