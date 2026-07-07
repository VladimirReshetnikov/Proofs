import Mathlib.Data.Finset.NAry
import Mathlib.Data.Set.Card

/-!
# Shared lexical syntax for binary power towers

This module is the canonical lexical layer for the OEIS power-tower
formalizations in this workspace.  The syntax knows only one atom and one
binary node.  A sequence supplies the interpretation of the atom and of the
binary exponentiation operator afterwards.
-/

namespace LeanProofs

namespace PowTower

/-- The shared lexical syntax of binary parenthesizations of a one-token power tower. -/
inductive Expr where
  | atom
  | pow (a b : Expr)
deriving Repr, DecidableEq

namespace Expr

open Expr

/-- The number of atoms in a lexical tower expression. -/
def size : Expr -> Nat
  | atom => 1
  | pow a b => size a + size b

/-- All binary parenthesizations with exactly `n` copies of the single atom. -/
def parenthesizations : Nat -> List Expr
  | 0 => []
  | 1 => [atom]
  | n + 2 =>
      (List.finRange (n + 1)).flatMap fun k =>
        (parenthesizations (k.1 + 1)).flatMap fun a =>
          (parenthesizations (n + 1 - k.1)).map fun b => pow a b
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)
  · exact Nat.succ_lt_succ k.2

theorem parenthesizations_zero_eq :
    parenthesizations 0 = [] := by
  rw [parenthesizations.eq_def]

theorem parenthesizations_one_eq :
    parenthesizations 1 = [atom] := by
  rw [parenthesizations.eq_def]

theorem parenthesizations_succ_succ (n : Nat) :
    parenthesizations (n + 2) =
      (List.finRange (n + 1)).flatMap fun k =>
        (parenthesizations (k.1 + 1)).flatMap fun a =>
          (parenthesizations (n + 1 - k.1)).map fun b => pow a b := by
  rw [parenthesizations.eq_def]

/--
A generic bridge from any local one-token binary syntax to the shared lexical
parenthesizations.  The local syntax supplies its atom, binary node, and the
standard Catalan recursion for its parenthesization list.
-/
theorem toExpr_mem_parenthesizations {β : Type u}
    (localParenthesizations : Nat -> List β)
    (localAtom : β) (localPow : β -> β -> β)
    (toExpr : β -> Expr)
    (hZero : localParenthesizations 0 = [])
    (hOne : localParenthesizations 1 = [localAtom])
    (hStep : ∀ n,
      localParenthesizations (n + 2) =
        (List.finRange (n + 1)).flatMap fun k =>
          (localParenthesizations (k.1 + 1)).flatMap fun a =>
            (localParenthesizations (n + 1 - k.1)).map fun b => localPow a b)
    (hAtom : toExpr localAtom = atom)
    (hPow : ∀ a b, toExpr (localPow a b) = pow (toExpr a) (toExpr b))
    {n : Nat} {e : β}
    (he : e ∈ localParenthesizations n) :
    toExpr e ∈ parenthesizations n := by
  revert e
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro e he
      cases n with
      | zero =>
          rw [hZero] at he
          simp at he
      | succ n =>
          cases n with
          | zero =>
              rw [hOne] at he
              rcases (List.mem_singleton.mp he) with rfl
              simp [parenthesizations, hAtom]
          | succ n =>
              rw [hStep n] at he
              simp only [List.mem_flatMap, List.mem_map] at he
              rcases he with ⟨k, _hk, a, ha, b, hb, rfl⟩
              simp only [parenthesizations, List.mem_flatMap, List.mem_map]
              refine ⟨k, List.mem_finRange k, toExpr a, ?_, toExpr b, ?_, ?_⟩
              · exact ih (k.1 + 1) (Nat.succ_lt_succ k.2) ha
              · exact ih (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _)) hb
              · exact (hPow a b).symm

/--
A generic bridge from shared lexical parenthesizations back to a local
one-token binary syntax with the standard Catalan parenthesization recursion.
-/
theorem ofExpr_mem_parenthesizations {β : Type u}
    (localParenthesizations : Nat -> List β)
    (localAtom : β) (localPow : β -> β -> β)
    (ofExpr : Expr -> β)
    (hZero : localParenthesizations 0 = [])
    (hOne : localParenthesizations 1 = [localAtom])
    (hStep : ∀ n,
      localParenthesizations (n + 2) =
        (List.finRange (n + 1)).flatMap fun k =>
          (localParenthesizations (k.1 + 1)).flatMap fun a =>
            (localParenthesizations (n + 1 - k.1)).map fun b => localPow a b)
    (hAtom : ofExpr atom = localAtom)
    (hPow : ∀ a b, ofExpr (pow a b) = localPow (ofExpr a) (ofExpr b))
    {n : Nat} {e : Expr}
    (he : e ∈ parenthesizations n) :
    ofExpr e ∈ localParenthesizations n := by
  have _hZero := hZero
  revert e
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro e he
      cases n with
      | zero =>
          simp [parenthesizations] at he
      | succ n =>
          cases n with
          | zero =>
              rcases (by simpa [parenthesizations] using he) with rfl
              rw [hOne]
              simp [hAtom]
          | succ n =>
              simp only [parenthesizations, List.mem_flatMap, List.mem_map] at he
              rcases he with ⟨k, _hk, a, ha, b, hb, rfl⟩
              rw [hStep n]
              simp only [List.mem_flatMap, List.mem_map]
              refine ⟨k, List.mem_finRange k, ofExpr a, ?_, ofExpr b, ?_, ?_⟩
              · exact ih (k.1 + 1) (Nat.succ_lt_succ k.2) ha
              · exact ih (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _)) hb
              · exact (hPow a b).symm

/-- Interpret the shared lexical syntax by supplying an atom and a binary operation. -/
def eval (atomValue : α) (powValue : α -> α -> α) : Expr -> α
  | atom => atomValue
  | pow a b => powValue (eval atomValue powValue a) (eval atomValue powValue b)

@[simp] theorem eval_atom (atomValue : α) (powValue : α -> α -> α) :
    eval atomValue powValue atom = atomValue := rfl

@[simp] theorem eval_pow (atomValue : α) (powValue : α -> α -> α) (a b : Expr) :
    eval atomValue powValue (pow a b) =
      powValue (eval atomValue powValue a) (eval atomValue powValue b) := rfl

/-- The lexical semantic value set for a chosen atom and binary interpretation. -/
def valueSet (atomValue : α) (powValue : α -> α -> α) (n : Nat) : Set α :=
  {v | ∃ e ∈ parenthesizations n, eval atomValue powValue e = v}

/--
The set obtained by applying an arbitrary evaluator to every shared lexical
parenthesization of size `n`.  This is a general computation-facing view; the
canonical semantic value set is `valueSet` below, obtained by taking
`evalFn = eval atomValue powValue`.
-/
def evalSet (evalFn : Expr -> α) (n : Nat) : Set α :=
  {v | ∃ e ∈ parenthesizations n, evalFn e = v}

/--
Finite executable view of `evalSet`, for evaluators whose values have
decidable equality.
-/
def evalFinset [DecidableEq α] (evalFn : Expr -> α) (n : Nat) : Finset α :=
  ((parenthesizations n).map evalFn).toFinset

theorem evalSet_eq_evalFinset [DecidableEq α] (evalFn : Expr -> α) (n : Nat) :
    evalSet evalFn n = (evalFinset evalFn n : Set α) := by
  ext v
  simp [evalSet, evalFinset]

theorem evalSet_ncard_eq_evalFinset_card [DecidableEq α] (evalFn : Expr -> α)
    (n : Nat) :
    (evalSet evalFn n).ncard = (evalFinset evalFn n).card := by
  rw [evalSet_eq_evalFinset]
  exact Set.ncard_coe_finset (evalFinset evalFn n)

/--
If one computation-facing evaluator is pointwise an interpretation of another
one, then its evaluated lexical set is the image of the other evaluated set.
-/
theorem evalSet_eq_image_evalSet_of_eval_eq {β : Type v}
    (evalTarget : Expr -> α) (evalSource : Expr -> β) (repr : β -> α)
    (h : ∀ e, evalTarget e = repr (evalSource e)) (n : Nat) :
    evalSet evalTarget n = repr '' evalSet evalSource n := by
  ext v
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨evalSource e, ⟨e, he, rfl⟩, (h e).symm⟩
  · rintro ⟨w, ⟨e, he, hw⟩, hv⟩
    refine ⟨e, he, ?_⟩
    rw [h, hw, hv]

theorem evalSet_ncard_eq_of_eval_eq_of_injOn {β : Type v}
    (evalTarget : Expr -> α) (evalSource : Expr -> β) (repr : β -> α)
    (h : ∀ e, evalTarget e = repr (evalSource e)) (n : Nat)
    (hInj : Set.InjOn repr (evalSet evalSource n)) :
    (evalSet evalTarget n).ncard = (evalSet evalSource n).ncard := by
  rw [evalSet_eq_image_evalSet_of_eval_eq evalTarget evalSource repr h n]
  exact Set.InjOn.ncard_image hInj

theorem evalFinset_eq_image_evalFinset_of_eval_eq [DecidableEq α] {β : Type v}
    [DecidableEq β] (evalTarget : Expr -> α) (evalSource : Expr -> β)
    (repr : β -> α) (h : ∀ e, evalTarget e = repr (evalSource e)) (n : Nat) :
    evalFinset evalTarget n = (evalFinset evalSource n).image repr := by
  ext v
  simp [evalFinset, h]

theorem evalFinset_card_eq_of_eval_eq_of_injOn [DecidableEq α] {β : Type v}
    [DecidableEq β] (evalTarget : Expr -> α) (evalSource : Expr -> β)
    (repr : β -> α) (h : ∀ e, evalTarget e = repr (evalSource e)) (n : Nat)
    (hInj : Set.InjOn repr (evalFinset evalSource n : Set β)) :
    (evalFinset evalTarget n).card = (evalFinset evalSource n).card := by
  rw [evalFinset_eq_image_evalFinset_of_eval_eq evalTarget evalSource repr h n]
  exact Finset.card_image_of_injOn hInj

theorem valueSet_eq_evalSet (atomValue : α) (powValue : α -> α -> α) (n : Nat) :
    valueSet atomValue powValue n = evalSet (eval atomValue powValue) n := by
  rfl

/-- The cardinality of the lexical semantic value set. -/
noncomputable def valueCard (atomValue : α) (powValue : α -> α -> α) (n : Nat) : Nat :=
  (valueSet atomValue powValue n).ncard

theorem valueSet_eq_evalFinset [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    valueSet atomValue powValue n =
      (evalFinset (eval atomValue powValue) n : Set α) := by
  rw [valueSet_eq_evalSet, evalSet_eq_evalFinset]

theorem valueCard_eq_evalFinset_card [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    valueCard atomValue powValue n =
      (evalFinset (eval atomValue powValue) n).card := by
  rw [valueCard, valueSet_eq_evalFinset]
  exact Set.ncard_coe_finset (evalFinset (eval atomValue powValue) n)

theorem valueCard_eq_evalSet_ncard_of_eval_eq_of_injOn {β : Type v}
    (atomValue : α) (powValue : α -> α -> α) (evalSource : Expr -> β)
    (repr : β -> α)
    (h : ∀ e, eval atomValue powValue e = repr (evalSource e)) (n : Nat)
    (hInj : Set.InjOn repr (evalSet evalSource n)) :
    valueCard atomValue powValue n = (evalSet evalSource n).ncard := by
  rw [valueCard, valueSet_eq_evalSet]
  exact evalSet_ncard_eq_of_eval_eq_of_injOn
    (eval atomValue powValue) evalSource repr h n hInj

theorem valueCard_eq_evalFinset_card_of_eval_eq_of_injOn [DecidableEq α] {β : Type v}
    [DecidableEq β] (atomValue : α) (powValue : α -> α -> α)
    (evalSource : Expr -> β) (repr : β -> α)
    (h : ∀ e, eval atomValue powValue e = repr (evalSource e)) (n : Nat)
    (hInj : Set.InjOn repr (evalFinset evalSource n : Set β)) :
    valueCard atomValue powValue n = (evalFinset evalSource n).card := by
  rw [valueCard_eq_evalFinset_card atomValue powValue n]
  exact evalFinset_card_eq_of_eval_eq_of_injOn
    (eval atomValue powValue) evalSource repr h n hInj

/--
The split-recursive presentation of the same values.  This is not the
canonical definition; it is the standard computation-oriented presentation,
proved equivalent to `valueSet` below.
-/
def recursiveValueSet (atomValue : α) (powValue : α -> α -> α) : Nat -> Set α
  | 0 => ∅
  | 1 => {atomValue}
  | n + 2 =>
      {v | ∃ k : Fin (n + 1),
        ∃ x ∈ recursiveValueSet atomValue powValue (k.1 + 1),
        ∃ y ∈ recursiveValueSet atomValue powValue (n + 1 - k.1),
          v = powValue x y}
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/--
The split-recursive set is extensionally equal to the canonical lexical
syntax-and-evaluation set.
-/
theorem valueSet_eq_recursiveValueSet (atomValue : α) (powValue : α -> α -> α) (n : Nat) :
    valueSet atomValue powValue n = recursiveValueSet atomValue powValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          ext v
          simp [valueSet, parenthesizations_zero_eq, recursiveValueSet]
      | succ n =>
          cases n with
          | zero =>
              ext v
              simp [valueSet, parenthesizations_one_eq, recursiveValueSet]
          | succ n =>
              ext v
              constructor
              · rintro ⟨e, he, rfl⟩
                simp only [parenthesizations, List.mem_flatMap, List.mem_map] at he
                rcases he with ⟨k, _hk, a, ha, b, hb, rfl⟩
                simp only [eval, recursiveValueSet]
                refine ⟨k, eval atomValue powValue a, ?_,
                  eval atomValue powValue b, ?_, rfl⟩
                · have hleft := ih (k.1 + 1) (Nat.succ_lt_succ k.2)
                  rw [← hleft]
                  exact ⟨a, ha, rfl⟩
                · have hright := ih (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _))
                  rw [← hright]
                  exact ⟨b, hb, rfl⟩
              · intro hv
                simp only [recursiveValueSet] at hv
                rcases hv with ⟨k, x, hx, y, hy, rfl⟩
                have hleft := ih (k.1 + 1) (Nat.succ_lt_succ k.2)
                have hxLex : x ∈ valueSet atomValue powValue (k.1 + 1) := by
                  rw [hleft]
                  exact hx
                have hright := ih (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _))
                have hyLex : y ∈ valueSet atomValue powValue (n + 1 - k.1) := by
                  rw [hright]
                  exact hy
                rcases hxLex with ⟨a, ha, rfl⟩
                rcases hyLex with ⟨b, hb, rfl⟩
                refine ⟨pow a b, ?_, rfl⟩
                simp only [parenthesizations, List.mem_flatMap, List.mem_map]
                exact ⟨k, List.mem_finRange k, a, ha, b, hb, rfl⟩

/--
The canonical lexical count can be computed as the cardinality of the
split-recursive value set.  This version does not require decidable equality,
so it applies also to function-valued interpretations such as A000081.
-/
theorem valueCard_eq_recursiveValueSet_ncard (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    valueCard atomValue powValue n =
      (recursiveValueSet atomValue powValue n).ncard := by
  rw [valueCard, valueSet_eq_recursiveValueSet]

/--
Finite-set version of `recursiveValueSet`, for interpretations whose values
have decidable equality.  This is a computation-oriented presentation, not the
canonical lexical definition; `recursiveValueFinset_coe` proves equivalence to
the shared lexical semantics through `recursiveValueSet`.
-/
def recursiveValueFinset [DecidableEq α] (atomValue : α) (powValue : α -> α -> α) :
    Nat -> Finset α
  | 0 => ∅
  | 1 => {atomValue}
  | n + 2 =>
      (Finset.univ : Finset (Fin (n + 1))).biUnion fun k =>
        Finset.image₂ powValue
          (recursiveValueFinset atomValue powValue (k.1 + 1))
          (recursiveValueFinset atomValue powValue (n + 1 - k.1))
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

theorem recursiveValueFinset_coe [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    (recursiveValueFinset atomValue powValue n : Set α) =
      recursiveValueSet atomValue powValue n := by
  induction n using recursiveValueFinset.induct with
  | case1 =>
      ext v
      simp [recursiveValueFinset, recursiveValueSet]
  | case2 =>
      ext v
      simp [recursiveValueFinset, recursiveValueSet]
  | case3 n ihLeft ihRight =>
      ext v
      simp [recursiveValueFinset, recursiveValueSet, ihLeft, ihRight]
      constructor
      · rintro ⟨i, a, ha, b, hb, hv⟩
        exact ⟨i, a, ha, b, hb, hv.symm⟩
      · rintro ⟨i, a, ha, b, hb, hv⟩
        exact ⟨i, a, ha, b, hb, hv.symm⟩

/--
The direct finite enumeration of lexical expressions and the finite
split-recursive computation produce the same finite set for every decidable
interpretation.
-/
theorem evalFinset_eq_recursiveValueFinset [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    evalFinset (eval atomValue powValue) n =
      recursiveValueFinset atomValue powValue n := by
  ext v
  change v ∈ (evalFinset (eval atomValue powValue) n : Set α) ↔
    v ∈ (recursiveValueFinset atomValue powValue n : Set α)
  rw [← evalSet_eq_evalFinset (eval atomValue powValue) n,
    ← valueSet_eq_evalSet atomValue powValue n,
    valueSet_eq_recursiveValueSet atomValue powValue n,
    ← recursiveValueFinset_coe atomValue powValue n]

theorem evalFinset_eq_recursiveValueFinset_of_eval_eq [DecidableEq α]
    (evalFn : Expr -> α) (atomValue : α) (powValue : α -> α -> α)
    (h : ∀ e, evalFn e = eval atomValue powValue e) (n : Nat) :
    evalFinset evalFn n = recursiveValueFinset atomValue powValue n := by
  rw [← evalFinset_eq_recursiveValueFinset atomValue powValue n]
  ext v
  simp [evalFinset, h]

theorem valueCard_eq_recursiveValueFinset_card [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    valueCard atomValue powValue n =
      (recursiveValueFinset atomValue powValue n).card := by
  rw [valueCard, valueSet_eq_recursiveValueSet]
  rw [← recursiveValueFinset_coe atomValue powValue n]
  exact Set.ncard_coe_finset (recursiveValueFinset atomValue powValue n)

/--
Compute one finite-set recurrence row from an already-built table of smaller
rows.  The theorem `recursiveValueFinsetFromTable_eq` proves that this
memoized presentation computes the same finite set as `recursiveValueFinset`.
-/
def recursiveValueFinsetFromTable [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (levels : List (Finset α)) : Nat -> Finset α
  | 0 => ∅
  | 1 => {atomValue}
  | n + 2 =>
      (Finset.univ : Finset (Fin (n + 1))).biUnion fun k =>
        Finset.image₂ powValue
          (levels.getD (k.1 + 1) ∅)
          (levels.getD (n + 1 - k.1) ∅)

theorem recursiveValueFinsetFromTable_eq [DecidableEq α] {atomValue : α}
    {powValue : α -> α -> α} {levels : List (Finset α)} {n : Nat}
    (hlevels : ∀ i < n, levels.getD i ∅ = recursiveValueFinset atomValue powValue i) :
    recursiveValueFinsetFromTable atomValue powValue levels n =
      recursiveValueFinset atomValue powValue n := by
  cases n with
  | zero =>
      simp [recursiveValueFinsetFromTable, recursiveValueFinset]
  | succ n =>
      cases n with
      | zero =>
          simp [recursiveValueFinsetFromTable, recursiveValueFinset]
      | succ n =>
          simp only [recursiveValueFinsetFromTable, recursiveValueFinset]
          apply Finset.biUnion_congr rfl
          intro k _hk
          rw [hlevels (k.1 + 1) (Nat.succ_lt_succ k.2)]
          rw [hlevels (n + 1 - k.1) (Nat.lt_succ_of_le (Nat.sub_le _ _))]

/-- Table of finite-set recurrence rows `0, ..., n - 1`, built once left to right. -/
def recursiveValueFinsetTable [DecidableEq α] (atomValue : α) (powValue : α -> α -> α) :
    Nat -> List (Finset α)
  | 0 => []
  | n + 1 =>
      let levels := recursiveValueFinsetTable atomValue powValue n
      levels ++ [recursiveValueFinsetFromTable atomValue powValue levels n]

theorem recursiveValueFinsetTable_length [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    (recursiveValueFinsetTable atomValue powValue n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [recursiveValueFinsetTable, ih]

theorem list_getD_eq_getElem {β : Type u} (xs : List β) {i : Nat} (fallback : β)
    (hi : i < xs.length) :
    xs.getD i fallback = xs[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

/-- The memo table agrees with `recursiveValueFinset` at every stored index. -/
theorem recursiveValueFinsetTable_getD [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n i : Nat) (hi : i < n) :
    (recursiveValueFinsetTable atomValue powValue n).getD i ∅ =
      recursiveValueFinset atomValue powValue i := by
  induction n generalizing i with
  | zero =>
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      have hle : i ≤ n := Nat.lt_succ_iff.mp hi
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hiTable : i < (recursiveValueFinsetTable atomValue powValue n).length := by
          simpa [recursiveValueFinsetTable_length] using hlt
        rw [recursiveValueFinsetTable]
        rw [list_getD_eq_getElem
          (recursiveValueFinsetTable atomValue powValue n ++
            [recursiveValueFinsetFromTable atomValue powValue
              (recursiveValueFinsetTable atomValue powValue n) n])
          ∅ (by simpa [recursiveValueFinsetTable_length] using hi)]
        rw [List.getElem_append_left hiTable]
        rw [← list_getD_eq_getElem (recursiveValueFinsetTable atomValue powValue n) ∅
          hiTable]
        exact ih i hlt
      · subst i
        rw [recursiveValueFinsetTable]
        rw [list_getD_eq_getElem
          (recursiveValueFinsetTable atomValue powValue n ++
            [recursiveValueFinsetFromTable atomValue powValue
              (recursiveValueFinsetTable atomValue powValue n) n])
          ∅ (by simp [recursiveValueFinsetTable_length])]
        rw [List.getElem_append_right (by simp [recursiveValueFinsetTable_length])]
        simp [recursiveValueFinsetTable_length,
          recursiveValueFinsetFromTable_eq (atomValue := atomValue) (powValue := powValue) ih]

/-- Memoized finite-set recurrence row, proved equal to `recursiveValueFinset`. -/
def recursiveValueFinsetMemo [DecidableEq α] (atomValue : α) (powValue : α -> α -> α)
    (n : Nat) : Finset α :=
  (recursiveValueFinsetTable atomValue powValue (n + 1)).getD n ∅

theorem recursiveValueFinsetMemo_eq [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) :
    recursiveValueFinsetMemo atomValue powValue n =
      recursiveValueFinset atomValue powValue n := by
  exact recursiveValueFinsetTable_getD atomValue powValue (n + 1) n (Nat.lt_succ_self n)

/-- Memoized finite-set counts for sizes `1, ..., n`, computed from one shared table. -/
def recursiveValueCountsMemoThrough [DecidableEq α] (atomValue : α)
    (powValue : α -> α -> α) (n : Nat) : List Nat :=
  ((recursiveValueFinsetTable atomValue powValue (n + 1)).drop 1).map Finset.card

theorem recursiveValueCountsMemoThrough_getD [DecidableEq α] {atomValue : α}
    {powValue : α -> α -> α} {N i : Nat} (hi : i < N) :
    (recursiveValueCountsMemoThrough atomValue powValue N).getD i 0 =
      (recursiveValueFinsetMemo atomValue powValue (i + 1)).card := by
  unfold recursiveValueCountsMemoThrough
  have hiDrop :
      i < (List.drop 1 (recursiveValueFinsetTable atomValue powValue (N + 1))).length := by
    simp [recursiveValueFinsetTable_length, hi]
  have hiCounts :
      i <
        (List.map Finset.card
          (List.drop 1 (recursiveValueFinsetTable atomValue powValue (N + 1)))).length := by
    simpa using hiDrop
  have hiTable :
      i + 1 < (recursiveValueFinsetTable atomValue powValue (N + 1)).length := by
    simpa [recursiveValueFinsetTable_length, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using Nat.succ_lt_succ hi
  rw [list_getD_eq_getElem _ _ hiCounts]
  rw [List.getElem_map]
  rw [List.getElem_drop]
  have hiTable' : 1 + i < (recursiveValueFinsetTable atomValue powValue (N + 1)).length := by
    simpa [Nat.add_comm] using hiTable
  have hleft :
      (recursiveValueFinsetTable atomValue powValue (N + 1))[1 + i] =
        recursiveValueFinset atomValue powValue (i + 1) := by
    rw [← list_getD_eq_getElem (recursiveValueFinsetTable atomValue powValue (N + 1))
      ∅ hiTable']
    simpa [Nat.add_comm] using
      recursiveValueFinsetTable_getD atomValue powValue (N + 1) (i + 1)
        (Nat.succ_lt_succ hi)
  rw [hleft]
  rw [recursiveValueFinsetMemo_eq]

theorem recursiveValueCountsMemoThrough_getD_eq_recursiveValueFinset_card
    [DecidableEq α] {atomValue : α} {powValue : α -> α -> α}
    {N i : Nat} (hi : i < N) :
    (recursiveValueCountsMemoThrough atomValue powValue N).getD i 0 =
      (recursiveValueFinset atomValue powValue (i + 1)).card := by
  rw [recursiveValueCountsMemoThrough_getD hi]
  rw [recursiveValueFinsetMemo_eq]

theorem recursiveValueFinset_card_eq_countsMemoThrough_getD
    [DecidableEq α] {atomValue : α} {powValue : α -> α -> α}
    {N n : Nat} (hpos : 0 < n) (hN : n ≤ N) :
    (recursiveValueFinset atomValue powValue n).card =
      (recursiveValueCountsMemoThrough atomValue powValue N).getD (n - 1) 0 := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ hpos).elim
  | succ i =>
      have hi : i < N := Nat.succ_le_iff.mp hN
      simpa using
        (recursiveValueCountsMemoThrough_getD_eq_recursiveValueFinset_card
          (atomValue := atomValue) (powValue := powValue) (N := N) (i := i) hi).symm

def e2 : Expr :=
  pow atom atom

def e3a : Expr :=
  pow atom e2

def e3b : Expr :=
  pow e2 atom

def e4a : Expr :=
  pow atom e3a

def e4b : Expr :=
  pow atom e3b

def e4c : Expr :=
  pow e2 e2

def e4d : Expr :=
  pow e3a atom

def e4e : Expr :=
  pow e3b atom

def e5a : Expr :=
  pow atom e4a

def e5b : Expr :=
  pow atom e4b

def e5c : Expr :=
  pow atom e4c

def e5d : Expr :=
  pow atom e4d

def e5e : Expr :=
  pow atom e4e

def e5f : Expr :=
  pow e2 e3a

def e5g : Expr :=
  pow e2 e3b

def e5h : Expr :=
  pow e3a e2

def e5i : Expr :=
  pow e3b e2

def e5j : Expr :=
  pow e4a atom

def e5k : Expr :=
  pow e4b atom

def e5l : Expr :=
  pow e4c atom

def e5m : Expr :=
  pow e4d atom

def e5n : Expr :=
  pow e4e atom

theorem parenthesizations_one :
    parenthesizations 1 = [atom] := by
  native_decide

theorem parenthesizations_two :
    parenthesizations 2 = [e2] := by
  native_decide

theorem parenthesizations_three :
    parenthesizations 3 = [e3a, e3b] := by
  native_decide

theorem parenthesizations_four :
    parenthesizations 4 = [e4a, e4b, e4c, e4d, e4e] := by
  native_decide

theorem parenthesizations_five :
    parenthesizations 5 =
      [e5a, e5b, e5c, e5d, e5e, e5f, e5g, e5h, e5i, e5j, e5k, e5l, e5m, e5n] := by
  native_decide

end Expr

end PowTower

end LeanProofs
