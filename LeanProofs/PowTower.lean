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

/-- The cardinality of the lexical semantic value set. -/
noncomputable def valueCard (atomValue : α) (powValue : α -> α -> α) (n : Nat) : Nat :=
  (valueSet atomValue powValue n).ncard

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
          simp [valueSet, parenthesizations, recursiveValueSet]
      | succ n =>
          cases n with
          | zero =>
              ext v
              simp [valueSet, parenthesizations, recursiveValueSet]
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
