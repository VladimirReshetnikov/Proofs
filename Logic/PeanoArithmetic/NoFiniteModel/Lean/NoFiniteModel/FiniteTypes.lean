import Init.Data.Fin.Lemmas

/-!
# Explicit finiteness and finite self-injections

`IsFiniteType α` expresses conventional finiteness by exhibiting an explicit
two-sided equivalence between `α` and `Fin n` for some natural number `n`.
From that data, an injective endomap is constructively surjective.  The proof
is self-contained and uses only decidable equality on `Fin n`; it does not
open the `Classical` namespace or invoke choice.
-/

namespace LeanProofs
namespace NoFinitePAModel

open Function

universe u

/-- A dependency-free equivalence between a type and a finite ordinal. -/
structure FinEquiv (α : Type u) (n : Nat) where
  toFun : α → Fin n
  invFun : Fin n → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ i, toFun (invFun i) = i

namespace FinEquiv

theorem toFun_injective {α : Type u} {n : Nat} (e : FinEquiv α n) :
    Injective e.toFun := by
  intro x y hxy
  calc
    x = e.invFun (e.toFun x) := (e.left_inv x).symm
    _ = e.invFun (e.toFun y) := congrArg e.invFun hxy
    _ = y := e.left_inv y

theorem invFun_injective {α : Type u} {n : Nat} (e : FinEquiv α n) :
    Injective e.invFun := by
  intro i j hij
  calc
    i = e.toFun (e.invFun i) := (e.right_inv i).symm
    _ = e.toFun (e.invFun j) := congrArg e.toFun hij
    _ = j := e.right_inv j

/-- The identity equivalence on a finite ordinal. -/
def refl (n : Nat) : FinEquiv (Fin n) n where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end FinEquiv

/-- A type is finite when it is equivalent to `Fin n` for some `n`.
`Nonempty` keeps the equivalence witness proposition-valued. -/
def IsFiniteType (α : Type u) : Prop :=
  ∃ n : Nat, Nonempty (FinEquiv α n)

/-- `Fin n` is finite in the explicit sense used by this development. -/
theorem fin_isFiniteType (n : Nat) : IsFiniteType (Fin n) :=
  ⟨n, ⟨FinEquiv.refl n⟩⟩

/-! ## A constructive finite pigeonhole argument -/

/-- Swap zero with `a` in `Fin (n+1)`.  Only the `a ≠ 0` case is needed
below; spelling out this transposition keeps the finite pigeonhole proof
independent of a permutation library. -/
def swapZero {n : Nat} (a x : Fin (n + 1)) : Fin (n + 1) :=
  if x = 0 then a else if x = a then 0 else x

theorem swapZero_involutive {n : Nat} {a : Fin (n + 1)} (ha : a ≠ 0)
    (x : Fin (n + 1)) : swapZero a (swapZero a x) = x := by
  by_cases hx0 : x = 0
  · subst x
    simp [swapZero, ha]
  · by_cases hxa : x = a
    · subst x
      simp [swapZero, ha]
    · simp [swapZero, hx0, hxa]

theorem swapZero_injective {n : Nat} {a : Fin (n + 1)} (ha : a ≠ 0) :
    Injective (swapZero a) := by
  intro x y hxy
  calc
    x = swapZero a (swapZero a x) := (swapZero_involutive ha x).symm
    _ = swapZero a (swapZero a y) := congrArg (swapZero a) hxy
    _ = y := swapZero_involutive ha y

/-- An injective endomap of `Fin n` is surjective.  At the successor step,
transpose `f 0` with zero, restrict the normalized map to the nonzero
elements, and invoke the induction hypothesis on `Fin n`. -/
theorem fin_surjective_of_injective :
    ∀ {n : Nat} (f : Fin n → Fin n), Injective f → Surjective f := by
  intro n
  induction n with
  | zero =>
      intro f hf y
      exact Fin.elim0 y
  | succ n ih =>
      intro f hf
      have normalized :
          ∀ (k : Fin (n + 1) → Fin (n + 1)), Injective k → k 0 = 0 →
            Surjective k := by
        intro k hk hk0
        have hnonzero : ∀ i : Fin n, k i.succ ≠ 0 := by
          intro i hi
          have hsame : k i.succ = k 0 := hi.trans hk0.symm
          exact Fin.succ_ne_zero i (hk hsame)
        let g : Fin n → Fin n := fun i => (k i.succ).pred (hnonzero i)
        have hg : Injective g := by
          intro i j hij
          apply Fin.succ_inj.mp
          apply hk
          calc
            k i.succ = ((k i.succ).pred (hnonzero i)).succ :=
              (Fin.succ_pred (k i.succ) (hnonzero i)).symm
            _ = ((k j.succ).pred (hnonzero j)).succ := congrArg Fin.succ hij
            _ = k j.succ := Fin.succ_pred (k j.succ) (hnonzero j)
        have hgsurj : Surjective g := ih g hg
        intro y
        by_cases hy : y = 0
        · subst y
          exact ⟨0, hk0⟩
        · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hy
          obtain ⟨i, hi⟩ := hgsurj j
          refine ⟨i.succ, ?_⟩
          calc
            k i.succ = ((k i.succ).pred (hnonzero i)).succ :=
              (Fin.succ_pred (k i.succ) (hnonzero i)).symm
            _ = j.succ := congrArg Fin.succ hi
            _ = y := hj.symm
      by_cases hf0 : f 0 = 0
      · exact normalized f hf hf0
      · let h : Fin (n + 1) → Fin (n + 1) :=
          fun i => swapZero (f 0) (f i)
        have hh0 : h 0 = 0 := by
          simp [h, swapZero, hf0]
        have hhinj : Injective h := by
          intro i j hij
          exact hf (swapZero_injective hf0 hij)
        have hhsurj : Surjective h := normalized h hhinj hh0
        intro y
        obtain ⟨i, hi⟩ := hhsurj (swapZero (f 0) y)
        refine ⟨i, ?_⟩
        exact swapZero_injective hf0 hi

/-- Transport the finite self-injection theorem across a displayed
equivalence with `Fin n`. -/
theorem surjective_of_injective_of_equiv_fin {α : Type u} {n : Nat}
    (e : FinEquiv α n) (f : α → α) (hf : Injective f) : Surjective f := by
  let g : Fin n → Fin n := fun i => e.toFun (f (e.invFun i))
  have hg : Injective g := by
    intro i j hij
    apply e.invFun_injective
    apply hf
    exact e.toFun_injective hij
  have hgsurj : Surjective g := fin_surjective_of_injective g hg
  intro y
  obtain ⟨i, hi⟩ := hgsurj (e.toFun y)
  refine ⟨e.invFun i, ?_⟩
  apply e.toFun_injective
  simpa [g] using hi

/-- Every injective endomap of an explicitly finite type is surjective. -/
theorem finite_self_surjective_of_injective {α : Type u}
    (hfinite : IsFiniteType α) (f : α → α) (hf : Injective f) :
    Surjective f := by
  rcases hfinite with ⟨n, ⟨e⟩⟩
  exact surjective_of_injective_of_equiv_fin e f hf

end NoFinitePAModel
end LeanProofs
