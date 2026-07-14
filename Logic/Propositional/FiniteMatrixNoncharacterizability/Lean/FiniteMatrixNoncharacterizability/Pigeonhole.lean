/-!
# A dependency-free finite pigeonhole lemma

The domain has one more element than the codomain, so every function has a
collision.  Keeping this lemma here avoids making the logical result depend on
a finite-cardinality library.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

/-- Swap `a` and zero in `Fin (n + 1)`, fixing every other element. -/
def swapZero {n : Nat} (a x : Fin (n + 1)) : Fin (n + 1) :=
  if x = a then 0 else if x = 0 then a else x

theorem swapZero_involutive {n : Nat} (a x : Fin (n + 1)) :
    swapZero a (swapZero a x) = x := by
  by_cases hxa : x = a
  · subst x
    simp [swapZero]
  · by_cases hx : x = 0
    · subst x
      simp [swapZero]
    · simp [swapZero, hxa, hx]

theorem swapZero_injective {n : Nat} (a : Fin (n + 1)) :
    Function.Injective (swapZero a) := by
  intro x y h
  have := congrArg (swapZero a) h
  simpa only [swapZero_involutive] using this

theorem swapZero_ne_zero_of_ne {n : Nat} {a x : Fin (n + 1)} (h : x ≠ a) :
    swapZero a x ≠ 0 := by
  intro hz
  have hx : x = a := by
    apply swapZero_injective a
    calc
      swapZero a x = 0 := hz
      _ = swapZero a a := by simp [swapZero]
  exact h hx

theorem fin_pred_injective_on_nonzero {n : Nat} {x y : Fin (n + 1)}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x.pred hx = y.pred hy) : x = y := by
  exact Fin.pred_inj.mp h

/-- The finite pigeonhole principle in exactly the form used below. -/
theorem fin_pigeonhole : ∀ n : Nat, ∀ f : Fin (n + 1) → Fin n,
    ∃ i j, i ≠ j ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
      intro f
      exact Fin.elim0 (f 0)
  | succ n ih =>
      intro f
      let a : Fin (n + 1) := f 0
      by_cases hcollision : ∃ i : Fin (n + 1), f i.succ = a
      · obtain ⟨i, hi⟩ := hcollision
        exact ⟨0, i.succ, (Fin.succ_ne_zero i).symm, hi.symm⟩
      · have hne : ∀ i : Fin (n + 1), f i.succ ≠ a := by
          intro i hi
          exact hcollision ⟨i, hi⟩
        let g : Fin (n + 1) → Fin n := fun i =>
          (swapZero a (f i.succ)).pred (swapZero_ne_zero_of_ne (hne i))
        obtain ⟨i, j, hij, hg⟩ := ih g
        refine ⟨i.succ, j.succ, ?_, ?_⟩
        · intro hs
          apply hij
          exact Fin.succ_inj.mp hs
        · apply swapZero_injective a
          apply fin_pred_injective_on_nonzero
              (swapZero_ne_zero_of_ne (hne i))
              (swapZero_ne_zero_of_ne (hne j))
          exact hg

end FiniteMatrixNoncharacterizability
end LeanProofs
