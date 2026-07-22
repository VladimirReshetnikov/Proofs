import PAListCoding.NumberTheory
import Mathlib.NumberTheory.Dioph

/-!
# Natural-number exponentiation is Diophantine

The existing `Power` predicate represents exponentiation by a coded
multiplication trace in the language of PA.  This module proves the different,
stronger metatheoretic statement that its standard-natural-number graph is
Diophantine: membership is equivalent to the existence of a solution of one
integer polynomial equation.

Mathlib's `Dioph.pow_dioph` is a formalized version of Matiyasevich's theorem.
It builds the polynomial condition from Pell equations and includes all edge
cases, in particular `a ^ 0 = 1` and `0 ^ 0 = 1`.  We specialize that theorem
to the two coordinate projections and then place the output in coordinate zero
to match this project's result-first convention `(m, n, k)`.
-/

namespace PAListCoding

open Fin2
open scoped Dioph

/-- The binary natural-power function, with base followed by exponent. -/
def NaturalPowFunction (v : Vector3 ℕ 2) : ℕ :=
  v &0 ^ v &1

/-- Its result-first three-variable graph: `(m, n, k)` belongs exactly when
    `m = n ^ k`. -/
def NaturalPowGraph : Set (Vector3 ℕ 3) :=
  {v | v &0 = v &1 ^ v &2}

/-- Matiyasevich's theorem specialized to binary natural exponentiation. -/
theorem naturalPow_diophantineFunction :
    Dioph.DiophFn NaturalPowFunction := by
  exact Dioph.pow_dioph
    (Dioph.proj_dioph (&0 : Fin2 2))
    (Dioph.proj_dioph (&1 : Fin2 2))

/-- The result-first graph `m = n^k` is a Diophantine subset of `ℕ³`. -/
theorem naturalPowGraph_diophantine :
    Dioph NaturalPowGraph := by
  apply Dioph.ext
    ((Dioph.diophFn_vec NaturalPowFunction).mp
      naturalPow_diophantineFunction)
  intro v
  change (v &1 ^ v &2 = v &0) ↔ (v &0 = v &1 ^ v &2)
  exact eq_comm

/-- The project's trace-defined `Power` relation has the same Diophantine
    graph over the standard natural numbers. -/
theorem power_diophantine :
    Dioph {v : Vector3 ℕ 3 | Power (v &0) (v &1) (v &2)} := by
  apply Dioph.ext naturalPowGraph_diophantine
  intro v
  change
    (v &0 = v &1 ^ v &2) ↔
      Power (v &0) (v &1) (v &2)
  exact (pow_iff (v &0) (v &1) (v &2)).symm

/-- Unfolded witness contract: one integer polynomial, with an existential
    tuple of auxiliary natural-number variables, defines `Power`. -/
theorem power_polynomial_exists :
    ∃ (β : Type) (p : Poly (Fin2 3 ⊕ β)),
      ∀ v : Vector3 ℕ 3,
        Power (v &0) (v &1) (v &2) ↔
          ∃ t : β → ℕ, p (Sum.elim v t) = 0 :=
  power_diophantine

end PAListCoding
