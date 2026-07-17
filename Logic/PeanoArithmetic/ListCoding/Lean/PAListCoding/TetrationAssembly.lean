import PAListCoding.IterationDioph

/-!
# Final Lean assembly for tetration

The mathematical work is now modular: one encoded tower step is
Diophantine, exact variable-length iteration follows from bounded universals,
and the state code is injective.  This file combines those ingredients into
the public result-first tetration graph, parameterized only by the five
arithmetic cipher primitive closures.
-/

namespace PAListCoding

namespace TetrationAssembly

open BoundedCipher BoundedCipherDioph CipherCircuit CircuitDioph
open IterationDioph SparseCipher
open Fin2
open scoped Dioph

/-- The result-first tetration graph is Diophantine once the arithmetic
cipher primitives satisfy their substitution contracts. -/
theorem naturalTetrationGraph_diophantine_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    Dioph NaturalTetrationGraph := by
  have dresult : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &0) := D&0
  have dbase : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &1) := D&1
  have dheight : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => v &2) := D&2
  have done : Dioph.DiophFn
      (fun _v : Vector3 ℕ 3 => 1) := BoundedDioph.constFn_dioph 1
  have dstart : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => tetrationStateCode (v &1) 1) :=
    tetrationStateCode_diophFn dbase done
  have dfinish : Dioph.DiophFn
      (fun v : Vector3 ℕ 3 => tetrationStateCode (v &1) (v &0)) :=
    tetrationStateCode_diophFn dbase dresult
  have hiter : Dioph {v : Vector3 ℕ 3 |
      ExactIter TetrationStep (v &2)
        (tetrationStateCode (v &1) 1)
        (tetrationStateCode (v &1) (v &0))} :=
    exactIter_dioph hcode hconstFixed hconst hindex hmul
      tetrationStep_diophantine dheight dstart dfinish
  apply Dioph.ext hiter
  intro v
  change
    ExactIter TetrationStep (v &2)
        (tetrationStateCode (v &1) 1)
        (tetrationStateCode (v &1) (v &0)) ↔
      v &0 = tetration (v &1) (v &2)
  exact (tetration_eq_iff_exactIter (v &0) (v &1) (v &2)).symm

/-- Function-graph form of the same result. -/
theorem naturalTetration_diophantineFunction_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    Dioph.DiophFn NaturalTetrationFunction := by
  apply (Dioph.diophFn_vec NaturalTetrationFunction).2
  apply Dioph.ext
    (naturalTetrationGraph_diophantine_of_cipherClosures
      hcode hconstFixed hconst hindex hmul)
  intro v
  change
    (v &0 = tetration (v &1) (v &2)) ↔
      (tetration (v &1) (v &2) = v &0)
  exact eq_comm

/-- Unfolded witness contract: a single integer polynomial, with a fixed
existential tuple of natural variables, defines the tetration graph. -/
theorem naturalTetration_polynomial_exists_of_cipherClosures
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel) :
    ∃ (β : Type) (p : Poly (Fin2 3 ⊕ β)),
      ∀ v : Vector3 ℕ 3,
        v &0 = tetration (v &1) (v &2) ↔
          ∃ t : β → ℕ, p (Sum.elim v t) = 0 :=
  naturalTetrationGraph_diophantine_of_cipherClosures
    hcode hconstFixed hconst hindex hmul

end TetrationAssembly

end PAListCoding
