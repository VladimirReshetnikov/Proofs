import Foundation.FirstOrder.Incompleteness.Halting
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# Undecidability of Peano-arithmetic theoremhood

The proof isolates a single computably generated family of closed PA
sentences whose theoremhood predicate is the halting problem. This is a
stronger obstruction than merely exhibiting an independent sentence: even
the restriction of PA theoremhood to this one family is not computable.

The arithmetization and representability theorem are supplied by
FormalizedFormalLogic/Foundation. Mathlib supplies the noncomputability of
the halting predicate for partial-recursive program codes.
-/

namespace PAUndecidable

open Encodable Part
open Nat.Partrec (Code)
open Nat.Partrec.Code
open LO Entailment FirstOrder
open LO.FirstOrder.Arithmetic

/-- The halting problem transported from partial-recursive codes to natural
Goedel numbers. Numbers which do not decode to a program code are rejected. -/
def HaltingCode (n : Nat) : Prop :=
  (Encodable.decode (α := Code) n).elim False fun c => (eval c 0).Dom

/-- `HaltingCode` is recursively enumerable. -/
theorem haltingCode_re : REPred HaltingCode := by
  exact REPred.iff_decoded_pred.mp (ComputablePred.halting_problem_re 0)

/-- `HaltingCode` is not a computable predicate. -/
theorem haltingCode_not_computable : ¬ComputablePred HaltingCode := by
  exact ComputablePred.iff_decoded_pred.not.mp
    (ComputablePred.halting_problem 0)

/-- Provability in `T` for the closed numeral instances of a fixed unary
arithmetic formula. -/
def InstanceTheoremhood (T : ArithmeticTheory)
    (φ : ArithmeticSemisentence 1) (n : Nat) : Prop :=
  T ⊢ φ/[n]

/-- The representing formula for `HaltingCode` reduces halting exactly to PA
theoremhood. The forward implication is Sigma-1 completeness; the reverse
implication is soundness in the standard natural-number model. -/
theorem haltingCode_iff_pa_provable (n : Nat) :
    HaltingCode n ↔
      InstanceTheoremhood 𝗣𝗔 (codeOfREPred HaltingCode) n := by
  exact re_complete haltingCode_re

/-- A concrete one-parameter family of PA sentences has noncomputable
theoremhood. Consequently no algorithm can decide PA theoremhood. -/
theorem peano_arithmetic_instance_theoremhood_not_computable :
    ¬ComputablePred
      (InstanceTheoremhood 𝗣𝗔 (codeOfREPred HaltingCode)) := by
  intro h
  apply haltingCode_not_computable
  exact h.of_eq fun n => (haltingCode_iff_pa_provable n).symm

/-- Existential presentation: there is a fixed unary arithmetic formula whose
closed numeral instances already form an undecidable fragment of PA
theoremhood. -/
theorem peano_arithmetic_theoremhood_not_decidable :
    ∃ φ : ArithmeticSemisentence 1,
      ¬ComputablePred (InstanceTheoremhood 𝗣𝗔 φ) :=
  ⟨codeOfREPred HaltingCode,
    peano_arithmetic_instance_theoremhood_not_computable⟩

end PAUndecidable
