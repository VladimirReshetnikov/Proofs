import Foundation.FirstOrder.Incompleteness.Halting
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# Undecidability of Peano-arithmetic theoremhood

The proof reduces the halting problem to the predicate on Goedel codes which
holds exactly when the code represents a formal PA theorem. It first isolates
a single computably generated family of closed PA sentences whose theoremhood
predicate is the halting problem, then composes that reduction with
Foundation's arithmetized numeral-substitution function.

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
open LO.FirstOrder.Arithmetic.HierarchySymbol

/-- A unary natural-number function with a Sigma-1-definable graph is
computable in mathlib's partial-recursive sense. This bridges Foundation's
arithmetical definability API to mathlib's computability API. -/
theorem computable_of_sigmaOne_definable_function₁
    (f : ℕ → ℕ) [𝚺₁-Function₁ f] : Computable f := by
  have hgraph : 𝚺₁-Relation (Function.Graph f) := inferInstance
  rcases hgraph with ⟨φ, hφ⟩
  have hvec : Computable fun p : ℕ × ℕ ↦
      p.2 ::ᵥ p.1 ::ᵥ (List.Vector.nil : List.Vector ℕ 0) := by
    exact Primrec.to_comp <|
      Primrec.vector_cons.comp Primrec.snd <|
        Primrec.vector_cons.comp Primrec.fst (.const _)
  have hgraphRE : REPred fun p : ℕ × ℕ ↦ p.2 = f p.1 := by
    apply REPred.of_eq ((sigma1_re id φ.sigma_prop).comp hvec)
    intro p
    simpa [List.Vector.cons_get, Matrix.empty_eq, Function.Graph]
      using hφ.df.iff ![p.2, p.1]
  have hnGraphDef : 𝚺₁-Relation fun y x : ℕ ↦ y ≠ f x := by
    definability
  rcases hnGraphDef with ⟨ψ, hψ⟩
  have hnGraphRE : REPred fun p : ℕ × ℕ ↦ p.2 ≠ f p.1 := by
    apply REPred.of_eq ((sigma1_re id ψ.sigma_prop).comp hvec)
    intro p
    simpa [List.Vector.cons_get, Matrix.empty_eq] using hψ.df.iff ![p.2, p.1]
  have hgraphComp : ComputablePred fun p : ℕ × ℕ ↦ p.2 = f p.1 :=
    ComputablePred.computable_iff_re_compl_re.mpr
      ⟨hgraphRE, by simpa using hnGraphRE⟩
  let hex : ∀ x : ℕ, ∃ y, y = f x := fun x ↦ ⟨f x, rfl⟩
  refine (Computable.find hgraphComp hex).of_eq fun x ↦ ?_
  exact Nat.find_spec (hex x)

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

/-- There is a fixed unary arithmetic formula whose closed numeral instances
already form an undecidable fragment of PA theoremhood. -/
theorem exists_undecidable_instance_theoremhood :
    ∃ φ : ArithmeticSemisentence 1,
      ¬ComputablePred (InstanceTheoremhood 𝗣𝗔 φ) :=
  ⟨codeOfREPred HaltingCode,
    peano_arithmetic_instance_theoremhood_not_computable⟩

open LO.FirstOrder.Arithmetic.Bootstrapping

/-- The Goedel code of the closed sentence obtained by substituting the
numeral for `n` into the fixed formula representing the halting problem. -/
noncomputable def HaltingSentenceCode (n : ℕ) : ℕ :=
  Arithmetic.substNumeral (⌜codeOfREPred HaltingCode⌝ : ℕ) n

/-- The map from a program code to the Goedel code of its representing closed
arithmetic sentence is Sigma-1 definable. -/
theorem haltingSentenceCode_sigmaOne : 𝚺₁-Function₁ HaltingSentenceCode := by
  letI : 𝚺₁-Function₂ (Arithmetic.substNumeral : ℕ → ℕ → ℕ) :=
    Arithmetic.substNumeral.defined.to_definable
  unfold HaltingSentenceCode
  exact DefinableFunction₂.comp (DefinableFunction.const _)
    (DefinableFunction.var 0)

/-- The map from program codes to the corresponding closed sentence codes is
computable. -/
theorem haltingSentenceCode_computable : Computable HaltingSentenceCode := by
  letI : 𝚺₁-Function₁ HaltingSentenceCode := haltingSentenceCode_sigmaOne
  exact computable_of_sigmaOne_definable_function₁ HaltingSentenceCode

/-- Numeral substitution on syntax agrees with Foundation's arithmetized
substitution function. -/
theorem haltingSentenceCode_eq_quote (n : ℕ) :
    HaltingSentenceCode n =
      (⌜((codeOfREPred HaltingCode)/[n] : ArithmeticSentence)⌝ : ℕ) := by
  simp [HaltingSentenceCode, Arithmetic.substNumeral, Sentence.quote_def,
    Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]

/-- Syntactic PA theoremhood as a predicate on natural-number Goedel codes.
Codes which are not conclusions of encoded PA derivations are rejected. -/
def EncodedPATheoremhood (e : ℕ) : Prop :=
  Provable 𝗣𝗔 e

/-- Halting many-one reduces to PA theoremhood through the computable map
`HaltingSentenceCode`. -/
theorem haltingCode_iff_encoded_pa_theoremhood (n : ℕ) :
    HaltingCode n ↔ EncodedPATheoremhood (HaltingSentenceCode n) := by
  rw [haltingCode_iff_pa_provable]
  rw [haltingSentenceCode_eq_quote]
  exact provable_iff_provable.symm

/-- There is no total computable decider for the set of Goedel codes of
first-order Peano-arithmetic theorems. -/
theorem peano_arithmetic_theoremhood_not_decidable :
    ¬ComputablePred EncodedPATheoremhood := by
  classical
  intro h
  apply haltingCode_not_computable
  have hc : ComputablePred fun n ↦
      EncodedPATheoremhood (HaltingSentenceCode n) :=
    computablePred_iff_computable_decide.mpr
      (h.decide.comp haltingSentenceCode_computable)
  exact hc.of_eq fun n ↦ (haltingCode_iff_encoded_pa_theoremhood n).symm

end PAUndecidable
