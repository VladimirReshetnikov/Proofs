import SetTheory.BusyBeaver
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
  Mathlib-facing recursive-function bridge for `SetTheory.BusyBeaver`.

  The standalone `SetTheory.BusyBeaver` module keeps the Rado-machine argument
  independent of mathlib.  This module records the honest mathlib connection:
  mathlib's `Computable` predicate on `Nat -> Nat` is the total-recursive
  predicate, every such function has a sequential `ToPartrec.Code`, and
  mathlib proves that this code is evaluated by a finite-support `TM2` machine.

  The remaining, deliberately separate bridge is the low-level compiler from a
  supported mathlib Turing machine with input to the blank-tape two-symbol Rado
  model with state-count accounting.
-/

namespace SetTheory
namespace BusyBeaver

namespace MathlibBridge

/-- `PartrecToTM2.K'` has exactly the four stack indices used by the evaluator. -/
instance instFintypePartrecToTM2K : Fintype Turing.PartrecToTM2.K' where
  elems := { Turing.PartrecToTM2.K'.main, Turing.PartrecToTM2.K'.rev,
    Turing.PartrecToTM2.K'.aux, Turing.PartrecToTM2.K'.stack }
  complete k := by
    cases k <;> simp

/-- The finite alphabet used after the `TM2 -> TM1` reduction of `PartrecToTM2.tr`. -/
abbrev PartrecToTM1Alphabet :=
  Turing.TM2to1.Γ' Turing.PartrecToTM2.K' (fun _ => Turing.PartrecToTM2.Γ')

/-- The `TM1` machine obtained by lowering mathlib's recursive-code evaluator. -/
abbrev PartrecToTM1Machine :=
  Turing.TM2to1.tr Turing.PartrecToTM2.tr

end MathlibBridge

/--
Mathlib's predicate for total recursive functions `Nat -> Nat`.

In mathlib this is named `Computable`: a total function is computable precisely
when the corresponding partial function is partial recursive.
-/
abbrev TotalRecursiveMathlib (f : Nat -> Nat) : Prop :=
  Computable f

/-- A mathlib-total-recursive function is partial recursive as a total partial function. -/
theorem totalRecursiveMathlib_natPartrec {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    Nat.Partrec (fun n => Part.some (f n)) := by
  change Nat.Partrec (f : Nat →. Nat)
  exact (Partrec.nat_iff (f := (f : Nat →. Nat))).mp
    (by simpa [TotalRecursiveMathlib, Computable] using hf)

/-- A mathlib-total-recursive function has a `Nat.Partrec.Code` computing it. -/
theorem totalRecursiveMathlib_has_natPartrec_code {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Nat.Partrec.Code, ∀ n, Nat.Partrec.Code.eval c n = Part.some (f n) := by
  rcases Nat.Partrec.Code.exists_code.mp (totalRecursiveMathlib_natPartrec hf) with ⟨c, hc⟩
  exact ⟨c, fun n => congrFun hc n⟩

/--
A mathlib-total-recursive function has a sequential `Turing.ToPartrec.Code`
whose list-valued semantics maps the singleton input `[n]` to `[f n]`.
-/
theorem totalRecursiveMathlib_has_toPartrec_code {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n, Turing.ToPartrec.Code.eval c [n] = Part.some [f n] := by
  have hPart : Partrec (f : Nat →. Nat) := by
    simpa [TotalRecursiveMathlib, Computable] using hf
  have hBasis :
      @Nat.Partrec' 1 (fun v : List.Vector Nat 1 => (f v.head : Part Nat)) :=
    Nat.Partrec'.part_iff₁.mpr hPart
  rcases Turing.ToPartrec.Code.exists_code hBasis with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  have hc' := hc ⟨[n], rfl⟩
  change Turing.ToPartrec.Code.eval c [n] = Part.some [f n] at hc'
  exact hc'

/--
Mathlib proves that the `PartrecToTM2` Turing machine evaluates the
`ToPartrec.Code` for a total recursive function.
-/
theorem totalRecursiveMathlib_eval_by_tm2 {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init c [n]) =
            Part.some (Turing.PartrecToTM2.halt [f n]) := by
  rcases totalRecursiveMathlib_has_toPartrec_code hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  rw [Turing.PartrecToTM2.tr_eval c [n], hc n]
  rfl

/-- The generated `PartrecToTM2` evaluator is supported by a finite set of labels. -/
theorem partrecToTM2_supports (c : Turing.ToPartrec.Code) :
    @Turing.TM2.Supports _ _ _ _
      ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      Turing.PartrecToTM2.tr
      (Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt) :=
  Turing.PartrecToTM2.tr_supports c Turing.PartrecToTM2.Cont'.halt

/--
Bundled form of the mathlib recursive-function-to-`TM2` bridge: a total
recursive function has a code evaluated by `PartrecToTM2`, and that evaluator is
finite-support.
-/
theorem totalRecursiveMathlib_eval_by_supported_tm2 {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      (∀ n,
        StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init c [n]) =
            Part.some (Turing.PartrecToTM2.halt [f n])) ∧
      @Turing.TM2.Supports _ _ _ _
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
        Turing.PartrecToTM2.tr
        (Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt) := by
  rcases totalRecursiveMathlib_eval_by_tm2 hf with ⟨c, hc⟩
  exact ⟨c, hc, partrecToTM2_supports c⟩

/--
The finite-support recursive-code evaluator also descends through mathlib's
proved `TM2 -> TM1`, finite-alphabet `TM1 -> TM1 Bool`, and `TM1 -> TM0`
reductions to a finite-support Bool `TM0` machine.

This theorem is intentionally support-only: it records the finite-machine
lowering needed for the later Rado compiler, while the exact output/tape
normalization bridge remains separate.
-/
theorem partrecToTM2_descends_to_supported_bool_tm0 (c : Turing.ToPartrec.Code) :
    ∃ (width : Nat)
      (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
      (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet),
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
      let tm0Bool := Turing.TM1to0.tr tm1Bool
      let suppTM2 :=
        Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt
      let suppTM1 :=
        Turing.TM2to1.trSupp Turing.PartrecToTM2.tr suppTM2
      let suppTM1Bool :=
        Turing.TM1to1.trSupp MathlibBridge.PartrecToTM1Machine suppTM1
      Turing.TM0.Supports tm0Bool
        (Turing.TM1to0.trStmts tm1Bool suppTM1Bool : Set _) := by
  classical
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  rcases Turing.TM1to1.exists_enc_dec
      (Γ := MathlibBridge.PartrecToTM1Alphabet) with
    ⟨width, enc, dec, _henc0, _hdec⟩
  refine ⟨width, enc, dec, ?_⟩
  dsimp
  exact Turing.TM1to0.tr_supports
    (Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine)
    (Turing.TM1to1.tr_supports enc dec MathlibBridge.PartrecToTM1Machine
      (Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr (partrecToTM2_supports c)))

end BusyBeaver
end SetTheory
