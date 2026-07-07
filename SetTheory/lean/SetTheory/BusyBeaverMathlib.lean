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

/--
Output relation produced by mathlib's `TM2 -> TM1` reduction when the main
stack of the source `TM2` machine contains `mainOutput`.
-/
def TM2to1MainOutput
    (tm1Output : Turing.ListBlank PartrecToTM1Alphabet)
    (mainOutput : List Turing.PartrecToTM2.Γ') : Prop :=
  Exists fun (stk : Turing.PartrecToTM2.K' -> List Turing.PartrecToTM2.Γ') =>
    Exists fun (tape : Turing.ListBlank
      (Turing.PartrecToTM2.K' -> Option Turing.PartrecToTM2.Γ')) =>
      Turing.TM2to1.addBottom tape = tm1Output ∧
      (∀ k : Turing.PartrecToTM2.K',
        Turing.ListBlank.map (Turing.proj k) tape =
          Turing.ListBlank.mk ((stk k).map some).reverse) ∧
      stk Turing.PartrecToTM2.K'.main = mainOutput

/-- Encode a finite `TM1` input list by replacing every source symbol by its Bool block. -/
abbrev TM1to1EncodedInput {Γ : Type*} {width : Nat}
    (enc : Γ -> List.Vector Bool width) (input : List Γ) : List Bool :=
  input.flatMap fun a => (enc a).toList

/--
Output relation for mathlib's finite-alphabet `TM1 -> TM1 Bool` simulation.

`TM1.eval` exposes only the inclusive right half-tape of the final source
configuration.  The Bool simulator encodes the whole final tape, so this
relation keeps the hidden source tape as a witness and relates the two exposed
right half-tapes.
-/
def TM1to1Output {Γ : Type*} [Inhabited Γ] {width : Nat}
    (enc : Γ -> List.Vector Bool width)
    (enc0 : enc default = List.Vector.replicate width false)
    (sourceOutput : Turing.ListBlank Γ) (boolOutput : Turing.ListBlank Bool) : Prop :=
  ∃ tape : Turing.Tape Γ,
    tape.right₀ = sourceOutput ∧
    (Turing.TM1to1.trTape enc0 tape).right₀ = boolOutput

/-- Singleton constant-one code in mathlib's list-valued recursive-code basis. -/
def UnaryZerosOneCode : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.succ.comp Turing.ToPartrec.Code.zero

/--
One body step for `UnaryZerosCode`.

The state is `m :: acc`.  If `m = 0`, it returns `0 :: acc`, so `fix` exits
with `acc`; if `m = k + 1`, it returns `1 :: k :: 0 :: acc`, so `fix`
continues with `k :: 0 :: acc`.
-/
def UnaryZerosStepCode : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.zero'.case
    (Turing.ToPartrec.Code.cons UnaryZerosOneCode
      (Turing.ToPartrec.Code.cons Turing.ToPartrec.Code.head
        (Turing.ToPartrec.Code.comp Turing.ToPartrec.Code.zero' Turing.ToPartrec.Code.tail)))

/-- A list-valued recursive code sending `[m]` to a unary list of `m` zeros. -/
def UnaryZerosCode : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.fix UnaryZerosStepCode

theorem replicate_zero_append_cons (m : Nat) (acc : List Nat) :
    List.replicate m 0 ++ 0 :: acc = 0 :: (List.replicate m 0 ++ acc) := by
  rw [← List.singleton_append, ← List.append_assoc]
  rw [← List.replicate_succ']
  rw [List.replicate_succ]
  rfl

theorem unaryZerosCode_mem (m : Nat) (acc : List Nat) :
    (List.replicate m 0 ++ acc) ∈ UnaryZerosCode.eval (m :: acc) := by
  induction m generalizing acc with
  | zero =>
      rw [UnaryZerosCode, Turing.ToPartrec.Code.fix_eval]
      refine PFun.mem_fix_iff.2 (Or.inl ?_)
      simp [UnaryZerosStepCode]
  | succ m IH =>
      rw [UnaryZerosCode, Turing.ToPartrec.Code.fix_eval]
      refine PFun.mem_fix_iff.2 (Or.inr ?_)
      refine ⟨m :: 0 :: acc, ?_, ?_⟩
      · simp [UnaryZerosStepCode, UnaryZerosOneCode]
      · have hIH := IH (0 :: acc)
        rw [UnaryZerosCode, Turing.ToPartrec.Code.fix_eval] at hIH
        convert hIH using 1
        rw [List.replicate_succ]
        rw [replicate_zero_append_cons m acc]
        simp

/-- `UnaryZerosCode` maps `m :: acc` to `replicate m 0 ++ acc`. -/
theorem unaryZerosCode_eval_cons (m : Nat) (acc : List Nat) :
    UnaryZerosCode.eval (m :: acc) = Part.some (List.replicate m 0 ++ acc) := by
  have hmem := unaryZerosCode_mem m acc
  refine Part.ext fun out => ?_
  constructor
  · intro hout
    exact Part.mem_some_iff.2 (Part.mem_unique hout hmem)
  · intro hout
    have hout' := Part.mem_some_iff.1 hout
    subst out
    exact hmem

/-- `UnaryZerosCode` maps `[m]` to exactly `m` zero entries. -/
theorem unaryZerosCode_eval_single (m : Nat) :
    UnaryZerosCode.eval [m] = Part.some (List.replicate m 0) := by
  simpa using unaryZerosCode_eval_cons m []

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
A mathlib-total-recursive function has a sequential `Turing.ToPartrec.Code`
whose output is unary data: on input `[n]` it returns a list of exactly `f n`
zeros.
-/
theorem totalRecursiveMathlib_has_unary_toPartrec_code {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n, Turing.ToPartrec.Code.eval c [n] =
        Part.some (List.replicate (f n) 0) := by
  rcases totalRecursiveMathlib_has_toPartrec_code hf with ⟨c, hc⟩
  refine ⟨Turing.ToPartrec.Code.comp MathlibBridge.UnaryZerosCode c, ?_⟩
  intro n
  simp [Turing.ToPartrec.Code.comp_eval, hc n,
    MathlibBridge.unaryZerosCode_eval_single]

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

/--
Unary-output variant of `totalRecursiveMathlib_eval_by_tm2`: the evaluator
halts with a list of exactly `f n` zeros.
-/
theorem totalRecursiveMathlib_eval_unary_by_tm2 {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init c [n]) =
            Part.some (Turing.PartrecToTM2.halt (List.replicate (f n) 0)) := by
  rcases totalRecursiveMathlib_has_unary_toPartrec_code hf with ⟨c, hc⟩
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

/-- Initializing `TM2.eval` on the evaluator's main stack gives `PartrecToTM2.init`. -/
theorem partrecToTM2_init_eq_tm2_init (c : Turing.ToPartrec.Code) (v : List Nat) :
    letI : Inhabited Turing.PartrecToTM2.Λ' :=
      ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
    Turing.PartrecToTM2.init c v =
      Turing.TM2.init Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList v) := by
  dsimp [Turing.PartrecToTM2.init, Turing.TM2.init]
  congr
  funext k
  cases k <;> rfl

/--
The mathlib recursive-code evaluator computes `[f n]` in the ordinary `TM2.eval`
interface on its main stack.
-/
theorem totalRecursiveMathlib_tm2_eval_main {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        letI : Inhabited Turing.PartrecToTM2.Λ' :=
          ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
        Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList [n]) =
            Part.some (Turing.PartrecToTM2.trList [f n]) := by
  rcases totalRecursiveMathlib_eval_by_tm2 hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  rw [Turing.TM2.eval, ← partrecToTM2_init_eq_tm2_init c [n], hc n]
  rfl

/--
Unary-output version of `totalRecursiveMathlib_tm2_eval_main`: the recursive
evaluator's main stack contains `trList (replicate (f n) 0)`.
-/
theorem totalRecursiveMathlib_tm2_eval_unary {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        letI : Inhabited Turing.PartrecToTM2.Λ' :=
          ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
        Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList [n]) =
            Part.some (Turing.PartrecToTM2.trList (List.replicate (f n) 0)) := by
  rcases totalRecursiveMathlib_eval_unary_by_tm2 hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  rw [Turing.TM2.eval, ← partrecToTM2_init_eq_tm2_init c [n], hc n]
  rfl

/--
Transport a `TM2.eval` result for the recursive-code evaluator through
mathlib's `TM2 -> TM1` simulation, retaining the decoded main-stack output
relation supplied by `Turing.TM2to1.tr_eval`.
-/
theorem partrecToTM2_eval_main_to_tm1_eval_main
    (c : Turing.ToPartrec.Code) {input output : List Nat}
    (hEval :
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList input) =
          Part.some (Turing.PartrecToTM2.trList output)) :
    letI : Inhabited Turing.PartrecToTM2.Λ' :=
      ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
    ∃ tm1Output,
      tm1Output ∈ Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
        (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList input)) ∧
      MathlibBridge.TM2to1MainOutput tm1Output
        (Turing.PartrecToTM2.trList output) := by
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  have hEval' :
      Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList input) =
          Part.some (Turing.PartrecToTM2.trList output) := hEval
  have hDomTM2 :
      (Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList input)).Dom := by
    rw [hEval']
    simp
  have hDomTM1 :
      (Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
        (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList input))).Dom :=
    (Turing.TM2to1.tr_eval_dom Turing.PartrecToTM2.tr
      Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList input)).2 hDomTM2
  let tm1Output :=
    (Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
      (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList input))).get hDomTM1
  have hTM1Mem :
      tm1Output ∈ Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
        (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList input)) :=
    Part.get_mem hDomTM1
  have hTM2Mem :
      Turing.PartrecToTM2.trList output ∈
        Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList input) := by
    rw [hEval']
    simp
  rcases Turing.TM2to1.tr_eval Turing.PartrecToTM2.tr
      Turing.PartrecToTM2.K'.main (Turing.PartrecToTM2.trList input)
      hTM1Mem hTM2Mem with ⟨stk, tape, hAddBottom, hStacks, hMain⟩
  exact ⟨tm1Output, hTM1Mem, stk, tape, hAddBottom, hStacks, hMain⟩

/--
For every mathlib-total-recursive function, the lowered `TM1` evaluator has an
output whose multiplexed main stack contains the encoded value `[f n]`.
-/
theorem totalRecursiveMathlib_tm1_eval_main {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        letI : Inhabited Turing.PartrecToTM2.Λ' :=
          ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
        ∃ tm1Output,
          tm1Output ∈ Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
            (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
              (Turing.PartrecToTM2.trList [n])) ∧
          MathlibBridge.TM2to1MainOutput tm1Output
            (Turing.PartrecToTM2.trList [f n]) := by
  rcases totalRecursiveMathlib_tm2_eval_main hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  exact partrecToTM2_eval_main_to_tm1_eval_main c (hc n)

/--
Unary-output version of `totalRecursiveMathlib_tm1_eval_main`: after the
`TM2 -> TM1` simulation, the decoded main stack contains `f n` zero entries.
-/
theorem totalRecursiveMathlib_tm1_eval_unary {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n,
        letI : Inhabited Turing.PartrecToTM2.Λ' :=
          ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
        ∃ tm1Output,
          tm1Output ∈ Turing.TM1.eval MathlibBridge.PartrecToTM1Machine
            (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
              (Turing.PartrecToTM2.trList [n])) ∧
          MathlibBridge.TM2to1MainOutput tm1Output
            (Turing.PartrecToTM2.trList (List.replicate (f n) 0)) := by
  rcases totalRecursiveMathlib_tm2_eval_unary hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n
  exact partrecToTM2_eval_main_to_tm1_eval_main c (hc n)

/-- The Bool-block encoding of a finite `TM1` input is the translated initial configuration. -/
theorem tm1to1_trCfg_init
    {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    {width : Nat} (enc : Γ -> List.Vector Bool width)
    (enc0 : enc default = List.Vector.replicate width false)
    (input : List Γ) :
    Turing.TM1to1.trCfg enc enc0
        (Turing.TM1.init (Γ := Γ) (Λ := Λ) (σ := σ) input) =
      Turing.TM1.init (Γ := Bool) (Λ := Turing.TM1to1.Λ' Γ Λ σ) (σ := σ)
        (MathlibBridge.TM1to1EncodedInput enc input) := by
  simp [Turing.TM1to1.trCfg, Turing.TM1.init, MathlibBridge.TM1to1EncodedInput,
    Turing.TM1to1.trTape, Turing.TM1to1.trTape', Turing.Tape.mk₁, Turing.Tape.mk₂, default]

/--
Transport a `TM1.eval` result through mathlib's finite-alphabet
`TM1 -> TM1 Bool` simulation, keeping the relation between the decoded source
output and the encoded Bool output.
-/
theorem tm1_eval_to_bool_tm1_eval
    {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
    {width : Nat} (enc : Γ -> List.Vector Bool width)
    (dec : List.Vector Bool width -> Γ)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a)
    (M : Λ -> Turing.TM1.Stmt Γ Λ σ)
    {input : List Γ} {sourceOutput : Turing.ListBlank Γ}
    (h : sourceOutput ∈ Turing.TM1.eval M input) :
    ∃ boolOutput,
      boolOutput ∈ Turing.TM1.eval (Turing.TM1to1.tr enc dec M)
        (MathlibBridge.TM1to1EncodedInput enc input) ∧
      MathlibBridge.TM1to1Output enc enc0 sourceOutput boolOutput := by
  rw [Turing.TM1.eval] at h
  rcases (Part.mem_map_iff
      (fun c : Turing.TM1.Cfg Γ Λ σ => c.Tape.right₀)).1 h with
    ⟨sourceCfg, hSourceCfg, hSourceOutput⟩
  have hInit :
      Turing.TM1to1.trCfg enc enc0
          (Turing.TM1.init (Γ := Γ) (Λ := Λ) (σ := σ) input) =
        Turing.TM1.init (Γ := Bool) (Λ := Turing.TM1to1.Λ' Γ Λ σ) (σ := σ)
          (MathlibBridge.TM1to1EncodedInput enc input) :=
    tm1to1_trCfg_init enc enc0 input
  rcases StateTransition.tr_eval
      (Turing.TM1to1.tr_respects (enc := enc) dec M encdec)
      hInit hSourceCfg with ⟨boolCfg, hRel, hBoolCfg⟩
  refine ⟨boolCfg.Tape.right₀, ?_, ?_⟩
  · rw [Turing.TM1.eval]
    exact (Part.mem_map_iff
      (fun c : Turing.TM1.Cfg Bool (Turing.TM1to1.Λ' Γ Λ σ) σ =>
        c.Tape.right₀)).2 ⟨boolCfg, hBoolCfg, rfl⟩
  · subst boolCfg
    exact ⟨sourceCfg.Tape, hSourceOutput, rfl⟩

/--
For every mathlib-total-recursive function, the recursive-code evaluator
descends through the finite-alphabet `TM1 -> TM1 Bool` simulation while
retaining the encoded `[f n]` main-stack output witness.
-/
theorem totalRecursiveMathlib_bool_tm1_eval_main {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ (c : Turing.ToPartrec.Code)
      (width : Nat)
      (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
      (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet),
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      ∃ (enc0 : enc default = List.Vector.replicate width false),
        (∀ a, dec (enc a) = a) ∧
        ∀ n,
          ∃ boolOutput,
            boolOutput ∈ Turing.TM1.eval
              (Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine)
              (MathlibBridge.TM1to1EncodedInput enc
                (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
                  (Turing.PartrecToTM2.trList [n]))) ∧
            ∃ tm1Output,
              MathlibBridge.TM2to1MainOutput tm1Output
                (Turing.PartrecToTM2.trList [f n]) ∧
              MathlibBridge.TM1to1Output enc enc0 tm1Output boolOutput := by
  classical
  rcases totalRecursiveMathlib_tm1_eval_main hf with ⟨c, hc⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  rcases Turing.TM1to1.exists_enc_dec
      (Γ := MathlibBridge.PartrecToTM1Alphabet) with
    ⟨width, enc, dec, enc0, encdec⟩
  refine ⟨c, width, enc, dec, enc0, encdec, ?_⟩
  intro n
  rcases hc n with ⟨tm1Output, hTM1Output, hMain⟩
  rcases tm1_eval_to_bool_tm1_eval enc dec enc0 encdec
      MathlibBridge.PartrecToTM1Machine hTM1Output with
    ⟨boolOutput, hBoolOutput, hBoolRel⟩
  exact ⟨boolOutput, hBoolOutput, tm1Output, hMain, hBoolRel⟩

/--
The same lowered evaluator, viewed as a Bool `TM0` by mathlib's `TM1 -> TM0`
simulation.  At this stage the final tape is still the Bool-block encoding of
the recursive evaluator's data, not yet the unary score tape needed for Rado's
busy-beaver game.
-/
theorem totalRecursiveMathlib_bool_tm0_eval_main {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ (c : Turing.ToPartrec.Code)
      (width : Nat)
      (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
      (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet),
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
      ∃ (enc0 : enc default = List.Vector.replicate width false),
        (∀ a, dec (enc a) = a) ∧
        ∀ n,
          ∃ boolOutput,
            boolOutput ∈ Turing.TM0.eval (Turing.TM1to0.tr tm1Bool)
              (MathlibBridge.TM1to1EncodedInput enc
                (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
                  (Turing.PartrecToTM2.trList [n]))) ∧
            ∃ tm1Output,
              MathlibBridge.TM2to1MainOutput tm1Output
                (Turing.PartrecToTM2.trList [f n]) ∧
              MathlibBridge.TM1to1Output enc enc0 tm1Output boolOutput := by
  rcases totalRecursiveMathlib_bool_tm1_eval_main hf with
    ⟨c, width, enc, dec, hEnc⟩
  refine ⟨c, width, enc, dec, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hEnc ⊢
  rcases hEnc with ⟨enc0, encdec, hEval⟩
  refine ⟨enc0, encdec, ?_⟩
  intro n
  rcases hEval n with ⟨boolOutput, hBoolTM1, hOutput⟩
  refine ⟨boolOutput, ?_, hOutput⟩
  rw [Turing.TM1to0.tr_eval]
  exact hBoolTM1

/--
Unary-output version of `totalRecursiveMathlib_bool_tm1_eval_main`.
-/
theorem totalRecursiveMathlib_bool_tm1_eval_unary {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ (c : Turing.ToPartrec.Code)
      (width : Nat)
      (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
      (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet),
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      ∃ (enc0 : enc default = List.Vector.replicate width false),
        (∀ a, dec (enc a) = a) ∧
        ∀ n,
          ∃ boolOutput,
            boolOutput ∈ Turing.TM1.eval
              (Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine)
              (MathlibBridge.TM1to1EncodedInput enc
                (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
                  (Turing.PartrecToTM2.trList [n]))) ∧
            ∃ tm1Output,
              MathlibBridge.TM2to1MainOutput tm1Output
                (Turing.PartrecToTM2.trList (List.replicate (f n) 0)) ∧
              MathlibBridge.TM1to1Output enc enc0 tm1Output boolOutput := by
  classical
  rcases totalRecursiveMathlib_tm1_eval_unary hf with ⟨c, hc⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  rcases Turing.TM1to1.exists_enc_dec
      (Γ := MathlibBridge.PartrecToTM1Alphabet) with
    ⟨width, enc, dec, enc0, encdec⟩
  refine ⟨c, width, enc, dec, enc0, encdec, ?_⟩
  intro n
  rcases hc n with ⟨tm1Output, hTM1Output, hMain⟩
  rcases tm1_eval_to_bool_tm1_eval enc dec enc0 encdec
      MathlibBridge.PartrecToTM1Machine hTM1Output with
    ⟨boolOutput, hBoolOutput, hBoolRel⟩
  exact ⟨boolOutput, hBoolOutput, tm1Output, hMain, hBoolRel⟩

/--
Unary-output version of `totalRecursiveMathlib_bool_tm0_eval_main`.
-/
theorem totalRecursiveMathlib_bool_tm0_eval_unary {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f) :
    ∃ (c : Turing.ToPartrec.Code)
      (width : Nat)
      (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
      (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet),
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
      ∃ (enc0 : enc default = List.Vector.replicate width false),
        (∀ a, dec (enc a) = a) ∧
        ∀ n,
          ∃ boolOutput,
            boolOutput ∈ Turing.TM0.eval (Turing.TM1to0.tr tm1Bool)
              (MathlibBridge.TM1to1EncodedInput enc
                (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
                  (Turing.PartrecToTM2.trList [n]))) ∧
            ∃ tm1Output,
              MathlibBridge.TM2to1MainOutput tm1Output
                (Turing.PartrecToTM2.trList (List.replicate (f n) 0)) ∧
              MathlibBridge.TM1to1Output enc enc0 tm1Output boolOutput := by
  rcases totalRecursiveMathlib_bool_tm1_eval_unary hf with
    ⟨c, width, enc, dec, hEnc⟩
  refine ⟨c, width, enc, dec, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hEnc ⊢
  rcases hEnc with ⟨enc0, encdec, hEval⟩
  refine ⟨enc0, encdec, ?_⟩
  intro n
  rcases hEval n with ⟨boolOutput, hBoolTM1, hOutput⟩
  refine ⟨boolOutput, ?_, hOutput⟩
  rw [Turing.TM1to0.tr_eval]
  exact hBoolTM1

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
