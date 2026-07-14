import CombinatoryLogic.SKI
import CombinatoryLogic.Iota

/-!
# Compiling SKI into the pure iota calculus

The compiler uses Barker's canonical definitions

* `I = ι ι`,
* `K = ι (ι (ι ι))`, and
* `S = ι (ι (ι (ι ι)))`.

It is homomorphic on application.  Its result type is the pure `Iota.Term`;
only the operational semantics embeds that result into `Iota.Runtime.Term`.
-/

namespace CombinatoryLogic

namespace Iota

open Term

/-- Canonical pure-iota implementation of `I`. -/
def i : Term := iota ⬝ iota

/-- Canonical pure-iota implementation of `K`. -/
def k : Term := iota ⬝ (iota ⬝ i)

/-- Canonical pure-iota implementation of `S`. -/
def s : Term := iota ⬝ k

namespace Runtime

open Term

/-- The embedded canonical iota `I` has the runtime `I` head behavior. -/
theorem i_head (x : Term) : StepsPlus (embed Iota.i ⬝ x) x := by
  apply StepsPlus.trans (StepsPlus.single (.appLeft x (.iota .iota)))
  apply StepsPlus.trans
    (StepsPlus.single (.appLeft x (.appLeft .k (.iota .s))))
  apply StepsPlus.trans
    (StepsPlus.single (.appLeft x (.s .s .k .k)))
  apply StepsPlus.trans
    (StepsPlus.single (.s .k (.k ⬝ .k) x))
  exact StepsPlus.single (.k x (.k ⬝ .k ⬝ x))

/-- `ι I` reduces to `S K`, the intermediate used in the `K` derivation. -/
theorem iota_i_steps_s_k : Steps (.iota ⬝ embed Iota.i) (.s ⬝ .k) := by
  apply Steps.trans (Steps.single (.iota (embed Iota.i)))
  exact (i_head .s).toSteps.appLeft .k

/-- The embedded canonical pure-iota `K` reduces to the runtime `K` atom. -/
theorem k_steps_runtimeK : StepsPlus (embed Iota.k) .k := by
  apply StepsPlus.trans (StepsPlus.single (.iota (.iota ⬝ embed Iota.i)))
  apply StepsPlus.trans
    (Reduction.Plus.transRight
      ((iota_i_steps_s_k.appLeft .s).appLeft .k)
      (StepsPlus.single (.s .k .s .k)))
  exact StepsPlus.single (.k .k (.s ⬝ .k))

/-- The embedded canonical iota `K` has the runtime `K` head behavior. -/
theorem k_head (x y : Term) : StepsPlus (embed Iota.k ⬝ x ⬝ y) x := by
  apply StepsPlus.trans (k_steps_runtimeK.appLeft x |>.appLeft y)
  exact StepsPlus.single (.k x y)

/-- The embedded canonical pure-iota `S` reduces to the runtime `S` atom. -/
theorem s_steps_runtimeS : StepsPlus (embed Iota.s) .s := by
  apply StepsPlus.trans (StepsPlus.single (.iota (embed Iota.k)))
  apply StepsPlus.trans (k_steps_runtimeK.appLeft .s |>.appLeft .k)
  exact StepsPlus.single (.k .s .k)

/-- The embedded canonical iota `S` has the runtime `S` head behavior. -/
theorem s_head (x y z : Term) :
    StepsPlus (embed Iota.s ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z)) := by
  apply StepsPlus.trans (s_steps_runtimeS.appLeft x |>.appLeft y |>.appLeft z)
  exact StepsPlus.single (.s x y z)

end Runtime

end Iota

namespace Compiler

/-- The canonical homomorphic compiler from SKI terms to pure iota terms. -/
def compile : SKI.Term → Iota.Term
  | .s => Iota.s
  | .k => Iota.k
  | .i => Iota.i
  | .app function argument => .app (compile function) (compile argument)

@[simp] theorem compile_s : compile .s = Iota.s := rfl
@[simp] theorem compile_k : compile .k = Iota.k := rfl
@[simp] theorem compile_i : compile .i = Iota.i := rfl
@[simp] theorem compile_app (function argument : SKI.Term) :
    compile (.app function argument) = .app (compile function) (compile argument) := rfl

/-- A compiled term is never the single pure `iota` leaf. -/
theorem compile_ne_iota (term : SKI.Term) : compile term ≠ .iota := by
  cases term <;> simp [compile, Iota.s, Iota.k, Iota.i]

/-- The compiler preserves syntax; it is not merely a semantic quotient map. -/
theorem compile_injective : Function.Injective compile := by
  intro a
  induction a with
  | s =>
      intro b h
      cases b with
      | s => rfl
      | k => simp [compile, Iota.s, Iota.k, Iota.i] at h
      | i => simp [compile, Iota.s, Iota.k, Iota.i] at h
      | app f x =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1.symm).elim
  | k =>
      intro b h
      cases b with
      | s => simp [compile, Iota.s, Iota.k, Iota.i] at h
      | k => rfl
      | i => simp [compile, Iota.k, Iota.i] at h
      | app f x =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1.symm).elim
  | i =>
      intro b h
      cases b with
      | s => simp [compile, Iota.s, Iota.k, Iota.i] at h
      | k => simp [compile, Iota.k, Iota.i] at h
      | i => rfl
      | app f x =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1.symm).elim
  | app f x ihf ihx =>
      intro b h
      cases b with
      | s =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1).elim
      | k =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1).elim
      | i =>
          have parts := Iota.Term.app.inj h
          exact (compile_ne_iota f parts.1).elim
      | app f' x' =>
          have parts := Iota.Term.app.inj h
          have hf : f = f' := ihf parts.1
          have hx : x = x' := ihx parts.2
          cases hf
          cases hx
          rfl

/-- The canonical compiler expands size by at most a factor of nine. -/
theorem compile_size_linear (term : SKI.Term) :
    (compile term).size ≤ 9 * term.size := by
  induction term with
  | s => decide
  | k => decide
  | i => decide
  | app function argument hf hx =>
      calc
        (compile function).size + (compile argument).size + 1 ≤
            (9 * function.size + 9 * argument.size) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hf hx) 1
        _ ≤ (9 * function.size + 9 * argument.size) + 9 :=
          Nat.add_le_add_left (by decide : 1 ≤ 9) _
        _ = 9 * (function.size + argument.size + 1) := by
          simp [Nat.mul_add, Nat.add_assoc]

/-- Runtime form of a compiled pure source term. -/
def compileRuntime (term : SKI.Term) : Iota.Runtime.Term :=
  Iota.Runtime.Term.embed (compile term)

@[simp] theorem compileRuntime_app (function argument : SKI.Term) :
    compileRuntime (.app function argument) =
      .app (compileRuntime function) (compileRuntime argument) := rfl

/-- Every one-step SKI contraction is simulated by at least one runtime step. -/
theorem step_simulation {source target : SKI.Term} (h : source.Step target) :
    Iota.Runtime.Term.StepsPlus (compileRuntime source) (compileRuntime target) := by
  induction h with
  | i x => exact Iota.Runtime.i_head (compileRuntime x)
  | k x y => exact Iota.Runtime.k_head (compileRuntime x) (compileRuntime y)
  | s x y z =>
      exact Iota.Runtime.s_head (compileRuntime x) (compileRuntime y) (compileRuntime z)
  | appLeft argument _ ih => exact ih.appLeft (compileRuntime argument)
  | appRight function _ ih => exact ih.appRight (compileRuntime function)

/-- Reflexive-transitive SKI reduction is preserved by the compiler. -/
theorem steps_simulation {source target : SKI.Term} (h : source.Steps target) :
    Iota.Runtime.Term.Steps (compileRuntime source) (compileRuntime target) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact Reduction.Star.trans ih (step_simulation step).toSteps

/-- Positive SKI reduction remains positive after compilation. -/
theorem stepsPlus_simulation {source target : SKI.Term} (h : source.StepsPlus target) :
    Iota.Runtime.Term.StepsPlus (compileRuntime source) (compileRuntime target) := by
  induction h with
  | single step => exact step_simulation step
  | tail _ step ih => exact ih.trans (step_simulation step)

/--
Generic faithful SKI embedding: the target contains an injective encoding
preserving every finite SKI reduction.  The separate `Universality` module
composes this embedding with the weak-lambda compiler.
-/
structure FaithfulSKIEmbedding (A : Type) (reaches : A → A → Prop) where
  encode : SKI.Term → A
  injective : Function.Injective encode
  simulates : ∀ {source target}, source.Steps target → reaches (encode source) (encode target)

/-- The canonical faithful embedding of SKI into pure iota. -/
def faithful_ski_embedding :
    FaithfulSKIEmbedding Iota.Term Iota.Reaches where
  encode := compile
  injective := compile_injective
  simulates := steps_simulation

/-- The compiled looping term has a genuine nonempty reduction cycle. -/
theorem compiled_omega_cycle :
    Iota.Runtime.Term.StepsPlus
      (compileRuntime SKI.Term.omega) (compileRuntime SKI.Term.omega) :=
  stepsPlus_simulation SKI.Term.omega_cycle

end Compiler

end CombinatoryLogic
