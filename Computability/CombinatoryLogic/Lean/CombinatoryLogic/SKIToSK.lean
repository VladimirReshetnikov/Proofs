import CombinatoryLogic.SKI
import CombinatoryLogic.SK

/-!
# The equivalence of SKI and pure SK

The canonical compiler replaces `I` by `S K K` and preserves application.
It positively simulates every SKI step.  Conversely, the constructor-preserving
SK-to-SKI inclusion is injective and positively simulates every SK step.

The canonical compiler cannot be injective: primitive SKI `I` and the literal
SKI term `S K K` have the same output.  The collision is stated explicitly.
-/

namespace CombinatoryLogic.SKIToSK

/-- Canonical compiler from SKI to pure SK. -/
def compile : SKI.Term → SK.Term
  | .s => .s
  | .k => .k
  | .i => .i
  | .app function argument => .app (compile function) (compile argument)

@[simp] theorem compile_s : compile .s = .s := rfl
@[simp] theorem compile_k : compile .k = .k := rfl
@[simp] theorem compile_i : compile .i = SK.Term.i := rfl
@[simp] theorem compile_app (function argument : SKI.Term) :
    compile (.app function argument) = .app (compile function) (compile argument) := rfl

/-- One SKI step compiles to at least one genuine SK step. -/
theorem step_simulation {source target : SKI.Term} (h : source.Step target) :
    SK.Term.StepsPlus (compile source) (compile target) := by
  induction h with
  | i x => exact SK.Term.i_head (compile x)
  | k x y => exact .single (.k (compile x) (compile y))
  | s x y z => exact .single (.s (compile x) (compile y) (compile z))
  | appLeft argument _ ih => exact ih.appLeft (compile argument)
  | appRight function _ ih => exact ih.appRight (compile function)

/-- Reflexive-transitive SKI reduction is preserved by compilation to SK. -/
theorem steps_simulation {source target : SKI.Term} (h : source.Steps target) :
    SK.Term.Steps (compile source) (compile target) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact Reduction.Star.trans ih (step_simulation step).toSteps

/-- Positive SKI reduction remains positive after compilation to SK. -/
theorem stepsPlus_simulation {source target : SKI.Term} (h : source.StepsPlus target) :
    SK.Term.StepsPlus (compile source) (compile target) := by
  induction h with
  | single step => exact step_simulation step
  | tail _ step ih => exact ih.trans (step_simulation step)

/-- The canonical SKI-to-SK compiler has at most fivefold syntax growth. -/
theorem compile_size_linear (term : SKI.Term) :
    (compile term).size ≤ 5 * term.size := by
  induction term with
  | s => decide
  | k => decide
  | i => decide
  | app function argument hf hx =>
      calc
        (compile function).size + (compile argument).size + 1 ≤
            (5 * function.size + 5 * argument.size) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hf hx) 1
        _ ≤ (5 * function.size + 5 * argument.size) + 5 :=
          Nat.add_le_add_left (by decide : 1 ≤ 5) _
        _ = 5 * (function.size + argument.size + 1) := by
          simp [Nat.mul_add, Nat.add_assoc]

/-- Primitive SKI `I` collides with the literal SKI expression `S K K`. -/
theorem compile_i_collision :
    compile .i = compile (.app (.app .s .k) .k) := rfl

/-- The canonical compiler is not syntactically injective. -/
theorem compile_not_injective : ¬ Function.Injective compile := by
  intro h
  have impossible : SKI.Term.i = .app (.app .s .k) .k := h compile_i_collision
  cases impossible

/--
The positive compositional simulation needed for SK: every SKI contraction
has a pure SK image.  Syntax injection is intentionally absent because it is
irrelevant to program simulation and false for `I ↦ S K K`.
-/
structure CompositionalPositiveSimulation (A : Type) (reachesPlus : A → A → Prop) where
  app : A → A → A
  encode : SKI.Term → A
  encode_app : ∀ function argument,
    encode (.app function argument) = app (encode function) (encode argument)
  simulatesStep : ∀ {source target}, source.Step target →
    reachesPlus (encode source) (encode target)

/-- Pure SK positively and compositionally simulates SKI. -/
def sk_simulates_ski :
    CompositionalPositiveSimulation SK.Term SK.Term.StepsPlus where
  app := .app
  encode := compile
  encode_app := fun _ _ => rfl
  simulatesStep := step_simulation

/-- The compiled SKI omega cycle is a genuine nonempty SK cycle. -/
theorem compiled_omega_cycle :
    SK.Term.StepsPlus (compile SKI.Term.omega) (compile SKI.Term.omega) :=
  stepsPlus_simulation SKI.Term.omega_cycle

/-- Constructor-preserving inclusion of pure SK into SKI. -/
def embed : SK.Term → SKI.Term
  | .s => .s
  | .k => .k
  | .app function argument => .app (embed function) (embed argument)

@[simp] theorem compile_embed (term : SK.Term) : compile (embed term) = term := by
  induction term with
  | s | k => rfl
  | app function argument hf hx => simp [embed, hf, hx]

/-- The SK-to-SKI inclusion is injective. -/
theorem embed_injective : Function.Injective embed := by
  intro a b h
  have := congrArg compile h
  simpa using this

/-- One SK step remains one genuine SKI step under inclusion. -/
theorem embed_step_simulation {source target : SK.Term} (h : source.Step target) :
    SKI.Term.Step (embed source) (embed target) := by
  induction h with
  | k x y => exact .k (embed x) (embed y)
  | s x y z => exact .s (embed x) (embed y) (embed z)
  | appLeft argument _ ih => exact .appLeft (embed argument) ih
  | appRight function _ ih => exact .appRight (embed function) ih

/-- Reflexive-transitive SK reduction is preserved by inclusion into SKI. -/
theorem embed_steps_simulation {source target : SK.Term} (h : source.Steps target) :
    SKI.Term.Steps (embed source) (embed target) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact .tail ih (embed_step_simulation step)

/-- Positive SK reduction is preserved by inclusion into SKI. -/
theorem embed_stepsPlus_simulation {source target : SK.Term} (h : source.StepsPlus target) :
    SKI.Term.StepsPlus (embed source) (embed target) := by
  induction h with
  | single step => exact .single (embed_step_simulation step)
  | tail _ step ih => exact .tail ih (embed_step_simulation step)

/-- Inclusion preserves syntax size exactly. -/
@[simp] theorem embed_size (term : SK.Term) : (embed term).size = term.size := by
  induction term with
  | s | k => rfl
  | app function argument hf hx => simp [embed, SKI.Term.size, SK.Term.size, hf, hx]

end CombinatoryLogic.SKIToSK
