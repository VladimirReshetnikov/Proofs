import CombinatoryLogic.Lambda
import CombinatoryLogic.SK

/-!
# Bracket abstraction from untyped lambda calculus to pure SK

The intermediate `Polynomial n` is an SK expression with `n` variables.
`abstract` is occurs-aware: a body not using variable zero compiles to a single
`K` branch.  This makes abstraction commute strictly with lifted substitutions,
which is the key to beta simulation.
-/

namespace CombinatoryLogic.LambdaToSK

/-- Pure SK polynomials in a context of `n` variables. -/
inductive Polynomial (n : Nat) where
  | var (index : Fin n)
  | s
  | k
  | app (function argument : Polynomial n)
  deriving Repr

namespace Polynomial

infixl:70 " ⬝ " => app

/-- The derived polynomial identity `S K K`. -/
def i : Polynomial n := s ⬝ k ⬝ k

/-- Substitute polynomials for variables. -/
def bind {n m : Nat} (σ : Fin n → Polynomial m) : Polynomial n → Polynomial m
  | .var index => σ index
  | .s => .s
  | .k => .k
  | .app function argument => bind σ function ⬝ bind σ argument

/-- Rename polynomial variables. -/
def rename {n m : Nat} (f : Fin n → Fin m) : Polynomial n → Polynomial m
  | .var index => .var (f index)
  | .s => .s
  | .k => .k
  | .app function argument => rename f function ⬝ rename f argument

/-- Lift a polynomial substitution through variable zero. -/
def liftSubst {n m : Nat} (σ : Fin n → Polynomial m) :
    Fin (n + 1) → Polynomial (m + 1) :=
  Fin.cases (.var 0) (fun index => rename Fin.succ (σ index))

/-- Remove variable zero exactly when it does not occur. -/
def unshift : Polynomial (n + 1) → Option (Polynomial n)
  | .var index => Fin.cases none (some ∘ .var) index
  | .s => some .s
  | .k => some .k
  | .app function argument =>
      match unshift function, unshift argument with
      | some function', some argument' => some (function' ⬝ argument')
      | _, _ => none

/-- Occurs-aware abstraction of variable zero. -/
def abstract : Polynomial (n + 1) → Polynomial n
  | .var index => Fin.cases i (fun j => k ⬝ .var j) index
  | .s => k ⬝ s
  | .k => k ⬝ k
  | .app function argument =>
      match unshift function, unshift argument with
      | some function', some argument' => k ⬝ (function' ⬝ argument')
      | _, _ => s ⬝ abstract function ⬝ abstract argument

/-- Interpret a polynomial by assigning a closed SK term to every variable. -/
def eval (ρ : Fin n → SK.Term) : Polynomial n → SK.Term
  | .var index => ρ index
  | .s => .s
  | .k => .k
  | .app function argument => eval ρ function ⬝ eval ρ argument

@[simp] theorem eval_bind (term : Polynomial n) (σ : Fin n → Polynomial m)
    (ρ : Fin m → SK.Term) :
    eval ρ (bind σ term) = eval (fun index => eval ρ (σ index)) term := by
  induction term with
  | var => rfl
  | s | k => rfl
  | app function argument hf hx => simp [bind, eval, hf, hx]

@[simp] theorem unshift_rename_succ (term : Polynomial n) :
    unshift (rename Fin.succ term) = some term := by
  induction term with
  | var index => rfl
  | s | k => rfl
  | app function argument hf hx => simp [rename, unshift, hf, hx]

theorem rename_eq_bind (term : Polynomial n) (f : Fin n → Fin m) :
    rename f term = bind (.var ∘ f) term := by
  induction term with
  | var => rfl
  | s | k => rfl
  | app function argument hf hx => simp [rename, bind, hf, hx]

theorem abstract_rename_succ (term : Polynomial n) :
    abstract (rename Fin.succ term) = k ⬝ term := by
  induction term with
  | var index => rfl
  | s | k => rfl
  | app function argument hf hx =>
      simp [rename, abstract, unshift_rename_succ]

/-- `unshift` is natural for substitutions lifted through variable zero. -/
theorem unshift_bind_lift (term : Polynomial (n + 1)) (σ : Fin n → Polynomial m) :
    unshift (bind (liftSubst σ) term) = Option.map (bind σ) (unshift term) := by
  induction term with
  | var index =>
      refine Fin.cases ?_ (fun j => ?_) index
      · rfl
      · simp [bind, liftSubst, unshift, unshift_rename_succ]
  | s | k => rfl
  | app function argument hf hx =>
      simp only [bind, unshift]
      rw [hf, hx]
      cases unshift function <;> cases unshift argument <;> rfl

/-- Abstraction commutes strictly with substitution lifted past variable zero. -/
theorem abstract_bind_lift (term : Polynomial (n + 1)) (σ : Fin n → Polynomial m) :
    abstract (bind (liftSubst σ) term) = bind σ (abstract term) := by
  induction term with
  | var index =>
      refine Fin.cases ?_ (fun j => ?_) index
      · rfl
      · simp [abstract, bind, liftSubst, abstract_rename_succ]
  | s | k => rfl
  | app function argument hf hx =>
      simp only [bind, abstract]
      have hfu := unshift_bind_lift function σ
      have hau := unshift_bind_lift argument σ
      cases uf : unshift function <;> cases ua : unshift argument <;>
        simp [uf, ua] at hfu hau ⊢ <;> simp [hfu, hau, hf, hx, bind]

/-- Evaluation after successful `unshift` ignores the variable-zero slot. -/
theorem eval_unshift {term : Polynomial (n + 1)} {lowered : Polynomial n}
    (h : unshift term = some lowered) (ρ : Fin n → SK.Term) (x : SK.Term) :
    eval (Fin.cases x ρ) term = eval ρ lowered := by
  induction term generalizing lowered with
  | var index =>
      refine Fin.cases (motive := fun index =>
          ∀ {lowered : Polynomial n},
            unshift (.var index) = some lowered →
              eval (Fin.cases x ρ) (.var index) = eval ρ lowered)
        ?_ (fun j => ?_) index h
      · intro lowered impossible
        cases impossible
      · intro lowered equality
        cases equality
        rfl
  | s | k => cases h; rfl
  | app function argument hf hx =>
      simp only [unshift] at h
      cases hfu : unshift function <;> cases hau : unshift argument <;> simp [hfu, hau] at h
      cases h
      simp [eval, hf hfu, hx hau]

/-- Bracket abstraction has the expected operational behavior under every valuation. -/
theorem abstract_correct (term : Polynomial (n + 1)) (ρ : Fin n → SK.Term) (x : SK.Term) :
    SK.Term.StepsPlus (eval ρ (abstract term) ⬝ x) (eval (Fin.cases x ρ) term) := by
  induction term with
  | var index =>
      refine Fin.cases ?_ (fun j => ?_) index
      · exact SK.Term.i_head x
      · exact .single (.k (ρ j) x)
  | s => exact .single (.k .s x)
  | k => exact .single (.k .k x)
  | app function argument hf hx =>
      simp only [abstract]
      cases hfu : unshift function with
      | some function' =>
          cases hau : unshift argument with
          | some argument' =>
              have ef := eval_unshift hfu ρ x
              have ea := eval_unshift hau ρ x
              simpa [eval, ef, ea] using
                (SK.Term.StepsPlus.single (.k (eval ρ (function' ⬝ argument')) x))
          | none =>
              apply SK.Term.StepsPlus.trans
                (SK.Term.StepsPlus.single
                  (.s (eval ρ (abstract function)) (eval ρ (abstract argument)) x))
              exact (hf.appLeft (eval ρ (abstract argument) ⬝ x)).trans
                (hx.appRight (eval (Fin.cases x ρ) function))
      | none =>
          apply SK.Term.StepsPlus.trans
            (SK.Term.StepsPlus.single
              (.s (eval ρ (abstract function)) (eval ρ (abstract argument)) x))
          exact (hf.appLeft (eval ρ (abstract argument) ⬝ x)).trans
            (hx.appRight (eval (Fin.cases x ρ) function))

end Polynomial

namespace Compiler

/-- Compile a scoped lambda term into an SK polynomial with the same context. -/
def compile : Lambda.Term n → Polynomial n
  | .var index => .var index
  | .app function argument => .app (compile function) (compile argument)
  | .lam body => Polynomial.abstract (compile body)

theorem compile_rename (term : Lambda.Term n) (f : Fin n → Fin m) :
    compile (term.rename f) = Polynomial.rename f (compile term) := by
  induction term generalizing m with
  | var => rfl
  | app function argument hf hx => simp [compile, Lambda.Term.rename, Polynomial.rename, hf, hx]
  | lam body ih =>
      simp only [compile, Lambda.Term.rename]
      rw [ih]
      rw [Polynomial.rename_eq_bind]
      rw [Polynomial.rename_eq_bind]
      have lifted :
          (Polynomial.var ∘ Fin.cases 0 (Fin.succ ∘ f)) =
            Polynomial.liftSubst (Polynomial.var ∘ f) := by
        funext index
        refine Fin.cases ?_ (fun j => ?_) index <;> rfl
      rw [lifted]
      exact Polynomial.abstract_bind_lift (compile body) (.var ∘ f)

private theorem compile_liftSubst (σ : Fin n → Lambda.Term m) (index : Fin (n + 1)) :
    compile (Lambda.Term.liftSubst σ index) =
      Polynomial.liftSubst (fun j => compile (σ j)) index := by
  refine Fin.cases ?_ (fun j => ?_) index
  · rfl
  · simp [Lambda.Term.liftSubst, Polynomial.liftSubst, compile_rename]

/-- Compilation commutes with simultaneous capture-avoiding substitution. -/
theorem compile_bind (term : Lambda.Term n) (σ : Fin n → Lambda.Term m) :
    compile (term.bind σ) = Polynomial.bind (fun index => compile (σ index)) (compile term) := by
  induction term generalizing m with
  | var => rfl
  | app function argument hf hx => simp [compile, Lambda.Term.bind, Polynomial.bind, hf, hx]
  | lam body ih =>
      simp only [compile, Lambda.Term.bind]
      rw [ih]
      have functions :
          (fun index => compile (Lambda.Term.liftSubst σ index)) =
            Polynomial.liftSubst (fun index => compile (σ index)) := by
        funext index
        exact compile_liftSubst σ index
      rw [functions]
      exact Polynomial.abstract_bind_lift (compile body) (fun index => compile (σ index))

/-- Compilation of top substitution. -/
theorem compile_substTop (argument : Lambda.Term n) (body : Lambda.Term (n + 1)) :
    compile (Lambda.Term.substTop argument body) =
      Polynomial.bind (Fin.cases (compile argument) .var) (compile body) := by
  rw [Lambda.Term.substTop, compile_bind]
  congr 1
  funext index
  refine Fin.cases ?_ (fun j => ?_) index <;> rfl

/-- Interpret an open compiled lambda term under a closed SK valuation. -/
def eval (term : Lambda.Term n) (ρ : Fin n → SK.Term) : SK.Term :=
  Polynomial.eval ρ (compile term)

/-- Every weak beta step is simulated by a nonempty SK reduction. -/
theorem step_simulation {source target : Lambda.Term n} (h : source.Step target)
    (ρ : Fin n → SK.Term) : SK.Term.StepsPlus (eval source ρ) (eval target ρ) := by
  induction h with
  | beta body argument =>
      have habs := Polynomial.abstract_correct (compile body) ρ (eval argument ρ)
      change SK.Term.StepsPlus
        (Polynomial.eval ρ (Polynomial.abstract (compile body)) ⬝ eval argument ρ)
        (Polynomial.eval ρ (compile (Lambda.Term.substTop argument body)))
      rw [compile_substTop, Polynomial.eval_bind]
      have valuations :
          (fun index => Polynomial.eval ρ
            (Fin.cases (compile argument) Polynomial.var index)) =
            Fin.cases (eval argument ρ) ρ := by
        funext index
        refine Fin.cases ?_ (fun j => ?_) index <;> rfl
      rw [valuations]
      simpa [eval, compile, Polynomial.eval] using habs
  | appLeft argument _ ih => exact ih.appLeft (eval argument ρ)
  | appRight function _ ih => exact ih.appRight (eval function ρ)

/-- Every finite weak-beta reduction is simulated by SK. -/
theorem steps_simulation {source target : Lambda.Term n} (h : source.Steps target)
    (ρ : Fin n → SK.Term) : SK.Term.Steps (eval source ρ) (eval target ρ) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact Reduction.Star.trans ih (step_simulation step ρ).toSteps

/-- Every positive weak-beta reduction remains positive in SK. -/
theorem stepsPlus_simulation {source target : Lambda.Term n} (h : source.StepsPlus target)
    (ρ : Fin n → SK.Term) : SK.Term.StepsPlus (eval source ρ) (eval target ρ) := by
  induction h with
  | single step => exact step_simulation step ρ
  | tail _ step ih => exact ih.trans (step_simulation step ρ)

/-- Compile a closed lambda term to pure SK. -/
def compileClosed (term : Lambda.Term 0) : SK.Term := eval term Fin.elim0

/--
An effective, compositional operational compiler from closed weak lambda terms.
The positive-step field prevents reflexivity from serving as a vacuous
"simulation".
-/
structure WeakLambdaSimulation (A : Type) (reachesPlus : A → A → Prop) where
  app : A → A → A
  encode : Lambda.Term 0 → A
  encode_app : ∀ function argument,
    encode (.app function argument) = app (encode function) (encode argument)
  simulatesStep : ∀ {source target}, source.Step target →
    reachesPlus (encode source) (encode target)

/-- The concrete compositional weak-lambda-to-SK compiler. -/
def sk_turing_complete : WeakLambdaSimulation SK.Term SK.Term.StepsPlus where
  app := .app
  encode := compileClosed
  encode_app := fun _ _ => rfl
  simulatesStep := fun h => step_simulation h Fin.elim0

/-- Pure SK simulates every finite weak-beta reduction of a closed lambda term. -/
theorem sk_simulates_weak_lambda {source target : Lambda.Term 0} (h : source.Steps target) :
    SK.Term.Steps (compileClosed source) (compileClosed target) :=
  steps_simulation h Fin.elim0

/-- The compiled lambda omega term has a nonempty SK reduction cycle. -/
theorem compiled_omega_cycle :
    SK.Term.StepsPlus (compileClosed Lambda.Term.omega) (compileClosed Lambda.Term.omega) :=
  stepsPlus_simulation Lambda.Term.omega_cycle Fin.elim0

end Compiler

end CombinatoryLogic.LambdaToSK
