import CombinatoryLogic.Iota
import CombinatoryLogic.Lambda

/-!
# A faithful operational embedding of pure iota into closed lambda terms

The auxiliary iota runtime is interpreted by the standard closed lambda
encodings

* `K = λx. λy. x`,
* `S = λx. λy. λz. x z (y z)`, and
* `ι = λx. x S K`.

Application is preserved literally.  Every runtime contraction, including a
contraction in either application context, is simulated by one or more weak
beta steps.  Restricting the interpretation along the pure-source inclusion
gives an injective encoding of pure iota terms and preserves both finite and
positive reduction.
-/

namespace CombinatoryLogic.IotaToLambda

namespace Closed

/-- The closed `K` combinator, usable in any ambient variable context. -/
def kAt (n : Nat) : Lambda.Term n :=
  .lam (.lam (.var (Fin.succ 0)))

/-- The closed `S` combinator, usable in any ambient variable context. -/
def sAt (n : Nat) : Lambda.Term n :=
  .lam (.lam (.lam
    (.app
      (.app (.var (Fin.succ (Fin.succ 0))) (.var 0))
      (.app (.var (Fin.succ 0)) (.var 0)))))

/-- Universal iota, `λx. x S K`, usable in any ambient variable context. -/
def iotaAt (n : Nat) : Lambda.Term n :=
  .lam (.app (.app (.var 0) (sAt (n + 1))) (kAt (n + 1)))

/-- The canonical closed lambda encoding of `K`. -/
abbrev k : Lambda.Term 0 := kAt 0

/-- The canonical closed lambda encoding of `S`. -/
abbrev s : Lambda.Term 0 := sAt 0

/-- The canonical closed lambda encoding `ι = λx. x S K`. -/
abbrev iota : Lambda.Term 0 := iotaAt 0

@[simp] theorem bind_kAt (σ : Fin n → Lambda.Term m) :
    (kAt n).bind σ = kAt m := by
  rfl

@[simp] theorem bind_sAt (σ : Fin n → Lambda.Term m) :
    (sAt n).bind σ = sAt m := by
  rfl

@[simp] theorem bind_iotaAt (σ : Fin n → Lambda.Term m) :
    (iotaAt n).bind σ = iotaAt m := by
  rfl

@[simp] theorem rename_kAt (f : Fin n → Fin m) :
    (kAt n).rename f = kAt m := by
  rfl

@[simp] theorem rename_sAt (f : Fin n → Fin m) :
    (sAt n).rename f = sAt m := by
  rfl

@[simp] theorem rename_iotaAt (f : Fin n → Fin m) :
    (iotaAt n).rename f = iotaAt m := by
  rfl

end Closed

/--
Interpret a runtime term as a closed lambda term placed in an arbitrary ambient
context. The ambient-context parameter makes closedness stable under the
substitutions performed by the head-reduction proofs.
-/
def encodeRuntimeAt (n : Nat) : Iota.Runtime.Term → Lambda.Term n
  | .iota => Closed.iotaAt n
  | .s => Closed.sAt n
  | .k => Closed.kAt n
  | .app function argument =>
      .app (encodeRuntimeAt n function) (encodeRuntimeAt n argument)

@[simp] theorem encodeRuntimeAt_iota :
    encodeRuntimeAt n .iota = Closed.iotaAt n := rfl

@[simp] theorem encodeRuntimeAt_s :
    encodeRuntimeAt n .s = Closed.sAt n := rfl

@[simp] theorem encodeRuntimeAt_k :
    encodeRuntimeAt n .k = Closed.kAt n := rfl

@[simp] theorem encodeRuntimeAt_app (function argument : Iota.Runtime.Term) :
    encodeRuntimeAt n (.app function argument) =
      .app (encodeRuntimeAt n function) (encodeRuntimeAt n argument) := rfl

/-- Runtime encodings contain no free variables. -/
@[simp] theorem rename_encodeRuntimeAt (term : Iota.Runtime.Term)
    (f : Fin n → Fin m) :
    (encodeRuntimeAt n term).rename f = encodeRuntimeAt m term := by
  induction term with
  | iota => exact Closed.rename_iotaAt f
  | s => exact Closed.rename_sAt f
  | k => exact Closed.rename_kAt f
  | app function argument hf hx =>
      simp [encodeRuntimeAt, Lambda.Term.rename, hf, hx]

/-- Substitution cannot affect a runtime encoding because it is closed. -/
@[simp] theorem bind_encodeRuntimeAt (term : Iota.Runtime.Term)
    (σ : Fin n → Lambda.Term m) :
    (encodeRuntimeAt n term).bind σ = encodeRuntimeAt m term := by
  induction term with
  | iota => exact Closed.bind_iotaAt σ
  | s => exact Closed.bind_sAt σ
  | k => exact Closed.bind_kAt σ
  | app function argument hf hx =>
      simp [encodeRuntimeAt, Lambda.Term.bind, hf, hx]

/-- Interpret every auxiliary runtime term as a closed lambda term. -/
def encodeRuntime (term : Iota.Runtime.Term) : Lambda.Term 0 :=
  encodeRuntimeAt 0 term

@[simp] theorem encodeRuntime_iota : encodeRuntime .iota = Closed.iota := rfl
@[simp] theorem encodeRuntime_s : encodeRuntime .s = Closed.s := rfl
@[simp] theorem encodeRuntime_k : encodeRuntime .k = Closed.k := rfl

/-- Runtime application is preserved exactly, not merely up to reduction. -/
@[simp] theorem encodeRuntime_app (function argument : Iota.Runtime.Term) :
    encodeRuntime (.app function argument) =
      .app (encodeRuntime function) (encodeRuntime argument) := rfl

/-- Intermediate closed term after the first beta step of a runtime `K` head. -/
def kAfterOne (x : Iota.Runtime.Term) : Lambda.Term 0 :=
  .lam (encodeRuntimeAt 1 x)

/-- Intermediate closed term after the first beta step of a runtime `S` head. -/
def sAfterOne (x : Iota.Runtime.Term) : Lambda.Term 0 :=
  .lam (.lam
    (.app
      (.app (encodeRuntimeAt 2 x) (.var 0))
      (.app (.var (Fin.succ 0)) (.var 0))))

/-- Intermediate closed term after the second beta step of a runtime `S` head. -/
def sAfterTwo (x y : Iota.Runtime.Term) : Lambda.Term 0 :=
  .lam
    (.app
      (.app (encodeRuntimeAt 1 x) (.var 0))
      (.app (encodeRuntimeAt 1 y) (.var 0)))

/-- The defining iota contraction is one weak beta step. -/
theorem iota_head_step (x : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app Closed.iota (encodeRuntime x))
      (.app (.app (encodeRuntime x) Closed.s) Closed.k) := by
  simpa [Closed.iota, Closed.iotaAt, Closed.s, Closed.k,
    encodeRuntime, Lambda.Term.substTop, Lambda.Term.bind] using
    (Lambda.Term.Step.beta
      (.app (.app (.var 0) (Closed.sAt 1)) (Closed.kAt 1))
      (encodeRuntime x))

/-- The first of the two beta steps implementing runtime `K`. -/
theorem k_head_first (x : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app Closed.k (encodeRuntime x))
      (kAfterOne x) := by
  simpa [Closed.k, Closed.kAt, kAfterOne, encodeRuntime,
    Lambda.Term.substTop, Lambda.Term.bind] using
    (Lambda.Term.Step.beta (.lam (.var (Fin.succ 0))) (encodeRuntime x))

/-- The second of the two beta steps implementing runtime `K`. -/
theorem k_head_second (x y : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app (kAfterOne x) (encodeRuntime y))
      (encodeRuntime x) := by
  simpa [kAfterOne, encodeRuntime, Lambda.Term.substTop] using
    (Lambda.Term.Step.beta (encodeRuntimeAt 1 x) (encodeRuntime y))

/-- The first of the three beta steps implementing runtime `S`. -/
theorem s_head_first (x : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app Closed.s (encodeRuntime x))
      (sAfterOne x) := by
  simpa [Closed.s, Closed.sAt, sAfterOne, encodeRuntime,
    Lambda.Term.substTop, Lambda.Term.bind, Lambda.Term.rename] using
    (Lambda.Term.Step.beta
      (.lam (.lam
        (.app
          (.app (.var (Fin.succ (Fin.succ 0))) (.var 0))
          (.app (.var (Fin.succ 0)) (.var 0)))))
      (encodeRuntime x))

/-- The second of the three beta steps implementing runtime `S`. -/
theorem s_head_second (x y : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app (sAfterOne x) (encodeRuntime y))
      (sAfterTwo x y) := by
  simpa [sAfterOne, sAfterTwo, encodeRuntime,
    Lambda.Term.substTop, Lambda.Term.bind] using
    (Lambda.Term.Step.beta
      (.lam
        (.app
          (.app (encodeRuntimeAt 2 x) (.var 0))
          (.app (.var (Fin.succ 0)) (.var 0))))
      (encodeRuntime y))

/-- The third of the three beta steps implementing runtime `S`. -/
theorem s_head_third (x y z : Iota.Runtime.Term) :
    Lambda.Term.Step
      (.app (sAfterTwo x y) (encodeRuntime z))
      (.app
        (.app (encodeRuntime x) (encodeRuntime z))
        (.app (encodeRuntime y) (encodeRuntime z))) := by
  simpa [sAfterTwo, encodeRuntime,
    Lambda.Term.substTop, Lambda.Term.bind] using
    (Lambda.Term.Step.beta
      (.app
        (.app (encodeRuntimeAt 1 x) (.var 0))
        (.app (encodeRuntimeAt 1 y) (.var 0)))
      (encodeRuntime z))

/-- The runtime iota head rule is simulated positively (in exactly one step). -/
theorem iota_head (x : Iota.Runtime.Term) :
    Lambda.Term.StepsPlus
      (.app Closed.iota (encodeRuntime x))
      (.app (.app (encodeRuntime x) Closed.s) Closed.k) :=
  .single (iota_head_step x)

/-- The runtime `K` head rule is simulated positively (in exactly two steps). -/
theorem k_head (x y : Iota.Runtime.Term) :
    Lambda.Term.StepsPlus
      (.app (.app Closed.k (encodeRuntime x)) (encodeRuntime y))
      (encodeRuntime x) :=
  .tail (.single (.appLeft (encodeRuntime y) (k_head_first x)))
    (k_head_second x y)

/-- The runtime `S` head rule is simulated positively (in exactly three steps). -/
theorem s_head (x y z : Iota.Runtime.Term) :
    Lambda.Term.StepsPlus
      (.app
        (.app (.app Closed.s (encodeRuntime x)) (encodeRuntime y))
        (encodeRuntime z))
      (.app
        (.app (encodeRuntime x) (encodeRuntime z))
        (.app (encodeRuntime y) (encodeRuntime z))) :=
  .tail
    (.tail
      (.single
        (.appLeft (encodeRuntime z)
          (.appLeft (encodeRuntime y) (s_head_first x))))
      (.appLeft (encodeRuntime z) (s_head_second x y)))
    (s_head_third x y z)

/-- Lift a positive weak-beta trace through a left application context. -/
theorem stepsPlus_appLeft {source target : Lambda.Term 0}
    (argument : Lambda.Term 0) (h : Lambda.Term.StepsPlus source target) :
    Lambda.Term.StepsPlus
      (.app source argument) (.app target argument) := by
  induction h with
  | single step => exact .single (.appLeft argument step)
  | tail _ step ih => exact .tail ih (.appLeft argument step)

/-- Lift a positive weak-beta trace through a right application context. -/
theorem stepsPlus_appRight (function : Lambda.Term 0)
    {source target : Lambda.Term 0} (h : Lambda.Term.StepsPlus source target) :
    Lambda.Term.StepsPlus
      (.app function source) (.app function target) := by
  induction h with
  | single step => exact .single (.appRight function step)
  | tail _ step ih => exact .tail ih (.appRight function step)

/-- Every contextual runtime step is simulated by a nonempty weak-beta trace. -/
theorem runtime_step_simulation {source target : Iota.Runtime.Term}
    (h : source.Step target) :
    Lambda.Term.StepsPlus (encodeRuntime source) (encodeRuntime target) := by
  induction h with
  | iota x => exact iota_head x
  | k x y => exact k_head x y
  | s x y z => exact s_head x y z
  | appLeft argument _ ih =>
      exact stepsPlus_appLeft (encodeRuntime argument) ih
  | appRight function _ ih =>
      exact stepsPlus_appRight (encodeRuntime function) ih

/-- Every finite runtime reduction is preserved by the lambda encoding. -/
theorem runtime_steps_simulation {source target : Iota.Runtime.Term}
    (h : source.Steps target) :
    Lambda.Term.Steps (encodeRuntime source) (encodeRuntime target) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih =>
      exact Reduction.Star.trans ih (runtime_step_simulation step).toSteps

/-- Every positive runtime reduction remains positive after lambda encoding. -/
theorem runtime_stepsPlus_simulation {source target : Iota.Runtime.Term}
    (h : source.StepsPlus target) :
    Lambda.Term.StepsPlus (encodeRuntime source) (encodeRuntime target) := by
  induction h with
  | single step => exact runtime_step_simulation step
  | tail _ step ih => exact Reduction.Plus.trans ih (runtime_step_simulation step)

/-- Lean/Coq parity alias for positive simulation of one runtime step. -/
theorem encodeRuntime_step_positive {source target : Iota.Runtime.Term}
    (h : source.Step target) :
    Lambda.Term.StepsPlus (encodeRuntime source) (encodeRuntime target) :=
  runtime_step_simulation h

/-- Lean/Coq parity alias for preservation of runtime reflexive-transitive closure. -/
theorem encodeRuntime_steps {source target : Iota.Runtime.Term}
    (h : source.Steps target) :
    Lambda.Term.Steps (encodeRuntime source) (encodeRuntime target) :=
  runtime_steps_simulation h

/-- Lean/Coq parity alias for preservation of positive runtime closure. -/
theorem encodeRuntime_progresses {source target : Iota.Runtime.Term}
    (h : source.StepsPlus target) :
    Lambda.Term.StepsPlus (encodeRuntime source) (encodeRuntime target) :=
  runtime_stepsPlus_simulation h

/-- Pure iota syntax interpreted through its injective runtime inclusion. -/
def encode (term : Iota.Term) : Lambda.Term 0 :=
  encodeRuntime (Iota.Runtime.Term.embed term)

/-- Lean/Coq parity name for the pure-source encoding. -/
abbrev encodePure := encode

@[simp] theorem encode_iota : encode .iota = Closed.iota := rfl

/-- Pure-source application is preserved exactly. -/
@[simp] theorem encode_app (function argument : Iota.Term) :
    encode (.app function argument) =
      .app (encode function) (encode argument) := rfl

/-- Interpreting after the pure-to-runtime inclusion is definitionally compatible. -/
@[simp] theorem encodeRuntime_embed (term : Iota.Term) :
    encodeRuntime (Iota.Runtime.Term.embed term) = encode term := rfl

/-- Lean/Coq parity alias for compatibility with the pure runtime inclusion. -/
theorem encode_embed (term : Iota.Term) :
    encodeRuntime (Iota.Runtime.Term.embed term) = encodePure term := rfl

/-- The runtime interpretation is syntactically injective, even before restriction to pure terms. -/
theorem encodeRuntimeAt_injective (n : Nat) :
    Function.Injective (encodeRuntimeAt n) := by
  intro source
  induction source with
  | iota =>
      intro target equality
      cases target with
      | iota => rfl
      | s =>
          simp [encodeRuntimeAt, Closed.iotaAt, Closed.sAt] at equality
      | k =>
          simp [encodeRuntimeAt, Closed.iotaAt, Closed.kAt] at equality
      | app function argument =>
          simp [encodeRuntimeAt, Closed.iotaAt] at equality
  | s =>
      intro target equality
      cases target with
      | iota =>
          simp [encodeRuntimeAt, Closed.iotaAt, Closed.sAt] at equality
      | s => rfl
      | k =>
          simp [encodeRuntimeAt, Closed.sAt, Closed.kAt] at equality
      | app function argument =>
          simp [encodeRuntimeAt, Closed.sAt] at equality
  | k =>
      intro target equality
      cases target with
      | iota =>
          simp [encodeRuntimeAt, Closed.iotaAt, Closed.kAt] at equality
      | s =>
          simp [encodeRuntimeAt, Closed.sAt, Closed.kAt] at equality
      | k => rfl
      | app function argument =>
          simp [encodeRuntimeAt, Closed.kAt] at equality
  | app function argument ihFunction ihArgument =>
      intro target equality
      cases target with
      | iota =>
          simp [encodeRuntimeAt, Closed.iotaAt] at equality
      | s =>
          simp [encodeRuntimeAt, Closed.sAt] at equality
      | k =>
          simp [encodeRuntimeAt, Closed.kAt] at equality
      | app function' argument' =>
          have parts := Lambda.Term.app.inj equality
          have functionEquality : function = function' := ihFunction parts.1
          have argumentEquality : argument = argument' := ihArgument parts.2
          cases functionEquality
          cases argumentEquality
          rfl

/-- The closed runtime interpretation loses no syntax. -/
theorem encodeRuntime_injective : Function.Injective encodeRuntime := by
  exact encodeRuntimeAt_injective 0

/-- In particular, the pure-source interpretation is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro source target equality
  exact Iota.Runtime.Term.embed_injective (encodeRuntime_injective equality)

/-- Finite pure-iota reduction is preserved by the closed lambda encoding. -/
theorem reaches_simulation {source target : Iota.Term}
    (h : Iota.Reaches source target) :
    Lambda.Term.Steps (encode source) (encode target) := by
  exact runtime_steps_simulation h

/-- Positive pure-iota reduction remains positive in closed lambda calculus. -/
theorem reachesPlus_simulation {source target : Iota.Term}
    (h : Iota.ReachesPlus source target) :
    Lambda.Term.StepsPlus (encode source) (encode target) := by
  exact runtime_stepsPlus_simulation h

/-- Lean/Coq parity alias for exact preservation of pure application. -/
theorem encodePure_app (function argument : Iota.Term) :
    encodePure (.app function argument) =
      .app (encodePure function) (encodePure argument) :=
  encode_app function argument

/-- Lean/Coq parity alias for injectivity of the pure-source encoding. -/
theorem encodePure_injective : Function.Injective encodePure :=
  encode_injective

/-- Lean/Coq parity alias for preservation of finite pure reduction. -/
theorem encodePure_reaches {source target : Iota.Term}
    (h : Iota.Reaches source target) :
    Lambda.Term.Steps (encodePure source) (encodePure target) :=
  reaches_simulation h

/-- Lean/Coq parity alias for preservation of positive pure reduction. -/
theorem encodePure_progresses {source target : Iota.Term}
    (h : Iota.ReachesPlus source target) :
    Lambda.Term.StepsPlus (encodePure source) (encodePure target) :=
  reachesPlus_simulation h

/--
An injective, application-homomorphic, reduction-preserving pure-iota
embedding.  This is deliberately a one-way operational simulation: no
reflection or full-abstraction claim is included.
-/
structure FaithfulIotaLambdaEmbedding (A : Type) (application : A → A → A)
    (reaches reachesPlus : A → A → Prop) where
  encode : Iota.Term → A
  encode_app : ∀ function argument,
    encode (.app function argument) = application (encode function) (encode argument)
  injective : Function.Injective encode
  simulates : ∀ {source target},
    Iota.Reaches source target → reaches (encode source) (encode target)
  simulatesPositive : ∀ {source target},
    Iota.ReachesPlus source target → reachesPlus (encode source) (encode target)

/-- The canonical faithful embedding of pure iota into closed weak lambda terms. -/
def faithful_iota_lambda_embedding :
    FaithfulIotaLambdaEmbedding
      (Lambda.Term 0) Lambda.Term.app Lambda.Term.Steps Lambda.Term.StepsPlus where
  encode := encode
  encode_app := encode_app
  injective := encode_injective
  simulates := reaches_simulation
  simulatesPositive := reachesPlus_simulation

/-- Short compatibility name for the faithful-embedding interface. -/
abbrev FaithfulIotaEmbedding := FaithfulIotaLambdaEmbedding

/-- Short compatibility name for the canonical faithful embedding witness. -/
abbrev faithful_iota_embedding := faithful_iota_lambda_embedding

end CombinatoryLogic.IotaToLambda
