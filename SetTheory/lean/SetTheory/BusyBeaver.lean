/-
  BusyBeaver.lean

  A small Rado-style busy-beaver interface and the standard domination theorem.

  The theorem here keeps the computability-theory interface explicit.  We define
  blank-tape two-symbol machines, their halting scores, and the maximum property
  expected of the busy-beaver score function.  Separately, we state the usual
  compiler fact for a chosen notion of total recursiveness: a fixed program for a
  total recursive function can be turned, with constant overhead, into a
  blank-tape n-state machine that prints the value at n.  From those two
  ingredients, domination is a short arithmetic argument.
-/

namespace SetTheory
namespace BusyBeaver

/-! ## Rado-style machines -/

/-- The two tape-head moves allowed in the classical busy-beaver game. -/
inductive Move where
  | left
  | right
  deriving DecidableEq, Repr

namespace Move

/-- Apply a head move to an integer tape position. -/
def apply : Move -> Int -> Int
  | left, pos => pos - 1
  | right, pos => pos + 1

end Move

/--
One transition action: write a bit, move one cell, and either enter another
operational state or halt (`none`).
-/
structure Action (states : Nat) where
  write : Bool
  move : Move
  next : Option (Fin states)
  deriving Repr

/--
An `n`-state busy-beaver machine.  The operational states are `Fin n`; the halt
state is represented separately as `none` in configurations and transitions.
-/
structure Machine (states : Nat) where
  transition : Fin states -> Bool -> Action states

/-! ### Typed-state variant for compiler proofs -/

universe u

/--
A Rado action whose next operational state lives in an arbitrary type.  This is
used as an intermediate compiler target before reindexing a finite state type
to `Fin states`.
-/
structure TypedAction (stateType : Type u) where
  write : Bool
  move : Move
  next : Option stateType
  deriving Repr

/-- A Rado-style machine with an arbitrary operational state type. -/
structure TypedMachine (stateType : Type u) where
  transition : stateType -> Bool -> TypedAction stateType

/--
The tape is represented by the finite list of positions currently containing
`1`.  The all-zero tape is `[]`.
-/
abbrev Tape := List Int

namespace Tape

/-- Read the bit at a tape position. -/
def read (tape : Tape) (pos : Int) : Bool :=
  if pos ∈ tape then true else false

/-- Write a bit at a tape position, preserving the finite-support view. -/
def write (tape : Tape) (pos : Int) (bit : Bool) : Tape :=
  if bit then
    if pos ∈ tape then tape else pos :: tape
  else
    tape.filter (fun q => q != pos)

@[simp]
theorem read_write_same (tape : Tape) (pos : Int) (bit : Bool) :
    read (write tape pos bit) pos = bit := by
  cases bit
  · simp [read, write]
  · simp [read, write]
    by_cases h : pos ∈ tape <;> simp [h]

theorem read_write_of_ne (tape : Tape) {pos q : Int} (h : q ≠ pos) (bit : Bool) :
    read (write tape pos bit) q = read tape q := by
  cases bit
  · simp [read, write]
    by_cases hq : q ∈ tape
    · simp [hq, h]
    · simp [hq]
  · simp [read, write]
    by_cases hp : pos ∈ tape
    · simp [hp]
    · simp [hp, h]

@[simp]
theorem write_read_self (tape : Tape) (pos : Int) :
    write tape pos (read tape pos) = tape := by
  simp [read, write]
  by_cases h : pos ∈ tape
  · simp [h]
  · simp [h]
    intro a ha heq
    exact h (heq ▸ ha)

theorem filter_ne_nodup (tape : Tape) (pos : Int) :
    tape.Nodup -> (tape.filter (fun q => q != pos)).Nodup := by
  induction tape with
  | nil => simp
  | cons a rest IH =>
      intro h
      rw [List.nodup_cons] at h
      by_cases ha : a != pos
      · simp [List.filter, ha, List.nodup_cons]
        constructor
        · intro hin
          exact h.1 hin
        · exact IH h.2
      · simp [List.filter, ha]
        exact IH h.2

@[simp]
theorem write_nodup {tape : Tape} {pos : Int} {bit : Bool}
    (h : tape.Nodup) : (write tape pos bit).Nodup := by
  cases bit
  · simp [write]
    exact filter_ne_nodup tape pos h
  · by_cases hp : pos ∈ tape
    · simp [write, hp, h]
    · simp [write, hp, List.nodup_cons, h]

end Tape

/-- The start state: state `0` when at least one operational state exists. -/
def startState : (states : Nat) -> Option (Fin states)
  | 0 => none
  | n + 1 => some ⟨0, Nat.succ_pos n⟩

/-- A machine configuration. -/
structure Config (states : Nat) where
  state : Option (Fin states)
  head : Int
  tape : Tape
  deriving Repr

/-- A typed-state Rado configuration. -/
structure TypedConfig (stateType : Type u) where
  state : Option stateType
  head : Int
  tape : Tape
  deriving Repr

namespace Config

/-- Embed a configuration into a machine with more operational states. -/
def castLE {states larger : Nat} (h : states ≤ larger) (cfg : Config states) :
    Config larger where
  state := cfg.state.map (Fin.castLE h)
  head := cfg.head
  tape := cfg.tape

end Config

/-- The blank initial configuration. -/
def initial (states : Nat) : Config states where
  state := startState states
  head := 0
  tape := []

namespace Machine

/--
Pad a machine to a larger state set.  Original states keep their transitions;
extra states are unreachable from the embedded start state and halt after
writing `0` and moving right.
-/
def castLE {states larger : Nat} (h : states ≤ larger) (M : Machine states) :
    Machine larger where
  transition q bit :=
    if hq : q.val < states then
      let action := M.transition ⟨q.val, hq⟩ bit
      { write := action.write
        move := action.move
        next := action.next.map (Fin.castLE h) }
    else
      { write := false
        move := Move.right
        next := none }

/-- Execute one transition.  Halted configurations stay fixed. -/
def step {states : Nat} (M : Machine states) (cfg : Config states) : Config states :=
  match cfg.state with
  | none => cfg
  | some q =>
      let action := M.transition q (Tape.read cfg.tape cfg.head)
      { state := action.next
        head := action.move.apply cfg.head
        tape := Tape.write cfg.tape cfg.head action.write }

/-- Run a machine for a fixed number of steps from the blank tape. -/
def run {states : Nat} (M : Machine states) : Nat -> Config states
  | 0 => initial states
  | t + 1 => M.step (M.run t)

@[simp]
theorem castLE_step {states larger : Nat} (h : states ≤ larger)
    (M : Machine states) (cfg : Config states) :
    (M.castLE h).step (cfg.castLE h) = (M.step cfg).castLE h := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some q =>
          simp [step, Config.castLE, Machine.castLE]

@[simp]
theorem startState_castLE {states larger : Nat} (hpos : 0 < states)
    (h : states ≤ larger) :
    (startState states).map (Fin.castLE h) = startState larger := by
  cases states with
  | zero => cases hpos
  | succ states' =>
      cases larger with
      | zero =>
          cases Nat.not_succ_le_zero states' h
      | succ larger' =>
          rfl

@[simp]
theorem initial_castLE {states larger : Nat} (hpos : 0 < states)
    (h : states ≤ larger) :
    (initial states).castLE h = initial larger := by
  simp [initial, Config.castLE, startState_castLE hpos h]

@[simp]
theorem castLE_run {states larger : Nat} (hpos : 0 < states)
    (h : states ≤ larger) (M : Machine states) :
    ∀ t, (M.castLE h).run t = (M.run t).castLE h
  | 0 => by simp [run, initial_castLE hpos h]
  | t + 1 => by
      simp [run, castLE_run hpos h M t]

@[simp]
theorem run_zero_states (M : Machine 0) :
    ∀ t, M.run t = initial 0
  | 0 => rfl
  | t + 1 => by
      simp [run, run_zero_states M t, step, initial, startState]

theorem step_tape_nodup {states : Nat} (M : Machine states) (cfg : Config states)
    (h : cfg.tape.Nodup) : (M.step cfg).tape.Nodup := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => exact h
      | some _q =>
          simp [step]
          exact Tape.write_nodup h

@[simp]
theorem run_tape_nodup {states : Nat} (M : Machine states) :
    ∀ t, (M.run t).tape.Nodup
  | 0 => by simp [run, initial]
  | t + 1 => by
      exact M.step_tape_nodup (M.run t) (run_tape_nodup M t)

/--
The machine halts with `score` if after some finite number of steps it is halted
and exactly `score` tape cells contain `1`.
-/
def HaltsWithScore {states : Nat} (M : Machine states) (score : Nat) : Prop :=
  ∃ t, (M.run t).state = none ∧ (M.run t).tape.length = score

theorem castLE_haltsWithScore {states larger score : Nat} (hpos : 0 < states)
    (h : states ≤ larger) {M : Machine states} :
    M.HaltsWithScore score -> (M.castLE h).HaltsWithScore score := by
  rintro ⟨t, hState, hScore⟩
  refine ⟨t, ?_, ?_⟩
  · simp [castLE_run hpos h M t, Config.castLE, hState]
  · simpa [castLE_run hpos h M t, Config.castLE] using hScore

theorem zero_states_haltsWithScore_eq_zero {score : Nat} {M : Machine 0} :
    M.HaltsWithScore score -> score = 0 := by
  rintro ⟨t, _hState, hScore⟩
  simpa [run_zero_states M t, initial] using hScore.symm

end Machine

namespace TypedMachine

/-- Execute one transition of a typed-state Rado machine.  Halted
configurations stay fixed. -/
def step {stateType : Type u} (M : TypedMachine stateType) (cfg : TypedConfig stateType) :
    TypedConfig stateType :=
  match cfg.state with
  | none => cfg
  | some q =>
      let action := M.transition q (Tape.read cfg.tape cfg.head)
      { state := action.next
        head := action.move.apply cfg.head
        tape := Tape.write cfg.tape cfg.head action.write }

/-- Run a typed-state Rado machine from a chosen start state on the blank tape. -/
def run {stateType : Type u} (M : TypedMachine stateType) (start : stateType) :
    Nat -> TypedConfig stateType
  | 0 => { state := some start, head := 0, tape := [] }
  | t + 1 => M.step (M.run start t)

/-- Run a typed-state Rado machine from an arbitrary configuration. -/
def runFrom {stateType : Type u} (M : TypedMachine stateType) (cfg : TypedConfig stateType) :
    Nat -> TypedConfig stateType
  | 0 => cfg
  | t + 1 => M.step (M.runFrom cfg t)

theorem run_eq_runFrom {stateType : Type u} (M : TypedMachine stateType) (start : stateType) :
    ∀ t,
      M.run start t =
        M.runFrom ({ state := some start, head := 0, tape := [] } : TypedConfig stateType) t
  | 0 => rfl
  | t + 1 => by
      simp [run, runFrom, run_eq_runFrom M start t]

theorem step_tape_nodup {stateType : Type u} (M : TypedMachine stateType)
    (cfg : TypedConfig stateType) (h : cfg.tape.Nodup) :
    (M.step cfg).tape.Nodup := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => exact h
      | some _q =>
          simp [step]
          exact Tape.write_nodup h

theorem runFrom_tape_nodup {stateType : Type u} (M : TypedMachine stateType)
    {cfg : TypedConfig stateType} (h : cfg.tape.Nodup) :
    ∀ t, (M.runFrom cfg t).tape.Nodup
  | 0 => h
  | t + 1 => by
      exact M.step_tape_nodup (M.runFrom cfg t) (runFrom_tape_nodup M h t)

@[simp]
theorem run_tape_nodup {stateType : Type u} (M : TypedMachine stateType)
    (start : stateType) :
    ∀ t, (M.run start t).tape.Nodup
  | 0 => by simp [run]
  | t + 1 => by
      exact M.step_tape_nodup (M.run start t) (run_tape_nodup M start t)

/-- A typed-state Rado machine halts with a given score from the blank tape. -/
def HaltsWithScore {stateType : Type u} (M : TypedMachine stateType) (start : stateType)
    (score : Nat) : Prop :=
  ∃ t, (M.run start t).state = none ∧ (M.run start t).tape.length = score

end TypedMachine

/-- A score is attainable by some `states`-state machine. -/
def AttainableScore (states score : Nat) : Prop :=
  ∃ M : Machine states, M.HaltsWithScore score

/-- A score is attainable by a machine using at most `states` operational states. -/
def AttainableScoreAtMost (states score : Nat) : Prop :=
  ∃ used, used ≤ states ∧ AttainableScore used score

theorem attainableScore_castLE {states larger score : Nat}
    (hpos : 0 < states) (h : states ≤ larger) :
    AttainableScore states score -> AttainableScore larger score := by
  rintro ⟨M, hM⟩
  exact ⟨M.castLE h, M.castLE_haltsWithScore hpos h hM⟩

/-! ## The busy-beaver score function and domination -/

/--
`IsSigma Sigma` is the maximum-property specification of the busy-beaver score
function for the machine model above.

The domination theorem only needs `upper`; `attained` records the usual "there is
a winner" half of the definition for positive state counts.
-/
structure IsSigma (Sigma : Nat -> Nat) : Prop where
  upper : ∀ {states score : Nat}, AttainableScore states score -> score ≤ Sigma states
  attained : ∀ {states : Nat}, 0 < states -> AttainableScore states (Sigma states)

/-- Eventual domination of one natural-number function by another. -/
def EventuallyDominates (g f : Nat -> Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n -> f n ≤ g n

/--
The standard linear-overhead blank-tape compiler property for a chosen predicate
`TotalRecursive` on total functions `Nat -> Nat`.

For every total recursive function `f`, there is a constant overhead `c` such
that the value `f (k + c)` can be printed by a blank-tape machine with exactly
`k + c` operational states.  The `k` states encode the input size; `c` is the
fixed program/decoding/output overhead.
-/
def HasLinearOverheadBlankCompiler (TotalRecursive : (Nat -> Nat) -> Prop) : Prop :=
  ∀ {f : Nat -> Nat}, TotalRecursive f ->
    ∃ overhead, ∀ k, AttainableScore (k + overhead) (f (k + overhead))

/--
A more flexible blank-tape compiler property: for every total recursive
function, all sufficiently large inputs `n` can be handled by a blank-tape
machine using at most `n` operational states.

This is the convenient target for a binary-input compiler, because the input
initializer need only fit below the available state budget eventually.
-/
def HasEventuallyAtMostBlankCompiler (TotalRecursive : (Nat -> Nat) -> Prop) : Prop :=
  ∀ {f : Nat -> Nat}, TotalRecursive f ->
    ∃ threshold, ∀ n, threshold ≤ n -> AttainableScoreAtMost n (f n)

/--
Even weaker compiler target sufficient for domination: for every sufficiently
large input `n`, a blank-tape machine using at most `n` states halts with some
score at least `f n`.

This is often the natural proof obligation for simulations that leave harmless
scratch `1`s on the tape: exact output cleanup is unnecessary for busy-beaver
domination.
-/
def HasEventuallyAtMostLowerBoundCompiler
    (TotalRecursive : (Nat -> Nat) -> Prop) : Prop :=
  ∀ {f : Nat -> Nat}, TotalRecursive f ->
    ∃ threshold, ∀ n, threshold ≤ n ->
      ∃ score, f n ≤ score ∧ AttainableScoreAtMost n score

/--
A direct, model-relative notion of total recursiveness: the function has the
linear-overhead blank-tape realizers needed by the domination proof.
-/
def TotalRecursiveInRadoModel (f : Nat -> Nat) : Prop :=
  ∃ overhead, ∀ k, AttainableScore (k + overhead) (f (k + overhead))

/--
Model-relative eventual realizability using at most the available number of
states.
-/
def TotalRecursiveEventuallyInRadoModel (f : Nat -> Nat) : Prop :=
  ∃ threshold, ∀ n, threshold ≤ n -> AttainableScoreAtMost n (f n)

/--
Model-relative eventual lower-bound realizability using at most the available
number of states.
-/
def TotalRecursiveEventuallyLowerBoundInRadoModel (f : Nat -> Nat) : Prop :=
  ∃ threshold, ∀ n, threshold ≤ n ->
    ∃ score, f n ≤ score ∧ AttainableScoreAtMost n score

/-- Any attainable score is bounded by any function satisfying `IsSigma`. -/
theorem score_le_sigma {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {states score : Nat} (h : AttainableScore states score) :
    score ≤ Sigma states :=
  hSigma.upper h

/--
`Σ` is monotone on positive state counts: a smaller positive-state machine can
be padded with unreachable states.
-/
theorem sigma_mono_of_pos {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {states larger : Nat} (hpos : 0 < states) (h : states ≤ larger) :
    Sigma states ≤ Sigma larger := by
  exact hSigma.upper (attainableScore_castLE hpos h (hSigma.attained hpos))

/-- Any score attainable with at most `states` states is bounded by `Σ states`. -/
theorem score_le_sigma_of_atMost {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {states score : Nat} (h : AttainableScoreAtMost states score) :
    score ≤ Sigma states := by
  rcases h with ⟨used, hUsed, hScore⟩
  by_cases hzero : used = 0
  · subst used
    rcases hScore with ⟨M, hM⟩
    have hScoreZero := Machine.zero_states_haltsWithScore_eq_zero (M := M) hM
    simp [hScoreZero]
  · have hpos : 0 < used := Nat.pos_of_ne_zero hzero
    exact Nat.le_trans (hSigma.upper hScore) (sigma_mono_of_pos hSigma hpos hUsed)

/--
The busy-beaver score function eventually dominates every total recursive
function, assuming the chosen total-recursiveness predicate has the standard
linear-overhead blank-tape compiler into the Rado machine model.
-/
theorem eventuallyDominates_of_hasLinearOverheadBlankCompiler
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : HasLinearOverheadBlankCompiler TotalRecursive)
    {f : Nat -> Nat} (hf : TotalRecursive f) :
    EventuallyDominates Sigma f := by
  rcases hCompiler hf with ⟨overhead, hRealize⟩
  refine ⟨overhead, ?_⟩
  intro n hn
  have hEq : (n - overhead) + overhead = n := Nat.sub_add_cancel hn
  have hScore :
      AttainableScore ((n - overhead) + overhead)
        (f ((n - overhead) + overhead)) :=
    hRealize (n - overhead)
  have hLe := hSigma.upper hScore
  simpa [hEq] using hLe

/--
The same domination conclusion from the weaker, eventually-at-most-`n` compiler
interface.
-/
theorem eventuallyDominates_of_hasEventuallyAtMostBlankCompiler
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : HasEventuallyAtMostBlankCompiler TotalRecursive)
    {f : Nat -> Nat} (hf : TotalRecursive f) :
    EventuallyDominates Sigma f := by
  rcases hCompiler hf with ⟨threshold, hRealize⟩
  refine ⟨threshold, ?_⟩
  intro n hn
  exact score_le_sigma_of_atMost hSigma (hRealize n hn)

/-- Exact eventually-at-most compilers are lower-bound compilers. -/
theorem hasEventuallyAtMostLowerBoundCompiler_of_exact
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : HasEventuallyAtMostBlankCompiler TotalRecursive) :
    HasEventuallyAtMostLowerBoundCompiler TotalRecursive := by
  intro f hf
  rcases hCompiler hf with ⟨threshold, hRealize⟩
  refine ⟨threshold, ?_⟩
  intro n hn
  exact ⟨f n, Nat.le_refl _, hRealize n hn⟩

/--
The same domination conclusion from the lower-bound, eventually-at-most-`n`
compiler interface.
-/
theorem eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : HasEventuallyAtMostLowerBoundCompiler TotalRecursive)
    {f : Nat -> Nat} (hf : TotalRecursive f) :
    EventuallyDominates Sigma f := by
  rcases hCompiler hf with ⟨threshold, hRealize⟩
  refine ⟨threshold, ?_⟩
  intro n hn
  rcases hRealize n hn with ⟨score, hLower, hScore⟩
  exact Nat.le_trans hLower (score_le_sigma_of_atMost hSigma hScore)

/--
Specialization of the domination theorem to the model-relative total-recursive
predicate `TotalRecursiveInRadoModel`.
-/
theorem eventuallyDominates_totalRecursiveInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasLinearOverheadBlankCompiler
    hSigma (fun hf => hf) hf

/--
Specialization to the model-relative eventual-at-most-state predicate.
-/
theorem eventuallyDominates_totalRecursiveEventuallyInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveEventuallyInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasEventuallyAtMostBlankCompiler
    hSigma (fun hf => hf) hf

/--
Specialization to the model-relative eventual lower-bound predicate.
-/
theorem eventuallyDominates_totalRecursiveEventuallyLowerBoundInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveEventuallyLowerBoundInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    hSigma (fun hf => hf) hf

/--
Alias with the more precise classical phrasing requested here: a busy-beaver
score function eventually dominates every total recursive function, once the
selected total-recursiveness predicate is connected to this Rado machine model
by the standard compiler.
-/
theorem sigma_eventually_dominates_every_total_recursive
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : HasLinearOverheadBlankCompiler TotalRecursive)
    {f : Nat -> Nat} (hf : TotalRecursive f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasLinearOverheadBlankCompiler hSigma hCompiler hf

/--
Alias for the model-relative total-recursive predicate.
-/
theorem sigma_eventually_dominates_every_totalRecursiveInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_totalRecursiveInRadoModel hSigma hf

/--
Alias for the model-relative eventual-at-most-state predicate.
-/
theorem sigma_eventually_dominates_every_totalRecursiveEventuallyInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveEventuallyInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_totalRecursiveEventuallyInRadoModel hSigma hf

/--
Alias for the model-relative eventual lower-bound predicate.
-/
theorem sigma_eventually_dominates_every_totalRecursiveEventuallyLowerBoundInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveEventuallyLowerBoundInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_totalRecursiveEventuallyLowerBoundInRadoModel hSigma hf

end BusyBeaver
end SetTheory
