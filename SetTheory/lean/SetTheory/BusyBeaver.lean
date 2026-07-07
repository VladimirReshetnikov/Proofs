/-
  BusyBeaver.lean

  A small Rado-style busy-beaver interface and the standard domination theorem.

  The theorem here keeps the computability-theory interface explicit.  We define
  blank-tape two-symbol machines, their halting scores, and the maximum property
  expected of the busy-beaver score function.  Separately, we state the usual
  compiler fact for a chosen notion of total computability: a fixed program for a
  total function can be turned, with constant overhead, into a blank-tape
  n-state machine that prints the value at n.  From those two ingredients,
  domination is a short arithmetic argument.
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

/-- The blank initial configuration. -/
def initial (states : Nat) : Config states where
  state := startState states
  head := 0
  tape := []

namespace Machine

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

/--
The machine halts with `score` if after some finite number of steps it is halted
and exactly `score` tape cells contain `1`.
-/
def HaltsWithScore {states : Nat} (M : Machine states) (score : Nat) : Prop :=
  ∃ t, (M.run t).state = none ∧ (M.run t).tape.length = score

end Machine

/-- A score is attainable by some `states`-state machine. -/
def AttainableScore (states score : Nat) : Prop :=
  ∃ M : Machine states, M.HaltsWithScore score

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
`Computable` on total functions `Nat -> Nat`.

For every computable total function `f`, there is a constant overhead `c` such
that the value `f (k + c)` can be printed by a blank-tape machine with exactly
`k + c` operational states.  The `k` states encode the input size; `c` is the
fixed program/decoding/output overhead.
-/
def HasLinearOverheadBlankCompiler (Computable : (Nat -> Nat) -> Prop) : Prop :=
  ∀ {f : Nat -> Nat}, Computable f ->
    ∃ overhead, ∀ k, AttainableScore (k + overhead) (f (k + overhead))

/--
A direct, model-relative notion of total computability: the function has the
linear-overhead blank-tape realizers needed by the domination proof.
-/
def TotalComputableInRadoModel (f : Nat -> Nat) : Prop :=
  ∃ overhead, ∀ k, AttainableScore (k + overhead) (f (k + overhead))

/-- Any attainable score is bounded by any function satisfying `IsSigma`. -/
theorem score_le_sigma {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {states score : Nat} (h : AttainableScore states score) :
    score ≤ Sigma states :=
  hSigma.upper h

/--
The busy-beaver score function eventually dominates every total computable
function, assuming the chosen computability predicate has the standard
linear-overhead blank-tape compiler into the Rado machine model.
-/
theorem eventuallyDominates_of_hasLinearOverheadBlankCompiler
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {Computable : (Nat -> Nat) -> Prop}
    (hCompiler : HasLinearOverheadBlankCompiler Computable)
    {f : Nat -> Nat} (hf : Computable f) :
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
Specialization of the domination theorem to the model-relative computability
predicate `TotalComputableInRadoModel`.
-/
theorem eventuallyDominates_totalComputableInRadoModel
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalComputableInRadoModel f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasLinearOverheadBlankCompiler
    hSigma (fun hf => hf) hf

end BusyBeaver
end SetTheory
