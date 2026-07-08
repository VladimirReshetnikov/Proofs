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

/-- If `a` occurs in `l` and `a ≠ b`, then `a` still occurs after erasing `b`. -/
theorem list_mem_erase_of_ne_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {a b : α} {l : List α} (hne : a ≠ b) (hmem : a ∈ l) :
    a ∈ l.erase b := by
  induction l with
  | nil => cases hmem
  | cons c cs IH =>
      by_cases hcb : c = b
      · subst c
        simp [List.erase_cons_head, hne] at hmem ⊢
        exact hmem
      · rw [List.erase_cons_tail]
        · simp at hmem ⊢
          rcases hmem with h | h
          · exact Or.inl h
          · exact Or.inr (IH h)
        · simpa [Bool.not_eq_true] using hcb

/--
A nodup list cannot inject into a shorter nodup list by membership.  This is
the finite-list counting lemma used to turn many distinct known-true tape
positions into a lower bound on the Rado score.
-/
theorem list_length_le_of_nodup_subset {α : Type*} [BEq α] [LawfulBEq α]
    {xs ys : List α} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hsub : ∀ x, x ∈ xs -> x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a rest IH =>
      rw [List.nodup_cons] at hxs
      have ha : a ∈ ys := hsub a (by simp)
      have hrestSub : ∀ x, x ∈ rest -> x ∈ ys.erase a := by
        intro x hx
        exact list_mem_erase_of_ne_of_mem
          (fun hxa => hxs.1 (hxa ▸ hx)) (hsub x (by simp [hx]))
      have hle := IH hxs.2 (List.Nodup.erase a hys) hrestSub
      have hlen := List.length_erase_add_one ha
      change rest.length + 1 ≤ ys.length
      rw [← hlen]
      exact Nat.succ_le_succ hle

theorem tape_mem_of_read_true {tape : Tape} {pos : Int}
    (h : Tape.read tape pos = true) : pos ∈ tape := by
  by_contra hp
  simp [Tape.read, hp] at h

/--
If a nodup list of positions all read as `1` on a nodup Rado tape, then the tape
score is at least the number of witnessed positions.
-/
theorem positions_length_le_tape_length_of_read_true {positions tape : Tape}
    (hPositions : positions.Nodup) (hTape : tape.Nodup)
    (hRead : ∀ pos, pos ∈ positions -> Tape.read tape pos = true) :
    positions.length ≤ tape.length := by
  exact list_length_le_of_nodup_subset hPositions hTape
    (fun pos hpos => tape_mem_of_read_true (hRead pos hpos))

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

/--
Pointwise relation between a Rado tape and mathlib's Bool tape.

`head` is the Rado head position corresponding to mathlib offset `0`; every
integer offset from that head reads the same bit in both tape models.
-/
def RadoMatchesTuringTape (head : Int) (tape : Tape) (T : Turing.Tape Bool) : Prop :=
  ∀ i : Int, Tape.read tape (head + i) = T.nth i

theorem radoMatchesTuringTape_write {head : Int} {tape : Tape} {T : Turing.Tape Bool}
    {bit : Bool} (h : RadoMatchesTuringTape head tape T) :
    RadoMatchesTuringTape head (Tape.write tape head bit) (T.write bit) := by
  intro i
  by_cases hi : i = 0
  · subst i
    change Tape.read (Tape.write tape head bit) (head + 0) = bit
    simp
  · rw [Tape.read_write_of_ne]
    · rw [h i]
      simp [Turing.Tape.write_nth, hi]
    · omega

theorem radoMatchesTuringTape_move_right {head : Int} {tape : Tape} {T : Turing.Tape Bool}
    (h : RadoMatchesTuringTape head tape T) :
    RadoMatchesTuringTape (head + 1) tape (T.move Turing.Dir.right) := by
  intro i
  rw [show head + 1 + i = head + (i + 1) by omega]
  rw [h (i + 1)]
  simp

theorem radoMatchesTuringTape_move_left {head : Int} {tape : Tape} {T : Turing.Tape Bool}
    (h : RadoMatchesTuringTape head tape T) :
    RadoMatchesTuringTape (head - 1) tape (T.move Turing.Dir.left) := by
  intro i
  rw [show head - 1 + i = head + (i - 1) by omega]
  rw [h (i - 1)]
  simp

theorem natOffsetPosition_injective (head : Int) :
    Function.Injective (fun n : Nat => head + (n : Int)) := by
  intro _a _b h
  exact Int.ofNat.inj (Int.add_left_cancel h)

theorem radoMatchesTuringTape_right₀_true {head : Int} {tape : Tape}
    {T : Turing.Tape Bool} (hMatch : RadoMatchesTuringTape head tape T)
    {n : Nat} (hTrue : T.right₀.nth n = true) :
    Tape.read tape (head + (n : Int)) = true := by
  rw [hMatch (n : Int)]
  rwa [Turing.Tape.right₀_nth] at hTrue

/-- Rado positions corresponding to natural offsets on mathlib's inclusive right tape. -/
def radoPositionsOfNatOffsets (head : Int) (offsets : List Nat) : Tape :=
  offsets.map (fun n : Nat => head + (n : Int))

theorem radoPositionsOfNatOffsets_nodup {head : Int} {offsets : List Nat}
    (hOffsets : offsets.Nodup) :
    (radoPositionsOfNatOffsets head offsets).Nodup := by
  exact hOffsets.map (f := fun n : Nat => head + (n : Int))
    (natOffsetPosition_injective head)

theorem radoPositionsOfNatOffsets_length (head : Int) (offsets : List Nat) :
    (radoPositionsOfNatOffsets head offsets).length = offsets.length := by
  simp [radoPositionsOfNatOffsets]

theorem radoPositionsOfNatOffsets_read_true {head : Int} {tape : Tape}
    {T : Turing.Tape Bool} (hMatch : RadoMatchesTuringTape head tape T)
    {offsets : List Nat}
    (hTrue : ∀ n, n ∈ offsets -> T.right₀.nth n = true) :
    ∀ pos, pos ∈ radoPositionsOfNatOffsets head offsets -> Tape.read tape pos = true := by
  intro pos hpos
  simp [radoPositionsOfNatOffsets] at hpos
  rcases hpos with ⟨n, hn, rfl⟩
  exact radoMatchesTuringTape_right₀_true hMatch (hTrue n hn)

theorem boolVector_exists_true_of_ne_false {width : Nat}
    {v : List.Vector Bool width}
    (hNe : v ≠ List.Vector.replicate width false) :
    ∃ i : Fin width, v.get i = true := by
  by_contra hNo
  apply hNe
  apply List.Vector.ext
  intro i
  have hfalse : v.get i ≠ true := by
    intro htrue
    exact hNo ⟨i, htrue⟩
  cases hv : v.get i
  · simp [List.Vector.get_replicate]
  · exact False.elim (hfalse hv)

/--
For any correct finite-alphabet Bool-block encoding with blank encoded as the
all-false block, every nonblank source symbol has at least one true bit in its
encoded block.
-/
theorem encoded_nondefault_has_true {Γ : Type*} [Inhabited Γ] {width : Nat}
    (enc : Γ -> List.Vector Bool width)
    (dec : List.Vector Bool width -> Γ)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a)
    {sym : Γ} (hSym : sym ≠ default) :
    ∃ i : Fin width, (enc sym).get i = true := by
  apply boolVector_exists_true_of_ne_false
  intro hFalse
  apply hSym
  calc
    sym = dec (enc sym) := (encdec sym).symm
    _ = dec (enc default) := by rw [hFalse, enc0]
    _ = default := encdec default

private theorem list_getI_flatMap_const_length {α β : Type*}
    [Inhabited α] [Inhabited β] (l : List α) (f : α -> List β)
    (width j b : Nat)
    (hfLen : ∀ a, (f a).length = width)
    (hfDefault : f default = List.replicate width default)
    (hb : b < width) :
    (l.flatMap f).getI (j * width + b) = (f (l.getI j)).getI b := by
  induction l generalizing j with
  | nil =>
      rw [List.flatMap_nil]
      have hBlock : (f (default : α)).getI b = (default : β) := by
        rw [hfDefault]
        have hbLen : b < (List.replicate width (default : β)).length := by
          simpa using hb
        rw [List.getI_eq_getElem _ hbLen]
        simp
      simp [hBlock]
  | cons a as IH =>
      cases j with
      | zero =>
          rw [List.flatMap_cons, List.getI_append]
          · simp
          · simpa [hfLen a] using hb
      | succ j =>
          rw [List.flatMap_cons, List.getI_append_right]
          · have hidx : (Nat.succ j * width + b) - (f a).length = j * width + b := by
              rw [hfLen a, Nat.succ_mul]
              omega
            rw [hidx]
            simpa using IH j
          · rw [hfLen a, Nat.succ_mul]
            omega

private theorem listBlank_flatMap_nth_block {Γ Γ' : Type*}
    [Inhabited Γ] [Inhabited Γ'] (L : Turing.ListBlank Γ)
    (f : Γ -> List Γ') (hf : ∃ width, f default = List.replicate width default)
    (width j b : Nat)
    (hfLen : ∀ a, (f a).length = width)
    (hfDefault : f default = List.replicate width default)
    (hb : b < width) :
    (L.flatMap f hf).nth (j * width + b) = (f (L.nth j)).getI b := by
  refine L.induction_on fun l => ?_
  rw [Turing.ListBlank.flatMap_mk, Turing.ListBlank.nth_mk, Turing.ListBlank.nth_mk]
  exact list_getI_flatMap_const_length l f width j b hfLen hfDefault hb

private theorem vector_toList_getI {width : Nat} (v : List.Vector Bool width)
    (bit : Fin width) :
    v.toList.getI bit.val = v.get bit := by
  have hLen : bit.val < v.toList.length := by
    rw [List.Vector.toList_length]
    exact bit.isLt
  rw [List.getI_eq_getElem _ hLen]
  rw [List.Vector.toList_getElem]
  rfl

/--
If a bit is true inside the fixed-width block encoding of a source `TM1`
output cell, then the Bool simulator exposes the same true bit at the
corresponding flattened right-tape offset.
-/
theorem tm1to1Output_block_true {Γ : Type*} [Inhabited Γ] {width : Nat}
    {enc : Γ -> List.Vector Bool width}
    {enc0 : enc default = List.Vector.replicate width false}
    {sourceOutput : Turing.ListBlank Γ} {boolOutput : Turing.ListBlank Bool}
    (hRel : TM1to1Output enc enc0 sourceOutput boolOutput)
    {sourceIndex : Nat} {bit : Fin width}
    (hBit : (enc (sourceOutput.nth sourceIndex)).get bit = true) :
    boolOutput.nth (sourceIndex * width + bit.val) = true := by
  rcases hRel with ⟨tape, hSource, hBool⟩
  rw [← hBool]
  rw [Turing.TM1to1.trTape]
  simp only [Turing.TM1to1.trTape', Turing.Tape.mk'_right₀]
  rw [listBlank_flatMap_nth_block]
  · rw [hSource]
    rw [vector_toList_getI]
    exact hBit
  · intro a
    exact List.Vector.toList_length (enc a)
  · simp only [enc0, List.Vector.replicate, Bool.default_bool, List.Vector.toList_mk]
  · exact bit.isLt

/-- Convert mathlib's tape-head directions to the Rado direction type. -/
def radoMoveOfTuringDir : Turing.Dir -> Move
  | Turing.Dir.left => Move.left
  | Turing.Dir.right => Move.right

@[simp]
theorem radoMoveOfTuringDir_apply (dir : Turing.Dir) (head : Int) :
    (radoMoveOfTuringDir dir).apply head =
      match dir with
      | Turing.Dir.left => head - 1
      | Turing.Dir.right => head + 1 := by
  cases dir <;> rfl

/--
Typed-state Rado states used to simulate a Bool `TM0`.

`normal q` corresponds to a genuine `TM0` label.  `writeReturn q` is the single
helper state needed because `TM0.write` does not move the head while a Rado
transition must move after writing.
-/
inductive TM0RadoState (Label : Type*) where
  | normal : Label -> TM0RadoState Label
  | writeReturn : Label -> TM0RadoState Label
  deriving Repr

/-- Typed-state Rado machine simulating a Bool `TM0` machine. -/
def tm0ToTypedRado {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) : TypedMachine (TM0RadoState Label) where
  transition state bit :=
    match state with
    | TM0RadoState.normal q =>
        match M q bit with
        | none =>
            { write := bit
              move := Move.right
              next := none }
        | some (q', Turing.TM0.Stmt.move dir) =>
            { write := bit
              move := radoMoveOfTuringDir dir
              next := some (TM0RadoState.normal q') }
        | some (q', Turing.TM0.Stmt.write out) =>
            { write := out
              move := Move.right
              next := some (TM0RadoState.writeReturn q') }
    | TM0RadoState.writeReturn q =>
        { write := bit
          move := Move.left
          next := some (TM0RadoState.normal q) }

/--
Relation between a Bool `TM0` configuration and the typed Rado simulator when
the simulator is at a genuine `TM0` label.
-/
def TM0RadoNormalRel {Label : Type*} (tmCfg : Turing.TM0.Cfg Bool Label)
    (radoCfg : TypedConfig (TM0RadoState Label)) : Prop :=
  radoCfg.state = some (TM0RadoState.normal tmCfg.q) ∧
    RadoMatchesTuringTape radoCfg.head radoCfg.tape tmCfg.Tape

/--
Finite-step reachability for the typed Rado simulator generated from a Bool
`TM0` machine.
-/
def TypedRadoReaches {Label : Type*} (M : TypedMachine (TM0RadoState Label)) :
    TypedConfig (TM0RadoState Label) -> TypedConfig (TM0RadoState Label) -> Prop :=
  Relation.ReflTransGen fun a b => b = TypedMachine.step M a

theorem typedRadoReaches_step {Label : Type*} (M : TypedMachine (TM0RadoState Label))
    (cfg : TypedConfig (TM0RadoState Label)) :
    TypedRadoReaches M cfg (TypedMachine.step M cfg) := by
  exact Relation.ReflTransGen.single rfl

theorem typedRadoReaches_step_step {Label : Type*} (M : TypedMachine (TM0RadoState Label))
    (cfg : TypedConfig (TM0RadoState Label)) :
    TypedRadoReaches M cfg (TypedMachine.step M (TypedMachine.step M cfg)) := by
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single rfl) rfl

theorem typedRadoRunFrom_step {Label : Type*} (M : TypedMachine (TM0RadoState Label))
    (cfg : TypedConfig (TM0RadoState Label)) :
    ∀ t,
      TypedMachine.runFrom M (TypedMachine.step M cfg) t =
        TypedMachine.runFrom M cfg (t + 1)
  | 0 => rfl
  | t + 1 => by
      simp [TypedMachine.runFrom, typedRadoRunFrom_step M cfg t]

theorem typedRadoReaches_runFrom {Label : Type*} {M : TypedMachine (TM0RadoState Label)}
    {cfg cfg' : TypedConfig (TM0RadoState Label)}
    (h : TypedRadoReaches M cfg cfg') :
    ∃ t, TypedMachine.runFrom M cfg t = cfg' := by
  unfold TypedRadoReaches at h
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨0, rfl⟩
  · intro a c hStep _hRest IH
    rcases IH with ⟨t, ht⟩
    refine ⟨t + 1, ?_⟩
    rw [← typedRadoRunFrom_step M a t]
    rw [← hStep]
    exact ht

theorem typedRadoReaches_run {Label : Type*} {M : TypedMachine (TM0RadoState Label)}
    {start : TM0RadoState Label} {cfg : TypedConfig (TM0RadoState Label)}
    (h : TypedRadoReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig (TM0RadoState Label))
      cfg) :
    ∃ t, M.run start t = cfg := by
  rcases typedRadoReaches_runFrom h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [TypedMachine.run_eq_runFrom M start t]
  exact ht

theorem typedRadoReaches_haltsWithScore {Label : Type*}
    {M : TypedMachine (TM0RadoState Label)}
    {start : TM0RadoState Label} {haltCfg : TypedConfig (TM0RadoState Label)}
    {score : Nat}
    (hReach : TypedRadoReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig (TM0RadoState Label))
      haltCfg)
    (hState : haltCfg.state = none)
    (hScore : haltCfg.tape.length = score) :
    M.HaltsWithScore start score := by
  rcases typedRadoReaches_run hReach with ⟨t, ht⟩
  exact ⟨t, by rw [ht]; exact hState, by rw [ht]; exact hScore⟩

/-- Reindex a typed configuration through an explicit finite-state equivalence. -/
def typedConfigToConfig {State : Type*} {n : Nat} (e : State ≃ Fin n)
    (cfg : TypedConfig State) : Config n where
  state := cfg.state.map e
  head := cfg.head
  tape := cfg.tape

/-- Reindex a typed Rado machine through an explicit finite-state equivalence. -/
def typedMachineToMachine {State : Type*} {n : Nat} (e : State ≃ Fin n)
    (M : TypedMachine State) : Machine n where
  transition q bit :=
    let action := M.transition (e.symm q) bit
    { write := action.write
      move := action.move
      next := action.next.map e }

@[simp]
theorem typedMachineToMachine_step {State : Type*} {n : Nat} (e : State ≃ Fin n)
    (M : TypedMachine State) (cfg : TypedConfig State) :
    (typedMachineToMachine e M).step (typedConfigToConfig e cfg) =
      typedConfigToConfig e (TypedMachine.step M cfg) := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some q =>
          simp [typedConfigToConfig, typedMachineToMachine, Machine.step, TypedMachine.step]

theorem startState_eq_some_zero {n : Nat} (hpos : 0 < n) :
    startState n = some (⟨0, hpos⟩ : Fin n) := by
  cases n with
  | zero => cases hpos
  | succ n => rfl

@[simp]
theorem typedMachineToMachine_run {State : Type*} {n : Nat} (e : State ≃ Fin n)
    (M : TypedMachine State) (start : State)
    (hStart : some (e start) = startState n) :
    ∀ t,
      (typedMachineToMachine e M).run t =
        typedConfigToConfig e (M.run start t)
  | 0 => by
      simp [Machine.run, TypedMachine.run, initial, typedConfigToConfig, hStart]
  | t + 1 => by
      simp [Machine.run, TypedMachine.run, typedMachineToMachine_run e M start hStart t]

theorem typedMachineToMachine_haltsWithScore {State : Type*} {n score : Nat}
    (e : State ≃ Fin n) (M : TypedMachine State) (start : State)
    (hStart : some (e start) = startState n)
    (hHalt : M.HaltsWithScore start score) :
    (typedMachineToMachine e M).HaltsWithScore score := by
  rcases hHalt with ⟨t, hState, hScore⟩
  refine ⟨t, ?_, ?_⟩
  · rw [typedMachineToMachine_run e M start hStart t]
    simp [typedConfigToConfig, hState]
  · rw [typedMachineToMachine_run e M start hStart t]
    simpa [typedConfigToConfig] using hScore

/-- A finite-state equivalence sending the chosen typed start state to `0`. -/
noncomputable def startEquivFin {State : Type*} [Fintype State] (start : State) :
    State ≃ Fin (Fintype.card State) :=
  (Fintype.equivFin State).trans
    (Equiv.swap ((Fintype.equivFin State) start)
      (⟨0, Fintype.card_pos_iff.2 ⟨start⟩⟩ : Fin (Fintype.card State)))

@[simp]
theorem startEquivFin_start {State : Type*} [Fintype State] (start : State) :
    startEquivFin start start =
      (⟨0, Fintype.card_pos_iff.2 ⟨start⟩⟩ : Fin (Fintype.card State)) := by
  simp [startEquivFin, Equiv.swap_apply_left]

theorem typedMachineToMachine_attainableScore {State : Type*} [Fintype State]
    (M : TypedMachine State) (start : State) {score : Nat}
    (hHalt : M.HaltsWithScore start score) :
    AttainableScore (Fintype.card State) score := by
  let e := startEquivFin start
  refine ⟨typedMachineToMachine e M, ?_⟩
  refine typedMachineToMachine_haltsWithScore e M start ?_ hHalt
  have hpos : 0 < Fintype.card State := Fintype.card_pos_iff.2 ⟨start⟩
  rw [startState_eq_some_zero hpos]
  simp [e]

/-- Finite-step reachability for any typed Rado machine. -/
def TypedMachineReaches {State : Type*} (M : TypedMachine State) :
    TypedConfig State -> TypedConfig State -> Prop :=
  Relation.ReflTransGen fun a b => b = TypedMachine.step M a

theorem typedMachineRunFrom_step {State : Type*} (M : TypedMachine State)
    (cfg : TypedConfig State) :
    ∀ t,
      TypedMachine.runFrom M (TypedMachine.step M cfg) t =
        TypedMachine.runFrom M cfg (t + 1)
  | 0 => rfl
  | t + 1 => by
      simp [TypedMachine.runFrom, typedMachineRunFrom_step M cfg t]

theorem typedMachineReaches_runFrom {State : Type*} {M : TypedMachine State}
    {cfg cfg' : TypedConfig State}
    (h : TypedMachineReaches M cfg cfg') :
    ∃ t, TypedMachine.runFrom M cfg t = cfg' := by
  unfold TypedMachineReaches at h
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨0, rfl⟩
  · intro a c hStep _hRest IH
    rcases IH with ⟨t, ht⟩
    refine ⟨t + 1, ?_⟩
    rw [← typedMachineRunFrom_step M a t]
    rw [← hStep]
    exact ht

theorem typedMachineReaches_run {State : Type*} {M : TypedMachine State}
    {start : State} {cfg : TypedConfig State}
    (h : TypedMachineReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig State)
      cfg) :
    ∃ t, M.run start t = cfg := by
  rcases typedMachineReaches_runFrom h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [TypedMachine.run_eq_runFrom M start t]
  exact ht

theorem typedMachineReaches_haltsWithScore {State : Type*}
    {M : TypedMachine State} {start : State} {haltCfg : TypedConfig State}
    {score : Nat}
    (hReach : TypedMachineReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig State)
      haltCfg)
    (hState : haltCfg.state = none)
    (hScore : haltCfg.tape.length = score) :
    M.HaltsWithScore start score := by
  rcases typedMachineReaches_run hReach with ⟨t, ht⟩
  exact ⟨t, by rw [ht]; exact hState, by rw [ht]; exact hScore⟩

theorem typedMachineReaches_attainableLowerBound {State : Type*} [Fintype State]
    {M : TypedMachine State} {start : State}
    {haltCfg : TypedConfig State} {positions : Tape}
    (hReach : TypedMachineReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig State)
      haltCfg)
    (hState : haltCfg.state = none)
    (hPositions : positions.Nodup)
    (hRead : ∀ pos, pos ∈ positions -> Tape.read haltCfg.tape pos = true) :
    ∃ score, positions.length ≤ score ∧
      AttainableScore (Fintype.card State) score := by
  rcases typedMachineReaches_run hReach with ⟨t, ht⟩
  have hTapeNodup : haltCfg.tape.Nodup := by
    rw [← ht]
    exact TypedMachine.run_tape_nodup M start t
  have hLower := positions_length_le_tape_length_of_read_true hPositions hTapeNodup hRead
  have hHalt : M.HaltsWithScore start haltCfg.tape.length :=
    typedMachineReaches_haltsWithScore hReach hState rfl
  exact ⟨haltCfg.tape.length, hLower, typedMachineToMachine_attainableScore M start hHalt⟩

noncomputable instance instFintypeSum {α β : Type*} [Fintype α] [Fintype β] :
    Fintype (α ⊕ β) := by
  classical
  refine ⟨(Finset.univ.map Function.Embedding.inl) ∪
    (Finset.univ.map Function.Embedding.inr), ?_⟩
  intro x
  cases x <;> simp

theorem fintype_card_sum {α β : Type*} [Fintype α] [Fintype β] :
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β := by
  classical
  change (((Finset.univ : Finset α).map Function.Embedding.inl) ∪
      ((Finset.univ : Finset β).map Function.Embedding.inr)).card =
    Fintype.card α + Fintype.card β
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_map, Finset.card_map, Finset.card_univ, Finset.card_univ]
  · rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_map] at hx hx2
    rcases hx with ⟨a, _ha, rfl⟩
    rcases hx2 with ⟨b, _hb, h⟩
    cases h

/--
The finite Rado tape obtained by writing the first `k` bits of `input` at
positions `0, ..., k - 1`, in the order produced by the initializer.
-/
def initInputTape (input : List Bool) : Nat -> Tape
  | 0 => []
  | k + 1 => Tape.write (initInputTape input k) (k : Int) (input.getI k)

@[simp]
theorem initInputTape_zero (input : List Bool) :
    initInputTape input 0 = [] := rfl

@[simp]
theorem initInputTape_succ (input : List Bool) (k : Nat) :
    initInputTape input (k + 1) =
      Tape.write (initInputTape input k) (k : Int) (input.getI k) := rfl

theorem initInputTape_read_nat (input : List Bool) :
    ∀ k j : Nat,
      Tape.read (initInputTape input k) (j : Int) =
        if j < k then input.getI j else false
  | 0, _j => by simp [initInputTape, Tape.read]
  | k + 1, j => by
      rw [initInputTape_succ]
      by_cases hEq : j = k
      · subst j
        simp
      · rw [Tape.read_write_of_ne]
        · rw [initInputTape_read_nat input k j]
          have hjIff : j < k + 1 ↔ j < k := by omega
          by_cases hjk : j < k
          · have hjsk : j < k + 1 := hjIff.2 hjk
            simp [hjk, hjsk]
          · have hjsk : ¬ j < k + 1 := fun h => hjk (hjIff.1 h)
            simp [hjk, hjsk]
        · exact_mod_cast hEq

theorem initInputTape_read_neg (input : List Bool) :
    ∀ k n : Nat,
      Tape.read (initInputTape input k) (Int.negSucc n) = false
  | 0, _n => by simp [initInputTape, Tape.read]
  | k + 1, n => by
      rw [initInputTape_succ]
      rw [Tape.read_write_of_ne]
      · exact initInputTape_read_neg input k n
      · omega

/-- After all input bits are written, the Rado tape matches mathlib's `TM0.init` tape. -/
theorem initInputTape_matches_tm0_init {Label : Type*} [Inhabited Label]
    (input : List Bool) :
    RadoMatchesTuringTape 0 (initInputTape input input.length)
      (Turing.TM0.init (Λ := Label) input).Tape := by
  intro i
  cases i with
  | ofNat j =>
      rw [zero_add]
      change Tape.read (initInputTape input input.length) (j : Int) =
        (Turing.TM0.init (Λ := Label) input).Tape.nth (j : Int)
      rw [initInputTape_read_nat]
      by_cases hj : j < input.length
      · rw [if_pos hj]
        simp [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂]
      · rw [if_neg hj]
        have hle : input.length ≤ j := Nat.le_of_not_gt hj
        have hgetDefault : input.getI j = (default : Bool) := by
          rw [List.getI_eq_default _ hle]
        have hget : input.getI j = false := by
          simpa using hgetDefault
        simp [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂, hget]
  | negSucc j =>
      rw [zero_add]
      rw [initInputTape_read_neg]
      simp [Turing.TM0.init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.nth]

/--
State space for a typed Rado machine that first writes a nonempty Bool input
and returns to the origin, then hands control to the usual `TM0` simulator.

The two `Fin input.length` summands are the write-right and return-left phases;
the final summand is the already-proved simulator state space.
-/
abbrev InitThenTM0State (Label : Type*) (input : List Bool) :=
  (Fin input.length ⊕ Fin input.length) ⊕ TM0RadoState Label

/--
Typed Rado wrapper that initializes the tape with `input` before running the
standard typed-Rado simulation of a Bool `TM0` machine.
-/
def initThenTM0ToTypedRado {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) (input : List Bool) :
    TypedMachine (InitThenTM0State Label input) where
  transition state bit :=
    match state with
    | Sum.inl (Sum.inl i) =>
        let out := input.get ⟨i.val, i.isLt⟩
        if hNext : i.val + 1 < input.length then
          { write := out, move := Move.right,
            next := some (Sum.inl (Sum.inl ⟨i.val + 1, hNext⟩)) }
        else
          { write := out, move := Move.right,
            next := some (Sum.inl (Sum.inr i)) }
    | Sum.inl (Sum.inr r) =>
        if r.val = 0 then
          { write := bit, move := Move.left,
            next := some (Sum.inr (TM0RadoState.normal (default : Label))) }
        else
          { write := bit, move := Move.left,
            next := some (Sum.inl (Sum.inr
              ⟨r.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩)) }
    | Sum.inr simState =>
        let action := (tm0ToTypedRado M).transition simState bit
        { write := action.write, move := action.move, next := action.next.map Sum.inr }

/-- Embed a plain `TM0`-simulator Rado configuration into the wrapper machine. -/
def liftSimCfg {Label : Type*} {input : List Bool}
    (cfg : TypedConfig (TM0RadoState Label)) :
    TypedConfig (InitThenTM0State Label input) where
  state := cfg.state.map Sum.inr
  head := cfg.head
  tape := cfg.tape

@[simp]
theorem liftSimCfg_step {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) (input : List Bool)
    (cfg : TypedConfig (TM0RadoState Label)) :
    TypedMachine.step (initThenTM0ToTypedRado M input) (liftSimCfg cfg) =
      liftSimCfg (TypedMachine.step (tm0ToTypedRado M) cfg) := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some simState =>
          cases simState <;> rfl

theorem liftSimCfg_reaches {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) (input : List Bool)
    {cfg cfg' : TypedConfig (TM0RadoState Label)}
    (h : TypedRadoReaches (tm0ToTypedRado M) cfg cfg') :
    TypedMachineReaches (initThenTM0ToTypedRado M input)
      (liftSimCfg cfg) (liftSimCfg cfg') := by
  unfold TypedRadoReaches at h
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a c hStep _hRest IH
    have hStepLift : liftSimCfg c =
        TypedMachine.step (initThenTM0ToTypedRado M input) (liftSimCfg a) := by
      rw [hStep]
      rw [liftSimCfg_step]
    exact Relation.ReflTransGen.head hStepLift IH

/-- Start configuration for the nonempty-input initializer. -/
abbrev initThenTM0Start {Label : Type*} {input : List Bool}
    (hInput : 0 < input.length) :
    TypedConfig (InitThenTM0State Label input) :=
  ({ state := some (Sum.inl (Sum.inl (⟨0, hInput⟩ : Fin input.length))),
      head := 0, tape := [] } : TypedConfig (InitThenTM0State Label input))

/-- Write-phase configuration after the first `k` input bits have been written. -/
abbrev initThenTM0WriteCfg {Label : Type*} (input : List Bool) (k : Nat)
    (hk : k < input.length) : TypedConfig (InitThenTM0State Label input) :=
  ({ state := some (Sum.inl (Sum.inl (⟨k, hk⟩ : Fin input.length))),
      head := (k : Int), tape := initInputTape input k } :
    TypedConfig (InitThenTM0State Label input))

/-- Return-phase configuration, moving left over the initialized input tape. -/
abbrev initThenTM0ReturnCfg {Label : Type*} (input : List Bool) (k : Nat)
    (hk : k < input.length) : TypedConfig (InitThenTM0State Label input) :=
  ({ state := some (Sum.inl (Sum.inr (⟨k, hk⟩ : Fin input.length))),
      head := ((k + 1 : Nat) : Int), tape := initInputTape input input.length } :
    TypedConfig (InitThenTM0State Label input))

/-- Wrapper configuration immediately after initialization, just before TM0 simulation. -/
abbrev initThenTM0SimInitCfg {Label : Type*} [Inhabited Label] (input : List Bool) :
    TypedConfig (InitThenTM0State Label input) :=
  let cfg : TypedConfig (TM0RadoState Label) :=
    { state := some (TM0RadoState.normal (default : Label))
      head := (0 : Int)
      tape := initInputTape input input.length }
  liftSimCfg cfg

theorem initThenTM0_write_reaches {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {input : List Bool}
    (hInput : 0 < input.length) :
    ∀ k (hk : k < input.length),
      TypedMachineReaches (initThenTM0ToTypedRado M input)
        (initThenTM0Start (Label := Label) hInput)
        (initThenTM0WriteCfg (Label := Label) input k hk)
  | 0, _hk => by
      exact Relation.ReflTransGen.refl
  | k + 1, hk => by
      have hkPrev : k < input.length := by omega
      have hPrev := initThenTM0_write_reaches M hInput k hkPrev
      have hStep : initThenTM0WriteCfg (Label := Label) input (k + 1) hk =
          TypedMachine.step (initThenTM0ToTypedRado M input)
            (initThenTM0WriteCfg (Label := Label) input k hkPrev) := by
        simp [initThenTM0WriteCfg, TypedMachine.step, initThenTM0ToTypedRado,
          initInputTape, Move.apply, hk, List.getI_eq_getElem _ hkPrev]
      exact Relation.ReflTransGen.trans hPrev (Relation.ReflTransGen.single hStep)

theorem initThenTM0_return_reaches {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) (input : List Bool) :
    ∀ k (hk : k < input.length),
      TypedMachineReaches (initThenTM0ToTypedRado M input)
        (initThenTM0ReturnCfg (Label := Label) input k hk)
        (initThenTM0SimInitCfg (Label := Label) input)
  | 0, hk => by
      have hStep : initThenTM0SimInitCfg (Label := Label) input =
          TypedMachine.step (initThenTM0ToTypedRado M input)
            (initThenTM0ReturnCfg (Label := Label) input 0 hk) := by
        simp [initThenTM0SimInitCfg, liftSimCfg, TypedMachine.step,
          initThenTM0ToTypedRado, Move.apply, Tape.write_read_self]
      exact Relation.ReflTransGen.single hStep
  | k + 1, hk => by
      have hkPrev : k < input.length := by omega
      have hStep : initThenTM0ReturnCfg (Label := Label) input k hkPrev =
          TypedMachine.step (initThenTM0ToTypedRado M input)
            (initThenTM0ReturnCfg (Label := Label) input (k + 1) hk) := by
        simp [initThenTM0ReturnCfg, TypedMachine.step, initThenTM0ToTypedRado, Move.apply,
          Tape.write_read_self]
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hStep)
        (initThenTM0_return_reaches M input k hkPrev)

/-- The initializer reaches the simulator's normal start state with `TM0.init input` on tape. -/
theorem initThenTM0_reaches_sim_init {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {input : List Bool}
    (hInput : 0 < input.length) :
    TypedMachineReaches (initThenTM0ToTypedRado M input)
      (initThenTM0Start (Label := Label) hInput)
      (initThenTM0SimInitCfg (Label := Label) input) := by
  let last := input.length - 1
  have hLast : last < input.length := by
    dsimp [last]
    omega
  have hLastSucc : last + 1 = input.length := by
    dsimp [last]
    omega
  have hWrite := initThenTM0_write_reaches M hInput last hLast
  have hStep : initThenTM0ReturnCfg (Label := Label) input last hLast =
      TypedMachine.step (initThenTM0ToTypedRado M input)
        (initThenTM0WriteCfg (Label := Label) input last hLast) := by
    have hNoNext : ¬ last + 1 < input.length := by omega
    simp [initThenTM0ReturnCfg, TypedMachine.step, initThenTM0ToTypedRado, Move.apply,
      hNoNext]
    have hGet : input.getI last = input[last] := by
      rw [List.getI_eq_getElem _ hLast]
    rw [← hGet]
    conv_lhs => rw [← hLastSucc, initInputTape_succ]
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans hWrite (Relation.ReflTransGen.single hStep))
    (initThenTM0_return_reaches M input last hLast)

/-- `TM0RadoState Label` is two tagged copies of `Label`. -/
def tm0RadoStateEquivProd (Label : Type*) : Bool × Label ≃ TM0RadoState Label where
  toFun
    | (false, q) => TM0RadoState.normal q
    | (true, q) => TM0RadoState.writeReturn q
  invFun
    | TM0RadoState.normal q => (false, q)
    | TM0RadoState.writeReturn q => (true, q)
  left_inv := by
    intro x
    cases x with
    | mk tag q => cases tag <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

instance tm0RadoStateFintype (Label : Type*) [Fintype Label] :
    Fintype (TM0RadoState Label) :=
  Fintype.ofEquiv (Bool × Label) (tm0RadoStateEquivProd Label)

theorem tm0RadoState_card (Label : Type*) [Fintype Label] :
    Fintype.card (TM0RadoState Label) = 2 * Fintype.card Label := by
  have h := Fintype.card_congr (tm0RadoStateEquivProd Label)
  rw [← h]
  simp [Fintype.card_prod]

theorem initThenTM0State_card (Label : Type*) [Fintype Label] (input : List Bool) :
    Fintype.card (InitThenTM0State Label input) =
      2 * input.length + Fintype.card (TM0RadoState Label) := by
  rw [fintype_card_sum, fintype_card_sum]
  simp [Nat.two_mul, Nat.add_assoc]

theorem tm0ToTypedRado_attainableScore {Label : Type*} [Inhabited Label] [Fintype Label]
    (M : Turing.TM0.Machine Bool Label) {score : Nat}
    (hHalt : (tm0ToTypedRado M).HaltsWithScore
      (TM0RadoState.normal (default : Label)) score) :
    AttainableScore (Fintype.card (TM0RadoState Label)) score :=
  typedMachineToMachine_attainableScore (tm0ToTypedRado M)
    (TM0RadoState.normal (default : Label)) hHalt

theorem typedRadoReaches_attainableLowerBound {Label : Type*} [Fintype Label]
    {M : TypedMachine (TM0RadoState Label)} {start : TM0RadoState Label}
    {haltCfg : TypedConfig (TM0RadoState Label)} {positions : Tape}
    (hReach : TypedRadoReaches M
      ({ state := some start, head := 0, tape := [] } : TypedConfig (TM0RadoState Label))
      haltCfg)
    (hState : haltCfg.state = none)
    (hPositions : positions.Nodup)
    (hRead : ∀ pos, pos ∈ positions -> Tape.read haltCfg.tape pos = true) :
    ∃ score, positions.length ≤ score ∧
      AttainableScore (Fintype.card (TM0RadoState Label)) score := by
  rcases typedRadoReaches_run hReach with ⟨t, ht⟩
  have hTapeNodup : haltCfg.tape.Nodup := by
    rw [← ht]
    exact TypedMachine.run_tape_nodup M start t
  have hLower := positions_length_le_tape_length_of_read_true hPositions hTapeNodup hRead
  have hHalt : M.HaltsWithScore start haltCfg.tape.length :=
    typedRadoReaches_haltsWithScore hReach hState rfl
  exact ⟨haltCfg.tape.length, hLower, typedMachineToMachine_attainableScore M start hHalt⟩

theorem tm0ToTypedRado_step_move {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {q q' : Label} {T : Turing.Tape Bool} {dir : Turing.Dir}
    {head : Int} {tape : Tape}
    (hM : M q T.head = some (q', Turing.TM0.Stmt.move dir))
    (hTape : RadoMatchesTuringTape head tape T) :
    TM0RadoNormalRel
      ({ q := q', Tape := T.move dir } : Turing.TM0.Cfg Bool Label)
      (TypedMachine.step (tm0ToTypedRado M)
        ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
          TypedConfig (TM0RadoState Label))) := by
  have hHead : Tape.read tape head = T.head := by
    simpa using hTape 0
  have hTapeNoop : RadoMatchesTuringTape head (Tape.write tape head T.head) T := by
    rw [← hHead, Tape.write_read_self]
    exact hTape
  constructor
  · cases dir <;>
      simp [TypedMachine.step, tm0ToTypedRado, hHead, hM, radoMoveOfTuringDir]
  · cases dir <;>
      simp [TypedMachine.step, tm0ToTypedRado, hHead, hM, radoMoveOfTuringDir]
    · exact radoMatchesTuringTape_move_left hTapeNoop
    · exact radoMatchesTuringTape_move_right hTapeNoop

theorem tm0ToTypedRado_step_write {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {q q' : Label} {T : Turing.Tape Bool} {out : Bool}
    {head : Int} {tape : Tape}
    (hM : M q T.head = some (q', Turing.TM0.Stmt.write out))
    (hTape : RadoMatchesTuringTape head tape T) :
    TM0RadoNormalRel
      ({ q := q', Tape := T.write out } : Turing.TM0.Cfg Bool Label)
      (TypedMachine.step (tm0ToTypedRado M)
        (TypedMachine.step (tm0ToTypedRado M)
          ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
            TypedConfig (TM0RadoState Label)))) := by
  have hHead : Tape.read tape head = T.head := by
    simpa using hTape 0
  have hWrite : RadoMatchesTuringTape head (Tape.write tape head out) (T.write out) :=
    radoMatchesTuringTape_write hTape
  have hRight : RadoMatchesTuringTape (head + 1) (Tape.write tape head out)
      ((T.write out).move Turing.Dir.right) :=
    radoMatchesTuringTape_move_right hWrite
  have hLeft := radoMatchesTuringTape_move_left hRight
  constructor
  · simp [TypedMachine.step, tm0ToTypedRado, hHead, hM]
  · simp [TypedMachine.step, tm0ToTypedRado, hHead, hM]
    change RadoMatchesTuringTape (head + 1 - 1) (Tape.write tape head out) (T.write out)
    simpa using hLeft

theorem tm0ToTypedRado_step_normal_explicit {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {q : Label} {T : Turing.Tape Bool} {c' : Turing.TM0.Cfg Bool Label}
    {head : Int} {tape : Tape}
    (hStep : c' ∈ Turing.TM0.step M ({ q := q, Tape := T } : Turing.TM0.Cfg Bool Label))
    (hTape : RadoMatchesTuringTape head tape T) :
    ∃ radoCfg',
      TM0RadoNormalRel c' radoCfg' ∧
      TypedRadoReaches (tm0ToTypedRado M)
        ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
          TypedConfig (TM0RadoState Label))
        radoCfg' := by
  cases hTrans : M q T.head with
  | none =>
      simp [Turing.TM0.step, hTrans] at hStep
  | some p =>
      rcases p with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          have hStepEq :
              ({ q := q', Tape := T.move dir } : Turing.TM0.Cfg Bool Label) = c' := by
            simpa [Turing.TM0.step, hTrans] using hStep
          subst c'
          refine ⟨TypedMachine.step (tm0ToTypedRado M)
              ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
                TypedConfig (TM0RadoState Label)), ?_, ?_⟩
          · exact tm0ToTypedRado_step_move M hTrans hTape
          · exact typedRadoReaches_step (tm0ToTypedRado M) _
      | write out =>
          have hStepEq :
              ({ q := q', Tape := T.write out } : Turing.TM0.Cfg Bool Label) = c' := by
            simpa [Turing.TM0.step, hTrans] using hStep
          subst c'
          refine ⟨TypedMachine.step (tm0ToTypedRado M)
              (TypedMachine.step (tm0ToTypedRado M)
                ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
                  TypedConfig (TM0RadoState Label))), ?_, ?_⟩
          · exact tm0ToTypedRado_step_write M hTrans hTape
          · exact typedRadoReaches_step_step (tm0ToTypedRado M) _

/--
One Bool `TM0` step is simulated by one or two typed Rado steps, preserving the
normal-state simulation relation.
-/
theorem tm0ToTypedRado_step_normal {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {tmCfg tmCfg' : Turing.TM0.Cfg Bool Label}
    {radoCfg : TypedConfig (TM0RadoState Label)}
    (hStep : tmCfg' ∈ Turing.TM0.step M tmCfg)
    (hRel : TM0RadoNormalRel tmCfg radoCfg) :
    ∃ radoCfg',
      TM0RadoNormalRel tmCfg' radoCfg' ∧
      TypedRadoReaches (tm0ToTypedRado M) radoCfg radoCfg' := by
  cases tmCfg with
  | mk q T =>
      cases radoCfg with
      | mk state head tape =>
          rcases hRel with ⟨hState, hTape⟩
          dsimp at hState hTape
          subst state
          exact tm0ToTypedRado_step_normal_explicit M hStep hTape

/--
A finite Bool `TM0` computation is simulated by a finite typed-Rado computation,
again preserving the normal-state relation at the endpoint.
-/
theorem tm0ToTypedRado_reaches_normal {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {tmCfg tmCfg' : Turing.TM0.Cfg Bool Label}
    {radoCfg : TypedConfig (TM0RadoState Label)}
    (hReach : Turing.TM0.Reaches M tmCfg tmCfg')
    (hRel : TM0RadoNormalRel tmCfg radoCfg) :
    ∃ radoCfg',
      TM0RadoNormalRel tmCfg' radoCfg' ∧
      TypedRadoReaches (tm0ToTypedRado M) radoCfg radoCfg' := by
  change Relation.ReflTransGen (fun a b => b ∈ Turing.TM0.step M a) tmCfg tmCfg' at hReach
  refine (Relation.ReflTransGen.head_induction_on
    (motive := fun a _ =>
      ∀ radoCfg : TypedConfig (TM0RadoState Label),
        TM0RadoNormalRel a radoCfg ->
          ∃ radoCfg',
            TM0RadoNormalRel tmCfg' radoCfg' ∧
            TypedRadoReaches (tm0ToTypedRado M) radoCfg radoCfg')
    hReach ?_ ?_) radoCfg hRel
  · intro radoCfg hRel
    exact ⟨radoCfg, hRel, Relation.ReflTransGen.refl⟩
  · intro _current _next hStep _hRest IH radoCfg hRel
    rcases tm0ToTypedRado_step_normal M hStep hRel with
      ⟨radoMid, hMidRel, hRadoStep⟩
    rcases IH radoMid hMidRel with ⟨radoEnd, hEndRel, hRadoRest⟩
    exact ⟨radoEnd, hEndRel, Relation.ReflTransGen.trans hRadoStep hRadoRest⟩

/-- A terminal Bool `TM0` configuration is simulated by one final Rado halt step. -/
theorem tm0ToTypedRado_halt_explicit {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {q : Label} {T : Turing.Tape Bool} {head : Int} {tape : Tape}
    (hM : M q T.head = none)
    (hTape : RadoMatchesTuringTape head tape T) :
    ∃ haltCfg : TypedConfig (TM0RadoState Label),
      haltCfg.state = none ∧
      haltCfg.tape = tape ∧
      TypedRadoReaches (tm0ToTypedRado M)
        ({ state := some (TM0RadoState.normal q), head := head, tape := tape } :
          TypedConfig (TM0RadoState Label))
        haltCfg := by
  have hHead : Tape.read tape head = T.head := by
    simpa using hTape 0
  let startCfg : TypedConfig (TM0RadoState Label) :=
    { state := some (TM0RadoState.normal q), head := head, tape := tape }
  refine ⟨TypedMachine.step (tm0ToTypedRado M) startCfg, ?_, ?_, ?_⟩
  · simp [startCfg, TypedMachine.step, tm0ToTypedRado, hHead, hM]
  · simp [startCfg, TypedMachine.step, tm0ToTypedRado, hHead, hM]
    rw [← hHead, Tape.write_read_self]
  · exact typedRadoReaches_step (tm0ToTypedRado M) startCfg

theorem tm0ToTypedRado_halt_normal {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {tmCfg : Turing.TM0.Cfg Bool Label}
    {radoCfg : TypedConfig (TM0RadoState Label)}
    (hTerminal : Turing.TM0.step M tmCfg = none)
    (hRel : TM0RadoNormalRel tmCfg radoCfg) :
    ∃ haltCfg : TypedConfig (TM0RadoState Label),
      haltCfg.state = none ∧
      haltCfg.tape = radoCfg.tape ∧
      TypedRadoReaches (tm0ToTypedRado M) radoCfg haltCfg := by
  cases tmCfg with
  | mk q T =>
      cases radoCfg with
      | mk state head tape =>
          rcases hRel with ⟨hState, hTape⟩
          dsimp at hState hTape
          subst state
          have hM : M q T.head = none := by
            simpa [Turing.TM0.step] using hTerminal
          exact tm0ToTypedRado_halt_explicit M hM hTape

/--
If a Bool `TM0` run reaches a terminal configuration, the typed Rado simulator
reaches a halted configuration with the same final Rado tape.
-/
theorem tm0ToTypedRado_reaches_halt_normal {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {tmCfg tmCfg' : Turing.TM0.Cfg Bool Label}
    {radoCfg : TypedConfig (TM0RadoState Label)}
    (hReach : Turing.TM0.Reaches M tmCfg tmCfg')
    (hTerminal : Turing.TM0.step M tmCfg' = none)
    (hRel : TM0RadoNormalRel tmCfg radoCfg) :
    ∃ normalCfg haltCfg : TypedConfig (TM0RadoState Label),
      TM0RadoNormalRel tmCfg' normalCfg ∧
      haltCfg.state = none ∧
      haltCfg.tape = normalCfg.tape ∧
      TypedRadoReaches (tm0ToTypedRado M) radoCfg haltCfg := by
  rcases tm0ToTypedRado_reaches_normal M hReach hRel with
    ⟨normalCfg, hNormalRel, hRadoReach⟩
  rcases tm0ToTypedRado_halt_normal M hTerminal hNormalRel with
    ⟨haltCfg, hHaltState, hHaltTape, hRadoHalt⟩
  exact ⟨normalCfg, haltCfg, hNormalRel, hHaltState, hHaltTape,
    Relation.ReflTransGen.trans hRadoReach hRadoHalt⟩

theorem tm0_eval_mem_terminal {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label)
    {input : List Bool} {output : Turing.ListBlank Bool}
    (hEval : output ∈ Turing.TM0.eval M input) :
    ∃ finalCfg : Turing.TM0.Cfg Bool Label,
      Turing.TM0.Reaches M (Turing.TM0.init input) finalCfg ∧
      Turing.TM0.step M finalCfg = none ∧
      finalCfg.Tape.right₀ = output := by
  rw [Turing.TM0.eval, Part.mem_map_iff] at hEval
  rcases hEval with ⟨finalCfg, hFinal, hOutput⟩
  rcases StateTransition.mem_eval.1 hFinal with ⟨hReach, hTerminal⟩
  exact ⟨finalCfg, hReach, hTerminal, hOutput⟩

theorem tm0RadoNormalRel_init_nil {Label : Type*} [Inhabited Label] :
    TM0RadoNormalRel (Turing.TM0.init ([] : List Bool))
      ({ state := some (TM0RadoState.normal (default : Label)), head := 0, tape := [] } :
        TypedConfig (TM0RadoState Label)) := by
  constructor
  · rfl
  · intro i
    simp [Tape.read, Turing.TM0.init]
    cases i with
    | ofNat n =>
        cases n <;> simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk',
          Turing.Tape.nth]
    | negSucc n =>
        simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.nth]

/--
Extract the terminal configuration behind a blank-input Bool `TM0.eval` result
and transport it to a halted finite Rado machine.  The theorem keeps the final
tape relation explicit; later output-normalization lemmas can identify the
actual busy-beaver score with the intended output value.
-/
theorem tm0_eval_nil_to_rado_halt {Label : Type*} [Inhabited Label] [Fintype Label]
    (M : Turing.TM0.Machine Bool Label)
    {output : Turing.ListBlank Bool}
    (hEval : output ∈ Turing.TM0.eval M ([] : List Bool)) :
    ∃ finalCfg : Turing.TM0.Cfg Bool Label,
    ∃ normalCfg haltCfg : TypedConfig (TM0RadoState Label),
      finalCfg.Tape.right₀ = output ∧
      TM0RadoNormalRel finalCfg normalCfg ∧
      haltCfg.state = none ∧
      haltCfg.tape = normalCfg.tape ∧
      (tm0ToTypedRado M).HaltsWithScore
        (TM0RadoState.normal (default : Label)) haltCfg.tape.length ∧
      AttainableScore (Fintype.card (TM0RadoState Label)) haltCfg.tape.length := by
  rcases tm0_eval_mem_terminal M hEval with ⟨finalCfg, hReach, hTerminal, hOutput⟩
  rcases tm0ToTypedRado_reaches_halt_normal M hReach hTerminal
      (tm0RadoNormalRel_init_nil (Label := Label)) with
    ⟨normalCfg, haltCfg, hNormalRel, hHaltState, hHaltTape, hRadoReach⟩
  have hTypedHalt : (tm0ToTypedRado M).HaltsWithScore
      (TM0RadoState.normal (default : Label)) haltCfg.tape.length :=
    typedRadoReaches_haltsWithScore hRadoReach hHaltState rfl
  exact ⟨finalCfg, normalCfg, haltCfg, hOutput, hNormalRel, hHaltState, hHaltTape,
    hTypedHalt, tm0ToTypedRado_attainableScore M hTypedHalt⟩

/-- The supported subtype is inhabited because `TM0.Supports` contains the start label. -/
@[reducible]
noncomputable def tm0SupportedInhabited {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S) : Inhabited S :=
  ⟨⟨default, hSupp.1⟩⟩

/-- Restrict a Bool `TM0` machine to a supporting set of labels. -/
noncomputable def tm0SupportedMachine {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S) :
    @Turing.TM0.Machine Bool S (tm0SupportedInhabited M hSupp) :=
  fun q bit => by
    classical
    exact (M q.1 bit).map fun p =>
      let q' : S :=
        if hp : p ∈ M q.1 bit then
          ⟨p.1, hSupp.2 hp q.2⟩
        else
          ⟨default, hSupp.1⟩
      (q', p.2)

theorem tm0SupportedMachine_apply_none {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {q : S} {bit : Bool}
    (h : M q.1 bit = none) :
    tm0SupportedMachine M hSupp q bit = none := by
  classical
  simp [tm0SupportedMachine, h]

theorem tm0SupportedMachine_apply_some {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {q : S} {bit : Bool} {q' : Label} {stmt : Turing.TM0.Stmt Bool}
    (h : M q.1 bit = some (q', stmt)) :
    ∃ hq' : q' ∈ S,
      tm0SupportedMachine M hSupp q bit = some (⟨q', hq'⟩, stmt) := by
  classical
  have hp : (q', stmt) ∈ M q.1 bit := by
    rw [h]
    rfl
  refine ⟨hSupp.2 hp q.2, ?_⟩
  simp [tm0SupportedMachine, h]

/-- Forget the supported-subtype label of a restricted configuration. -/
def tm0SupportedCfgToCfg {Label : Type*} {S : Set Label}
    (cfg : Turing.TM0.Cfg Bool S) : Turing.TM0.Cfg Bool Label where
  q := cfg.q.1
  Tape := cfg.Tape

@[simp]
theorem tm0SupportedCfgToCfg_init {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S) (input : List Bool) :
    tm0SupportedCfgToCfg
        (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input) =
      Turing.TM0.init input := by
  rfl

@[simp]
theorem tm0SupportedMachine_step {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    (cfg : Turing.TM0.Cfg Bool S) :
    Option.map tm0SupportedCfgToCfg
        (@Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
          (tm0SupportedMachine M hSupp) cfg) =
      Turing.TM0.step M (tm0SupportedCfgToCfg cfg) := by
  classical
  cases cfg with
  | mk q T =>
      cases hTrans : M q.1 T.head with
      | none =>
          simp [Turing.TM0.step, tm0SupportedCfgToCfg,
            tm0SupportedMachine_apply_none M hSupp hTrans, hTrans]
      | some p =>
          rcases p with ⟨q', stmt⟩
          rcases tm0SupportedMachine_apply_some M hSupp hTrans with ⟨_hq', hRestrict⟩
          cases stmt <;>
            simp [Turing.TM0.step, tm0SupportedCfgToCfg, hTrans, hRestrict]

/-- Restrict an original configuration whose label is known to lie in the support. -/
def tm0CfgRestrict {Label : Type*} {S : Set Label}
    (cfg : Turing.TM0.Cfg Bool Label) (h : cfg.q ∈ S) : Turing.TM0.Cfg Bool S where
  q := ⟨cfg.q, h⟩
  Tape := cfg.Tape

@[simp]
theorem tm0SupportedCfgToCfg_restrict {Label : Type*} {S : Set Label}
    (cfg : Turing.TM0.Cfg Bool Label) (h : cfg.q ∈ S) :
    tm0SupportedCfgToCfg (tm0CfgRestrict cfg h) = cfg := by
  cases cfg
  rfl

theorem tm0SupportedMachine_step_of_original {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {cfg cfg' : Turing.TM0.Cfg Bool Label}
    (hStep : cfg' ∈ Turing.TM0.step M cfg)
    (hCfg : cfg.q ∈ S) :
    ∃ hCfg' : cfg'.q ∈ S,
      @Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
          (tm0SupportedMachine M hSupp) (tm0CfgRestrict cfg hCfg) =
        some (tm0CfgRestrict cfg' hCfg') := by
  cases cfg with
  | mk q T =>
      cases hTrans : M q T.head with
      | none =>
          simp [Turing.TM0.step, hTrans] at hStep
      | some p =>
          rcases p with ⟨q', stmt⟩
          have hp : (q', stmt) ∈ M q T.head := by
            rw [hTrans]
            rfl
          have hq' : q' ∈ S := hSupp.2 hp hCfg
          rcases tm0SupportedMachine_apply_some M hSupp (q := ⟨q, hCfg⟩) hTrans with
            ⟨_hq'', hRestrict⟩
          cases stmt with
          | move dir =>
              have hStepEq :
                  ({ q := q', Tape := T.move dir } : Turing.TM0.Cfg Bool Label) = cfg' := by
                simpa [Turing.TM0.step, hTrans] using hStep
              subst cfg'
              refine ⟨hq', ?_⟩
              simp [Turing.TM0.step, tm0CfgRestrict, hRestrict]
          | write out =>
              have hStepEq :
                  ({ q := q', Tape := T.write out } : Turing.TM0.Cfg Bool Label) = cfg' := by
                simpa [Turing.TM0.step, hTrans] using hStep
              subst cfg'
              refine ⟨hq', ?_⟩
              simp [Turing.TM0.step, tm0CfgRestrict, hRestrict]

theorem tm0SupportedMachine_reaches_of_original {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {cfg cfg' : Turing.TM0.Cfg Bool Label}
    (hReach : Turing.TM0.Reaches M cfg cfg')
    (hCfg : cfg.q ∈ S) :
    ∃ hCfg' : cfg'.q ∈ S,
      @Turing.TM0.Reaches Bool S (tm0SupportedInhabited M hSupp) inferInstance
        (tm0SupportedMachine M hSupp)
        (tm0CfgRestrict cfg hCfg) (tm0CfgRestrict cfg' hCfg') := by
  change Relation.ReflTransGen (fun a b => b ∈ Turing.TM0.step M a) cfg cfg' at hReach
  refine (Relation.ReflTransGen.head_induction_on
    (motive := fun a _ =>
      ∀ hA : a.q ∈ S,
        ∃ hB : cfg'.q ∈ S,
          @Turing.TM0.Reaches Bool S (tm0SupportedInhabited M hSupp) inferInstance
            (tm0SupportedMachine M hSupp)
            (tm0CfgRestrict a hA) (tm0CfgRestrict cfg' hB))
    hReach ?_ ?_) hCfg
  · intro hA
    exact ⟨hA, Relation.ReflTransGen.refl⟩
  · intro current next hStep _hRest IH hCurrent
    rcases tm0SupportedMachine_step_of_original M hSupp hStep hCurrent with
      ⟨hNext, hRestrictStep⟩
    rcases IH hNext with ⟨hFinal, hRestrictRest⟩
    have hStepMem : tm0CfgRestrict next hNext ∈
        @Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
          (tm0SupportedMachine M hSupp) (tm0CfgRestrict current hCurrent) := by
      rw [hRestrictStep]
      rfl
    exact ⟨hFinal, Relation.ReflTransGen.head hStepMem hRestrictRest⟩

theorem tm0SupportedMachine_step_none_of_original {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {cfg : Turing.TM0.Cfg Bool Label}
    (hCfg : cfg.q ∈ S)
    (hTerminal : Turing.TM0.step M cfg = none) :
    @Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
        (tm0SupportedMachine M hSupp) (tm0CfgRestrict cfg hCfg) = none := by
  have hForget := tm0SupportedMachine_step M hSupp (tm0CfgRestrict cfg hCfg)
  rw [tm0SupportedCfgToCfg_restrict, hTerminal] at hForget
  cases hStep : @Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
      (tm0SupportedMachine M hSupp) (tm0CfgRestrict cfg hCfg) with
  | none => rfl
  | some _next =>
      simp [hStep] at hForget

theorem tm0SupportedMachine_eval_of_original {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label}
    (hSupp : Turing.TM0.Supports M S)
    {input : List Bool} {output : Turing.ListBlank Bool}
    (hEval : output ∈ Turing.TM0.eval M input) :
    output ∈ @Turing.TM0.eval Bool S (tm0SupportedInhabited M hSupp) inferInstance
      (tm0SupportedMachine M hSupp) input := by
  rcases tm0_eval_mem_terminal M hEval with ⟨finalCfg, hReach, hTerminal, hOutput⟩
  rcases tm0SupportedMachine_reaches_of_original M hSupp hReach hSupp.1 with
    ⟨hFinal, hRestrictReach⟩
  have hRestrictTerminal := tm0SupportedMachine_step_none_of_original M hSupp hFinal hTerminal
  have hInitEq : tm0CfgRestrict (Turing.TM0.init input) hSupp.1 =
      (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input) := rfl
  rw [hInitEq] at hRestrictReach
  change StateTransition.Reaches
      (@Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
        (tm0SupportedMachine M hSupp))
      (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input)
      (tm0CfgRestrict finalCfg hFinal) at hRestrictReach
  have hEvalFinal : tm0CfgRestrict finalCfg hFinal ∈
      StateTransition.eval
        (@Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
          (tm0SupportedMachine M hSupp))
        (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input) :=
    StateTransition.mem_eval.2 ⟨hRestrictReach, hRestrictTerminal⟩
  change output ∈ (StateTransition.eval
      (@Turing.TM0.step Bool S (tm0SupportedInhabited M hSupp) inferInstance
        (tm0SupportedMachine M hSupp))
      (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input)).map
        (fun c => c.Tape.right₀)
  rw [Part.mem_map_iff]
  refine ⟨tm0CfgRestrict finalCfg hFinal, hEvalFinal, ?_⟩
  simpa [tm0CfgRestrict] using hOutput

theorem tm0_supported_eval_nil_to_rado_halt {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label} [Fintype S]
    (hSupp : Turing.TM0.Supports M S)
    {output : Turing.ListBlank Bool}
    (hEval : output ∈ Turing.TM0.eval M ([] : List Bool)) :
    ∃ finalCfg : Turing.TM0.Cfg Bool S,
    ∃ normalCfg haltCfg : TypedConfig (TM0RadoState S),
      finalCfg.Tape.right₀ = output ∧
      TM0RadoNormalRel finalCfg normalCfg ∧
      haltCfg.state = none ∧
      haltCfg.tape = normalCfg.tape ∧
      (@tm0ToTypedRado S (tm0SupportedInhabited M hSupp)
        (tm0SupportedMachine M hSupp)).HaltsWithScore
        (TM0RadoState.normal (@default S (tm0SupportedInhabited M hSupp)))
        haltCfg.tape.length ∧
      AttainableScore (Fintype.card (TM0RadoState S)) haltCfg.tape.length := by
  letI : Inhabited S := tm0SupportedInhabited M hSupp
  exact tm0_eval_nil_to_rado_halt (tm0SupportedMachine M hSupp)
    (tm0SupportedMachine_eval_of_original M hSupp hEval)

/--
General input-initializer handoff: once a typed Rado prefix reaches a
configuration matching `TM0.init input`, any supported Bool `TM0` evaluation on
that input yields a halted finite Rado machine.
-/
theorem tm0_supported_eval_to_rado_halt_of_initial_reaches {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label} [Fintype S]
    (hSupp : Turing.TM0.Supports M S)
    {input : List Bool} {output : Turing.ListBlank Bool}
    {initCfg : TypedConfig (TM0RadoState S)}
    (hEval : output ∈ Turing.TM0.eval M input)
    (hInitRel : TM0RadoNormalRel
      (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input)
      initCfg)
    (hInitReach : TypedRadoReaches
      (@tm0ToTypedRado S (tm0SupportedInhabited M hSupp) (tm0SupportedMachine M hSupp))
      ({ state := some (TM0RadoState.normal (@default S (tm0SupportedInhabited M hSupp))),
          head := 0, tape := [] } : TypedConfig (TM0RadoState S))
      initCfg) :
    ∃ finalCfg : Turing.TM0.Cfg Bool S,
    ∃ normalCfg haltCfg : TypedConfig (TM0RadoState S),
      finalCfg.Tape.right₀ = output ∧
      TM0RadoNormalRel finalCfg normalCfg ∧
      haltCfg.state = none ∧
      haltCfg.tape = normalCfg.tape ∧
      (@tm0ToTypedRado S (tm0SupportedInhabited M hSupp)
        (tm0SupportedMachine M hSupp)).HaltsWithScore
        (TM0RadoState.normal (@default S (tm0SupportedInhabited M hSupp)))
        haltCfg.tape.length ∧
      AttainableScore (Fintype.card (TM0RadoState S)) haltCfg.tape.length := by
  letI : Inhabited S := tm0SupportedInhabited M hSupp
  have hEvalRestrict := tm0SupportedMachine_eval_of_original M hSupp hEval
  rcases tm0_eval_mem_terminal (tm0SupportedMachine M hSupp) hEvalRestrict with
    ⟨finalCfg, hReach, hTerminal, hOutput⟩
  rcases tm0ToTypedRado_reaches_halt_normal (tm0SupportedMachine M hSupp)
      hReach hTerminal hInitRel with
    ⟨normalCfg, haltCfg, hNormalRel, hHaltState, hHaltTape, hRadoReach⟩
  have hReachFromBlank : TypedRadoReaches
      (tm0ToTypedRado (tm0SupportedMachine M hSupp))
      ({ state := some (TM0RadoState.normal (default : S)), head := 0, tape := [] } :
        TypedConfig (TM0RadoState S)) haltCfg :=
    Relation.ReflTransGen.trans hInitReach hRadoReach
  have hTypedHalt : (tm0ToTypedRado (tm0SupportedMachine M hSupp)).HaltsWithScore
      (TM0RadoState.normal (default : S)) haltCfg.tape.length :=
    typedRadoReaches_haltsWithScore hReachFromBlank hHaltState rfl
  exact ⟨finalCfg, normalCfg, haltCfg, hOutput, hNormalRel, hHaltState, hHaltTape,
    hTypedHalt, tm0ToTypedRado_attainableScore (tm0SupportedMachine M hSupp) hTypedHalt⟩

/--
Lower-bound variant of `tm0_supported_eval_to_rado_halt_of_initial_reaches`:
if the exposed right output has true bits at all offsets in a nodup list, then
the resulting finite Rado machine has attainable score at least the length of
that list.
-/
theorem tm0_supported_eval_to_rado_lowerBound_of_initial_reaches
    {Label : Type*} [Inhabited Label]
    (M : Turing.TM0.Machine Bool Label) {S : Set Label} [Fintype S]
    (hSupp : Turing.TM0.Supports M S)
    {input : List Bool} {output : Turing.ListBlank Bool}
    {initCfg : TypedConfig (TM0RadoState S)} {offsets : List Nat}
    (hEval : output ∈ Turing.TM0.eval M input)
    (hInitRel : TM0RadoNormalRel
      (@Turing.TM0.init Bool S (tm0SupportedInhabited M hSupp) inferInstance input)
      initCfg)
    (hInitReach : TypedRadoReaches
      (@tm0ToTypedRado S (tm0SupportedInhabited M hSupp) (tm0SupportedMachine M hSupp))
      ({ state := some (TM0RadoState.normal (@default S (tm0SupportedInhabited M hSupp))),
          head := 0, tape := [] } : TypedConfig (TM0RadoState S))
      initCfg)
    (hOffsets : offsets.Nodup)
    (hOutputTrue : ∀ n, n ∈ offsets -> output.nth n = true) :
    ∃ score, offsets.length ≤ score ∧
      AttainableScore (Fintype.card (TM0RadoState S)) score := by
  letI : Inhabited S := tm0SupportedInhabited M hSupp
  have hEvalRestrict := tm0SupportedMachine_eval_of_original M hSupp hEval
  rcases tm0_eval_mem_terminal (tm0SupportedMachine M hSupp) hEvalRestrict with
    ⟨finalCfg, hReach, hTerminal, hOutput⟩
  rcases tm0ToTypedRado_reaches_halt_normal (tm0SupportedMachine M hSupp)
      hReach hTerminal hInitRel with
    ⟨normalCfg, haltCfg, hNormalRel, hHaltState, hHaltTape, hRadoReach⟩
  have hReachFromBlank : TypedRadoReaches
      (tm0ToTypedRado (tm0SupportedMachine M hSupp))
      ({ state := some (TM0RadoState.normal (default : S)), head := 0, tape := [] } :
        TypedConfig (TM0RadoState S)) haltCfg :=
    Relation.ReflTransGen.trans hInitReach hRadoReach
  let positions : Tape := radoPositionsOfNatOffsets normalCfg.head offsets
  have hPositions : positions.Nodup := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_nodup hOffsets
  have hOutputTrueFinal : ∀ n, n ∈ offsets -> finalCfg.Tape.right₀.nth n = true := by
    intro n hn
    rw [hOutput]
    exact hOutputTrue n hn
  have hReadNormal : ∀ pos, pos ∈ positions -> Tape.read normalCfg.tape pos = true := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_read_true hNormalRel.2 hOutputTrueFinal
  have hRead : ∀ pos, pos ∈ positions -> Tape.read haltCfg.tape pos = true := by
    intro pos hpos
    rw [hHaltTape]
    exact hReadNormal pos hpos
  rcases typedRadoReaches_attainableLowerBound hReachFromBlank hHaltState hPositions hRead with
    ⟨score, hLower, hScore⟩
  have hLen : positions.length = offsets.length := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_length normalCfg.head offsets
  refine ⟨score, ?_, hScore⟩
  rw [← hLen]
  exact hLower

/--
Blank-tape wrapper lower-bound bridge: if a finite Bool `TM0` machine evaluates
`input` and its output has true bits at all offsets in a nodup list, then the
typed Rado wrapper that first writes `input` from blank tape attains a score at
least the number of witnessed offsets.
-/
theorem tm0_eval_to_init_wrapper_lowerBound {Label : Type*}
    [Inhabited Label] [Fintype Label]
    (M : Turing.TM0.Machine Bool Label)
    {input : List Bool} (hInput : 0 < input.length)
    {output : Turing.ListBlank Bool} {offsets : List Nat}
    (hEval : output ∈ Turing.TM0.eval M input)
    (hOffsets : offsets.Nodup)
    (hOutputTrue : ∀ n, n ∈ offsets -> output.nth n = true) :
    ∃ score, offsets.length ≤ score ∧
      AttainableScore (Fintype.card (InitThenTM0State Label input)) score := by
  rcases tm0_eval_mem_terminal M hEval with ⟨finalCfg, hReach, hTerminal, hOutput⟩
  let initCfg : TypedConfig (TM0RadoState Label) :=
    { state := some (TM0RadoState.normal (default : Label))
      head := (0 : Int)
      tape := initInputTape input input.length }
  have hInitRel : TM0RadoNormalRel (Turing.TM0.init input) initCfg := by
    constructor
    · rfl
    · exact initInputTape_matches_tm0_init input
  rcases tm0ToTypedRado_reaches_halt_normal M hReach hTerminal hInitRel with
    ⟨normalCfg, haltCfg, hNormalRel, hHaltState, hHaltTape, hRadoReach⟩
  have hInitReach : TypedMachineReaches (initThenTM0ToTypedRado M input)
      (initThenTM0Start (Label := Label) hInput) (liftSimCfg (input := input) initCfg) := by
    simpa [initThenTM0SimInitCfg, initCfg] using initThenTM0_reaches_sim_init M hInput
  have hSimReach : TypedMachineReaches (initThenTM0ToTypedRado M input)
      (liftSimCfg (input := input) initCfg) (liftSimCfg (input := input) haltCfg) :=
    liftSimCfg_reaches M input hRadoReach
  have hFullReach : TypedMachineReaches (initThenTM0ToTypedRado M input)
      (initThenTM0Start (Label := Label) hInput) (liftSimCfg (input := input) haltCfg) :=
    Relation.ReflTransGen.trans hInitReach hSimReach
  let positions : Tape := radoPositionsOfNatOffsets normalCfg.head offsets
  have hPositions : positions.Nodup := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_nodup hOffsets
  have hOutputTrueFinal : ∀ n, n ∈ offsets -> finalCfg.Tape.right₀.nth n = true := by
    intro n hn
    rw [hOutput]
    exact hOutputTrue n hn
  have hReadNormal : ∀ pos, pos ∈ positions -> Tape.read normalCfg.tape pos = true := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_read_true hNormalRel.2 hOutputTrueFinal
  have hRead : ∀ pos, pos ∈ positions ->
      Tape.read (liftSimCfg (input := input) haltCfg).tape pos = true := by
    intro pos hpos
    dsimp [liftSimCfg]
    rw [hHaltTape]
    exact hReadNormal pos hpos
  have hState : (liftSimCfg (input := input) haltCfg).state = none := by
    simp [liftSimCfg, hHaltState]
  rcases typedMachineReaches_attainableLowerBound
      (M := initThenTM0ToTypedRado M input)
      (start := (Sum.inl (Sum.inl (⟨0, hInput⟩ : Fin input.length)) :
        InitThenTM0State Label input))
      (haltCfg := liftSimCfg (input := input) haltCfg)
      (positions := positions) hFullReach hState hPositions hRead with
    ⟨score, hLower, hScore⟩
  have hLen : positions.length = offsets.length := by
    dsimp [positions]
    exact radoPositionsOfNatOffsets_length normalCfg.head offsets
  exact ⟨score, by rwa [hLen] at hLower, hScore⟩

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

/--
In the `PartrecToTM2` stack alphabet, a zero natural contributes no bits, so a
unary list of `m` zeros is exactly `m` separator symbols.
-/
theorem trList_replicate_zero (m : Nat) :
    Turing.PartrecToTM2.trList (List.replicate m 0) =
      List.replicate m Turing.PartrecToTM2.Γ'.cons := by
  induction m with
  | zero => rfl
  | succ m IH =>
      change Turing.PartrecToTM2.Γ'.cons ::
          Turing.PartrecToTM2.trList (List.replicate m 0) =
        Turing.PartrecToTM2.Γ'.cons ::
          List.replicate m Turing.PartrecToTM2.Γ'.cons
      rw [IH]

/-- The encoded unary-zero output stack has length exactly `m`. -/
theorem trList_replicate_zero_length (m : Nat) :
    (Turing.PartrecToTM2.trList (List.replicate m 0)).length = m := by
  rw [trList_replicate_zero]
  simp

private theorem listBlank_nth_mk_replicate {α : Type*} [Inhabited α]
    (x : α) {m i : Nat} (hi : i < m) :
    (Turing.ListBlank.mk (List.replicate m x)).nth i = x := by
  rw [Turing.ListBlank.nth_mk]
  have hiLen : i < (List.replicate m x).length := by
    simpa using hi
  rw [List.getI_eq_getElem _ hiLen]
  simp

/--
If the lowered `TM2 -> TM1` output exposes `m` unary-zero separators on the
source main stack, then each of the first `m` lowered source cells carries a
nonempty main-stack entry.
-/
theorem tm2to1MainOutput_replicate_cons_main_some
    {tm1Output : Turing.ListBlank PartrecToTM1Alphabet} {m i : Nat}
    (h : TM2to1MainOutput tm1Output
      (List.replicate m Turing.PartrecToTM2.Γ'.cons))
    (hi : i < m) :
    (tm1Output.nth i).2 Turing.PartrecToTM2.K'.main =
      some Turing.PartrecToTM2.Γ'.cons := by
  rcases h with ⟨stk, tape, hAdd, hMaps, hMain⟩
  rw [← hAdd]
  rw [Turing.TM2to1.addBottom_nth_snd]
  have hMap := congrArg
    (fun L : Turing.ListBlank (Option Turing.PartrecToTM2.Γ') => L.nth i)
    (hMaps Turing.PartrecToTM2.K'.main)
  rw [Turing.proj_map_nth] at hMap
  refine hMap.trans ?_
  rw [hMain]
  simpa [List.reverse_replicate] using
    (listBlank_nth_mk_replicate (some Turing.PartrecToTM2.Γ'.cons) hi)

/--
The first `m` source cells in the lowered unary-zero output cannot be blank
source symbols.
-/
theorem tm2to1MainOutput_replicate_cons_ne_default
    {tm1Output : Turing.ListBlank PartrecToTM1Alphabet} {m i : Nat}
    (h : TM2to1MainOutput tm1Output
      (List.replicate m Turing.PartrecToTM2.Γ'.cons))
    (hi : i < m) :
    tm1Output.nth i ≠ (default : PartrecToTM1Alphabet) := by
  intro hDefault
  have hSome := tm2to1MainOutput_replicate_cons_main_some h hi
  rw [hDefault] at hSome
  simp [PartrecToTM1Alphabet] at hSome

private theorem block_offset_div {width i b : Nat} (hb : b < width) :
    (i * width + b) / width = i := by
  have hWidth : 0 < width := Nat.zero_lt_of_lt hb
  rw [Nat.mul_comm i width]
  rw [Nat.mul_add_div hWidth]
  rw [Nat.div_eq_of_lt hb]
  simp

/--
A unary-zero main-stack output of length `m`, after the finite-alphabet Bool
encoding, yields `m` distinct true Bool output offsets.
-/
theorem tm2to1_tm1to1_unary_true_offsets {width : Nat}
    (enc : PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a)
    {tm1Output : Turing.ListBlank PartrecToTM1Alphabet}
    {boolOutput : Turing.ListBlank Bool} {m : Nat}
    (hMain : TM2to1MainOutput tm1Output
      (Turing.PartrecToTM2.trList (List.replicate m 0)))
    (hBool : TM1to1Output enc enc0 tm1Output boolOutput) :
    ∃ offsets : List Nat,
      offsets.Nodup ∧ offsets.length = m ∧
        ∀ n, n ∈ offsets -> boolOutput.nth n = true := by
  classical
  have hMainCons : TM2to1MainOutput tm1Output
      (List.replicate m Turing.PartrecToTM2.Γ'.cons) := by
    simpa [trList_replicate_zero] using hMain
  let bitWitness : (i : Fin m) -> ∃ bit : Fin width,
      (enc (tm1Output.nth i.val)).get bit = true := fun i =>
    encoded_nondefault_has_true enc dec enc0 encdec
      (tm2to1MainOutput_replicate_cons_ne_default hMainCons i.isLt)
  let bitOf : Fin m -> Fin width := fun i => Classical.choose (bitWitness i)
  let offsets : List Nat := (List.finRange m).map fun i : Fin m =>
    i.val * width + (bitOf i).val
  refine ⟨offsets, ?_, ?_, ?_⟩
  · dsimp [offsets]
    exact (List.nodup_finRange m).map (by
      intro a b hEq
      apply Fin.ext
      have hDiv := congrArg (fun n : Nat => n / width) hEq
      have hA := block_offset_div (i := a.val) (b := (bitOf a).val) (bitOf a).isLt
      have hB := block_offset_div (i := b.val) (b := (bitOf b).val) (bitOf b).isLt
      simpa [hA, hB] using hDiv)
  · dsimp [offsets]
    simp
  · intro n hn
    dsimp [offsets] at hn
    rw [List.mem_map] at hn
    rcases hn with ⟨i, _hi, rfl⟩
    have hBit : (enc (tm1Output.nth i.val)).get (bitOf i) = true :=
      Classical.choose_spec (bitWitness i)
    exact tm1to1Output_block_true hBool hBit

theorem partrecToTM1Encoding_width_pos {width : Nat}
    (enc : PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    0 < width := by
  let sym : PartrecToTM1Alphabet := (true, fun _ => none)
  have hSym : sym ≠ default := by
    intro h
    have hfst := congrArg Prod.fst h
    simp [sym, PartrecToTM1Alphabet] at hfst
  rcases encoded_nondefault_has_true enc dec enc0 encdec hSym with ⟨bit, _hbit⟩
  exact Nat.zero_lt_of_lt bit.isLt

theorem TM1to1EncodedInput_length {Γ : Type*} {width : Nat}
    (enc : Γ -> List.Vector Bool width) (input : List Γ) :
    (TM1to1EncodedInput enc input).length = input.length * width := by
  induction input with
  | nil => simp [TM1to1EncodedInput]
  | cons _a rest IH =>
      simp [TM1to1EncodedInput, IH, List.Vector.toList_length, Nat.succ_mul, Nat.add_comm]

theorem trPosNum_length (p : PosNum) :
    (Turing.PartrecToTM2.trPosNum p).length = PosNum.natSize p := by
  induction p with
  | one => simp [Turing.PartrecToTM2.trPosNum, PosNum.natSize]
  | bit0 p ih | bit1 p ih => simp [Turing.PartrecToTM2.trPosNum, PosNum.natSize, ih]

theorem trNum_length (m : Num) :
    (Turing.PartrecToTM2.trNum m).length = Num.natSize m := by
  cases m <;> simp [Turing.PartrecToTM2.trNum, Num.natSize, trPosNum_length]

theorem trNat_length (n : Nat) :
    (Turing.PartrecToTM2.trNat n).length = Nat.size n := by
  simp [Turing.PartrecToTM2.trNat, trNum_length, Num.natSize_to_nat]

theorem trList_singleton_length (n : Nat) :
    (Turing.PartrecToTM2.trList [n]).length = Nat.size n + 1 := by
  simp [Turing.PartrecToTM2.trList, trNat_length]

theorem tm2to1_trInit_length_pos
    (k : Turing.PartrecToTM2.K') (input : List Turing.PartrecToTM2.Γ') :
    0 < (@Turing.TM2to1.trInit Turing.PartrecToTM2.K'
      (fun _ => Turing.PartrecToTM2.Γ') inferInstance k input).length := by
  simp [Turing.TM2to1.trInit]

/-- The Bool input used by the lowered recursive-code evaluator is nonempty. -/
theorem encoded_partrec_input_length_pos {width : Nat}
    (enc : PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) (n : Nat) :
    0 < (TM1to1EncodedInput enc
      (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [n]))).length := by
  rw [TM1to1EncodedInput_length]
  exact Nat.mul_pos (tm2to1_trInit_length_pos _ _)
    (partrecToTM1Encoding_width_pos enc dec enc0 encdec)

theorem tm2to1_trInit_length_le_succ
    (k : Turing.PartrecToTM2.K') (input : List Turing.PartrecToTM2.Γ') :
    (@Turing.TM2to1.trInit Turing.PartrecToTM2.K'
      (fun _ => Turing.PartrecToTM2.Γ') inferInstance k input).length ≤
        input.length + 1 := by
  simp [Turing.TM2to1.trInit]

/-- The Bool encoding of the recursive evaluator's input has fixed-width binary size. -/
theorem encoded_partrec_input_length_le {width : Nat}
    (enc : PartrecToTM1Alphabet -> List.Vector Bool width) (n : Nat) :
    (TM1to1EncodedInput enc
      (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [n]))).length ≤
      width * (Nat.size n + 2) := by
  rw [TM1to1EncodedInput_length]
  have hInit' :
      (@Turing.TM2to1.trInit Turing.PartrecToTM2.K'
        (fun _ => Turing.PartrecToTM2.Γ') inferInstance Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [n])).length ≤ Nat.size n + 2 := by
    simpa [trList_singleton_length, trNat_length, Nat.add_assoc] using
      tm2to1_trInit_length_le_succ Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [n])
  calc
    (@Turing.TM2to1.trInit Turing.PartrecToTM2.K'
        (fun _ => Turing.PartrecToTM2.Γ') inferInstance Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [n])).length * width
        ≤ (Nat.size n + 2) * width := Nat.mul_le_mul_right width hInit'
    _ = width * (Nat.size n + 2) := Nat.mul_comm _ _

theorem linear_mul_le_two_pow_pred_of_large (D m : Nat)
    (hm : 2 * (D + 1) + 1 ≤ m) : D * m ≤ 2 ^ (m - 1) := by
  let M := 2 * (D + 1) + 1
  have hbaseLinear : D * M ≤ 2 * (D + 1) ^ 2 + 1 := by
    dsimp [M]
    grind
  have hbasePow : 2 * (D + 1) ^ 2 + 1 ≤ 2 ^ (M - 1) := by
    have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (D + 1)
    dsimp [M]
    simpa [Nat.add_assoc, Nat.mul_add, Nat.add_comm, Nat.add_left_comm] using h
  have hbase : D * M ≤ 2 ^ (M - 1) := Nat.le_trans hbaseLinear hbasePow
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
      have hnpos : 0 < n := by omega
      have hDleDn : D ≤ D * n := by
        exact Nat.le_mul_of_pos_right D hnpos
      have hDlePow : D ≤ 2 ^ (n - 1) := Nat.le_trans hDleDn ih
      calc
        D * (n + 1) = D * n + D := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := Nat.add_le_add ih hDlePow
        _ = 2 ^ (n + 1 - 1) := by
          have hpred : n - 1 + 1 = n :=
            Nat.sub_add_cancel (Nat.succ_le_iff.mp hnpos)
          rw [Nat.add_sub_cancel]
          rw [← hpred]
          simp [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]

theorem nat_size_linear_le_self_of_large (D n : Nat)
    (hn : 2 ^ (2 * (D + 1) + 1) ≤ n) : D * Nat.size n ≤ n := by
  let M := 2 * (D + 1) + 1
  have hMltSize : M < Nat.size n := (Nat.lt_size (m := M) (n := n)).2 hn
  have hDsizePow : D * Nat.size n ≤ 2 ^ (Nat.size n - 1) :=
    linear_mul_le_two_pow_pred_of_large D (Nat.size n) hMltSize.le
  have hSizePos : 0 < Nat.size n := lt_of_le_of_lt (Nat.zero_le M) hMltSize
  have hPredLt : Nat.size n - 1 < Nat.size n := Nat.pred_lt hSizePos.ne'
  have hPowLe : 2 ^ (Nat.size n - 1) ≤ n :=
    (Nat.lt_size (m := Nat.size n - 1) (n := n)).1 hPredLt
  exact Nat.le_trans hDsizePow hPowLe

theorem init_wrapper_state_count_le_linear (width C inputLen s : Nat)
    (hInput : inputLen ≤ width * (s + 2)) (hs : 0 < s) :
    2 * inputLen + C ≤ (2 * width + (4 * width + C) + 1) * s := by
  have hInput2 : 2 * inputLen + C ≤ 2 * (width * (s + 2)) + C := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hInput) C
  have hConst : 4 * width + C ≤ (4 * width + C) * s := by
    exact Nat.le_mul_of_pos_right (4 * width + C) hs
  have hConst' : 4 * width + C ≤ ((4 * width + C) + 1) * s := by
    exact Nat.le_trans hConst (Nat.mul_le_mul_right s (Nat.le_succ (4 * width + C)))
  have hCore : 2 * (width * (s + 2)) + C ≤
      (2 * width + (4 * width + C) + 1) * s := by
    calc
      2 * (width * (s + 2)) + C = 2 * width * s + (4 * width + C) := by
        grind
      _ ≤ 2 * width * s + ((4 * width + C) + 1) * s :=
        Nat.add_le_add_left hConst' _
      _ = (2 * width + (4 * width + C) + 1) * s := by
        simp [Nat.add_mul, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm]
  exact Nat.le_trans hInput2 hCore

theorem init_wrapper_state_count_le_linear_size {Label : Type*} [Fintype Label]
    {width : Nat} {input : List Bool} {n : Nat}
    (hInput : input.length ≤ width * (Nat.size n + 2))
    (hSize : 0 < Nat.size n) :
    Fintype.card (InitThenTM0State Label input) ≤
      (2 * width + (4 * width + Fintype.card (TM0RadoState Label)) + 1) *
        Nat.size n := by
  rw [initThenTM0State_card]
  exact init_wrapper_state_count_le_linear width
    (Fintype.card (TM0RadoState Label)) input.length (Nat.size n) hInput hSize

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
Unary-output Bool-`TM1` lowering for a caller-supplied finite-alphabet encoder.
This form is intended for the final score compiler, which should choose an
encoding whose Bool blocks are convenient to count.
-/
theorem totalRecursiveMathlib_bool_tm1_eval_unary_with_encoding {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f)
    {width : Nat}
    (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    ∃ c : Turing.ToPartrec.Code,
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
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
  rcases totalRecursiveMathlib_tm1_eval_unary hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
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
Unary-output Bool-`TM0` lowering for a caller-supplied finite-alphabet encoder.
-/
theorem totalRecursiveMathlib_bool_tm0_eval_unary_with_encoding {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f)
    {width : Nat}
    (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    ∃ c : Turing.ToPartrec.Code,
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
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
  rcases totalRecursiveMathlib_bool_tm1_eval_unary_with_encoding
      hf enc dec enc0 encdec with ⟨c, hEval⟩
  refine ⟨c, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hEval ⊢
  intro n
  rcases hEval n with ⟨boolOutput, hBoolTM1, hOutput⟩
  refine ⟨boolOutput, ?_, hOutput⟩
  rw [Turing.TM1to0.tr_eval]
  exact hBoolTM1

/--
Unary-output Bool-`TM0` lowering, packaged with a nodup list of true output
offsets whose length is exactly the computed value.
-/
theorem totalRecursiveMathlib_bool_tm0_eval_unary_true_offsets {f : Nat -> Nat}
    (hf : TotalRecursiveMathlib f)
    {width : Nat}
    (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    ∃ c : Turing.ToPartrec.Code,
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
      ∀ n,
        ∃ (boolOutput : Turing.ListBlank Bool) (offsets : List Nat),
          boolOutput ∈ Turing.TM0.eval (Turing.TM1to0.tr tm1Bool)
            (MathlibBridge.TM1to1EncodedInput enc
              (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
                (Turing.PartrecToTM2.trList [n]))) ∧
          offsets.Nodup ∧ offsets.length = f n ∧
          ∀ offset, offset ∈ offsets -> boolOutput.nth offset = true := by
  rcases totalRecursiveMathlib_bool_tm0_eval_unary_with_encoding
      hf enc dec enc0 encdec with ⟨c, hEval⟩
  refine ⟨c, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hEval ⊢
  intro n
  rcases hEval n with ⟨boolOutput, hBoolEval, tm1Output, hMain, hBoolRel⟩
  rcases MathlibBridge.tm2to1_tm1to1_unary_true_offsets
      enc dec enc0 encdec hMain hBoolRel with
    ⟨offsets, hOffsets, hLen, hTrue⟩
  exact ⟨boolOutput, offsets, hBoolEval, hOffsets, hLen, hTrue⟩

/--
The finite-support recursive-code evaluator descends through the same
caller-supplied finite-alphabet Bool encoding used by the evaluator theorem.
-/
theorem partrecToTM2_descends_to_supported_bool_tm0_with_encoding
    (c : Turing.ToPartrec.Code) {width : Nat}
    (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet) :
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
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp
  exact Turing.TM1to0.tr_supports
    (Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine)
    (Turing.TM1to1.tr_supports enc dec MathlibBridge.PartrecToTM1Machine
      (Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr (partrecToTM2_supports c)))

/--
For a mathlib-total-recursive function and a caller-supplied correct Bool
encoding, the fully lowered evaluator plus the blank-tape initializer wrapper
attains, for every input `n`, some Rado score at least `f n`.
-/
theorem totalRecursiveMathlib_init_wrapper_attainable_lowerBound_with_encoding
    {f : Nat -> Nat} (hf : TotalRecursiveMathlib f)
    {width : Nat}
    (enc : MathlibBridge.PartrecToTM1Alphabet -> List.Vector Bool width)
    (dec : List.Vector Bool width -> MathlibBridge.PartrecToTM1Alphabet)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    ∃ c : Turing.ToPartrec.Code,
      letI : Inhabited Turing.PartrecToTM2.Λ' :=
        ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
      let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
      let suppTM2 := Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt
      let suppTM1 := Turing.TM2to1.trSupp Turing.PartrecToTM2.tr suppTM2
      let suppTM1Bool := Turing.TM1to1.trSupp MathlibBridge.PartrecToTM1Machine suppTM1
      let S : Set (Turing.TM1to0.Λ' tm1Bool) :=
        Turing.TM1to0.trStmts tm1Bool suppTM1Bool
      ∀ n,
        let input := MathlibBridge.TM1to1EncodedInput enc
          (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
            (Turing.PartrecToTM2.trList [n]))
        ∃ score, f n ≤ score ∧
          AttainableScore (Fintype.card (MathlibBridge.InitThenTM0State S input)) score := by
  rcases totalRecursiveMathlib_bool_tm0_eval_unary_true_offsets
      hf enc dec enc0 encdec with ⟨c, hEval⟩
  refine ⟨c, ?_⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hEval ⊢
  intro n
  let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
  let tm0Bool := Turing.TM1to0.tr tm1Bool
  let suppTM2 := Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt
  let suppTM1 := Turing.TM2to1.trSupp Turing.PartrecToTM2.tr suppTM2
  let suppTM1Bool := Turing.TM1to1.trSupp MathlibBridge.PartrecToTM1Machine suppTM1
  let S : Set (Turing.TM1to0.Λ' tm1Bool) := Turing.TM1to0.trStmts tm1Bool suppTM1Bool
  let input := MathlibBridge.TM1to1EncodedInput enc
    (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList [n]))
  have hSupp : Turing.TM0.Supports tm0Bool S := by
    dsimp [tm0Bool, tm1Bool, S, suppTM1Bool, suppTM1, suppTM2]
    exact partrecToTM2_descends_to_supported_bool_tm0_with_encoding c enc dec
  letI : Inhabited S := MathlibBridge.tm0SupportedInhabited tm0Bool hSupp
  rcases hEval n with ⟨boolOutput, offsets, hBoolEval, hOffsets, hLen, hTrue⟩
  have hEvalSupported : boolOutput ∈
      @Turing.TM0.eval Bool S (MathlibBridge.tm0SupportedInhabited tm0Bool hSupp) inferInstance
        (MathlibBridge.tm0SupportedMachine tm0Bool hSupp) input := by
    exact MathlibBridge.tm0SupportedMachine_eval_of_original tm0Bool hSupp hBoolEval
  have hInput : 0 < input.length := by
    dsimp [input]
    exact MathlibBridge.encoded_partrec_input_length_pos enc dec enc0 encdec n
  rcases MathlibBridge.tm0_eval_to_init_wrapper_lowerBound
      (MathlibBridge.tm0SupportedMachine tm0Bool hSupp) hInput hEvalSupported hOffsets hTrue with
    ⟨score, hLower, hScore⟩
  refine ⟨score, ?_, hScore⟩
  rw [← hLen]
  exact hLower

/--
Mathlib-total-recursive functions satisfy the eventual lower-bound compiler
interface for the two-symbol blank-tape Rado model.

The proof keeps every bridge explicit: mathlib's recursive code is evaluated by
`PartrecToTM2`, lowered through mathlib's proved TM simulations to a supported
Bool `TM0`, wrapped by the local blank-tape initializer, and finally budgeted by
the binary input-size bound above.
-/
theorem totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler :
    HasEventuallyAtMostLowerBoundCompiler TotalRecursiveMathlib := by
  intro f hf
  classical
  rcases Turing.TM1to1.exists_enc_dec
      (Γ := MathlibBridge.PartrecToTM1Alphabet) with
    ⟨width, enc, dec, enc0, encdec⟩
  rcases totalRecursiveMathlib_init_wrapper_attainable_lowerBound_with_encoding
      hf enc dec enc0 encdec with
    ⟨c, hLower⟩
  letI : Inhabited Turing.PartrecToTM2.Λ' :=
    ⟨Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt⟩
  dsimp at hLower
  let tm1Bool := Turing.TM1to1.tr enc dec MathlibBridge.PartrecToTM1Machine
  let suppTM2 := Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt
  let suppTM1 := Turing.TM2to1.trSupp Turing.PartrecToTM2.tr suppTM2
  let suppTM1Bool := Turing.TM1to1.trSupp MathlibBridge.PartrecToTM1Machine suppTM1
  let S : Set (Turing.TM1to0.Λ' tm1Bool) :=
    Turing.TM1to0.trStmts tm1Bool suppTM1Bool
  let C := Fintype.card (MathlibBridge.TM0RadoState S)
  let D := 2 * width + (4 * width + C) + 1
  let threshold := 2 ^ (2 * (D + 1) + 1)
  refine ⟨threshold, ?_⟩
  intro n hn
  let input := MathlibBridge.TM1to1EncodedInput enc
    (Turing.TM2to1.trInit Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList [n]))
  rcases hLower n with ⟨score, hScoreLower, hAttain⟩
  refine ⟨score, hScoreLower, ?_⟩
  refine ⟨Fintype.card (MathlibBridge.InitThenTM0State S input), ?_, hAttain⟩
  have hInputLen : input.length ≤ width * (Nat.size n + 2) := by
    dsimp [input]
    exact MathlibBridge.encoded_partrec_input_length_le enc n
  have hThresholdPos : 0 < threshold := by
    dsimp [threshold]
    exact Nat.pow_pos (by decide : 0 < 2)
  have hnPos : 0 < n := Nat.lt_of_lt_of_le hThresholdPos hn
  have hSizePos : 0 < Nat.size n := (Nat.size_pos).2 hnPos
  have hStateLeD : Fintype.card (MathlibBridge.InitThenTM0State S input) ≤
      D * Nat.size n := by
    dsimp [D, C]
    exact MathlibBridge.init_wrapper_state_count_le_linear_size
      (Label := S) (width := width) (input := input) (n := n)
      hInputLen hSizePos
  have hDSizeLeN : D * Nat.size n ≤ n := by
    dsimp [threshold] at hn
    exact MathlibBridge.nat_size_linear_le_self_of_large D n hn
  exact Nat.le_trans hStateLeD hDSizeLeN

/--
Concrete final theorem for mathlib's total-recursive predicate: any busy-beaver
score function eventually dominates every total recursive function `Nat -> Nat`.
-/
theorem sigma_eventually_dominates_every_totalRecursiveMathlib
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveMathlib f) :
    EventuallyDominates Sigma f :=
  eventuallyDominates_of_hasEventuallyAtMostLowerBoundCompiler
    hSigma totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler hf

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
