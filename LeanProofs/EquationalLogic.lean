/-!
# A tiny checker for one-operation equational proofs

This module is deliberately small and first-order.  A certificate step says:

* the source equation is an instance of a previously known equation;
* a subterm at a specified position is replaced by an equal term, again using
  an instance of a previously known equation;
* the syntactic result is the target equation.

The checker is computational, but its soundness theorem is semantic: every
checked equation holds in every algebra satisfying the initial equations.
-/

namespace LeanProofs

namespace EquationalLogic

/-- Terms over variables and one binary operation. -/
inductive Term where
  | var : Nat → Term
  | op : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Interpret a term in an arbitrary one-binary-operation algebra. -/
def eval {α : Type u} (op : α → α → α) (env : Nat → α) : Term → α
  | var n => env n
  | Term.op l r => op (eval op env l) (eval op env r)

/-- Subterm at a binary-tree path (`false` = left, `true` = right). -/
def subterm? : Term → List Bool → Option Term
  | t, [] => some t
  | Term.op l _, false :: path => subterm? l path
  | Term.op _ r, true :: path => subterm? r path
  | var _, _ :: _ => none

/-- Replace the subterm at a binary-tree path. -/
def replace? : Term → List Bool → Term → Option Term
  | _, [], replacement => some replacement
  | Term.op l r, false :: path, replacement => do
      let l' ← replace? l path replacement
      some (Term.op l' r)
  | Term.op l r, true :: path, replacement => do
      let r' ← replace? r path replacement
      some (Term.op l r')
  | var _, _ :: _, _ => none

theorem replace?_sound {α : Type u} {op : α → α → α} {env : Nat → α}
    {t old replacement t' : Term} {path : List Bool}
    (hrep : replace? t path replacement = some t')
    (hsub : subterm? t path = some old)
    (heq : eval op env old = eval op env replacement) :
    eval op env t = eval op env t' := by
  induction t generalizing path old t' with
  | var n =>
      cases path with
      | nil =>
          simp [replace?, subterm?] at hrep hsub
          cases hrep
          cases hsub
          exact heq
      | cons _ _ =>
          simp [replace?] at hrep
  | op l r ihl ihr =>
      cases path with
      | nil =>
          simp [replace?, subterm?] at hrep hsub
          cases hrep
          cases hsub
          exact heq
      | cons dir path =>
          cases dir
          · simp [replace?, subterm?] at hrep hsub
            cases h : replace? l path replacement with
            | none =>
                simp [h] at hrep
            | some l' =>
                simp [h] at hrep
                cases hrep
                have hl := ihl h hsub heq
                simp [eval, hl]
          · simp [replace?, subterm?] at hrep hsub
            cases h : replace? r path replacement with
            | none =>
                simp [h] at hrep
            | some r' =>
                simp [h] at hrep
                cases hrep
                have hr := ihr h hsub heq
                simp [eval, hr]

end Term

/-- A finite substitution, represented as an association list. -/
abbrev Subst := List (Nat × Term)

namespace Subst

def lookup (σ : Subst) (n : Nat) : Option Term :=
  match σ with
  | [] => none
  | (m, t) :: rest => if m = n then some t else lookup rest n

def evalEnv {α : Type u} (op : α → α → α) (env : Nat → α) (σ : Subst) : Nat → α :=
  fun n =>
    match lookup σ n with
    | some t => t.eval op env
    | none => env n

end Subst

namespace Term

/-- Instantiate variables using a finite substitution. -/
def inst (σ : Subst) : Term → Term
  | var n =>
      match Subst.lookup σ n with
      | some t => t
      | none => var n
  | Term.op l r => Term.op (inst σ l) (inst σ r)

theorem eval_inst {α : Type u} {op : α → α → α} {env : Nat → α}
    (σ : Subst) :
    ∀ t : Term, (inst σ t).eval op env = t.eval op (Subst.evalEnv op env σ)
  | var n => by
      simp [inst, eval, Subst.evalEnv]
      cases Subst.lookup σ n <;> rfl
  | Term.op l r => by
      simp [inst, eval, eval_inst σ l, eval_inst σ r]

end Term

/-- An equation between two terms. -/
structure Equation where
  lhs : Term
  rhs : Term
  deriving DecidableEq, Repr

namespace Equation

def symm (e : Equation) : Equation :=
  { lhs := e.rhs, rhs := e.lhs }

def inst (σ : Subst) (e : Equation) : Equation :=
  { lhs := e.lhs.inst σ, rhs := e.rhs.inst σ }

/-- Semantic validity of an equation in an arbitrary algebra. -/
def Valid {α : Type u} (op : α → α → α) (e : Equation) : Prop :=
  ∀ env : Nat → α, e.lhs.eval op env = e.rhs.eval op env

theorem valid_symm {α : Type u} {op : α → α → α} {e : Equation}
    (h : Valid op e) : Valid op e.symm := by
  intro env
  exact (h env).symm

theorem valid_inst {α : Type u} {op : α → α → α} {e : Equation}
    (h : Valid op e) (σ : Subst) : Valid op (e.inst σ) := by
  intro env
  simp [inst, Term.eval_inst]
  exact h (Subst.evalEnv op env σ)

/-- Position inside one side of an equation. -/
structure Pos where
  side : Bool
  path : List Bool
  deriving DecidableEq, Repr

/-- The subterm at a position (`false` side = lhs, `true` side = rhs). -/
def subterm? (e : Equation) (pos : Pos) : Option Term :=
  if pos.side then e.rhs.subterm? pos.path else e.lhs.subterm? pos.path

/-- Replace the subterm at a position. -/
def replace? (e : Equation) (pos : Pos) (replacement : Term) : Option Equation :=
  if pos.side then
    match e.rhs.replace? pos.path replacement with
    | some rhs' => some { lhs := e.lhs, rhs := rhs' }
    | none => none
  else
    match e.lhs.replace? pos.path replacement with
    | some lhs' => some { lhs := lhs', rhs := e.rhs }
    | none => none

theorem replace?_valid {α : Type u} {op : α → α → α}
    {source target : Equation} {pos : Pos} {old replacement : Term}
    (hrep : source.replace? pos replacement = some target)
    (hsub : source.subterm? pos = some old)
    (hsource : Valid op source)
    (hrule : Valid op { lhs := old, rhs := replacement }) :
    Valid op target := by
  intro env
  cases pos with
  | mk side path =>
      cases side
      · simp [replace?, subterm?] at hrep hsub
        cases h : source.lhs.replace? path replacement with
        | none =>
            simp [h] at hrep
        | some lhs' =>
            simp [h] at hrep
            cases hrep
            have hctx := Term.replace?_sound (op := op) (env := env) h hsub (hrule env)
            exact hctx.symm.trans (hsource env)
      · simp [replace?, subterm?] at hrep hsub
        cases h : source.rhs.replace? path replacement with
        | none =>
            simp [h] at hrep
        | some rhs' =>
            simp [h] at hrep
            cases hrep
            have hctx := Term.replace?_sound (op := op) (env := env) h hsub (hrule env)
            exact (hsource env).trans hctx

end Equation

namespace Matching

/-- Add a variable binding, checking consistency with any previous binding. -/
def bind (n : Nat) (t : Term) (σ : Subst) : Option Subst :=
  match Subst.lookup σ n with
  | none => some ((n, t) :: σ)
  | some old => if old = t then some σ else none

/-- First-order matching from a pattern term to a target term. -/
def matchTerm : Term → Term → Subst → Option Subst
  | Term.var n, target, σ => bind n target σ
  | Term.op l r, Term.op l' r', σ => do
      let σ ← matchTerm l l' σ
      matchTerm r r' σ
  | Term.op _ _, Term.var _, _ => none

def instanceSubst? (pattern target : Equation) : Option Subst := do
  let σ ← matchTerm pattern.lhs target.lhs []
  let σ ← matchTerm pattern.rhs target.rhs σ
  if pattern.inst σ = target then
    some σ
  else
    none

theorem instanceSubst?_sound {pattern target : Equation} {σ : Subst}
    (h : instanceSubst? pattern target = some σ) :
    pattern.inst σ = target := by
  unfold instanceSubst? at h
  cases h₁ : matchTerm pattern.lhs target.lhs [] with
  | none =>
      simp [h₁] at h
  | some σ₁ =>
      cases h₂ : matchTerm pattern.rhs target.rhs σ₁ with
      | none =>
          simp [h₁, h₂] at h
      | some σ₂ =>
          by_cases hEq : pattern.inst σ₂ = target
          · simp [h₁, h₂, hEq] at h
            cases h
            exact hEq
          · simp [h₁, h₂, hEq] at h

theorem valid_of_instance {α : Type u} {op : α → α → α}
    {pattern target : Equation} {σ : Subst}
    (hinst : instanceSubst? pattern target = some σ)
    (hvalid : pattern.Valid op) :
    target.Valid op := by
  have hEq := instanceSubst?_sound hinst
  rw [← hEq]
  exact Equation.valid_inst hvalid σ

end Matching

/-- All equations in a list are semantically valid. -/
def AllValid {α : Type u} (op : α → α → α) (eqs : List Equation) : Prop :=
  ∀ e, e ∈ eqs → e.Valid op

namespace Certificate

theorem bool_and_eq_true {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp at h ⊢

/-- Whether an equation is known, up to instantiation and symmetry. -/
def knownFrom? : List Equation → Equation → Bool
  | [], _ => false
  | pattern :: rest, target =>
      (Matching.instanceSubst? pattern target).isSome ||
        (Matching.instanceSubst? pattern.symm target).isSome ||
        knownFrom? rest target

def known? (eqs : List Equation) (target : Equation) : Bool :=
  decide (target.lhs = target.rhs) || knownFrom? eqs target

theorem knownFrom?_sound {α : Type u} {op : α → α → α}
    {eqs : List Equation} {target : Equation}
    (hknown : knownFrom? eqs target = true)
    (hall : AllValid op eqs) :
    target.Valid op := by
  induction eqs with
  | nil =>
      simp [knownFrom?] at hknown
  | cons pattern rest ih =>
      simp [knownFrom?] at hknown
      cases h₁ : Matching.instanceSubst? pattern target with
      | some σ =>
          exact Matching.valid_of_instance h₁ (hall pattern (by simp))
      | none =>
          simp [h₁] at hknown
          cases h₂ : Matching.instanceSubst? pattern.symm target with
          | some σ =>
              have hpattern : pattern.Valid op := hall pattern (by simp)
              exact Matching.valid_of_instance h₂ (Equation.valid_symm hpattern)
          | none =>
              simp [h₂] at hknown
              exact ih hknown (by
                intro e he
                exact hall e (by simp [he]))

theorem known?_sound {α : Type u} {op : α → α → α}
    {eqs : List Equation} {target : Equation}
    (hknown : known? eqs target = true)
    (hall : AllValid op eqs) :
    target.Valid op := by
  unfold known? at hknown
  cases hEq : decide (target.lhs = target.rhs)
  · simp [hEq] at hknown
    exact knownFrom?_sound hknown hall
  · have hlr : target.lhs = target.rhs := of_decide_eq_true hEq
    intro env
    simp [hlr]

/-- One replacement step in a proof certificate. -/
structure Step where
  source : Equation
  rule : Equation
  pos : Equation.Pos
  target : Equation
  deriving DecidableEq, Repr

namespace Step

def check (eqs : List Equation) (step : Step) : Bool :=
  known? eqs step.source &&
    match step.source.subterm? step.pos, step.target.subterm? step.pos with
    | some old, some replacement =>
        (Matching.instanceSubst? step.rule { lhs := old, rhs := replacement }).isSome &&
          decide (step.source.replace? step.pos replacement = some step.target) &&
          known? eqs step.rule
    | _, _ => false

theorem check_sound {α : Type u} {op : α → α → α}
    {eqs : List Equation} {step : Step}
    (hcheck : step.check eqs = true)
    (hall : AllValid op eqs) :
    step.target.Valid op := by
  unfold check at hcheck
  cases hsourceKnown : known? eqs step.source
  · simp [hsourceKnown] at hcheck
  · simp [hsourceKnown] at hcheck
    cases hOld : step.source.subterm? step.pos with
    | none =>
        simp [hOld] at hcheck
    | some old =>
        cases hNew : step.target.subterm? step.pos with
        | none =>
            simp [hOld, hNew] at hcheck
        | some replacement =>
            simp [hOld, hNew] at hcheck
            cases hinst : Matching.instanceSubst? step.rule { lhs := old, rhs := replacement } with
            | none =>
                simp [hinst] at hcheck
            | some σ =>
                simp [hinst] at hcheck
                have hrep : step.source.replace? step.pos replacement = some step.target :=
                  hcheck.1
                have hsourceValid := known?_sound hsourceKnown hall
                have hruleValid := known?_sound hcheck.2 hall
                have hlocal := Matching.valid_of_instance hinst hruleValid
                exact Equation.replace?_valid hrep hOld hsourceValid hlocal

end Step

/-- A certificate item either adds an instantiated known equation or rewrites. -/
inductive Item where
  | add : Equation → Item
  | rewrite : Step → Item
  deriving DecidableEq, Repr

namespace Item

def target : Item → Equation
  | add e => e
  | rewrite step => step.target

def check (eqs : List Equation) : Item → Bool
  | add e => known? eqs e
  | rewrite step => step.check eqs

theorem check_sound {α : Type u} {op : α → α → α}
    {eqs : List Equation} {item : Item}
    (hcheck : item.check eqs = true)
    (hall : AllValid op eqs) :
    item.target.Valid op := by
  cases item with
  | add e =>
      exact known?_sound hcheck hall
  | rewrite step =>
      exact Step.check_sound hcheck hall

end Item

/-- Run a mixed certificate of instantiation additions and rewrite steps. -/
def runItems : List Equation → List Item → Option (List Equation)
  | eqs, [] => some eqs
  | eqs, item :: rest =>
      if item.check eqs then
        runItems (item.target :: eqs) rest
      else
        none

theorem runItems_sound {α : Type u} {op : α → α → α}
    {initial final : List Equation} {items : List Item}
    (hrun : runItems initial items = some final)
    (hinitial : AllValid op initial) :
    AllValid op final := by
  induction items generalizing initial with
  | nil =>
      simp [runItems] at hrun
      cases hrun
      exact hinitial
  | cons item rest ih =>
      unfold runItems at hrun
      cases hcheck : item.check initial
      · simp [hcheck] at hrun
      · simp [hcheck] at hrun
        apply ih hrun
        intro e he
        simp at he
        rcases he with rfl | hmem
        · exact Item.check_sound hcheck hinitial
        · exact hinitial e hmem

/-- Run a certificate, consing each checked target onto the known-equation list. -/
def run : List Equation → List Step → Option (List Equation)
  | eqs, [] => some eqs
  | eqs, step :: rest =>
      if step.check eqs then
        run (step.target :: eqs) rest
      else
        none

theorem run_sound {α : Type u} {op : α → α → α}
    {initial final : List Equation} {steps : List Step}
    (hrun : run initial steps = some final)
    (hinitial : AllValid op initial) :
    AllValid op final := by
  induction steps generalizing initial with
  | nil =>
      simp [run] at hrun
      cases hrun
      exact hinitial
  | cons step rest ih =>
      unfold run at hrun
      cases hcheck : step.check initial
      · simp [hcheck] at hrun
      · simp [hcheck] at hrun
        apply ih hrun
        intro e he
        simp at he
        rcases he with rfl | hmem
        · exact Step.check_sound hcheck hinitial
        · exact hinitial e hmem

end Certificate

end EquationalLogic

end LeanProofs
