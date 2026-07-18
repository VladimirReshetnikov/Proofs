import PAListCoding.TetrationDiophantine

/-!
# Variable-rank natural hyperoperations

This module fixes the conventional rank numbering

* rank `0`: successor in the last argument;
* rank `1`: addition;
* rank `2`: multiplication;
* rank `3`: exponentiation;
* rank `4`: tetration;
* rank `5`: pentation.

For ranks at least three it is convenient to subtract three and work with a
uniform hierarchy.  Level zero of that hierarchy is exponentiation, and each
successor level iterates the preceding level from the initial value one.

The second half of the file gives a small deterministic evaluator.  Its stack
is a natural number built from an injective polynomial pair; no list-decoding
operation occurs in the transition relation.  This is the semantic layer for
the Diophantine reachability proof in `HyperoperationDiophantine`.
-/

namespace PAListCoding

/-! ## The hierarchy and its conventional indexing -/

/-- Iterate `f` from one.  This is the common zero-argument convention for
tetration, pentation, and every higher operation in this development. -/
def iterateFromOne (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => f (iterateFromOne f n)

/-- The uniform hierarchy beginning at exponentiation.  Thus level zero is
power, level one is tetration, and level two is pentation. -/
def hyperoperationCore : ℕ → ℕ → ℕ → ℕ
  | 0, base, argument => base ^ argument
  | rank + 1, base, argument =>
      iterateFromOne (hyperoperationCore rank base) argument

@[simp] theorem hyperoperationCore_zero (base argument : ℕ) :
    hyperoperationCore 0 base argument = base ^ argument := rfl

@[simp] theorem hyperoperationCore_succ_zero (rank base : ℕ) :
    hyperoperationCore (rank + 1) base 0 = 1 := rfl

@[simp] theorem hyperoperationCore_succ_succ (rank base argument : ℕ) :
    hyperoperationCore (rank + 1) base (argument + 1) =
      hyperoperationCore rank base
        (hyperoperationCore (rank + 1) base argument) := rfl

/-- Pentation with the same empty-iteration convention as tetration. -/
def pentation (base : ℕ) : ℕ → ℕ
  | 0 => 1
  | argument + 1 => tetration base (pentation base argument)

theorem hyperoperationCore_one_eq_tetration (base argument : ℕ) :
    hyperoperationCore 1 base argument = tetration base argument := by
  induction argument with
  | zero => rfl
  | succ argument ih =>
      simp only [Nat.reduceAdd, hyperoperationCore_succ_succ,
        hyperoperationCore_zero, tetration_succ, ih]

theorem hyperoperationCore_two_eq_pentation (base argument : ℕ) :
    hyperoperationCore 2 base argument = pentation base argument := by
  induction argument with
  | zero => rfl
  | succ argument ih =>
      simp only [Nat.reduceAdd, hyperoperationCore_succ_succ, pentation, ih,
        hyperoperationCore_one_eq_tetration]

/-- The standard three-argument hyperoperator.  The first argument is the
rank, followed by the base and the ordinary right-hand argument. -/
def hyperoperator : ℕ → ℕ → ℕ → ℕ
  | 0, _base, argument => argument + 1
  | 1, base, argument => base + argument
  | 2, base, argument => base * argument
  | rank + 3, base, argument => hyperoperationCore rank base argument

@[simp] theorem hyperoperator_rank_zero (base argument : ℕ) :
    hyperoperator 0 base argument = argument + 1 := rfl

@[simp] theorem hyperoperator_rank_one (base argument : ℕ) :
    hyperoperator 1 base argument = base + argument := rfl

@[simp] theorem hyperoperator_rank_two (base argument : ℕ) :
    hyperoperator 2 base argument = base * argument := rfl

@[simp] theorem hyperoperator_rank_three (base argument : ℕ) :
    hyperoperator 3 base argument = base ^ argument := rfl

theorem hyperoperator_rank_four (base argument : ℕ) :
    hyperoperator 4 base argument = tetration base argument := by
  exact hyperoperationCore_one_eq_tetration base argument

theorem hyperoperator_rank_five (base argument : ℕ) :
    hyperoperator 5 base argument = pentation base argument := by
  exact hyperoperationCore_two_eq_pentation base argument

/-! ## Polynomial machine-state codes -/

/-- The injective polynomial pair `(x+y)^2+y`, reused from the tetration
state code. -/
def hyperPair (x y : ℕ) : ℕ :=
  (x + y) * (x + y) + y

theorem hyperPair_injective {x y x' y' : ℕ}
    (h : hyperPair x y = hyperPair x' y') :
    x = x' ∧ y = y' := by
  exact tetrationStateCode_injective (by
    simpa [hyperPair, tetrationStateCode] using h)

/-- Zero is the empty stack.  Adding one to a pair makes every nonempty stack
positive and keeps push injective. -/
def hyperStackCons (rank stack : ℕ) : ℕ :=
  hyperPair rank stack + 1

theorem hyperStackCons_injective {rank stack rank' stack' : ℕ}
    (h : hyperStackCons rank stack = hyperStackCons rank' stack') :
    rank = rank' ∧ stack = stack' := by
  apply hyperPair_injective
  have hpairs : hyperPair rank stack + 1 = hyperPair rank' stack' + 1 := by
    simpa only [hyperStackCons] using h
  exact Nat.add_right_cancel hpairs

theorem hyperStackCons_ne_zero (rank stack : ℕ) :
    hyperStackCons rank stack ≠ 0 := by
  simp [hyperStackCons]

/-- Evaluation mode stores the fixed base, current rank and argument, and
the pending-rank stack.  The middle tag is zero. -/
def hyperEvalCode (base rank argument stack : ℕ) : ℕ :=
  hyperPair base (hyperPair 0 (hyperPair rank (hyperPair argument stack)))

/-- Return mode stores the fixed base, current value, and pending stack.  Its
middle tag is one, making it disjoint from every evaluation state. -/
def hyperReturnCode (base value stack : ℕ) : ℕ :=
  hyperPair base (hyperPair 1 (hyperPair value stack))

theorem hyperEvalCode_injective {base rank argument stack
    base' rank' argument' stack' : ℕ}
    (h : hyperEvalCode base rank argument stack =
      hyperEvalCode base' rank' argument' stack') :
    base = base' ∧ rank = rank' ∧ argument = argument' ∧ stack = stack' := by
  rcases hyperPair_injective h with ⟨hbase, hpayload⟩
  rcases hyperPair_injective hpayload with ⟨_htag, hwork⟩
  rcases hyperPair_injective hwork with ⟨hrank, hrest⟩
  rcases hyperPair_injective hrest with ⟨hargument, hstack⟩
  exact ⟨hbase, hrank, hargument, hstack⟩

theorem hyperReturnCode_injective {base value stack base' value' stack' : ℕ}
    (h : hyperReturnCode base value stack =
      hyperReturnCode base' value' stack') :
    base = base' ∧ value = value' ∧ stack = stack' := by
  rcases hyperPair_injective h with ⟨hbase, hpayload⟩
  rcases hyperPair_injective hpayload with ⟨_htag, hrest⟩
  rcases hyperPair_injective hrest with ⟨hvalue, hstack⟩
  exact ⟨hbase, hvalue, hstack⟩

theorem hyperEvalCode_ne_returnCode (base rank argument stack
    base' value stack' : ℕ) :
    hyperEvalCode base rank argument stack ≠
      hyperReturnCode base' value stack' := by
  intro h
  have hpayload := (hyperPair_injective h).2
  have htag := (hyperPair_injective hpayload).1
  omega

/-! ## A deterministic evaluator -/

/-- One evaluator transition.  A positive core rank and positive argument
first evaluates the preceding argument at the same rank and pushes the lower
rank.  A return through a nonempty stack starts that pending lower-rank call.
The rank-zero branch is the only branch using exponentiation. -/
def HyperStep (source target : ℕ) : Prop :=
  (∃ base argument stack,
      source = hyperEvalCode base 0 argument stack ∧
      target = hyperReturnCode base (base ^ argument) stack) ∨
  (∃ rank base stack,
      source = hyperEvalCode base (rank + 1) 0 stack ∧
      target = hyperReturnCode base 1 stack) ∨
  (∃ rank base argument stack,
      source = hyperEvalCode base (rank + 1) (argument + 1) stack ∧
      target = hyperEvalCode base (rank + 1) argument
        (hyperStackCons rank stack)) ∨
  (∃ rank base value stack,
      source = hyperReturnCode base value (hyperStackCons rank stack) ∧
      target = hyperEvalCode base rank value stack)

theorem hyperStep_eval_rank_zero (base argument stack target : ℕ) :
    HyperStep (hyperEvalCode base 0 argument stack) target ↔
      target = hyperReturnCode base (base ^ argument) stack := by
  constructor
  · rintro (hpower | hzero | hsucc | hreturn)
    · rcases hpower with ⟨base', argument', stack', hsource, htarget⟩
      rcases hyperEvalCode_injective hsource with
        ⟨rfl, _hrank, rfl, rfl⟩
      exact htarget
    · rcases hzero with ⟨rank', base', stack', hsource, _htarget⟩
      have hrank := (hyperEvalCode_injective hsource).2.1
      omega
    · rcases hsucc with
        ⟨rank', base', argument', stack', hsource, _htarget⟩
      have hrank := (hyperEvalCode_injective hsource).2.1
      omega
    · rcases hreturn with ⟨rank', base', value', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base 0 argument stack base' value'
        (hyperStackCons rank' stack') hsource).elim
  · intro htarget
    exact Or.inl ⟨base, argument, stack, rfl, htarget⟩

theorem hyperStep_eval_succ_zero (rank base stack target : ℕ) :
    HyperStep (hyperEvalCode base (rank + 1) 0 stack) target ↔
      target = hyperReturnCode base 1 stack := by
  constructor
  · rintro (hpower | hzero | hsucc | hreturn)
    · rcases hpower with ⟨base', argument', stack', hsource, _htarget⟩
      have hrank := (hyperEvalCode_injective hsource).2.1
      omega
    · rcases hzero with ⟨rank', base', stack', hsource, htarget⟩
      rcases hyperEvalCode_injective hsource with
        ⟨rfl, hrank, _hargument, rfl⟩
      have : rank = rank' := by omega
      subst rank'
      exact htarget
    · rcases hsucc with
        ⟨rank', base', argument', stack', hsource, _htarget⟩
      have hargument := (hyperEvalCode_injective hsource).2.2.1
      omega
    · rcases hreturn with ⟨rank', base', value', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base (rank + 1) 0 stack base' value'
        (hyperStackCons rank' stack') hsource).elim
  · intro htarget
    exact Or.inr <| Or.inl ⟨rank, base, stack, rfl, htarget⟩

theorem hyperStep_eval_succ_succ
    (rank base argument stack target : ℕ) :
    HyperStep (hyperEvalCode base (rank + 1) (argument + 1) stack) target ↔
      target = hyperEvalCode base (rank + 1) argument
        (hyperStackCons rank stack) := by
  constructor
  · rintro (hpower | hzero | hsucc | hreturn)
    · rcases hpower with ⟨base', argument', stack', hsource, _htarget⟩
      have hrank := (hyperEvalCode_injective hsource).2.1
      omega
    · rcases hzero with ⟨rank', base', stack', hsource, _htarget⟩
      have hargument := (hyperEvalCode_injective hsource).2.2.1
      omega
    · rcases hsucc with
        ⟨rank', base', argument', stack', hsource, htarget⟩
      rcases hyperEvalCode_injective hsource with
        ⟨rfl, hrank, hargument, rfl⟩
      have hrank' : rank = rank' := by omega
      have hargument' : argument = argument' := by omega
      subst rank'
      subst argument'
      exact htarget
    · rcases hreturn with ⟨rank', base', value', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base (rank + 1) (argument + 1)
        stack base' value' (hyperStackCons rank' stack') hsource).elim
  · intro htarget
    exact Or.inr <| Or.inr <| Or.inl
      ⟨rank, base, argument, stack, rfl, htarget⟩

theorem hyperStep_from_return (base value stack target : ℕ) :
    HyperStep (hyperReturnCode base value stack) target ↔
      ∃ rank tail,
        stack = hyperStackCons rank tail ∧
        target = hyperEvalCode base rank value tail := by
  constructor
  · rintro (hpower | hzero | hsucc | hreturn)
    · rcases hpower with ⟨base', argument', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base' 0 argument' stack' base value
        stack hsource.symm).elim
    · rcases hzero with ⟨rank', base', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base' (rank' + 1) 0 stack' base value
        stack hsource.symm).elim
    · rcases hsucc with
        ⟨rank', base', argument', stack', hsource, _htarget⟩
      exact (hyperEvalCode_ne_returnCode base' (rank' + 1) (argument' + 1)
        stack' base value stack hsource.symm).elim
    · rcases hreturn with
        ⟨rank', base', value', stack', hsource, htarget⟩
      rcases hyperReturnCode_injective hsource with
        ⟨rfl, rfl, hstack⟩
      exact ⟨rank', stack', hstack, htarget⟩
  · rintro ⟨rank, tail, hstack, htarget⟩
    subst stack
    exact Or.inr <| Or.inr <| Or.inr
      ⟨rank, base, value, tail, rfl, htarget⟩

theorem hyperStep_return_cons (rank base value stack target : ℕ) :
    HyperStep (hyperReturnCode base value (hyperStackCons rank stack)) target ↔
      target = hyperEvalCode base rank value stack := by
  rw [hyperStep_from_return]
  constructor
  · rintro ⟨rank', stack', hstack, htarget⟩
    rcases hyperStackCons_injective hstack with ⟨rfl, rfl⟩
    exact htarget
  · intro htarget
    exact ⟨rank, stack, rfl, htarget⟩

theorem hyperReturnCode_empty_terminal (base value : ℕ) :
    ∀ target, ¬ HyperStep (hyperReturnCode base value 0) target := by
  intro target hstep
  rcases (hyperStep_from_return base value 0 target).1 hstep with
    ⟨rank, stack, hstack, _htarget⟩
  exact hyperStackCons_ne_zero rank stack hstack.symm

theorem hyperStep_deterministic {source left right : ℕ}
    (hleft : HyperStep source left) (hright : HyperStep source right) :
    left = right := by
  rcases hleft with hpower | hzero | hsucc | hreturn
  · rcases hpower with ⟨base, argument, stack, rfl, rfl⟩
    exact ((hyperStep_eval_rank_zero base argument stack right).1 hright).symm
  · rcases hzero with ⟨rank, base, stack, rfl, rfl⟩
    exact ((hyperStep_eval_succ_zero rank base stack right).1 hright).symm
  · rcases hsucc with ⟨rank, base, argument, stack, rfl, rfl⟩
    exact ((hyperStep_eval_succ_succ rank base argument stack right).1
      hright).symm
  · rcases hreturn with ⟨rank, base, value, stack, rfl, rfl⟩
    exact ((hyperStep_return_cons rank base value stack right).1 hright).symm

/-! ## Exact evaluator runs -/

/-- Forward presentation of an exact number of steps.  `ExactIter` appends
the last step instead; the equivalence below lets the normal-form argument
peel the first transition of two deterministic runs. -/
def ForwardIter (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, source, target => source = target
  | steps + 1, source, target =>
      ∃ next, R source next ∧ ForwardIter R steps next target

private theorem exactIter_one {R : ℕ → ℕ → Prop} {source target : ℕ}
    (h : R source target) : ExactIter R 1 source target := by
  exact ⟨source, rfl, h⟩

private theorem exactIter_trans {R : ℕ → ℕ → Prop}
    {firstSteps secondSteps source middle target : ℕ}
    (hfirst : ExactIter R firstSteps source middle)
    (hsecond : ExactIter R secondSteps middle target) :
    ExactIter R (firstSteps + secondSteps) source target := by
  induction secondSteps generalizing target with
  | zero =>
      simpa only [Nat.add_zero] using hsecond ▸ hfirst
  | succ secondSteps ih =>
      rcases hsecond with ⟨beforeLast, hprefix, hlast⟩
      exact ⟨beforeLast, ih hprefix, hlast⟩

private theorem forwardIter_append_last {R : ℕ → ℕ → Prop}
    {steps source middle target : ℕ}
    (hprefix : ForwardIter R steps source middle) (hlast : R middle target) :
    ForwardIter R (steps + 1) source target := by
  induction steps generalizing source with
  | zero =>
      subst source
      exact ⟨target, hlast, rfl⟩
  | succ steps ih =>
      rcases hprefix with ⟨next, hnext, hprefix⟩
      exact ⟨next, hnext, ih hprefix⟩

theorem exactIter_iff_forwardIter (R : ℕ → ℕ → Prop)
    (steps source target : ℕ) :
    ExactIter R steps source target ↔ ForwardIter R steps source target := by
  constructor
  · intro h
    induction steps generalizing target with
    | zero => exact h
    | succ steps ih =>
        rcases h with ⟨beforeLast, hprefix, hlast⟩
        exact forwardIter_append_last (ih beforeLast hprefix) hlast
  · intro h
    induction steps generalizing source with
    | zero => exact h
    | succ steps ih =>
        rcases h with ⟨next, hfirst, hrest⟩
        have hone : ExactIter R 1 source next := exactIter_one hfirst
        have htail : ExactIter R steps next target := ih next hrest
        simpa only [Nat.add_comm] using exactIter_trans hone htail

theorem forwardIter_terminal_unique {R : ℕ → ℕ → Prop}
    (hdet : ∀ {source left right}, R source left → R source right → left = right)
    {leftSteps rightSteps source left right : ℕ}
    (hleftTerminal : ∀ target, ¬ R left target)
    (hrightTerminal : ∀ target, ¬ R right target)
    (hleft : ForwardIter R leftSteps source left)
    (hright : ForwardIter R rightSteps source right) :
    left = right := by
  induction leftSteps generalizing rightSteps source with
  | zero =>
      subst source
      cases rightSteps with
      | zero => exact hright
      | succ rightSteps =>
          rcases hright with ⟨next, hstep, _hrest⟩
          exact (hleftTerminal next hstep).elim
  | succ leftSteps ih =>
      rcases hleft with ⟨leftNext, hleftStep, hleftRest⟩
      cases rightSteps with
      | zero =>
          subst source
          exact (hrightTerminal leftNext hleftStep).elim
      | succ rightSteps =>
          rcases hright with ⟨rightNext, hrightStep, hrightRest⟩
          have hnext : leftNext = rightNext := hdet hleftStep hrightStep
          subst rightNext
          exact ih hleftRest hrightRest

theorem exactIter_terminal_unique {R : ℕ → ℕ → Prop}
    (hdet : ∀ {source left right}, R source left → R source right → left = right)
    {leftSteps rightSteps source left right : ℕ}
    (hleftTerminal : ∀ target, ¬ R left target)
    (hrightTerminal : ∀ target, ¬ R right target)
    (hleft : ExactIter R leftSteps source left)
    (hright : ExactIter R rightSteps source right) :
    left = right :=
  @forwardIter_terminal_unique R hdet leftSteps rightSteps source left right
    hleftTerminal hrightTerminal
    ((exactIter_iff_forwardIter R leftSteps source left).1 hleft)
    ((exactIter_iff_forwardIter R rightSteps source right).1 hright)

/-- Evaluation of a core hyperoperation always reaches its return state while
leaving the caller's pending stack untouched.  The nested induction mirrors
the defining recursion: first decrease the ordinary argument at the current
rank, then evaluate the pending call at the lower rank. -/
theorem hyperoperationCore_exactIter (rank base argument stack : ℕ) :
    ∃ steps,
      ExactIter HyperStep steps
        (hyperEvalCode base rank argument stack)
        (hyperReturnCode base (hyperoperationCore rank base argument) stack) := by
  induction rank generalizing argument stack with
  | zero =>
      exact ⟨1, exactIter_one <|
        (hyperStep_eval_rank_zero base argument stack _).2 rfl⟩
  | succ rank ihRank =>
      induction argument generalizing stack with
      | zero =>
          exact ⟨1, exactIter_one <|
            (hyperStep_eval_succ_zero rank base stack _).2 rfl⟩
      | succ argument ihArgument =>
          obtain ⟨firstSteps, hfirst⟩ :=
            ihArgument (hyperStackCons rank stack)
          obtain ⟨lastSteps, hlast⟩ :=
            ihRank (hyperoperationCore (rank + 1) base argument) stack
          have hpush : ExactIter HyperStep 1
              (hyperEvalCode base (rank + 1) (argument + 1) stack)
              (hyperEvalCode base (rank + 1) argument
                (hyperStackCons rank stack)) :=
            exactIter_one <|
              (hyperStep_eval_succ_succ rank base argument stack _).2 rfl
          have hpop : ExactIter HyperStep 1
              (hyperReturnCode base
                (hyperoperationCore (rank + 1) base argument)
                (hyperStackCons rank stack))
              (hyperEvalCode base rank
                (hyperoperationCore (rank + 1) base argument) stack) :=
            exactIter_one <|
              (hyperStep_return_cons rank base
                (hyperoperationCore (rank + 1) base argument) stack _).2 rfl
          refine ⟨((1 + firstSteps) + 1) + lastSteps, ?_⟩
          have hrun := exactIter_trans hpush hfirst
          have hrun := exactIter_trans hrun hpop
          have hrun := exactIter_trans hrun hlast
          simpa only [hyperoperationCore_succ_succ] using hrun

/-- Semantic characterization of the uniform exponentiation-and-above
hierarchy by terminating machine reachability. -/
theorem hyperoperationCore_eq_iff_exists_exactIter
    (result rank base argument : ℕ) :
    result = hyperoperationCore rank base argument ↔
      ∃ steps,
        ExactIter HyperStep steps
          (hyperEvalCode base rank argument 0)
          (hyperReturnCode base result 0) := by
  constructor
  · intro hresult
    subst result
    exact hyperoperationCore_exactIter rank base argument 0
  · rintro ⟨resultSteps, hresult⟩
    obtain ⟨correctSteps, hcorrect⟩ :=
      hyperoperationCore_exactIter rank base argument 0
    have hcodes :
        hyperReturnCode base (hyperoperationCore rank base argument) 0 =
          hyperReturnCode base result 0 :=
      @exactIter_terminal_unique HyperStep hyperStep_deterministic
        correctSteps resultSteps (hyperEvalCode base rank argument 0)
        (hyperReturnCode base (hyperoperationCore rank base argument) 0)
        (hyperReturnCode base result 0)
        (hyperReturnCode_empty_terminal base
          (hyperoperationCore rank base argument))
        (hyperReturnCode_empty_terminal base result) hcorrect hresult
    exact (hyperReturnCode_injective hcodes).2.1.symm

end PAListCoding
