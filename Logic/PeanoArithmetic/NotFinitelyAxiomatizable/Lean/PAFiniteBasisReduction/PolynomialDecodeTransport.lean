import PAFiniteBasisReduction.HullProgramTrace

/-!
# Standard decoding facts for polynomial program nodes

Program rows explicitly bound every child code by its parent code.  At a
standard parent this makes each child standard by PA's discrete-order facts.
The lemmas here then reduce polynomial node and list equations to the external
injective encodings on `Nat`.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u v

namespace FiniteSkolemCut
namespace ProgramTrace

/-! ## External partial inverses -/

/-- Partial inverse of the injective positive polynomial node code. -/
noncomputable def nodeComponents (target : Nat) : Option (Nat × Nat) :=
  by
    classical
    exact if h : ∃ fields : Nat × Nat,
        Program.nodeCode fields.1 fields.2 = target then
      some (Classical.choose h)
    else
      none

theorem nodeComponents_eq_some_iff {target left right : Nat} :
    nodeComponents target = some (left, right) ↔
      Program.nodeCode left right = target := by
  classical
  constructor
  · intro h
    unfold nodeComponents at h
    split at h
    next hex =>
      have hp : Classical.choose hex = (left, right) := Option.some.inj h
      simpa [hp] using Classical.choose_spec hex
    next => simp at h
  · intro hcode
    have hex : ∃ fields : Nat × Nat,
        Program.nodeCode fields.1 fields.2 = target :=
      ⟨(left, right), hcode⟩
    unfold nodeComponents
    rw [dif_pos hex]
    apply congrArg some
    apply Prod.ext
    · exact (Program.nodeCode_injective
        ((Classical.choose_spec hex).trans hcode.symm)).1
    · exact (Program.nodeCode_injective
        ((Classical.choose_spec hex).trans hcode.symm)).2

theorem nodeComponents_children_lt {target left right : Nat}
    (h : nodeComponents target = some (left, right)) :
    left < target ∧ right < target := by
  have hcode := nodeComponents_eq_some_iff.mp h
  rw [← hcode]
  exact ⟨Program.left_lt_nodeCode left right,
    Program.right_lt_nodeCode left right⟩

/-- Partial inverse of the fixed-length vector code. -/
noncomputable def vectorComponents (rank target : Nat) :
    Option (Fin rank → Nat) :=
  by
    classical
    exact if h : ∃ fields : Fin rank → Nat,
        Program.vectorCode fields = target then
      some (Classical.choose h)
    else
      none

theorem vectorComponents_eq_some_iff {rank target : Nat}
    {fields : Fin rank → Nat} :
    vectorComponents rank target = some fields ↔
      Program.vectorCode fields = target := by
  classical
  constructor
  · intro h
    unfold vectorComponents at h
    split at h
    next hex =>
      have hp : Classical.choose hex = fields := Option.some.inj h
      simpa [hp] using Classical.choose_spec hex
    next => simp at h
  · intro hcode
    have hex : ∃ fields : Fin rank → Nat,
        Program.vectorCode fields = target := ⟨fields, hcode⟩
    unfold vectorComponents
    rw [dif_pos hex]
    apply congrArg some
    apply Program.vectorCode_injective
    exact (Classical.choose_spec hex).trans hcode.symm

theorem vectorComponents_entries_lt {rank target : Nat}
    {fields : Fin rank → Nat}
    (h : vectorComponents rank target = some fields)
    (i : Fin rank) : fields i < target := by
  have hcode := vectorComponents_eq_some_iff.mp h
  rw [← hcode]
  exact Program.vector_entry_lt_code fields i

/-! ## Formula-index dispatch -/

/-- A formula body decoded for an existential Skolem row, carrying exactly
the evidence needed by `Program.exSkolem`. -/
structure ExBodyEntry (rank index : Nat) where
  body : PA.Formula
  quantifiedRank : formulaRank (PA.Formula.ex body) ≤ rank
  index_eq : Program.formulaIndex rank body = index

/-- A formula body decoded for a universal-counterexample Skolem row. -/
structure AllBodyEntry (rank index : Nat) where
  body : PA.Formula
  quantifiedRank : formulaRank (PA.Formula.all body) ≤ rank
  index_eq : Program.formulaIndex rank body = index

noncomputable def exBodyAt (rank index : Nat) :
    Option (ExBodyEntry rank index) := by
  classical
  exact if h : Nonempty (ExBodyEntry rank index) then
    some (Classical.choice h)
  else
    none

noncomputable def allBodyAt (rank index : Nat) :
    Option (AllBodyEntry rank index) := by
  classical
  exact if h : Nonempty (AllBodyEntry rank index) then
    some (Classical.choice h)
  else
    none

theorem ExBodyEntry.body_rank {rank index : Nat}
    (entry : ExBodyEntry rank index) : formulaRank entry.body ≤ rank := by
  have h := entry.quantifiedRank
  simp only [formulaRank] at h
  omega

theorem AllBodyEntry.body_rank {rank index : Nat}
    (entry : AllBodyEntry rank index) : formulaRank entry.body ≤ rank := by
  have h := entry.quantifiedRank
  simp only [formulaRank] at h
  omega

theorem ExBodyEntry.body_unique {rank index : Nat}
    (left right : ExBodyEntry rank index) : left.body = right.body := by
  apply Program.formulaIndex_injective_of_rank left.body_rank right.body_rank
  exact left.index_eq.trans right.index_eq.symm

theorem AllBodyEntry.body_unique {rank index : Nat}
    (left right : AllBodyEntry rank index) : left.body = right.body := by
  apply Program.formulaIndex_injective_of_rank left.body_rank right.body_rank
  exact left.index_eq.trans right.index_eq.symm

theorem exBodyAt_complete {rank : Nat} (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.ex body) ≤ rank) :
    ∃ entry : ExBodyEntry rank (Program.formulaIndex rank body),
      exBodyAt rank (Program.formulaIndex rank body) = some entry ∧
      entry.body = body := by
  classical
  let actual : ExBodyEntry rank (Program.formulaIndex rank body) :=
    ⟨body, hRank, rfl⟩
  have hnonempty : Nonempty
      (ExBodyEntry rank (Program.formulaIndex rank body)) := ⟨actual⟩
  let chosen := Classical.choice hnonempty
  refine ⟨chosen, ?_, chosen.body_unique actual⟩
  simp [exBodyAt, hnonempty, chosen]

theorem allBodyAt_complete {rank : Nat} (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.all body) ≤ rank) :
    ∃ entry : AllBodyEntry rank (Program.formulaIndex rank body),
      allBodyAt rank (Program.formulaIndex rank body) = some entry ∧
      entry.body = body := by
  classical
  let actual : AllBodyEntry rank (Program.formulaIndex rank body) :=
    ⟨body, hRank, rfl⟩
  have hnonempty : Nonempty
      (AllBodyEntry rank (Program.formulaIndex rank body)) := ⟨actual⟩
  let chosen := Classical.choice hnonempty
  refine ⟨chosen, ?_, chosen.body_unique actual⟩
  simp [allBodyAt, hnonempty, chosen]

/-- A closed polynomial node term evaluates to the corresponding external
standard node code in every ambient PA model. -/
theorem eval_nodeTerm_numerals {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (left right : Nat) (e : Nat → alpha) :
    PA.Term.eval M e
        (nodeTerm (PA.Term.numeral left) (PA.Term.numeral right)) =
      PA.Term.numeralValue M (Program.nodeCode left right) := by
  have hsat := sat_of_bprov_axs hPA
    (bprov_nodeTerm_normalize
      (PA.Formula.BProv_eqRefl (B := PA.Formula.Ax_s) (G := [])
        (PA.Term.numeral left))
      (PA.Formula.BProv_eqRefl (B := PA.Formula.Ax_s) (G := [])
        (PA.Term.numeral right))) e
  simpa [PA.Formula.Sat, PA.Term.eval_numeral] using hsat

/-- Once the two arguments of a polynomial node are standard, equality with
a standard numeral is exactly equality of the external node codes. -/
theorem nodeCode_eq_of_eval_nodeTerm_eq_numeral
    {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (leftTerm rightTerm : PA.Term)
    (e : Nat → alpha) (left right target : Nat)
    (hleft : PA.Term.eval M e leftTerm = PA.Term.numeralValue M left)
    (hright : PA.Term.eval M e rightTerm = PA.Term.numeralValue M right)
    (hnode : PA.Term.eval M e (nodeTerm leftTerm rightTerm) =
      PA.Term.numeralValue M target) :
    Program.nodeCode left right = target := by
  apply numeralValue_injective_of_pa hPA
  calc
    PA.Term.numeralValue M (Program.nodeCode left right) =
        PA.Term.eval M e
          (nodeTerm (PA.Term.numeral left) (PA.Term.numeral right)) :=
      (eval_nodeTerm_numerals hPA left right e).symm
    _ = PA.Term.eval M e (nodeTerm leftTerm rightTerm) := by
      simp only [eval_nodeTerm, PA.Term.eval_numeral]
      rw [hleft, hright]
    _ = PA.Term.numeralValue M target := hnode

/-- A term-built list whose entries are standard evaluates to the external
self-delimiting list code of those entries. -/
theorem eval_listTerm_standard_entries {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {beta : Type v}
    (xs : List beta) (term : beta → PA.Term) (value : beta → Nat)
    (e : Nat → alpha)
    (h : ∀ x ∈ xs,
      PA.Term.eval M e (term x) = PA.Term.numeralValue M (value x)) :
    PA.Term.eval M e (listTerm (xs.map term)) =
      PA.Term.numeralValue M (Program.listCode (xs.map value)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, listTerm, Program.listCode]
      calc
        PA.Term.eval M e (nodeTerm (term x) (listTerm (xs.map term))) =
            PA.Term.eval M e
              (nodeTerm (PA.Term.numeral (value x))
                (PA.Term.numeral (Program.listCode (xs.map value)))) := by
          simp only [eval_nodeTerm, PA.Term.eval_numeral]
          rw [h x (by simp), ih]
          intro y hy
          exact h y (by simp [hy])
        _ = PA.Term.numeralValue M
              (Program.nodeCode (value x)
                (Program.listCode (xs.map value))) :=
          eval_nodeTerm_numerals hPA (value x)
            (Program.listCode (xs.map value)) e

/-- Bounded polynomial-node arguments under a standard parent code are
standard, and the raw node equation reduces to the external `nodeCode`.
The strict bounds are intended to come directly from the row formula. -/
theorem standard_node_components_of_bounds {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    {left right : alpha} {target : Nat}
    (hleftBound : RawLt M left (PA.Term.numeralValue M target))
    (hrightBound : RawLt M right (PA.Term.numeralValue M target))
    (hnode : M.succ
        (M.add
          (M.mul (M.add left right) (M.add left right)) left) =
      PA.Term.numeralValue M target) :
    ∃ leftCode rightCode,
      leftCode < target ∧ rightCode < target ∧
      left = PA.Term.numeralValue M leftCode ∧
      right = PA.Term.numeralValue M rightCode ∧
      Program.nodeCode leftCode rightCode = target := by
  rcases rawLt_numeralValue_cases hPA target hleftBound with
    ⟨leftCode, hleftLt, hleft⟩
  rcases rawLt_numeralValue_cases hPA target hrightBound with
    ⟨rightCode, hrightLt, hright⟩
  refine ⟨leftCode, rightCode, hleftLt, hrightLt, hleft, hright, ?_⟩
  let e : Nat → alpha := scons left (scons right (fun _ => M.zero))
  apply nodeCode_eq_of_eval_nodeTerm_eq_numeral hPA
    (PA.Term.var 0) (PA.Term.var 1) e leftCode rightCode target
  · simpa [e, PA.Term.eval, scons] using hleft
  · simpa [e, PA.Term.eval, scons] using hright
  · simpa [e, eval_nodeTerm, PA.Term.eval, scons] using hnode

/-- A fixed-length tuple of child-code terms bounded by a standard parent is
an externally standard vector, and its object-language list term denotes the
corresponding external vector code. -/
theorem standard_argumentVector_of_bounds {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    {rank target : Nat} (terms : Fin rank → PA.Term) (e : Nat → alpha)
    (hbounds : ∀ i : Fin rank,
      RawLt M (PA.Term.eval M e (terms i))
        (PA.Term.numeralValue M target)) :
    ∃ codes : Fin rank → Nat,
      (∀ i, codes i < target) ∧
      (∀ i, PA.Term.eval M e (terms i) =
        PA.Term.numeralValue M (codes i)) ∧
      PA.Term.eval M e (listTerm (List.ofFn terms)) =
        PA.Term.numeralValue M (Program.vectorCode codes) := by
  classical
  have hstandard (i : Fin rank) :
      ∃ code, code < target ∧
        PA.Term.eval M e (terms i) = PA.Term.numeralValue M code :=
    rawLt_numeralValue_cases hPA target (hbounds i)
  let codes : Fin rank → Nat := fun i => (hstandard i).choose
  have hcodesLt (i : Fin rank) : codes i < target :=
    (hstandard i).choose_spec.1
  have hcodesEval (i : Fin rank) :
      PA.Term.eval M e (terms i) = PA.Term.numeralValue M (codes i) :=
    (hstandard i).choose_spec.2
  refine ⟨codes, hcodesLt, hcodesEval, ?_⟩
  let indices : List (Fin rank) := List.ofFn (fun i : Fin rank => i)
  have hlist := eval_listTerm_standard_entries hPA indices
    (fun i => terms i) (fun i => codes i) e (by
      intro i hi
      exact hcodesEval i)
  simpa [indices, Program.vectorCode, List.map_ofFn,
    Function.comp_def] using hlist

/-- Equality of two standard polynomial nodes determines both children. -/
theorem standard_node_injective {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {a b c d : Nat}
    (h : PA.Term.numeralValue M (Program.nodeCode a b) =
      PA.Term.numeralValue M (Program.nodeCode c d)) :
    a = c ∧ b = d := by
  apply Program.nodeCode_injective
  exact numeralValue_injective_of_pa hPA h

/-- Equality of standard self-delimiting list codes determines the list. -/
theorem standard_listCode_injective {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {xs ys : List Nat}
    (h : PA.Term.numeralValue M (Program.listCode xs) =
      PA.Term.numeralValue M (Program.listCode ys)) :
    xs = ys := by
  apply Program.listCode_injective
  exact numeralValue_injective_of_pa hPA h

end ProgramTrace
end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
