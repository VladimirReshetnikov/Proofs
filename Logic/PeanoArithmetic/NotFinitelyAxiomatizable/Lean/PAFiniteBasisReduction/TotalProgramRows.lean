import PAFiniteBasisReduction.ProgramBetaCoding
import PAFiniteBasisReduction.PolynomialDecodeTransport

/-!
# Total standard rows for the polynomial program evaluator

The object-language evaluator has a row at every natural-number code, not
only at codes in the image of `Program.code`.  A malformed child can still
occur below a well-formed outer node, so the old partial decoder is not
enough.  Here we define, by strong recursion on the positive polynomial
code, the program which denotes the value of every standard row.  Malformed
shapes denote zero; recognized shapes recursively consume their strictly
smaller child codes.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- Polynomial-node fields bundled with the strict bounds supplied by the
positive node encoding. -/
abbrev BoundedNodeComponents (target : Nat) :=
  { fields : Nat × Nat // fields.1 < target /\ fields.2 < target }

/-- A fixed-length decoded vector bundled with the fact that every entry is
strictly below its (positive list) code. -/
abbrev BoundedVectorComponents (rank target : Nat) :=
  { fields : Fin rank -> Nat // forall i, fields i < target }

/-- Bound-carrying wrapper around `nodeComponents`.  Keeping the recursive
decrease certificate inside the decoded value avoids dependent match
equations in the strong-recursion body. -/
noncomputable def boundedNodeComponents (target : Nat) :
    Option (BoundedNodeComponents target) :=
  Option.pmap (fun fields h => ⟨fields, h⟩) (nodeComponents target)
    (fun _ h => nodeComponents_children_lt h)

theorem boundedNodeComponents_eq_some_iff {target : Nat}
    {fields : BoundedNodeComponents target} :
    boundedNodeComponents target = some fields ↔
      nodeComponents target = some fields.1 := by
  classical
  unfold boundedNodeComponents
  constructor
  . intro h
    rcases Option.pmap_eq_some_iff.mp h with
      ⟨raw, hrawBounds, hraw, heq⟩
    have hval : fields.1 = raw := congrArg Subtype.val heq
    simpa [hval] using hraw
  . intro hraw
    apply Option.pmap_eq_some_iff.mpr
    refine ⟨fields.1, fields.2, hraw, ?_⟩
    apply Subtype.ext
    rfl

/-- Bound-carrying wrapper around the fixed-length vector decoder. -/
noncomputable def boundedVectorComponents (rank target : Nat) :
    Option (BoundedVectorComponents rank target) :=
  Option.pmap (fun fields h => ⟨fields, h⟩)
    (vectorComponents rank target)
    (fun _ h i => vectorComponents_entries_lt h i)

theorem boundedVectorComponents_eq_some_iff {rank target : Nat}
    {fields : BoundedVectorComponents rank target} :
    boundedVectorComponents rank target = some fields ↔
      vectorComponents rank target = some fields.1 := by
  classical
  unfold boundedVectorComponents
  constructor
  . intro h
    rcases Option.pmap_eq_some_iff.mp h with
      ⟨raw, hrawBounds, hraw, heq⟩
    have hval : fields.1 = raw := congrArg Subtype.val heq
    simpa [hval] using hraw
  . intro hraw
    apply Option.pmap_eq_some_iff.mpr
    refine ⟨fields.1, fields.2, hraw, ?_⟩
    apply Subtype.ext
    rfl

/-- One unfolding step of the total external row evaluator.  The `previous`
argument may be used only at codes strictly below `target`; all such bounds
come from positivity of the polynomial node/list encodings. -/
noncomputable def totalRowProgramStep (rank target : Nat)
    (previous : (child : Nat) -> child < target -> Program rank) :
    Program rank :=
  match boundedNodeComponents target with
  | none => .zero
  | some outer =>
      let tag := outer.1.1
      let payload := outer.1.2
      if tag = 0 /\ payload = 0 then .star
      else if tag = 1 /\ payload = 0 then .zero
      else if tag = 2 then .succ (previous payload outer.2.2)
      else if tag = 3 then
        match boundedNodeComponents payload with
        | none => .zero
        | some children => .add
            (previous children.1.1
              (Nat.lt_trans children.2.1 outer.2.2))
            (previous children.1.2
              (Nat.lt_trans children.2.2 outer.2.2))
      else if tag = 4 then
        match boundedNodeComponents payload with
        | none => .zero
        | some children => .mul
            (previous children.1.1
              (Nat.lt_trans children.2.1 outer.2.2))
            (previous children.1.2
              (Nat.lt_trans children.2.2 outer.2.2))
      else if tag = 5 then
        match boundedNodeComponents payload with
        | none => .zero
        | some fields =>
            match boundedVectorComponents rank fields.1.2 with
            | none => .zero
            | some children =>
                match exBodyAt rank fields.1.1 with
                | none => .zero
                | some entry => .exSkolem entry.body entry.quantifiedRank
                    (fun i => previous (children.1 i) <| Nat.lt_trans
                      (children.2 i) <| Nat.lt_trans fields.2.2 outer.2.2)
      else if tag = 6 then
        match boundedNodeComponents payload with
        | none => .zero
        | some fields =>
            match boundedVectorComponents rank fields.1.2 with
            | none => .zero
            | some children =>
                match allBodyAt rank fields.1.1 with
                | none => .zero
                | some entry => .allSkolem entry.body entry.quantifiedRank
                    (fun i => previous (children.1 i) <| Nat.lt_trans
                      (children.2 i) <| Nat.lt_trans fields.2.2 outer.2.2)
      else .zero

/-- Program denoting the value assigned to an arbitrary standard row. -/
noncomputable def totalRowProgram (rank : Nat) : Nat -> Program rank :=
  Nat.lt_wfRel.wf.fix (totalRowProgramStep rank)

theorem totalRowProgram_eq (rank target : Nat) :
    totalRowProgram rank target =
      totalRowProgramStep rank target
        (fun child _ => totalRowProgram rank child) := by
  apply WellFounded.fix_eq

theorem totalRowProgram_of_star {rank target : Nat}
    {outer : BoundedNodeComponents target}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 0) (hpayload : outer.1.2 = 0) :
    totalRowProgram rank target = .star := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload]

theorem totalRowProgram_of_zero {rank target : Nat}
    {outer : BoundedNodeComponents target}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 1) (hpayload : outer.1.2 = 0) :
    totalRowProgram rank target = .zero := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload]

theorem totalRowProgram_of_succ {rank target child : Nat}
    {outer : BoundedNodeComponents target}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 2) (hpayload : outer.1.2 = child) :
    totalRowProgram rank target = .succ (totalRowProgram rank child) := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload]

theorem totalRowProgram_of_add {rank target payload left right : Nat}
    {outer : BoundedNodeComponents target}
    {children : BoundedNodeComponents outer.1.2}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 3) (hpayload : outer.1.2 = payload)
    (hchildren : boundedNodeComponents outer.1.2 = some children)
    (hleft : children.1.1 = left) (hright : children.1.2 = right) :
    totalRowProgram rank target =
      .add (totalRowProgram rank left) (totalRowProgram rank right) := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload, hchildren,
    hleft, hright]

theorem totalRowProgram_of_mul {rank target payload left right : Nat}
    {outer : BoundedNodeComponents target}
    {children : BoundedNodeComponents outer.1.2}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 4) (hpayload : outer.1.2 = payload)
    (hchildren : boundedNodeComponents outer.1.2 = some children)
    (hleft : children.1.1 = left) (hright : children.1.2 = right) :
    totalRowProgram rank target =
      .mul (totalRowProgram rank left) (totalRowProgram rank right) := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload, hchildren,
    hleft, hright]

theorem totalRowProgram_of_ex {rank target payload : Nat}
    {outer : BoundedNodeComponents target}
    {fields : BoundedNodeComponents outer.1.2}
    {children : BoundedVectorComponents rank fields.1.2}
    {entry : ExBodyEntry rank fields.1.1}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 5) (hpayload : outer.1.2 = payload)
    (hnode : boundedNodeComponents outer.1.2 = some fields)
    (hargs : boundedVectorComponents rank fields.1.2 = some children)
    (hbody : exBodyAt rank fields.1.1 = some entry) :
    totalRowProgram rank target =
      .exSkolem entry.body entry.quantifiedRank
        (fun i => totalRowProgram rank (children.1 i)) := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload, hnode,
    hargs, hbody]

theorem totalRowProgram_of_all {rank target payload : Nat}
    {outer : BoundedNodeComponents target}
    {fields : BoundedNodeComponents outer.1.2}
    {children : BoundedVectorComponents rank fields.1.2}
    {entry : AllBodyEntry rank fields.1.1}
    (houter : boundedNodeComponents target = some outer)
    (htag : outer.1.1 = 6) (hpayload : outer.1.2 = payload)
    (hnode : boundedNodeComponents outer.1.2 = some fields)
    (hargs : boundedVectorComponents rank fields.1.2 = some children)
    (hbody : allBodyAt rank fields.1.1 = some entry) :
    totalRowProgram rank target =
      .allSkolem entry.body entry.quantifiedRank
        (fun i => totalRowProgram rank (children.1 i)) := by
  rw [totalRowProgram_eq]
  simp [totalRowProgramStep, houter, htag, hpayload, hnode,
    hargs, hbody]

/-! Raw-decoder corollaries used by semantic inversion of a standard row. -/

theorem totalRowProgram_of_star_components {rank target : Nat}
    (houter : nodeComponents target = some (0, 0)) :
    totalRowProgram rank target = .star := by
  let outer : BoundedNodeComponents target :=
    ⟨(0, 0), nodeComponents_children_lt houter⟩
  apply totalRowProgram_of_star
    (outer := outer) (boundedNodeComponents_eq_some_iff.mpr houter)
  · rfl
  · rfl

theorem totalRowProgram_of_zero_components {rank target : Nat}
    (houter : nodeComponents target = some (1, 0)) :
    totalRowProgram rank target = .zero := by
  let outer : BoundedNodeComponents target :=
    ⟨(1, 0), nodeComponents_children_lt houter⟩
  apply totalRowProgram_of_zero
    (outer := outer) (boundedNodeComponents_eq_some_iff.mpr houter)
  · rfl
  · rfl

theorem totalRowProgram_of_succ_components {rank target child : Nat}
    (houter : nodeComponents target = some (2, child)) :
    totalRowProgram rank target = .succ (totalRowProgram rank child) := by
  let outer : BoundedNodeComponents target :=
    ⟨(2, child), nodeComponents_children_lt houter⟩
  apply totalRowProgram_of_succ
    (outer := outer) (boundedNodeComponents_eq_some_iff.mpr houter)
  · rfl
  · rfl

theorem totalRowProgram_of_add_components
    {rank target payload left right : Nat}
    (houter : nodeComponents target = some (3, payload))
    (hchildren : nodeComponents payload = some (left, right)) :
    totalRowProgram rank target =
      .add (totalRowProgram rank left) (totalRowProgram rank right) := by
  let outer : BoundedNodeComponents target :=
    ⟨(3, payload), nodeComponents_children_lt houter⟩
  let children : BoundedNodeComponents payload :=
    ⟨(left, right), nodeComponents_children_lt hchildren⟩
  exact totalRowProgram_of_add
    (outer := outer) (children := children)
    (boundedNodeComponents_eq_some_iff.mpr houter) rfl rfl
    (boundedNodeComponents_eq_some_iff.mpr hchildren) rfl rfl

theorem totalRowProgram_of_mul_components
    {rank target payload left right : Nat}
    (houter : nodeComponents target = some (4, payload))
    (hchildren : nodeComponents payload = some (left, right)) :
    totalRowProgram rank target =
      .mul (totalRowProgram rank left) (totalRowProgram rank right) := by
  let outer : BoundedNodeComponents target :=
    ⟨(4, payload), nodeComponents_children_lt houter⟩
  let children : BoundedNodeComponents payload :=
    ⟨(left, right), nodeComponents_children_lt hchildren⟩
  exact totalRowProgram_of_mul
    (outer := outer) (children := children)
    (boundedNodeComponents_eq_some_iff.mpr houter) rfl rfl
    (boundedNodeComponents_eq_some_iff.mpr hchildren) rfl rfl

theorem totalRowProgram_of_ex_components
    {rank target payload index vector : Nat}
    {children : Fin rank → Nat} {entry : ExBodyEntry rank index}
    (houter : nodeComponents target = some (5, payload))
    (hnode : nodeComponents payload = some (index, vector))
    (hargs : vectorComponents rank vector = some children)
    (hbody : exBodyAt rank index = some entry) :
    totalRowProgram rank target =
      .exSkolem entry.body entry.quantifiedRank
        (fun i => totalRowProgram rank (children i)) := by
  let outer : BoundedNodeComponents target :=
    ⟨(5, payload), nodeComponents_children_lt houter⟩
  let fields : BoundedNodeComponents payload :=
    ⟨(index, vector), nodeComponents_children_lt hnode⟩
  let args : BoundedVectorComponents rank vector :=
    ⟨children, fun i => vectorComponents_entries_lt hargs i⟩
  exact totalRowProgram_of_ex
    (outer := outer) (fields := fields) (children := args)
    (entry := entry) (boundedNodeComponents_eq_some_iff.mpr houter)
    rfl rfl (boundedNodeComponents_eq_some_iff.mpr hnode)
    (boundedVectorComponents_eq_some_iff.mpr hargs) hbody

theorem totalRowProgram_of_all_components
    {rank target payload index vector : Nat}
    {children : Fin rank → Nat} {entry : AllBodyEntry rank index}
    (houter : nodeComponents target = some (6, payload))
    (hnode : nodeComponents payload = some (index, vector))
    (hargs : vectorComponents rank vector = some children)
    (hbody : allBodyAt rank index = some entry) :
    totalRowProgram rank target =
      .allSkolem entry.body entry.quantifiedRank
        (fun i => totalRowProgram rank (children i)) := by
  let outer : BoundedNodeComponents target :=
    ⟨(6, payload), nodeComponents_children_lt houter⟩
  let fields : BoundedNodeComponents payload :=
    ⟨(index, vector), nodeComponents_children_lt hnode⟩
  let args : BoundedVectorComponents rank vector :=
    ⟨children, fun i => vectorComponents_entries_lt hargs i⟩
  exact totalRowProgram_of_all
    (outer := outer) (fields := fields) (children := args)
    (entry := entry) (boundedNodeComponents_eq_some_iff.mpr houter)
    rfl rfl (boundedNodeComponents_eq_some_iff.mpr hnode)
    (boundedVectorComponents_eq_some_iff.mpr hargs) hbody

/-- On an actual polynomial program code, total row decoding returns the
original program.  This is the bridge from the total table (which also has
malformed rows) back to the requested hull element. -/
@[simp] theorem totalRowProgram_code (p : Program rank) :
    totalRowProgram rank (Program.code p) = p := by
  classical
  induction p with
  | star =>
      let outer : BoundedNodeComponents (Program.nodeCode 0 0) :=
        ⟨(0, 0), Program.left_lt_nodeCode 0 0,
          Program.right_lt_nodeCode 0 0⟩
      have houter : boundedNodeComponents (Program.nodeCode 0 0) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      exact totalRowProgram_of_star houter rfl rfl
  | zero =>
      let outer : BoundedNodeComponents (Program.nodeCode 1 0) :=
        ⟨(1, 0), Program.left_lt_nodeCode 1 0,
          Program.right_lt_nodeCode 1 0⟩
      have houter : boundedNodeComponents (Program.nodeCode 1 0) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      exact totalRowProgram_of_zero houter rfl rfl
  | succ p ih =>
      change totalRowProgram rank (Program.nodeCode 2 (Program.code p)) = _
      let outer : BoundedNodeComponents
          (Program.nodeCode 2 (Program.code p)) :=
        ⟨(2, Program.code p), Program.left_lt_nodeCode 2 (Program.code p),
          Program.right_lt_nodeCode 2 (Program.code p)⟩
      have houter : boundedNodeComponents
          (Program.nodeCode 2 (Program.code p)) = some outer :=
        boundedNodeComponents_eq_some_iff.mpr
          (nodeComponents_eq_some_iff.mpr rfl)
      rw [totalRowProgram_of_succ houter rfl rfl, ih]
  | add left right ihLeft ihRight =>
      change totalRowProgram rank
        (Program.nodeCode 3
          (Program.nodeCode (Program.code left) (Program.code right))) = _
      let payload := Program.nodeCode (Program.code left) (Program.code right)
      let outer : BoundedNodeComponents (Program.nodeCode 3 payload) :=
        ⟨(3, payload), Program.left_lt_nodeCode 3 payload,
          Program.right_lt_nodeCode 3 payload⟩
      let children : BoundedNodeComponents payload :=
        ⟨(Program.code left, Program.code right),
          Program.left_lt_nodeCode _ _, Program.right_lt_nodeCode _ _⟩
      have houter : boundedNodeComponents (Program.nodeCode 3 payload) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      have hchildren : boundedNodeComponents outer.1.2 = some children :=
        boundedNodeComponents_eq_some_iff.mpr
          (nodeComponents_eq_some_iff.mpr rfl)
      rw [totalRowProgram_of_add houter rfl rfl hchildren rfl rfl,
        ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      change totalRowProgram rank
        (Program.nodeCode 4
          (Program.nodeCode (Program.code left) (Program.code right))) = _
      let payload := Program.nodeCode (Program.code left) (Program.code right)
      let outer : BoundedNodeComponents (Program.nodeCode 4 payload) :=
        ⟨(4, payload), Program.left_lt_nodeCode 4 payload,
          Program.right_lt_nodeCode 4 payload⟩
      let children : BoundedNodeComponents payload :=
        ⟨(Program.code left, Program.code right),
          Program.left_lt_nodeCode _ _, Program.right_lt_nodeCode _ _⟩
      have houter : boundedNodeComponents (Program.nodeCode 4 payload) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      have hchildren : boundedNodeComponents outer.1.2 = some children :=
        boundedNodeComponents_eq_some_iff.mpr
          (nodeComponents_eq_some_iff.mpr rfl)
      rw [totalRowProgram_of_mul houter rfl rfl hchildren rfl rfl,
        ihLeft, ihRight]
  | exSkolem body hRank args ih =>
      rcases exBodyAt_complete body hRank with
        ⟨entry, hentry, hbody⟩
      change totalRowProgram rank
        (Program.nodeCode 5
          (Program.nodeCode (Program.formulaIndex rank body)
            (Program.vectorCode (fun i => Program.code (args i))))) = _
      let childCodes := fun i : Fin rank => Program.code (args i)
      let vector := Program.vectorCode childCodes
      let payload := Program.nodeCode (Program.formulaIndex rank body) vector
      let outer : BoundedNodeComponents (Program.nodeCode 5 payload) :=
        ⟨(5, payload), Program.left_lt_nodeCode 5 payload,
          Program.right_lt_nodeCode 5 payload⟩
      let fields : BoundedNodeComponents payload :=
        ⟨(Program.formulaIndex rank body, vector),
          Program.left_lt_nodeCode _ _, Program.right_lt_nodeCode _ _⟩
      let children : BoundedVectorComponents rank vector :=
        ⟨childCodes, fun i => Program.vector_entry_lt_code childCodes i⟩
      have houter : boundedNodeComponents (Program.nodeCode 5 payload) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      have hfields : boundedNodeComponents outer.1.2 = some fields :=
        boundedNodeComponents_eq_some_iff.mpr
          (nodeComponents_eq_some_iff.mpr rfl)
      have hchildren : boundedVectorComponents rank fields.1.2 =
          some children := boundedVectorComponents_eq_some_iff.mpr
        (vectorComponents_eq_some_iff.mpr rfl)
      have hentry' : exBodyAt rank fields.1.1 = some entry := hentry
      rw [totalRowProgram_of_ex houter rfl rfl hfields hchildren hentry']
      apply Program.code_injective
      simp [Program.code, childCodes, children, hbody, ih]

  | allSkolem body hRank args ih =>
      rcases allBodyAt_complete body hRank with
        ⟨entry, hentry, hbody⟩
      change totalRowProgram rank
        (Program.nodeCode 6
          (Program.nodeCode (Program.formulaIndex rank body)
            (Program.vectorCode (fun i => Program.code (args i))))) = _
      let childCodes := fun i : Fin rank => Program.code (args i)
      let vector := Program.vectorCode childCodes
      let payload := Program.nodeCode (Program.formulaIndex rank body) vector
      let outer : BoundedNodeComponents (Program.nodeCode 6 payload) :=
        ⟨(6, payload), Program.left_lt_nodeCode 6 payload,
          Program.right_lt_nodeCode 6 payload⟩
      let fields : BoundedNodeComponents payload :=
        ⟨(Program.formulaIndex rank body, vector),
          Program.left_lt_nodeCode _ _, Program.right_lt_nodeCode _ _⟩
      let children : BoundedVectorComponents rank vector :=
        ⟨childCodes, fun i => Program.vector_entry_lt_code childCodes i⟩
      have houter : boundedNodeComponents (Program.nodeCode 6 payload) =
          some outer := boundedNodeComponents_eq_some_iff.mpr
        (nodeComponents_eq_some_iff.mpr rfl)
      have hfields : boundedNodeComponents outer.1.2 = some fields :=
        boundedNodeComponents_eq_some_iff.mpr
          (nodeComponents_eq_some_iff.mpr rfl)
      have hchildren : boundedVectorComponents rank fields.1.2 =
          some children := boundedVectorComponents_eq_some_iff.mpr
        (vectorComponents_eq_some_iff.mpr rfl)
      have hentry' : allBodyAt rank fields.1.1 = some entry := hentry
      rw [totalRowProgram_of_all houter rfl rfl hfields hchildren hentry']
      apply Program.code_injective
      simp [Program.code, childCodes, children, hbody, ih]

/-! ## Finite total-row tables -/

/-- The programs denoting rows `0, ..., target`, in beta-table order. -/
noncomputable def standardRowPrograms (rank target : Nat) :
    List (Program rank) :=
  List.ofFn (fun i : Fin (target + 1) => totalRowProgram rank i.val)

@[simp] theorem standardRowPrograms_length (rank target : Nat) :
    (standardRowPrograms rank target).length = target + 1 := by
  simp [standardRowPrograms]

@[simp] theorem standardRowPrograms_get (rank target : Nat)
    (i : Fin (standardRowPrograms rank target).length) :
    (standardRowPrograms rank target).get i =
      totalRowProgram rank i.val := by
  rw [List.get_eq_getElem]
  change (List.ofFn (fun j : Fin (target + 1) =>
    totalRowProgram rank j.val))[i.val] = totalRowProgram rank i.val
  rw [List.getElem_ofFn]

/-- The total standard rows through any external bound admit beta parameters
which are themselves denoted by finite Skolem programs.  Consequently both
beta parameters belong to the eventual Skolem hull. -/
theorem finite_total_row_beta_programs {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (S : CanonicalSelectors M) (star : alpha)
    (hSupport : ProgramBetaCoding.supportRank ≤ rank) (target : Nat) :
    ∃ codeProgram stepProgram : Program rank,
      ∀ k ≤ target,
        RawBetaEntry M (Program.eval M S star (totalRowProgram rank k))
          (Program.eval M S star codeProgram)
          (Program.eval M S star stepProgram)
          (PA.Term.numeralValue M k) := by
  rcases ProgramBetaCoding.finite_list_beta_programs hPA S star hSupport
      (standardRowPrograms rank target) with
    ⟨codeProgram, stepProgram, htable⟩
  refine ⟨codeProgram, stepProgram, ?_⟩
  intro k hk
  let i : Fin ((standardRowPrograms rank target).map
      (Program.eval M S star)).length :=
    ⟨k, by simp; omega⟩
  have hentry := htable i
  simp only [List.get_eq_getElem, List.getElem_map] at hentry
  have hi : k < (standardRowPrograms rank target).length := by
    simp
    omega
  have hget : (standardRowPrograms rank target)[k] =
      totalRowProgram rank k := by
    change (standardRowPrograms rank target).get ⟨k, hi⟩ = _
    exact standardRowPrograms_get rank target ⟨k, hi⟩
  simpa [i, hget] using hentry

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
