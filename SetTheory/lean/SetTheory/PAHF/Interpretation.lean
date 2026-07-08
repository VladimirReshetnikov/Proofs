/-
  SetTheory.PAHF.Interpretation

  Syntactic term/formula interpretation (`termGraphAt`, `formulaAt`, `translateFormula`), the theory-interpretation layer, and the final PA <-> HF bi-interpretability certificates.
-/
import SetTheory.Completeness
import SetTheory.PAHF.PASyntax

namespace SetTheory

/-! ## Syntactic interpretation and the bi-interpretation certificates -/

namespace AckermannHF

/-- Equality of ordinal-coded HF objects follows from equality of their decoded
natural numbers. -/
theorem ordinal_eq_of_natOfOrdinal_eq {a b : OrdinalHF}
    (h : natOfOrdinal a = natOfOrdinal b) : a = b := by
  apply Subtype.ext
  rw [← natOfOrdinal_spec a, ← natOfOrdinal_spec b, h]

/-- Set-theoretic successor on finite ordinals: `a ↦ a ∪ {a}`. -/
noncomputable def ordinalSuccSet (a : OrdinalHF) : OrdinalHF :=
  ⟨adjoin a.val a.val,
    ⟨natOfOrdinal a + 1, by
      rw [ordinalCode_succ, natOfOrdinal_spec a]⟩⟩

theorem ordinalSuccSet_eq (a : OrdinalHF) :
    ordinalSuccSet a = ordinalOfNat (natOfOrdinal a + 1) := by
  apply Subtype.ext
  simp only [ordinalSuccSet, ordinalOfNat]
  rw [ordinalCode_succ, natOfOrdinal_spec a]

theorem natOfOrdinal_ordinalSuccSet (a : OrdinalHF) :
    natOfOrdinal (ordinalSuccSet a) = natOfOrdinal a + 1 := by
  rw [ordinalSuccSet_eq, natOfOrdinal_ordinalOfNat]

/-- Iterate finite-ordinal successor `n` times from `a`. -/
noncomputable def ordinalAddIter (a : OrdinalHF) : Nat → OrdinalHF
  | 0 => a
  | n+1 => ordinalSuccSet (ordinalAddIter a n)

/-- Addition of finite ordinals, defined by iterating successor along the
second ordinal. -/
noncomputable def ordinalAddSet (a b : OrdinalHF) : OrdinalHF :=
  ordinalAddIter a (natOfOrdinal b)

theorem natOfOrdinal_ordinalAddIter (a : OrdinalHF) (n : Nat) :
    natOfOrdinal (ordinalAddIter a n) = natOfOrdinal a + n := by
  induction n with
  | zero =>
      simp only [ordinalAddIter, Nat.add_zero]
  | succ n ih =>
      simp only [ordinalAddIter, natOfOrdinal_ordinalSuccSet, ih, Nat.add_succ]

theorem natOfOrdinal_ordinalAddSet (a b : OrdinalHF) :
    natOfOrdinal (ordinalAddSet a b) = natOfOrdinal a + natOfOrdinal b := by
  unfold ordinalAddSet
  exact natOfOrdinal_ordinalAddIter a (natOfOrdinal b)

theorem ordinalAddSet_eq (a b : OrdinalHF) :
    ordinalAddSet a b = ordinalOfNat (natOfOrdinal a + natOfOrdinal b) :=
  ordinal_eq_of_natOfOrdinal_eq
    (by rw [natOfOrdinal_ordinalAddSet, natOfOrdinal_ordinalOfNat])

/-- Iterate finite-ordinal addition by `a`, `n` times, from zero. -/
noncomputable def ordinalMulIter (a : OrdinalHF) : Nat → OrdinalHF
  | 0 => ordinalOfNat 0
  | n+1 => ordinalAddSet (ordinalMulIter a n) a

/-- Multiplication of finite ordinals, defined by iterating addition along the
second ordinal. -/
noncomputable def ordinalMulSet (a b : OrdinalHF) : OrdinalHF :=
  ordinalMulIter a (natOfOrdinal b)

theorem natOfOrdinal_ordinalMulIter (a : OrdinalHF) (n : Nat) :
    natOfOrdinal (ordinalMulIter a n) = natOfOrdinal a * n := by
  induction n with
  | zero =>
      simp only [ordinalMulIter, natOfOrdinal_ordinalOfNat, Nat.mul_zero]
  | succ n ih =>
      simp only [ordinalMulIter, natOfOrdinal_ordinalAddSet, ih, Nat.mul_succ]

theorem natOfOrdinal_ordinalMulSet (a b : OrdinalHF) :
    natOfOrdinal (ordinalMulSet a b) = natOfOrdinal a * natOfOrdinal b := by
  unfold ordinalMulSet
  exact natOfOrdinal_ordinalMulIter a (natOfOrdinal b)

theorem ordinalMulSet_eq (a b : OrdinalHF) :
    ordinalMulSet a b = ordinalOfNat (natOfOrdinal a * natOfOrdinal b) :=
  ordinal_eq_of_natOfOrdinal_eq
    (by rw [natOfOrdinal_ordinalMulSet, natOfOrdinal_ordinalOfNat])

/-- The PA structure interpreted inside Ackermann HF by taking the finite
von Neumann ordinals as the number domain.  Successor is the set-theoretic
operation `a ∪ {a}`; addition and multiplication are finite iterations of
successor and addition, respectively. -/
noncomputable def ordinalPAModel : PA.Model OrdinalHF where
  zero := ordinalOfNat 0
  succ := ordinalSuccSet
  add := ordinalAddSet
  mul := ordinalMulSet
  succ_injective := by
    intro a b h
    apply ordinal_eq_of_natOfOrdinal_eq
    have hn := congrArg natOfOrdinal h
    simp only [natOfOrdinal_ordinalSuccSet] at hn
    omega
  zero_not_succ := by
    intro a h
    have hn := congrArg natOfOrdinal h
    simp only [natOfOrdinal_ordinalSuccSet, natOfOrdinal_ordinalOfNat] at hn
    omega
  induction := by
    intro P h0 hs a
    have hnat : ∀ n, P (ordinalOfNat n) := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
          have hstep := hs (ordinalOfNat n) ih
          simpa [ordinalSuccSet_eq, natOfOrdinal_ordinalOfNat] using hstep
    simpa [ordinalOfNat_natOfOrdinal a] using hnat (natOfOrdinal a)
  add_zero := by
    intro a
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalAddSet, natOfOrdinal_ordinalOfNat, Nat.add_zero]
  add_succ := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalAddSet, natOfOrdinal_ordinalSuccSet, Nat.add_succ]
  mul_zero := by
    intro a
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalMulSet, natOfOrdinal_ordinalOfNat, Nat.mul_zero]
  mul_succ := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [natOfOrdinal_ordinalMulSet, natOfOrdinal_ordinalAddSet,
      natOfOrdinal_ordinalSuccSet, Nat.mul_succ]

/-- The first round trip of the bi-interpretability construction: starting
from arithmetic, interpreting HF by Ackermann coding, and then interpreting
arithmetic back as finite ordinals gives a PA model isomorphic to the original
natural-number model. -/
noncomputable def paRoundTripIso : PA.Iso PA.natModel ordinalPAModel where
  toFun := ordinalOfNat
  invFun := natOfOrdinal
  left_inv := natOfOrdinal_ordinalOfNat
  right_inv := ordinalOfNat_natOfOrdinal
  map_zero := rfl
  map_succ := by
    intro n
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalSuccSet,
      natOfOrdinal_ordinalOfNat]
  map_add := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalAddSet,
      natOfOrdinal_ordinalOfNat, Nat.add_eq]
  map_mul := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [PA.natModel, ordinalPAModel, natOfOrdinal_ordinalMulSet,
      natOfOrdinal_ordinalOfNat, Nat.mul_eq]

theorem ordinalPA_sat_PA (e : Nat → OrdinalHF) :
    ∀ f, PA.Formula.Ax_s f → PA.Formula.Sat ordinalPAModel e f :=
  PA.Formula.sat_axiom_s ordinalPAModel e

/-! ## Syntactic PA-in-HF term interpretation -/

namespace PAInHF

open Form

/-- Interpret a PA term as an HF formula graph.

`termGraphAt ρ out t` says that slot `out` contains the value of the PA term
`t`, where PA variable `n` is read from HF slot `ρ n`.  The slot map is part
of the definition, rather than hidden in a convention, because recursive
subterm witnesses introduce local binders and shift all older slots. -/
def termGraphAt (ρ : Nat → Nat) (out : Nat) : PA.Term → Form
  | PA.Term.var n => fEq out (ρ n)
  | PA.Term.zero => HF_emptyAt out
  | PA.Term.succ t =>
      fEx (fAnd
        (termGraphAt (fun n => ρ n + 1) 0 t)
        (HF_succAt (out+1) 0))
  | PA.Term.add a b =>
      fEx (fEx (fAnd
        (termGraphAt (fun n => ρ n + 2) 1 a)
        (fAnd
          (termGraphAt (fun n => ρ n + 2) 0 b)
          (addGraphAt (out+2) 1 0))))
  | PA.Term.mul a b =>
      fEx (fEx (fEx (fAnd
        (termGraphAt (fun n => ρ n + 3) 1 a)
        (fAnd
          (termGraphAt (fun n => ρ n + 3) 2 b)
          (fAnd (fEq 0 (out+3)) mulGraph)))))

theorem termGraphAt_free (t : PA.Term) :
    ∀ {ρ : Nat → Nat} {out i : Nat}, Free i (termGraphAt ρ out t) →
      i = out ∨ ∃ n, PA.Term.Free n t ∧ i = ρ n := by
  induction t with
  | var n =>
      intro ρ out i h
      simp only [termGraphAt, Free] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨n, rfl, h⟩
  | zero =>
      intro ρ out i h
      have hi := HF_emptyAt_free h
      exact Or.inl hi
  | succ t ih =>
      intro ρ out i h
      simp only [termGraphAt, Free] at h
      rcases h with h | h
      · have ht := ih h
        rcases ht with ht | ht
        · omega
        · rcases ht with ⟨n, hn, hi⟩
          exact Or.inr ⟨n, hn, by omega⟩
      · have hs := HF_succAt_free h
        omega
  | add a b iha ihb =>
      intro ρ out i h
      simp only [termGraphAt, Free] at h
      rcases h with h | h
      · have ha := iha h
        rcases ha with ha | ha
        · omega
        · rcases ha with ⟨n, hn, hi⟩
          exact Or.inr ⟨n, Or.inl hn, by omega⟩
      · rcases h with h | h
        · have hb := ihb h
          rcases hb with hb | hb
          · omega
          · rcases hb with ⟨n, hn, hi⟩
            exact Or.inr ⟨n, Or.inr hn, by omega⟩
        · have hg := addGraphAt_free h
          omega
  | mul a b iha ihb =>
      intro ρ out i h
      simp only [termGraphAt, Free] at h
      rcases h with h | h
      · have ha := iha h
        rcases ha with ha | ha
        · omega
        · rcases ha with ⟨n, hn, hi⟩
          exact Or.inr ⟨n, Or.inl hn, by omega⟩
      · rcases h with h | h
        · have hb := ihb h
          rcases hb with hb | hb
          · omega
          · rcases hb with ⟨n, hn, hi⟩
            exact Or.inr ⟨n, Or.inr hn, by omega⟩
        · rcases h with h | h
          · omega
          · have hm := mulGraph_free h
            omega

/-- The PA-term graph only depends on the slot map at variables free in the
term. -/
theorem termGraphAt_map_ext_free (t : PA.Term) :
    ∀ {ρ σ : Nat → Nat} {out : Nat},
      (∀ n, PA.Term.Free n t → ρ n = σ n) →
        termGraphAt ρ out t = termGraphAt σ out t := by
  induction t with
  | var n =>
      intro ρ σ out h
      simp [termGraphAt, h n rfl]
  | zero =>
      intro ρ σ out h
      rfl
  | succ t ih =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@ih (fun n => ρ n + 1) (fun n => σ n + 1) 0
        (fun n hn => by rw [h n hn])]
  | add a b iha ihb =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@iha (fun n => ρ n + 2) (fun n => σ n + 2) 1
        (fun n hn => by rw [h n (Or.inl hn)])]
      rw [@ihb (fun n => ρ n + 2) (fun n => σ n + 2) 0
        (fun n hn => by rw [h n (Or.inr hn)])]
  | mul a b iha ihb =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@iha (fun n => ρ n + 3) (fun n => σ n + 3) 1
        (fun n hn => by rw [h n (Or.inl hn)])]
      rw [@ihb (fun n => ρ n + 3) (fun n => σ n + 3) 2
        (fun n hn => by rw [h n (Or.inr hn)])]

theorem termGraphAt_map_ext (t : PA.Term) :
    ∀ {ρ σ : Nat → Nat} {out : Nat},
      (∀ n, ρ n = σ n) → termGraphAt ρ out t = termGraphAt σ out t := by
  induction t with
  | var n =>
      intro ρ σ out h
      simp [termGraphAt, h n]
  | zero =>
      intro ρ σ out h
      rfl
  | succ t ih =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@ih (fun n => ρ n + 1) (fun n => σ n + 1) 0
        (fun n => by rw [h n])]
  | add a b iha ihb =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@iha (fun n => ρ n + 2) (fun n => σ n + 2) 1
        (fun n => by rw [h n])]
      rw [@ihb (fun n => ρ n + 2) (fun n => σ n + 2) 0
        (fun n => by rw [h n])]
  | mul a b iha ihb =>
      intro ρ σ out h
      simp only [termGraphAt]
      rw [@iha (fun n => ρ n + 3) (fun n => σ n + 3) 1
        (fun n => by rw [h n])]
      rw [@ihb (fun n => ρ n + 3) (fun n => σ n + 3) 2
        (fun n => by rw [h n])]

/-- Translating a renamed PA term composes the slot map with the PA renaming. -/
theorem termGraphAt_PA_rename (t : PA.Term) :
    ∀ {ρ : Nat → Nat} {out : Nat} {r : Nat → Nat},
      termGraphAt ρ out (PA.Term.rename r t) =
        termGraphAt (fun n => ρ (r n)) out t := by
  induction t with
  | var n =>
      intro ρ out r
      rfl
  | zero =>
      intro ρ out r
      rfl
  | succ t ih =>
      intro ρ out r
      simp only [PA.Term.rename, termGraphAt]
      rw [@ih (fun n => ρ n + 1) 0 r]
  | add a b iha ihb =>
      intro ρ out r
      simp only [PA.Term.rename, termGraphAt]
      rw [@iha (fun n => ρ n + 2) 1 r]
      rw [@ihb (fun n => ρ n + 2) 0 r]
  | mul a b iha ihb =>
      intro ρ out r
      simp only [PA.Term.rename, termGraphAt]
      rw [@iha (fun n => ρ n + 3) 1 r]
      rw [@ihb (fun n => ρ n + 3) 2 r]

/-- HF-renaming commutes with the empty-set macro. -/
theorem rename_HF_emptyAt (r : Nat → Nat) (i : Nat) :
    rename r (HF_emptyAt i) = HF_emptyAt (r i) := by
  simp [HF_emptyAt, rename, up]

/-- HF-renaming commutes with the adjunction macro. -/
theorem rename_HF_adjoinAt (r : Nat → Nat) (c a b : Nat) :
    rename r (HF_adjoinAt c a b) = HF_adjoinAt (r c) (r a) (r b) := by
  simp [HF_adjoinAt, fIff, rename, up]

/-- HF-renaming commutes with the ordinal-successor macro. -/
theorem rename_HF_succAt (r : Nat → Nat) (s a : Nat) :
    rename r (HF_succAt s a) = HF_succAt (r s) (r a) := by
  simp [HF_succAt, rename_HF_adjoinAt]

/-- HF-renaming commutes with the singleton macro. -/
theorem rename_HF_singleAt (r : Nat → Nat) (i j : Nat) :
    rename r (HF_singleAt i j) = HF_singleAt (r i) (r j) := by
  simp [HF_singleAt, fIff, rename, up]

/-- HF-renaming commutes with the unordered-pair macro. -/
theorem rename_HF_upairAt (r : Nat → Nat) (i j k : Nat) :
    rename r (HF_upairAt i j k) = HF_upairAt (r i) (r j) (r k) := by
  simp [HF_upairAt, fIff, rename, up]

/-- HF-renaming commutes with the Kuratowski-pair macro. -/
theorem rename_HF_kpairAt (r : Nat → Nat) (p a b : Nat) :
    rename r (HF_kpairAt p a b) = HF_kpairAt (r p) (r a) (r b) := by
  simp [HF_kpairAt, fIff, rename, up, rename_HF_singleAt,
    rename_HF_upairAt]

/-- HF-renaming commutes with the pair-membership macro. -/
theorem rename_HF_pairMemAt (r : Nat → Nat) (a b rel : Nat) :
    rename r (HF_pairMemAt a b rel) =
      HF_pairMemAt (r a) (r b) (r rel) := by
  simp [HF_pairMemAt, rename, up, rename_HF_kpairAt]

/-- HF-renaming commutes with the functionality macro for finite graphs. -/
theorem rename_HF_pairFunctionalAt (r : Nat → Nat) (f : Nat) :
    rename r (HF_pairFunctionalAt f) = HF_pairFunctionalAt (r f) := by
  simp [HF_pairFunctionalAt, rename, up, rename_HF_pairMemAt]

/-- HF-renaming commutes with the key-boundedness macro for finite graphs. -/
theorem rename_HF_pairKeysBelowSuccAt (r : Nat → Nat) (f m : Nat) :
    rename r (HF_pairKeysBelowSuccAt f m) =
      HF_pairKeysBelowSuccAt (r f) (r m) := by
  simp [HF_pairKeysBelowSuccAt, rename, up, rename_HF_pairMemAt]

/-- HF-renaming commutes with the totality-below-successor macro for finite
graphs. -/
theorem rename_HF_pairTotalBelowSuccAt (r : Nat → Nat) (f m : Nat) :
    rename r (HF_pairTotalBelowSuccAt f m) =
      HF_pairTotalBelowSuccAt (r f) (r m) := by
  simp [HF_pairTotalBelowSuccAt, rename, up, rename_HF_pairMemAt]

/-- HF-renaming commutes with the successor-step macro for finite graphs. -/
theorem rename_HF_pairSuccStepAt (r : Nat → Nat) (f m : Nat) :
    rename r (HF_pairSuccStepAt f m) = HF_pairSuccStepAt (r f) (r m) := by
  simp [HF_pairSuccStepAt, rename, up, rename_HF_pairMemAt, rename_HF_succAt]

/-- HF-renaming commutes with the successor-recursion base macro. -/
theorem rename_HF_pairBaseAt (r : Nat → Nat) (f s : Nat) :
    rename r (HF_pairBaseAt f s) = HF_pairBaseAt (r f) (r s) := by
  simp [HF_pairBaseAt, rename, up, rename_HF_emptyAt, rename_HF_pairMemAt]

/-- HF-renaming commutes with the zero-start recursion base macro. -/
theorem rename_HF_pairZeroBaseAt (r : Nat → Nat) (f : Nat) :
    rename r (HF_pairZeroBaseAt f) = HF_pairZeroBaseAt (r f) := by
  simp [HF_pairZeroBaseAt, rename, up, rename_HF_emptyAt, rename_HF_pairMemAt]

/-- HF-renaming commutes with the successor-recursion approximation macro. -/
theorem rename_HF_succRecApproxAt (r : Nat → Nat) (f s m : Nat) :
    rename r (HF_succRecApproxAt f s m) =
      HF_succRecApproxAt (r f) (r s) (r m) := by
  simp [HF_succRecApproxAt, rename, rename_HF_pairFunctionalAt,
    rename_HF_pairKeysBelowSuccAt, rename_HF_pairBaseAt,
    rename_HF_pairTotalBelowSuccAt, rename_HF_pairSuccStepAt]

/-- HF-renaming commutes with the addition-graph macro. -/
theorem rename_addGraphAt (r : Nat → Nat) (out left right : Nat) :
    rename r (addGraphAt out left right) =
      addGraphAt (r out) (r left) (r right) := by
  simp [addGraphAt, rename, up, rename_HF_succRecApproxAt,
    rename_HF_pairMemAt]

/-- HF-renaming commutes with the multiplication-step macro. -/
theorem rename_mulStepAt (r : Nat → Nat) (f a m : Nat) :
    rename r (mulStepAt f a m) = mulStepAt (r f) (r a) (r m) := by
  simp [mulStepAt, rename, up, rename_HF_pairMemAt, rename_HF_succAt,
    rename_addGraphAt]

/-- HF-renaming commutes with the multiplication-recursion approximation
macro. -/
theorem rename_mulRecApproxAt (r : Nat → Nat) (f a m : Nat) :
    rename r (mulRecApproxAt f a m) =
      mulRecApproxAt (r f) (r a) (r m) := by
  simp [mulRecApproxAt, rename, rename_HF_pairFunctionalAt,
    rename_HF_pairKeysBelowSuccAt, rename_HF_pairZeroBaseAt,
    rename_HF_pairTotalBelowSuccAt, rename_mulStepAt]

/-- HF-renaming commutes with the multiplication-graph macro. -/
theorem rename_mulGraphAt (r : Nat → Nat) (out left right : Nat) :
    rename r (mulGraphAt out left right) =
      mulGraphAt (r out) (r left) (r right) := by
  simp [mulGraphAt, rename, up, rename_mulRecApproxAt, rename_HF_pairMemAt]

/-- HF-renaming a translated PA-term graph composes the graph slots with the
renaming. -/
theorem termGraphAt_rename (t : PA.Term) :
    ∀ {ρ : Nat → Nat} {out : Nat} {r : Nat → Nat},
      rename r (termGraphAt ρ out t) =
        termGraphAt (fun n => r (ρ n)) (r out) t := by
  induction t with
  | var n =>
      intro ρ out r
      rfl
  | zero =>
      intro ρ out r
      simp [termGraphAt, rename_HF_emptyAt]
  | succ t ih =>
      intro ρ out r
      simp [termGraphAt, rename, up, ih, rename_HF_succAt]
  | add a b iha ihb =>
      intro ρ out r
      simp [termGraphAt, rename, up, iha, ihb, rename_addGraphAt]
  | mul a b iha ihb =>
      intro ρ out r
      simp [termGraphAt, rename, up, iha, ihb, mulGraph, rename_mulGraphAt]

/-- Instantiating the distinguished output variable of a term graph gives the
same graph at the chosen concrete output slot. -/
theorem termGraphAt_inst_out (t : PA.Term) (ρ : Nat → Nat) (k : Nat) :
    rename (inst k) (termGraphAt (fun n => ρ n + 1) 0 t) =
      termGraphAt ρ k t := by
  rw [termGraphAt_rename]
  exact termGraphAt_map_ext t (out := k)
    (fun n => by simp [inst])

/-- A satisfied term graph remains satisfied after inserting a fresh HF slot in
front of the whole environment, with all graph slots shifted by one. -/
theorem Sat_termGraphAt_shift_front {α : Type u} {mem : α → α → Prop}
    (t : PA.Term) (ρ : Nat → Nat) (out : Nat)
    (e : Nat → α) (d : α)
    (h : Sat mem e (termGraphAt ρ out t)) :
    Sat mem (scons d e) (termGraphAt (fun n => ρ n + 1) (out + 1) t) := by
  have hrename :
      rename Nat.succ (termGraphAt ρ out t) =
        termGraphAt (fun n => ρ n + 1) (out + 1) t := by
    simpa [Nat.succ_eq_add_one] using
      (termGraphAt_rename t (ρ := ρ) (out := out) (r := Nat.succ))
  rw [← hrename]
  apply (Sat_rename (mem := mem) (termGraphAt ρ out t)
    Nat.succ (scons d e)).mpr
  have henv : ∀ n, scons d e (Nat.succ n) = e n := by
    intro n
    rfl
  exact (Sat_ext (mem := mem) (termGraphAt ρ out t)
    (fun n => scons d e (Nat.succ n)) e henv).mpr h

/-- Inverse form of `Sat_termGraphAt_shift_front`: if a shifted graph is
satisfied after adding a fresh head slot, the original graph is satisfied in
the tail environment. -/
theorem Sat_termGraphAt_shift_front_inv {α : Type u} {mem : α → α → Prop}
    (t : PA.Term) (ρ : Nat → Nat) (out : Nat)
    (e : Nat → α) (d : α)
    (h : Sat mem (scons d e)
      (termGraphAt (fun n => ρ n + 1) (out + 1) t)) :
    Sat mem e (termGraphAt ρ out t) := by
  have hrename :
      rename Nat.succ (termGraphAt ρ out t) =
        termGraphAt (fun n => ρ n + 1) (out + 1) t := by
    simpa [Nat.succ_eq_add_one] using
      (termGraphAt_rename t (ρ := ρ) (out := out) (r := Nat.succ))
  rw [← hrename] at h
  have hshift := (Sat_rename (mem := mem) (termGraphAt ρ out t)
    Nat.succ (scons d e)).mp h
  have henv : ∀ n, scons d e (Nat.succ n) = e n := by
    intro n
    rfl
  exact (Sat_ext (mem := mem) (termGraphAt ρ out t)
    (fun n => scons d e (Nat.succ n)) e henv).mp hshift

/-- A satisfied term graph with output in the head slot remains satisfied after
inserting one fresh HF slot immediately behind that output. -/
theorem Sat_termGraphAt_insert_after_output {α : Type u}
    {mem : α → α → Prop}
    (t : PA.Term) (ρ : Nat → Nat) (e : Nat → α) (outSlot d : α)
    (h : Sat mem (scons outSlot e)
      (termGraphAt (fun n => ρ n + 1) 0 t)) :
    Sat mem (scons outSlot (scons d e))
      (termGraphAt (fun n => ρ n + 2) 0 t) := by
  let r : Nat → Nat := SetTheory.up Nat.succ
  have hrename :
      rename r (termGraphAt (fun n => ρ n + 1) 0 t) =
        termGraphAt (fun n => ρ n + 2) 0 t := by
    rw [termGraphAt_rename]
    simp [r, SetTheory.up]
  rw [← hrename]
  apply (Sat_rename (mem := mem) (termGraphAt (fun n => ρ n + 1) 0 t)
    r (scons outSlot (scons d e))).mpr
  have henv : ∀ n,
      scons outSlot (scons d e) (r n) = scons outSlot e n := by
    intro n
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (Sat_ext (mem := mem) (termGraphAt (fun n => ρ n + 1) 0 t)
    (fun n => scons outSlot (scons d e) (r n)) (scons outSlot e)
    henv).mpr h

/-- Inverse form of `Sat_termGraphAt_insert_after_output`: a graph whose
output is in the head slot does not depend on an extra slot inserted just after
that output. -/
theorem Sat_termGraphAt_insert_after_output_inv {α : Type u}
    {mem : α → α → Prop}
    (t : PA.Term) (ρ : Nat → Nat) (e : Nat → α) (outSlot d : α)
    (h : Sat mem (scons outSlot (scons d e))
      (termGraphAt (fun n => ρ n + 2) 0 t)) :
    Sat mem (scons outSlot e)
      (termGraphAt (fun n => ρ n + 1) 0 t) := by
  let r : Nat → Nat := SetTheory.up Nat.succ
  have hrename :
      rename r (termGraphAt (fun n => ρ n + 1) 0 t) =
        termGraphAt (fun n => ρ n + 2) 0 t := by
    rw [termGraphAt_rename]
    simp [r, SetTheory.up]
  rw [← hrename] at h
  have hshift := (Sat_rename (mem := mem)
    (termGraphAt (fun n => ρ n + 1) 0 t)
    r (scons outSlot (scons d e))).mp h
  have henv : ∀ n,
      scons outSlot (scons d e) (r n) = scons outSlot e n := by
    intro n
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (Sat_ext (mem := mem) (termGraphAt (fun n => ρ n + 1) 0 t)
    (fun n => scons outSlot (scons d e) (r n)) (scons outSlot e)
    henv).mp hshift

/-- Every PA term whose free variables denote ordinal-like HF objects has a
finite-HF graph witness, and that witness is again ordinal-like.

The graph witness is returned in a fresh head slot.  This is the shape needed
by the translated equality and quantifier rules, where term values are supplied
by existential binders rather than by changing the ambient environment. -/
theorem termGraphAt_total_of_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term) :
    ∀ (ρ : Nat → Nat) (e : Nat → α),
      (∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n))) →
        ∃ x, OrdinalLike M.mem x ∧
          Sat M.mem (scons x e) (termGraphAt (fun n => ρ n + 1) 0 t) := by
  induction t with
  | var n =>
      intro ρ e hfree
      refine ⟨e (ρ n), hfree n rfl, ?_⟩
      change e (ρ n) = scons (e (ρ n)) e (ρ n + 1)
      rw [← Nat.succ_eq_add_one (ρ n)]
      rfl
  | zero =>
      intro ρ e _hfree
      refine ⟨M.empty, ?_, ?_⟩
      · simpa using
          FirstOrderAdjunctionModel.ordinalLike_empty M.toFirstOrderAdjunctionModel
      · apply (FirstOrderAdjunctionModel.HF_emptyAt_empty
          M.toFirstOrderAdjunctionModel (scons M.empty e) 0).mpr
        rfl
  | succ t ih =>
      intro ρ e hfree
      rcases ih ρ e hfree with ⟨x, hxOrd, hxGraph⟩
      let sx := M.adjoin x x
      refine ⟨sx, ?_, ?_⟩
      · exact FirstOrderAdjunctionModel.ordinalLike_adjoin_self
          M.toFirstOrderAdjunctionModel hxOrd rfl
      · refine ⟨x, ?_, ?_⟩
        · exact Sat_termGraphAt_insert_after_output t ρ e x sx hxGraph
        · apply (FirstOrderAdjunctionModel.HF_succAt_spec
            M.toFirstOrderAdjunctionModel (scons x (scons sx e)) 1 0).mpr
          change sx = M.toFirstOrderAdjunctionModel.adjoin x x
          rfl
  | add a b iha ihb =>
      intro ρ e hfree
      rcases iha ρ e (fun n hn => hfree n (Or.inl hn)) with
        ⟨x, hxOrd, hxGraph⟩
      rcases ihb ρ e (fun n hn => hfree n (Or.inr hn)) with
        ⟨y, hyOrd, hyGraph⟩
      rcases FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike M
          x y hyOrd with
        ⟨f, z, hf, hz⟩
      have hzOrd : OrdinalLike M.mem z :=
        FirstOrderFiniteAdjunctionModel.succRecApprox_value_ordinalLike
          M hxOrd hyOrd hf hz
      let E : Nat → α := scons y (scons x (scons z e))
      have hxGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 2) 1 a) := by
        have h1 : Sat M.mem (scons x (scons z e))
            (termGraphAt (fun n => ρ n + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a ρ e x z hxGraph
        have h2 : Sat M.mem E
            (termGraphAt (fun n => (ρ n + 2) + 1) 1 a) :=
          Sat_termGraphAt_shift_front a (fun n => ρ n + 2) 0
            (scons x (scons z e)) y h1
        simpa [E, Nat.add_assoc] using h2
      have hyGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 2) 0 b) := by
        have h1 : Sat M.mem (scons y (scons z e))
            (termGraphAt (fun n => ρ n + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b ρ e y z hyGraph
        have h2 : Sat M.mem E
            (termGraphAt (fun n => (ρ n + 1) + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b (fun n => ρ n + 1)
            (scons z e) y x h1
        simpa [E, Nat.add_assoc] using h2
      refine ⟨z, hzOrd, ?_⟩
      refine ⟨x, y, ?_, ?_, ?_⟩
      · exact hxGraphE
      · exact hyGraphE
      · apply addGraphAt_of_succRecApprox_model M.toFirstOrderAdjunctionModel
          E 2 1 0 (f := f)
        · change FirstOrderAdjunctionModel.SuccRecApprox
            M.toFirstOrderAdjunctionModel x f y
          exact hf
        · change M.mem (FirstOrderAdjunctionModel.kpair
            M.toFirstOrderAdjunctionModel y z) f
          exact hz
  | mul a b iha ihb =>
      intro ρ e hfree
      rcases iha ρ e (fun n hn => hfree n (Or.inl hn)) with
        ⟨x, hxOrd, hxGraph⟩
      rcases ihb ρ e (fun n hn => hfree n (Or.inr hn)) with
        ⟨y, hyOrd, hyGraph⟩
      rcases mulRecTotal_of_ordinalLike_finite_model M x y hxOrd hyOrd with
        ⟨f, z, hf, hz⟩
      have hzOrd : OrdinalLike M.mem z :=
        mulRecApprox_value_ordinalLike M hxOrd hyOrd hf hz
      let E : Nat → α := scons z (scons x (scons y (scons z e)))
      have hxGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 3) 1 a) := by
        have h1 : Sat M.mem (scons x (scons z e))
            (termGraphAt (fun n => ρ n + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a ρ e x z hxGraph
        have h2 : Sat M.mem (scons x (scons y (scons z e)))
            (termGraphAt (fun n => (ρ n + 1) + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a (fun n => ρ n + 1)
            (scons z e) x y h1
        have h3 : Sat M.mem E
            (termGraphAt (fun n => ((ρ n + 1) + 2) + 1) 1 a) :=
          Sat_termGraphAt_shift_front a (fun n => (ρ n + 1) + 2) 0
            (scons x (scons y (scons z e))) z h2
        simpa [E, Nat.add_assoc] using h3
      have hyGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 3) 2 b) := by
        have h1 : Sat M.mem (scons y (scons z e))
            (termGraphAt (fun n => ρ n + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b ρ e y z hyGraph
        have h2 : Sat M.mem (scons x (scons y (scons z e)))
            (termGraphAt (fun n => (ρ n + 2) + 1) 1 b) :=
          Sat_termGraphAt_shift_front b (fun n => ρ n + 2) 0
            (scons y (scons z e)) x h1
        have h3 : Sat M.mem E
            (termGraphAt (fun n => ((ρ n + 2) + 1) + 1) 2 b) :=
          Sat_termGraphAt_shift_front b (fun n => (ρ n + 2) + 1) 1
            (scons x (scons y (scons z e))) z h2
        simpa [E, Nat.add_assoc] using h3
      refine ⟨z, hzOrd, ?_⟩
      refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
      · exact hxGraphE
      · exact hyGraphE
      · rfl
      · apply mulGraphAt_of_mulRecApprox_model M.toFirstOrderAdjunctionModel
          E 0 1 2 (f := f)
        · change MulRecApprox M.toFirstOrderAdjunctionModel x f y
          exact hf
        · change M.mem (FirstOrderAdjunctionModel.kpair
            M.toFirstOrderAdjunctionModel y z) f
          exact hz

/-- In a finite first-order HF model, every satisfied translated PA-term graph
with ordinal-like free inputs has an ordinal-like output. -/
theorem termGraphAt_value_ordinalLike_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term) :
    ∀ (ρ : Nat → Nat) (out : Nat) (e : Nat → α),
      (∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n))) →
        Sat M.mem e (termGraphAt ρ out t) →
          OrdinalLike M.mem (e out) := by
  induction t with
  | var n =>
      intro ρ out e hfree hgraph
      have hout : e out = e (ρ n) := hgraph
      rw [hout]
      exact hfree n rfl
  | zero =>
      intro ρ out e _hfree hgraph
      have hout := (FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel e out).mp hgraph
      rw [hout]
      exact FirstOrderAdjunctionModel.ordinalLike_empty
        M.toFirstOrderAdjunctionModel
  | succ t ih =>
      intro ρ out e hfree hgraph
      rcases hgraph with ⟨x, hxGraph, hsGraph⟩
      have hxOrd : OrdinalLike M.mem x := by
        have hfree' : ∀ n, PA.Term.Free n t →
            OrdinalLike M.mem (scons x e ((fun n => ρ n + 1) n)) := by
          intro n hn
          simpa [scons] using hfree n hn
        exact ih (fun n => ρ n + 1) 0 (scons x e) hfree' hxGraph
      have hout := (FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel (scons x e) (out+1) 0).mp hsGraph
      change e out = M.adjoin x x at hout
      exact FirstOrderAdjunctionModel.ordinalLike_adjoin_self
        M.toFirstOrderAdjunctionModel hxOrd hout
  | add a b iha ihb =>
      intro ρ out e hfree hgraph
      rcases hgraph with ⟨x, y, haGraph, hbGraph, haddGraph⟩
      let E : Nat → α := scons y (scons x e)
      have hxOrd : OrdinalLike M.mem x := by
        have hfreeA : ∀ n, PA.Term.Free n a →
            OrdinalLike M.mem (E ((fun n => ρ n + 2) n)) := by
          intro n hn
          simpa [E, scons] using hfree n (Or.inl hn)
        exact iha (fun n => ρ n + 2) 1 E hfreeA haGraph
      have hyOrd : OrdinalLike M.mem y := by
        have hfreeB : ∀ n, PA.Term.Free n b →
            OrdinalLike M.mem (E ((fun n => ρ n + 2) n)) := by
          intro n hn
          simpa [E, scons] using hfree n (Or.inr hn)
        exact ihb (fun n => ρ n + 2) 0 E hfreeB hbGraph
      rcases haddGraph with ⟨f, hfSat, houtSat⟩
      have hf : FirstOrderAdjunctionModel.SuccRecApprox
          M.toFirstOrderAdjunctionModel x f y := by
        simpa [E, scons] using
          (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec
            M.toFirstOrderAdjunctionModel (scons f E)
            0 (1+1) (0+1)).mp hfSat
      have hout : M.mem (FirstOrderAdjunctionModel.kpair
          M.toFirstOrderAdjunctionModel y (e out)) f := by
        simpa [E, scons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (FirstOrderAdjunctionModel.HF_pairMemAt_spec
            M.toFirstOrderAdjunctionModel (scons f E)
            (0+1) ((out+2)+1) 0).mp houtSat
      exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_ordinalLike
        M hxOrd hyOrd hf hout
  | mul a b iha ihb =>
      intro ρ out e hfree hgraph
      rcases hgraph with ⟨y, x, z, haGraph, hbGraph, hcopy, hmulGraph⟩
      let E : Nat → α := scons z (scons x (scons y e))
      have hxOrd : OrdinalLike M.mem x := by
        have hfreeA : ∀ n, PA.Term.Free n a →
            OrdinalLike M.mem (E ((fun n => ρ n + 3) n)) := by
          intro n hn
          simpa [E, scons] using hfree n (Or.inl hn)
        exact iha (fun n => ρ n + 3) 1 E hfreeA haGraph
      have hyOrd : OrdinalLike M.mem y := by
        have hfreeB : ∀ n, PA.Term.Free n b →
            OrdinalLike M.mem (E ((fun n => ρ n + 3) n)) := by
          intro n hn
          simpa [E, scons] using hfree n (Or.inr hn)
        exact ihb (fun n => ρ n + 3) 2 E hfreeB hbGraph
      rcases hmulGraph with ⟨f, hfSat, houtSat⟩
      have hf : MulRecApprox M.toFirstOrderAdjunctionModel x f y := by
        simpa [E, scons] using
          (mulRecApproxAt_spec M.toFirstOrderAdjunctionModel
            (scons f E) 0 (1+1) (2+1)).mp hfSat
      have hzPair : M.mem (FirstOrderAdjunctionModel.kpair
          M.toFirstOrderAdjunctionModel y z) f := by
        simpa [E, scons] using
          (FirstOrderAdjunctionModel.HF_pairMemAt_spec
            M.toFirstOrderAdjunctionModel (scons f E)
            (2+1) (0+1) 0).mp houtSat
      have hzOrd : OrdinalLike M.mem z :=
        mulRecApprox_value_ordinalLike M hxOrd hyOrd hf hzPair
      change z = e out at hcopy
      rwa [← hcopy]

/-- In a finite first-order HF model, translated PA-term graphs are
single-valued: two graph witnesses for the same term and agreeing variable
slots have equal outputs. -/
theorem termGraphAt_outputs_eq_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term) :
    ∀ {ρ₁ ρ₂ : Nat → Nat} {out₁ out₂ : Nat}
      {e₁ e₂ : Nat → α},
      (∀ n, PA.Term.Free n t → e₁ (ρ₁ n) = e₂ (ρ₂ n)) →
      (∀ n, PA.Term.Free n t → OrdinalLike M.mem (e₁ (ρ₁ n))) →
      Sat M.mem e₁ (termGraphAt ρ₁ out₁ t) →
      Sat M.mem e₂ (termGraphAt ρ₂ out₂ t) →
      e₁ out₁ = e₂ out₂ := by
  induction t with
  | var n =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hvars _hord h₁ h₂
      have hleft : e₁ out₁ = e₁ (ρ₁ n) := h₁
      have hright : e₂ out₂ = e₂ (ρ₂ n) := h₂
      exact hleft.trans ((hvars n rfl).trans hright.symm)
  | zero =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ _hvars _hord h₁ h₂
      have hleft := (FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel e₁ out₁).mp h₁
      have hright := (FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel e₂ out₂).mp h₂
      exact hleft.trans hright.symm
  | succ t ih =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hvars hord h₁ h₂
      rcases h₁ with ⟨x₁, hx₁Graph, hs₁Graph⟩
      rcases h₂ with ⟨x₂, hx₂Graph, hs₂Graph⟩
      have hx : x₁ = x₂ := by
        exact ih
          (ρ₁ := fun n => ρ₁ n + 1) (ρ₂ := fun n => ρ₂ n + 1)
          (out₁ := 0) (out₂ := 0)
          (e₁ := scons x₁ e₁) (e₂ := scons x₂ e₂)
          (by
            intro n hn
            simpa [scons] using hvars n hn)
          (by
            intro n hn
            simpa [scons] using hord n hn)
          hx₁Graph hx₂Graph
      have hout₁ := (FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel (scons x₁ e₁) (out₁+1) 0).mp hs₁Graph
      have hout₂ := (FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel (scons x₂ e₂) (out₂+1) 0).mp hs₂Graph
      change e₁ out₁ = M.adjoin x₁ x₁ at hout₁
      change e₂ out₂ = M.adjoin x₂ x₂ at hout₂
      rw [hout₁, hout₂, hx]
  | add a b iha ihb =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hvars hord h₁ h₂
      rcases h₁ with ⟨x₁, y₁, ha₁, hb₁, hadd₁⟩
      rcases h₂ with ⟨x₂, y₂, ha₂, hb₂, hadd₂⟩
      let E₁ : Nat → α := scons y₁ (scons x₁ e₁)
      let E₂ : Nat → α := scons y₂ (scons x₂ e₂)
      have hx : x₁ = x₂ := by
        exact iha
          (ρ₁ := fun n => ρ₁ n + 2) (ρ₂ := fun n => ρ₂ n + 2)
          (out₁ := 1) (out₂ := 1) (e₁ := E₁) (e₂ := E₂)
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inl hn))
          (by
            intro n hn
            simpa [E₁, scons] using hord n (Or.inl hn))
          ha₁ ha₂
      have hy : y₁ = y₂ := by
        exact ihb
          (ρ₁ := fun n => ρ₁ n + 2) (ρ₂ := fun n => ρ₂ n + 2)
          (out₁ := 0) (out₂ := 0) (e₁ := E₁) (e₂ := E₂)
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inr hn))
          (by
            intro n hn
            simpa [E₁, scons] using hord n (Or.inr hn))
          hb₁ hb₂
      have hyOrd : OrdinalLike M.mem y₁ := by
        have hfreeB : ∀ n, PA.Term.Free n b →
            OrdinalLike M.mem (E₁ ((fun n => ρ₁ n + 2) n)) := by
          intro n hn
          simpa [E₁, scons] using hord n (Or.inr hn)
        exact termGraphAt_value_ordinalLike_finite_model M b
          (fun n => ρ₁ n + 2) 0 E₁ hfreeB hb₁
      have hout := addGraphAt_outputs_eq_finite_model M E₁ E₂
        (out₁+2) (out₂+2) 1 1 0 0 hx hy hyOrd hadd₁ hadd₂
      simpa [E₁, E₂, scons] using hout
  | mul a b iha ihb =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hvars hord h₁ h₂
      rcases h₁ with ⟨y₁, x₁, z₁, ha₁, hb₁, hcopy₁, hmul₁⟩
      rcases h₂ with ⟨y₂, x₂, z₂, ha₂, hb₂, hcopy₂, hmul₂⟩
      let E₁ : Nat → α := scons z₁ (scons x₁ (scons y₁ e₁))
      let E₂ : Nat → α := scons z₂ (scons x₂ (scons y₂ e₂))
      have hx : x₁ = x₂ := by
        exact iha
          (ρ₁ := fun n => ρ₁ n + 3) (ρ₂ := fun n => ρ₂ n + 3)
          (out₁ := 1) (out₂ := 1) (e₁ := E₁) (e₂ := E₂)
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inl hn))
          (by
            intro n hn
            simpa [E₁, scons] using hord n (Or.inl hn))
          ha₁ ha₂
      have hy : y₁ = y₂ := by
        exact ihb
          (ρ₁ := fun n => ρ₁ n + 3) (ρ₂ := fun n => ρ₂ n + 3)
          (out₁ := 2) (out₂ := 2) (e₁ := E₁) (e₂ := E₂)
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inr hn))
          (by
            intro n hn
            simpa [E₁, scons] using hord n (Or.inr hn))
          hb₁ hb₂
      have hxOrd : OrdinalLike M.mem x₁ := by
        have hfreeA : ∀ n, PA.Term.Free n a →
            OrdinalLike M.mem (E₁ ((fun n => ρ₁ n + 3) n)) := by
          intro n hn
          simpa [E₁, scons] using hord n (Or.inl hn)
        exact termGraphAt_value_ordinalLike_finite_model M a
          (fun n => ρ₁ n + 3) 1 E₁ hfreeA ha₁
      have hyOrd : OrdinalLike M.mem y₁ := by
        have hfreeB : ∀ n, PA.Term.Free n b →
            OrdinalLike M.mem (E₁ ((fun n => ρ₁ n + 3) n)) := by
          intro n hn
          simpa [E₁, scons] using hord n (Or.inr hn)
        exact termGraphAt_value_ordinalLike_finite_model M b
          (fun n => ρ₁ n + 3) 2 E₁ hfreeB hb₁
      have hz : z₁ = z₂ := by
        exact mulGraphAt_outputs_eq_finite_model M E₁ E₂
          0 0 1 1 2 2 hx hy hxOrd hyOrd hmul₁ hmul₂
      change z₁ = e₁ out₁ at hcopy₁
      change z₂ = e₂ out₂ at hcopy₂
      exact hcopy₁.symm.trans (hz.trans hcopy₂)

/-- Semantic transport for translated PA-term graphs across environments whose
output slots and free-variable slots agree. -/
theorem termGraphAt_transport_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (t : PA.Term) :
    ∀ {ρ₁ ρ₂ : Nat → Nat} {out₁ out₂ : Nat} {e₁ e₂ : Nat → α},
      e₁ out₁ = e₂ out₂ →
      (∀ n, PA.Term.Free n t → e₁ (ρ₁ n) = e₂ (ρ₂ n)) →
      Sat M.mem e₁ (termGraphAt ρ₁ out₁ t) →
      Sat M.mem e₂ (termGraphAt ρ₂ out₂ t) := by
  induction t with
  | var n =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hout hvars hgraph
      change e₂ out₂ = e₂ (ρ₂ n)
      exact hout.symm.trans ((hgraph : e₁ out₁ = e₁ (ρ₁ n)).trans
        (hvars n rfl))
  | zero =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hout _hvars hgraph
      have hEmpty : e₁ out₁ = M.empty :=
        (FirstOrderAdjunctionModel.HF_emptyAt_empty M e₁ out₁).mp hgraph
      apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e₂ out₂).mpr
      exact hout.symm.trans hEmpty
  | succ t ih =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hout hvars hgraph
      rcases hgraph with ⟨x, ht, hs⟩
      refine ⟨x, ?_, ?_⟩
      · exact ih (out₁ := 0) (out₂ := 0)
          (e₁ := scons x e₁) (e₂ := scons x e₂)
          (ρ₁ := fun n => ρ₁ n + 1) (ρ₂ := fun n => ρ₂ n + 1)
          rfl
          (by
            intro n hn
            simpa [scons] using hvars n hn)
          ht
      · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
          (scons x e₁) (out₁+1) 0).mp hs
        apply (FirstOrderAdjunctionModel.HF_succAt_spec M
          (scons x e₂) (out₂+1) 0).mpr
        change e₂ out₂ = M.adjoin x x
        rw [← hout]
        exact hsVal
  | add a b iha ihb =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hout hvars hgraph
      rcases hgraph with ⟨x, y, ha, hb, hadd⟩
      let E₁ : Nat → α := scons y (scons x e₁)
      let E₂ : Nat → α := scons y (scons x e₂)
      refine ⟨x, y, ?_, ?_, ?_⟩
      · exact iha (out₁ := 1) (out₂ := 1)
          (e₁ := E₁) (e₂ := E₂)
          (ρ₁ := fun n => ρ₁ n + 2) (ρ₂ := fun n => ρ₂ n + 2)
          rfl
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inl hn))
          ha
      · exact ihb (out₁ := 0) (out₂ := 0)
          (e₁ := E₁) (e₂ := E₂)
          (ρ₁ := fun n => ρ₁ n + 2) (ρ₂ := fun n => ρ₂ n + 2)
          rfl
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inr hn))
          hb
      · rcases hadd with ⟨f, hfSat, houtSat⟩
        have hf : FirstOrderAdjunctionModel.SuccRecApprox M x f y := by
          simpa [E₁, scons] using
            (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M
              (scons f E₁) 0 (1+1) (0+1)).mp hfSat
        have hpair : M.mem (FirstOrderAdjunctionModel.kpair M y (e₁ out₁)) f := by
          simpa [E₁, scons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
              (scons f E₁) (0+1) ((out₁+2)+1) 0).mp houtSat
        apply addGraphAt_of_succRecApprox_model M E₂ (out₂+2) 1 0 (f := f)
        · change FirstOrderAdjunctionModel.SuccRecApprox M x f y
          exact hf
        · change M.mem (FirstOrderAdjunctionModel.kpair M y (e₂ out₂)) f
          rw [← hout]
          exact hpair
  | mul a b iha ihb =>
      intro ρ₁ ρ₂ out₁ out₂ e₁ e₂ hout hvars hgraph
      rcases hgraph with ⟨y, x, z, ha, hb, hcopy, hmul⟩
      let E₁ : Nat → α := scons z (scons x (scons y e₁))
      let E₂ : Nat → α := scons z (scons x (scons y e₂))
      refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
      · exact iha (out₁ := 1) (out₂ := 1)
          (e₁ := E₁) (e₂ := E₂)
          (ρ₁ := fun n => ρ₁ n + 3) (ρ₂ := fun n => ρ₂ n + 3)
          rfl
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inl hn))
          ha
      · exact ihb (out₁ := 2) (out₂ := 2)
          (e₁ := E₁) (e₂ := E₂)
          (ρ₁ := fun n => ρ₁ n + 3) (ρ₂ := fun n => ρ₂ n + 3)
          rfl
          (by
            intro n hn
            simpa [E₁, E₂, scons] using hvars n (Or.inr hn))
          hb
      · change z = e₂ out₂
        change z = e₁ out₁ at hcopy
        rw [← hout]
        exact hcopy
      · exact (Sat_ext_free mulGraph E₁ E₂ (by
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl <;> rfl)).mp hmul

/-- The graph of a PA variable is just equality with the slot selected by the
current slot map.  This version works over any membership relation. -/
theorem termGraphAt_var_spec {α : Type u} {mem : α → α → Prop}
    (ρ : Nat → Nat) (out n : Nat) (e : Nat → α) :
    Sat mem e (termGraphAt ρ out (PA.Term.var n)) ↔ e out = e (ρ n) := by
  rfl

/-- The graph of the PA zero term says exactly that the output slot is empty.
This version works over any membership relation. -/
theorem termGraphAt_zero_spec {α : Type u} {mem : α → α → Prop}
    (ρ : Nat → Nat) (out : Nat) (e : Nat → α) :
    Sat mem e (termGraphAt ρ out PA.Term.zero) ↔ ∀ x, ¬ mem x (e out) := by
  exact HF_emptyAt_spec e out

/-- The graph of the successor of a variable says exactly that the output slot
is the adjunction of that variable's value to itself.  This version states the
adjunction property directly, so it works over any membership relation. -/
theorem termGraphAt_succ_var_spec {α : Type u} {mem : α → α → Prop}
    (ρ : Nat → Nat) (out n : Nat) (e : Nat → α) :
    Sat mem e (termGraphAt ρ out (PA.Term.succ (PA.Term.var n))) ↔
      ∀ x, mem x (e out) ↔ mem x (e (ρ n)) ∨ x = e (ρ n) := by
  constructor
  · intro h
    rcases h with ⟨x, hx, hs⟩
    have hx' : x = e (ρ n) := by
      change x = scons x e (ρ n + 1) at hx
      rwa [← Nat.succ_eq_add_one (ρ n)] at hx
    have hs' := (HF_adjoinAt_spec (scons x e) (out+1) 0 0).mp hs
    intro y
    have hsy := hs' y
    change mem y (e out) ↔ mem y x ∨ y = x at hsy
    simpa [hx'] using hsy
  · intro h
    refine ⟨e (ρ n), ?_, ?_⟩
    · change scons (e (ρ n)) e 0 = scons (e (ρ n)) e (ρ n + 1)
      rw [← Nat.succ_eq_add_one (ρ n)]
      rfl
    · apply (HF_adjoinAt_spec (scons (e (ρ n)) e) (out+1) 0 0).mpr
      intro y
      change mem y (e out) ↔ mem y (e (ρ n)) ∨ y = e (ρ n)
      exact h y

/-- In any adjunction model, the graph of a PA variable is just equality with
the slot selected by the current slot map. -/
theorem termGraphAt_var_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (out n : Nat) (e : Nat → α) :
    Sat M.mem e (termGraphAt ρ out (PA.Term.var n)) ↔ e out = e (ρ n) := by
  rfl

/-- In any adjunction model, the graph of the PA zero term is the HF empty
object. -/
theorem termGraphAt_zero_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (out : Nat) (e : Nat → α) :
    Sat M.mem e (termGraphAt ρ out PA.Term.zero) ↔ e out = M.empty := by
  exact HF_emptyAt_empty M e out

/-- In any adjunction model, the graph of the successor of a variable is
self-adjunction of the value of that variable. -/
theorem termGraphAt_succ_var_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (out n : Nat) (e : Nat → α) :
    Sat M.mem e (termGraphAt ρ out (PA.Term.succ (PA.Term.var n))) ↔
      e out = M.adjoin (e (ρ n)) (e (ρ n)) := by
  constructor
  · intro h
    rcases h with ⟨x, hx, hs⟩
    have hx' : x = e (ρ n) := by
      change x = scons x e (ρ n + 1) at hx
      rwa [← Nat.succ_eq_add_one (ρ n)] at hx
    have hs' := (HF_succAt_spec M (scons x e) (out+1) 0).mp hs
    change e out = M.adjoin x x at hs'
    simpa [hx'] using hs'
  · intro h
    refine ⟨e (ρ n), ?_, ?_⟩
    · change scons (e (ρ n)) e 0 = scons (e (ρ n)) e (ρ n + 1)
      rw [← Nat.succ_eq_add_one (ρ n)]
      rfl
    · apply (HF_succAt_spec M (scons (e (ρ n)) e) (out+1) 0).mpr
      change e out = M.adjoin (e (ρ n)) (e (ρ n))
      exact h

/-- In any chosen first-order adjunction model, the graph of the successor of a
variable is self-adjunction of the value of that variable. -/
theorem termGraphAt_succ_var_firstOrder_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out n : Nat) (e : Nat → α) :
    Sat M.mem e (termGraphAt ρ out (PA.Term.succ (PA.Term.var n))) ↔
      e out = M.adjoin (e (ρ n)) (e (ρ n)) := by
  constructor
  · intro h
    rcases h with ⟨x, hx, hs⟩
    have hx' : x = e (ρ n) := by
      change x = scons x e (ρ n + 1) at hx
      rwa [← Nat.succ_eq_add_one (ρ n)] at hx
    have hs' := (FirstOrderAdjunctionModel.HF_succAt_spec M
      (scons x e) (out+1) 0).mp hs
    change e out = M.adjoin x x at hs'
    simpa [hx'] using hs'
  · intro h
    refine ⟨e (ρ n), ?_, ?_⟩
    · change scons (e (ρ n)) e 0 = scons (e (ρ n)) e (ρ n + 1)
      rw [← Nat.succ_eq_add_one (ρ n)]
      rfl
    · apply (FirstOrderAdjunctionModel.HF_succAt_spec M
        (scons (e (ρ n)) e) (out+1) 0).mpr
      change e out = M.adjoin (e (ρ n)) (e (ρ n))
      exact h

theorem termGraphAt_add_var_zero_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out n : Nat) (e : Nat → α) (h : e out = e (ρ n)) :
    Sat M.mem e (termGraphAt ρ out (PA.Term.add (PA.Term.var n) PA.Term.zero)) := by
  refine ⟨e (ρ n), M.empty, ?_, ?_, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 2) 1 n
      (scons M.empty (scons (e (ρ n)) e))).mpr
    simp [scons]
  · apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
      (scons M.empty (scons (e (ρ n)) e)) 0).mpr
    rfl
  · apply addGraphAt_zero_right_model M
      (scons M.empty (scons (e (ρ n)) e)) (out+2) 1 0
    · simpa [scons] using h
    · rfl

theorem termGraphAt_mul_var_zero_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out n : Nat) (e : Nat → α) (h : e out = M.empty) :
    Sat M.mem e (termGraphAt ρ out (PA.Term.mul (PA.Term.var n) PA.Term.zero)) := by
  refine ⟨M.empty, e (ρ n), M.empty, ?_, ?_, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 3) 1 n
      (scons M.empty (scons (e (ρ n)) (scons M.empty e)))).mpr
    simp [scons]
  · apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
      (scons M.empty (scons (e (ρ n)) (scons M.empty e))) 2).mpr
    rfl
  · refine ⟨?_, ?_⟩
    · change M.empty = e out
      exact h.symm
    · apply mulGraphAt_zero_right_model M
        (scons M.empty (scons (e (ρ n)) (scons M.empty e))) 0 1 2
      · rfl
      · rfl

/-- A multiplication term graph from explicit multiplication-recursion trace
data. -/
theorem termGraphAt_mul_var_var_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f : α}
    (hf : MulRecApprox M (e (ρ left)) f (e (ρ right)))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) (e out)) f) :
    Sat M.mem e
      (termGraphAt ρ out (PA.Term.mul (PA.Term.var left) (PA.Term.var right))) := by
  refine ⟨e (ρ right), e (ρ left), e out, ?_, ?_, rfl, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 3) 1 left
      (scons (e out) (scons (e (ρ left)) (scons (e (ρ right)) e)))).mpr
    simp [scons]
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 3) 2 right
      (scons (e out) (scons (e (ρ left)) (scons (e (ρ right)) e)))).mpr
    simp [scons]
  · apply mulGraphAt_of_mulRecApprox_model M
      (scons (e out) (scons (e (ρ left)) (scons (e (ρ right)) e)))
      0 1 2 (f := f)
    · change MulRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) (e out)) f
      exact hout

/-- A graph for `x * S(y)` from a multiplication-recursion trace for `x*y`
and an addition trace for `(x*y)+x`. -/
theorem termGraphAt_mul_var_succ_var_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f z g y : α}
    (hrightOrd : OrdinalLike M.mem (e (ρ right)))
    (hout : e out = y)
    (hf : MulRecApprox M (e (ρ left)) f (e (ρ right)))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox M z g (e (ρ left)))
    (hy : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ left)) y) g) :
    Sat M.mem e
      (termGraphAt ρ out
        (PA.Term.mul (PA.Term.var left) (PA.Term.succ (PA.Term.var right)))) := by
  let sy := M.adjoin (e (ρ right)) (e (ρ right))
  let E := scons y (scons (e (ρ left)) (scons sy e))
  refine ⟨sy, e (ρ left), y, ?_, ?_, ?_, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 3) 1 left E).mpr
    simp [E, scons]
  · apply (termGraphAt_succ_var_firstOrder_model M (fun n => ρ n + 3)
      2 right E).mpr
    change sy = M.adjoin (e (ρ right)) (e (ρ right))
    rfl
  · change y = e out
    exact hout.symm
  · apply mulGraphAt_succ_right_of_mulRecApprox_model M E 0 1 2 (ρ right + 3)
      (f := f) (z := z) (g := g) (y := y)
    · simpa [E, sy, scons] using hrightOrd
    · change sy = M.adjoin (e (ρ right)) (e (ρ right))
      rfl
    · rfl
    · change MulRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f
      exact hz
    · change FirstOrderAdjunctionModel.SuccRecApprox M z g (e (ρ left))
      exact hg
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ left)) y) g
      exact hy

/-- A graph for `(x*y)+x` from explicit multiplication and addition traces. -/
theorem termGraphAt_add_mul_var_var_var_of_traces_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f z g y : α}
    (hout : e out = y)
    (hf : MulRecApprox M (e (ρ left)) f (e (ρ right)))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox M z g (e (ρ left)))
    (hy : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ left)) y) g) :
    Sat M.mem e
      (termGraphAt ρ out
        (PA.Term.add
          (PA.Term.mul (PA.Term.var left) (PA.Term.var right))
          (PA.Term.var left))) := by
  let E := scons (e (ρ left)) (scons z e)
  refine ⟨z, e (ρ left), ?_, ?_, ?_⟩
  · apply termGraphAt_mul_var_var_of_mulRecApprox_model M (fun n => ρ n + 2)
      1 left right E (f := f)
    · change MulRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f
      exact hz
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 2) 0 left E).mpr
    simp [E, scons]
  · apply addGraphAt_of_succRecApprox_model M E (out+2) 1 0 (f := g)
    · change FirstOrderAdjunctionModel.SuccRecApprox M z g (e (ρ left))
      exact hg
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ left)) (e out)) g
      rw [hout]
      exact hy

/-- A binary addition term graph from explicit successor-recursion trace data. -/
theorem termGraphAt_add_var_var_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f : α}
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right)))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) (e out)) f) :
    Sat M.mem e
      (termGraphAt ρ out (PA.Term.add (PA.Term.var left) (PA.Term.var right))) := by
  refine ⟨e (ρ left), e (ρ right), ?_, ?_, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 2) 1 left
      (scons (e (ρ right)) (scons (e (ρ left)) e))).mpr
    simp [scons]
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 2) 0 right
      (scons (e (ρ right)) (scons (e (ρ left)) e))).mpr
    simp [scons]
  · apply addGraphAt_of_succRecApprox_model M
      (scons (e (ρ right)) (scons (e (ρ left)) e)) (out+2) 1 0
      (f := f)
    · change FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) (e out)) f
      exact hout

/-- A graph for `x + S(y)` from a successor-recursion trace for `x + y`. -/
theorem termGraphAt_add_var_succ_var_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f z : α}
    (hrightOrd : OrdinalLike M.mem (e (ρ right)))
    (hout : e out = M.adjoin z z)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right)))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f) :
    Sat M.mem e
      (termGraphAt ρ out
        (PA.Term.add (PA.Term.var left) (PA.Term.succ (PA.Term.var right)))) := by
  let sy := M.adjoin (e (ρ right)) (e (ρ right))
  refine ⟨e (ρ left), sy, ?_, ?_, ?_⟩
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => ρ n + 2) 1 left
      (scons sy (scons (e (ρ left)) e))).mpr
    simp [scons]
  · apply (termGraphAt_succ_var_firstOrder_model M (fun n => ρ n + 2) 0 right
      (scons sy (scons (e (ρ left)) e))).mpr
    change sy = M.adjoin (e (ρ right)) (e (ρ right))
    rfl
  · apply addGraphAt_succ_right_of_succRecApprox_model M
      (scons sy (scons (e (ρ left)) e)) (out+2) 1 0 (ρ right + 2)
      (f := f) (z := z)
    · simpa [sy, scons] using hrightOrd
    · change sy = M.adjoin (e (ρ right)) (e (ρ right))
      rfl
    · change e out = M.adjoin z z
      exact hout
    · change FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f
      exact hz

/-- A graph for `S(x + y)` from a successor-recursion trace for `x + y`. -/
theorem termGraphAt_succ_add_var_var_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat)
    (out left right : Nat) (e : Nat → α) {f z : α}
    (hout : e out = M.adjoin z z)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right)))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f) :
    Sat M.mem e
      (termGraphAt ρ out
        (PA.Term.succ (PA.Term.add (PA.Term.var left) (PA.Term.var right)))) := by
  refine ⟨z, ?_, ?_⟩
  · apply termGraphAt_add_var_var_of_succRecApprox_model M (fun n => ρ n + 1)
      0 left right (scons z e) (f := f)
    · change FirstOrderAdjunctionModel.SuccRecApprox M (e (ρ left)) f (e (ρ right))
      exact hf
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e (ρ right)) z) f
      exact hz
  · apply (FirstOrderAdjunctionModel.HF_succAt_spec M (scons z e)
      (out+1) 0).mpr
    change e out = M.adjoin z z
    exact hout

theorem termGraphAt_exact (t : PA.Term) :
    ∀ (ρ : Nat → Nat) (out : Nat) (v e),
      (∀ n, e (ρ n) = ordinalCode (v n)) →
        (Sat Mem e (termGraphAt ρ out t) ↔
          e out = ordinalCode (PA.Term.eval PA.natModel v t)) := by
  induction t with
  | var n =>
      intro ρ out v e hρ
      constructor
      · intro h
        exact h.trans (hρ n)
      · intro h
        exact h.trans (hρ n).symm
  | zero =>
      intro ρ out v e hρ
      constructor
      · intro h
        have hzero := (HF_emptyAt_empty standardModel e out).mp h
        change e out = empty at hzero
        simpa [PA.Term.eval, PA.natModel, ordinalCode_zero] using hzero
      · intro h
        apply (HF_emptyAt_empty standardModel e out).mpr
        change e out = empty
        simpa [PA.Term.eval, PA.natModel, ordinalCode_zero] using h
  | succ t ih =>
      intro ρ out v e hρ
      constructor
      · intro h
        rcases h with ⟨x, ht, hs⟩
        have hρ' : ∀ n, scons x e (ρ n + 1) = ordinalCode (v n) := by
          intro n
          simpa [scons] using hρ n
        have htval := (ih (fun n => ρ n + 1) 0 v (scons x e) hρ').mp ht
        change x = ordinalCode (PA.Term.eval PA.natModel v t) at htval
        have hsval := (HF_succAt_spec standardModel (scons x e) (out+1) 0).mp hs
        change e out = adjoin x x at hsval
        rw [hsval, htval]
        simp only [PA.Term.eval, PA.natModel]
        rw [ordinalCode_succ]
      · intro h
        let x := ordinalCode (PA.Term.eval PA.natModel v t)
        refine ⟨x, ?_, ?_⟩
        · apply (ih (fun n => ρ n + 1) 0 v (scons x e) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · apply (HF_succAt_spec standardModel (scons x e) (out+1) 0).mpr
          change e out = adjoin x x
          rw [h]
          simp only [PA.Term.eval, PA.natModel, x]
          rw [ordinalCode_succ]
  | add a b iha ihb =>
      intro ρ out v e hρ
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, hAdd⟩
        have hρ' : ∀ n, scons y (scons x e) (ρ n + 2) = ordinalCode (v n) := by
          intro n
          simpa [scons] using hρ n
        have hx := (iha (fun n => ρ n + 2) 1 v (scons y (scons x e)) hρ').mp ha
        have hy := (ihb (fun n => ρ n + 2) 0 v (scons y (scons x e)) hρ').mp hb
        have hout := addGraphAt_value_of_ordinalInputs (out+2) 1 0
          (PA.Term.eval PA.natModel v a) (PA.Term.eval PA.natModel v b)
          (scons y (scons x e)) hx hy hAdd
        change e out =
          ordinalCode (PA.Term.eval PA.natModel v a + PA.Term.eval PA.natModel v b) at hout
        simpa [PA.Term.eval, PA.natModel] using hout
      · intro h
        let x := ordinalCode (PA.Term.eval PA.natModel v a)
        let y := ordinalCode (PA.Term.eval PA.natModel v b)
        refine ⟨x, y, ?_, ?_, ?_⟩
        · apply (iha (fun n => ρ n + 2) 1 v (scons y (scons x e)) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · apply (ihb (fun n => ρ n + 2) 0 v (scons y (scons x e)) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · apply addGraphAt_ordinalCode (out+2) 1 0
            (PA.Term.eval PA.natModel v a) (PA.Term.eval PA.natModel v b)
            (scons y (scons x e))
          · change e out =
              ordinalCode (PA.Term.eval PA.natModel v a + PA.Term.eval PA.natModel v b)
            simpa [PA.Term.eval, PA.natModel] using h
          · rfl
          · rfl
  | mul a b iha ihb =>
      intro ρ out v e hρ
      constructor
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hMul⟩
        have hρ' : ∀ n, scons z (scons x (scons y e)) (ρ n + 3) =
            ordinalCode (v n) := by
          intro n
          simpa [scons] using hρ n
        have hx := (iha (fun n => ρ n + 3) 1 v
          (scons z (scons x (scons y e))) hρ').mp ha
        have hy := (ihb (fun n => ρ n + 3) 2 v
          (scons z (scons x (scons y e))) hρ').mp hb
        have hz := mulGraph_value_of_ordinalInputs
          (PA.Term.eval PA.natModel v a) (PA.Term.eval PA.natModel v b)
          (scons z (scons x (scons y e))) hx hy hMul
        have hcopy' : z = e out := hcopy
        rw [hcopy'] at hz
        change e out = ordinalCode
          (PA.Term.eval PA.natModel v a * PA.Term.eval PA.natModel v b) at hz
        simpa [PA.Term.eval, PA.natModel] using hz
      · intro h
        let y := ordinalCode (PA.Term.eval PA.natModel v b)
        let x := ordinalCode (PA.Term.eval PA.natModel v a)
        let z := ordinalCode
          (PA.Term.eval PA.natModel v a * PA.Term.eval PA.natModel v b)
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · apply (iha (fun n => ρ n + 3) 1 v
            (scons z (scons x (scons y e))) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · apply (ihb (fun n => ρ n + 3) 2 v
            (scons z (scons x (scons y e))) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · change z = e out
          simpa [PA.Term.eval, PA.natModel, z] using h.symm
        · change Sat Mem (scons z (scons x (scons y e))) mulGraph
          simpa [z, x, y] using
            (mulGraph_ordinalCode
              (PA.Term.eval PA.natModel v a)
              (PA.Term.eval PA.natModel v b) e)

/-- Slot-map extension across a translated PA quantifier.  The new PA variable
`0` is read from the newly bound HF slot `0`; older PA variables are shifted
past that binder. -/
def upVarMap (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

/-- Slot map for the formula after replacing PA variable `p` by zero.

The first `k` HF slots are local term witnesses, the next `p` slots are PA
variables bound by surrounding object-language quantifiers, and the remaining
PA variables are read through `ρ`. -/
def substZeroAfterMap (p k : Nat) (ρ : Nat → Nat) : Nat → Nat :=
  fun n => if n < p then k + n else ρ (n - p) + k + p

/-- Slot map for the original formula before replacing PA variable `p` by zero.

Compared with `substZeroAfterMap`, variable `p` is read from the freshly
inserted HF slot `k+p`, and variables above `p` are shifted one slot upward. -/
def substZeroBeforeMap (p k : Nat) (ρ : Nat → Nat) : Nat → Nat :=
  fun n =>
    if n < p then k + n
    else if n = p then k + p
    else ρ (n - p - 1) + k + p + 1

@[simp] theorem substZeroAfterMap_lt {p k n : Nat} {ρ : Nat → Nat}
    (h : n < p) : substZeroAfterMap p k ρ n = k + n := by
  simp [substZeroAfterMap, h]

@[simp] theorem substZeroAfterMap_ge {p k n : Nat} {ρ : Nat → Nat}
    (h : p ≤ n) : substZeroAfterMap p k ρ n = ρ (n - p) + k + p := by
  have hnlt : ¬ n < p := by omega
  simp [substZeroAfterMap, hnlt]

@[simp] theorem substZeroBeforeMap_lt {p k n : Nat} {ρ : Nat → Nat}
    (h : n < p) : substZeroBeforeMap p k ρ n = k + n := by
  simp [substZeroBeforeMap, h]

@[simp] theorem substZeroBeforeMap_eq {p k : Nat} {ρ : Nat → Nat} :
    substZeroBeforeMap p k ρ p = k + p := by
  simp [substZeroBeforeMap]

theorem substZeroBeforeMap_gt {p k n : Nat} {ρ : Nat → Nat}
    (h : p < n) :
    substZeroBeforeMap p k ρ n = ρ (n - p - 1) + k + p + 1 := by
  have hnlt : ¬ n < p := by omega
  have hne : n ≠ p := by omega
  simp [substZeroBeforeMap, hnlt, hne]

theorem substZeroBeforeMap_ne_replaced_slot {p k n : Nat} {ρ : Nat → Nat}
    (h : n ≠ p) : substZeroBeforeMap p k ρ n ≠ k + p := by
  by_cases hlt : n < p
  · rw [substZeroBeforeMap_lt (ρ := ρ) (k := k) hlt]
    omega
  · have hgt : p < n := by omega
    rw [substZeroBeforeMap_gt (ρ := ρ) (k := k) hgt]
    omega

theorem substZeroAfterMap_add (p k d : Nat) (ρ : Nat → Nat) :
    ∀ n, substZeroAfterMap p k ρ n + d =
      substZeroAfterMap p (k+d) ρ n := by
  intro n
  by_cases h : n < p
  · simp [substZeroAfterMap, h]
    omega
  · have hge : p ≤ n := by omega
    simp [substZeroAfterMap, h]
    omega

theorem substZeroBeforeMap_add (p k d : Nat) (ρ : Nat → Nat) :
    ∀ n, substZeroBeforeMap p k ρ n + d =
      substZeroBeforeMap p (k+d) ρ n := by
  intro n
  by_cases hlt : n < p
  · simp [substZeroBeforeMap, hlt]
    omega
  · by_cases heq : n = p
    · subst n
      simp [substZeroBeforeMap]
      omega
    · simp [substZeroBeforeMap, hlt, heq]
      omega

theorem upVarMap_substZeroAfterMap_zero (p : Nat) (ρ : Nat → Nat) :
    ∀ n, upVarMap (substZeroAfterMap p 0 ρ) n =
      substZeroAfterMap (p+1) 0 ρ n := by
  intro n
  cases n with
  | zero =>
      simp [upVarMap, substZeroAfterMap]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        simp [upVarMap, substZeroAfterMap, hlt, hslt]
      · have hnlt : ¬ n + 1 < p + 1 := by omega
        have hidx : n + 1 - (p + 1) = n - p := by omega
        simp [upVarMap, substZeroAfterMap, hlt, hnlt, hidx]
        omega

theorem upVarMap_substZeroBeforeMap_zero (p : Nat) (ρ : Nat → Nat) :
    ∀ n, upVarMap (substZeroBeforeMap p 0 ρ) n =
      substZeroBeforeMap (p+1) 0 ρ n := by
  intro n
  cases n with
  | zero =>
      simp [upVarMap, substZeroBeforeMap]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        simp [upVarMap, substZeroBeforeMap, hlt, hslt]
      · by_cases heq : n = p
        · subst n
          simp [upVarMap, substZeroBeforeMap]
        · have hgt : p < n := by omega
          have hsgt : p + 1 < n + 1 := by omega
          have hnlt : ¬ n + 1 < p + 1 := by omega
          simp [upVarMap, substZeroBeforeMap, hlt, heq, hnlt]
          omega

theorem substZeroAfterMap_zero_zero (ρ : Nat → Nat) :
    ∀ n, substZeroAfterMap 0 0 ρ n = ρ n := by
  intro n
  simp [substZeroAfterMap]

theorem substZeroBeforeMap_zero_zero (ρ : Nat → Nat) :
    ∀ n, substZeroBeforeMap 0 0 ρ n = upVarMap ρ n := by
  intro n
  cases n <;> simp [substZeroBeforeMap, upVarMap]

/-- Insert a value at de Bruijn slot `k`, leaving slots below `k` fixed and
shifting slots at and above `k` upward.  In substitution lemmas, `k` is the
number of local witnesses already sitting in front of the PA-variable
environment. -/
def insertAt {α : Type u} (k : Nat) (x : α) (e : Nat → α) : Nat → α :=
  fun n => if n < k then e n else if n = k then x else e (n - 1)

theorem insertAt_zero {α : Type u} (x : α) (e : Nat → α) :
    ∀ n, insertAt 0 x e n = scons x e n := by
  intro n
  cases n <;> simp [insertAt, scons]

@[simp] theorem insertAt_lt {α : Type u} {k n : Nat} {x : α} {e : Nat → α}
    (h : n < k) : insertAt k x e n = e n := by
  simp [insertAt, h]

@[simp] theorem insertAt_eq {α : Type u} {k : Nat} {x : α} {e : Nat → α} :
    insertAt k x e k = x := by
  simp [insertAt]

theorem insertAt_gt {α : Type u} {k n : Nat} {x : α} {e : Nat → α}
    (h : k < n) : insertAt k x e n = e (n - 1) := by
  have hnot : ¬ n < k := by omega
  have hne : n ≠ k := by omega
  simp [insertAt, hnot, hne]

/-- Replace the value at de Bruijn slot `k`, leaving all other slots fixed. -/
def replaceAt {α : Type u} (k : Nat) (x : α) (e : Nat → α) : Nat → α :=
  fun n => if n = k then x else e n

@[simp] theorem replaceAt_eq {α : Type u} {k : Nat} {x : α} {e : Nat → α} :
    replaceAt k x e k = x := by
  simp [replaceAt]

theorem replaceAt_ne {α : Type u} {k n : Nat} {x : α} {e : Nat → α}
    (h : n ≠ k) : replaceAt k x e n = e n := by
  simp [replaceAt, h]

theorem replaceAt_zero_scons {α : Type u} (x d : α) (e : Nat → α) :
    ∀ n, replaceAt 0 x (scons d e) n = scons x e n := by
  intro n
  cases n <;> simp [replaceAt, scons]

def succReplaceAt {α : Type u} (M : FirstOrderAdjunctionModel α)
    (k : Nat) (e : Nat → α) : Nat → α :=
  replaceAt k (M.adjoin (e k) (e k)) e

@[simp] theorem succReplaceAt_eq {α : Type u}
    (M : FirstOrderAdjunctionModel α) (k : Nat) (e : Nat → α) :
    succReplaceAt M k e k = M.adjoin (e k) (e k) := by
  simp [succReplaceAt]

theorem succReplaceAt_ne {α : Type u}
    (M : FirstOrderAdjunctionModel α) {k n : Nat} (e : Nat → α)
    (h : n ≠ k) : succReplaceAt M k e n = e n := by
  exact replaceAt_ne h

theorem scons_insertAt {α : Type u} (k : Nat) (x d : α) (e : Nat → α) :
    ∀ n, scons d (insertAt k x e) n = insertAt (k+1) x (scons d e) n := by
  intro n
  cases n with
  | zero =>
      simp [insertAt, scons]
  | succ n =>
      simp only [scons]
      by_cases hlt : n < k
      · have hslt : n + 1 < k + 1 := by omega
        rw [insertAt_lt hlt, insertAt_lt hslt]
        rfl
      · by_cases heq : n = k
        · subst n
          rw [insertAt_eq, insertAt_eq]
        · have hgt : k < n := by omega
          have hsgt : k + 1 < n + 1 := by omega
          rw [insertAt_gt hgt, insertAt_gt hsgt]
          cases n with
          | zero => omega
          | succ n => rfl

theorem scons2_insertAt {α : Type u} (k : Nat) (x d₁ d₂ : α) (e : Nat → α) :
    ∀ n, scons d₂ (scons d₁ (insertAt k x e)) n =
      insertAt (k+2) x (scons d₂ (scons d₁ e)) n := by
  intro n
  calc
    scons d₂ (scons d₁ (insertAt k x e)) n =
        scons d₂ (insertAt (k+1) x (scons d₁ e)) n := by
          cases n with
          | zero => rfl
          | succ n => exact scons_insertAt k x d₁ e n
    _ = insertAt ((k+1)+1) x (scons d₂ (scons d₁ e)) n :=
        scons_insertAt (k+1) x d₂ (scons d₁ e) n
    _ = insertAt (k+2) x (scons d₂ (scons d₁ e)) n := by
        congr

theorem scons3_insertAt {α : Type u} (k : Nat) (x d₁ d₂ d₃ : α) (e : Nat → α) :
    ∀ n, scons d₃ (scons d₂ (scons d₁ (insertAt k x e))) n =
      insertAt (k+3) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
  intro n
  calc
    scons d₃ (scons d₂ (scons d₁ (insertAt k x e))) n =
        scons d₃ (insertAt (k+2) x (scons d₂ (scons d₁ e))) n := by
          cases n with
          | zero => rfl
          | succ n => exact scons2_insertAt k x d₁ d₂ e n
    _ = insertAt ((k+2)+1) x (scons d₃ (scons d₂ (scons d₁ e))) n :=
        scons_insertAt (k+2) x d₃ (scons d₂ (scons d₁ e)) n
    _ = insertAt (k+3) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
        congr

theorem scons_insertAt_prefix {α : Type u} (p k : Nat) (x d : α) (e : Nat → α) :
    ∀ n, scons d (insertAt (k+p) x e) n =
      insertAt ((k+1)+p) x (scons d e) n := by
  intro n
  calc
    scons d (insertAt (k+p) x e) n =
        insertAt ((k+p)+1) x (scons d e) n :=
      scons_insertAt (k+p) x d e n
    _ = insertAt ((k+1)+p) x (scons d e) n := by
      rw [show (k+p)+1 = (k+1)+p by omega]

theorem scons2_insertAt_prefix {α : Type u}
    (p k : Nat) (x d₁ d₂ : α) (e : Nat → α) :
    ∀ n, scons d₂ (scons d₁ (insertAt (k+p) x e)) n =
      insertAt ((k+2)+p) x (scons d₂ (scons d₁ e)) n := by
  intro n
  calc
    scons d₂ (scons d₁ (insertAt (k+p) x e)) n =
        insertAt ((k+p)+2) x (scons d₂ (scons d₁ e)) n :=
      scons2_insertAt (k+p) x d₁ d₂ e n
    _ = insertAt ((k+2)+p) x (scons d₂ (scons d₁ e)) n := by
      rw [show (k+p)+2 = (k+2)+p by omega]

theorem scons3_insertAt_prefix {α : Type u}
    (p k : Nat) (x d₁ d₂ d₃ : α) (e : Nat → α) :
    ∀ n, scons d₃ (scons d₂ (scons d₁ (insertAt (k+p) x e))) n =
      insertAt ((k+3)+p) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
  intro n
  calc
    scons d₃ (scons d₂ (scons d₁ (insertAt (k+p) x e))) n =
        insertAt ((k+p)+3) x (scons d₃ (scons d₂ (scons d₁ e))) n :=
      scons3_insertAt (k+p) x d₁ d₂ d₃ e n
    _ = insertAt ((k+3)+p) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
      rw [show (k+p)+3 = (k+3)+p by omega]

/-- Shift a replacement-term graph through one fresh local witness slot while
keeping the inserted replacement value immediately after the local prefix. -/
theorem Sat_termGraphAt_insertAt_shift_prefix {α : Type u}
    {mem : α → α → Prop} (t : PA.Term) (p k : Nat)
    (ρ : Nat → Nat) (termVal d : α) (e : Nat → α)
    (h : Sat mem (insertAt (k+p) termVal e)
      (termGraphAt (fun n => ρ n + k + p + 1) (k+p) t)) :
    Sat mem (insertAt ((k+1)+p) termVal (scons d e))
      (termGraphAt (fun n => ρ n + (k+1) + p + 1) ((k+1)+p) t) := by
  have hshift : Sat mem (scons d (insertAt (k+p) termVal e))
      (termGraphAt (fun n => (ρ n + k + p + 1) + 1) ((k+p)+1) t) :=
    Sat_termGraphAt_shift_front t (fun n => ρ n + k + p + 1)
      (k+p) (insertAt (k+p) termVal e) d h
  have henv : ∀ n,
      scons d (insertAt (k+p) termVal e) n =
        insertAt ((k+1)+p) termVal (scons d e) n :=
    scons_insertAt_prefix p k termVal d e
  have hshift' : Sat mem (insertAt ((k+1)+p) termVal (scons d e))
      (termGraphAt (fun n => (ρ n + k + p + 1) + 1) ((k+p)+1) t) :=
    (Sat_ext (termGraphAt (fun n => (ρ n + k + p + 1) + 1)
      ((k+p)+1) t)
      (scons d (insertAt (k+p) termVal e))
      (insertAt ((k+1)+p) termVal (scons d e)) henv).mp hshift
  have hEq : termGraphAt (fun n => (ρ n + k + p + 1) + 1)
      ((k+p)+1) t =
      termGraphAt (fun n => ρ n + (k+1) + p + 1) ((k+1)+p) t := by
    rw [show (k+p)+1 = (k+1)+p by omega]
    exact termGraphAt_map_ext t (out := (k+1)+p) (fun n => by omega)
  rwa [hEq] at hshift'

/-- Atomic substituted-variable case for arbitrary PA-term substitution in
translated term graphs. -/
theorem termGraphAt_substTermAt_replaced_var_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term)
    (p k : Nat) (ρ : Nat → Nat) (out : Nat) (termVal : α)
    (e : Nat → α)
    (hout : out < k)
    (hfree : ∀ n, PA.Term.Free n t →
      OrdinalLike M.mem (e (ρ n + k + p)))
    (hterm : Sat M.mem (insertAt (k+p) termVal e)
      (termGraphAt (fun n => ρ n + k + p + 1) (k+p) t)) :
    Sat M.mem e
        (termGraphAt (substZeroAfterMap p k ρ) out
          (PA.Term.rename (fun n => n + p) t)) ↔
      Sat M.mem (insertAt (k+p) termVal e)
        (termGraphAt (substZeroBeforeMap p k ρ) out (PA.Term.var p)) := by
  have houtSlot : out < k + p := by omega
  constructor
  · intro h
    have hRenamed : Sat M.mem e
        (termGraphAt (fun n => ρ n + k + p) out t) := by
      have hPA := termGraphAt_PA_rename t
        (ρ := substZeroAfterMap p k ρ) (out := out)
        (r := fun n => n + p)
      rw [hPA] at h
      have hMap := termGraphAt_map_ext t
        (ρ := fun n => substZeroAfterMap p k ρ (n + p))
        (σ := fun n => ρ n + k + p) (out := out)
        (fun n => by
          have hge : p ≤ n + p := by omega
          rw [substZeroAfterMap_ge (ρ := ρ) (k := k) hge]
          congr
          omega)
      rwa [hMap] at h
    have hval : e out = insertAt (k+p) termVal e (k+p) :=
      termGraphAt_outputs_eq_finite_model M t
        (ρ₁ := fun n => ρ n + k + p)
        (ρ₂ := fun n => ρ n + k + p + 1)
        (out₁ := out) (out₂ := k+p)
        (e₁ := e) (e₂ := insertAt (k+p) termVal e)
        (by
          intro n hn
          have hgt : k+p < ρ n + k + p + 1 := by omega
          rw [insertAt_gt hgt]
          congr)
        hfree hRenamed hterm
    apply (termGraphAt_var_spec (mem := M.mem)
      (substZeroBeforeMap p k ρ) out p
      (insertAt (k+p) termVal e)).mpr
    change insertAt (k+p) termVal e out =
      insertAt (k+p) termVal e (substZeroBeforeMap p k ρ p)
    rw [insertAt_lt houtSlot, substZeroBeforeMap_eq]
    exact hval
  · intro h
    have hEq := (termGraphAt_var_spec (mem := M.mem)
      (substZeroBeforeMap p k ρ) out p
      (insertAt (k+p) termVal e)).mp h
    change insertAt (k+p) termVal e out =
      insertAt (k+p) termVal e (substZeroBeforeMap p k ρ p) at hEq
    rw [insertAt_lt houtSlot, substZeroBeforeMap_eq] at hEq
    have hTransport : Sat M.mem e
        (termGraphAt (fun n => ρ n + k + p) out t) := by
      apply termGraphAt_transport_model M.toFirstOrderAdjunctionModel t
        (ρ₁ := fun n => ρ n + k + p + 1)
        (ρ₂ := fun n => ρ n + k + p)
        (out₁ := k+p) (out₂ := out)
        (e₁ := insertAt (k+p) termVal e) (e₂ := e)
      · exact hEq.symm
      · intro n hn
        have hgt : k+p < ρ n + k + p + 1 := by omega
        rw [insertAt_gt hgt]
        congr
      · exact hterm
    have hPA := termGraphAt_PA_rename t
      (ρ := substZeroAfterMap p k ρ) (out := out)
      (r := fun n => n + p)
    rw [hPA]
    have hMap := termGraphAt_map_ext t
      (ρ := fun n => substZeroAfterMap p k ρ (n + p))
      (σ := fun n => ρ n + k + p) (out := out)
      (fun n => by
        have hge : p ≤ n + p := by omega
        rw [substZeroAfterMap_ge (ρ := ρ) (k := k) hge]
        congr
        omega)
    rwa [hMap]

/-- Transport translated PA-term graphs across arbitrary PA-term substitution.

The theorem is deliberately semantic: it requires an explicit graph witness for
the replacement term in the inserted slot, rather than hiding term totality in
the substitution definition. -/
theorem termGraphAt_substTermAt_insert_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (replacement target : PA.Term) :
    ∀ (p k : Nat) (ρ : Nat → Nat) (out : Nat) (termVal : α)
      (e : Nat → α),
      out < k →
      (∀ n, PA.Term.Free n replacement →
        OrdinalLike M.mem (e (ρ n + k + p))) →
      Sat M.mem (insertAt (k+p) termVal e)
        (termGraphAt (fun n => ρ n + k + p + 1) (k+p) replacement) →
      (Sat M.mem e
          (termGraphAt (substZeroAfterMap p k ρ) out
            (PA.Term.subst (PA.Formula.substTermAt p replacement) target)) ↔
        Sat M.mem (insertAt (k+p) termVal e)
          (termGraphAt (substZeroBeforeMap p k ρ) out target)) := by
  induction target with
  | var n =>
      intro p k ρ out termVal e hout hfree hterm
      by_cases hlt : n < p
      · simp only [PA.Term.subst]
        rw [PA.Formula.substTermAt_lt hlt]
        have houtSlot : out < k + p := by omega
        have hnSlot : substZeroBeforeMap p k ρ n < k + p := by
          rw [substZeroBeforeMap_lt hlt]
          omega
        constructor
        · intro h
          change e out = e (substZeroAfterMap p k ρ n) at h
          change insertAt (k+p) termVal e out =
            insertAt (k+p) termVal e (substZeroBeforeMap p k ρ n)
          rw [insertAt_lt houtSlot, insertAt_lt hnSlot]
          simpa [substZeroAfterMap_lt hlt, substZeroBeforeMap_lt hlt] using h
        · intro h
          change insertAt (k+p) termVal e out =
            insertAt (k+p) termVal e (substZeroBeforeMap p k ρ n) at h
          change e out = e (substZeroAfterMap p k ρ n)
          rw [insertAt_lt houtSlot, insertAt_lt hnSlot] at h
          simpa [substZeroAfterMap_lt hlt, substZeroBeforeMap_lt hlt] using h
      · by_cases heq : n = p
        · subst n
          simp only [PA.Term.subst]
          rw [PA.Formula.substTermAt_eq]
          exact termGraphAt_substTermAt_replaced_var_model M replacement
            p k ρ out termVal e hout hfree hterm
        · have hgt : p < n := by omega
          simp only [PA.Term.subst]
          rw [PA.Formula.substTermAt_gt hgt]
          have houtSlot : out < k + p := by omega
          have hAfter :
              substZeroAfterMap p k ρ (n - 1) =
                ρ (n - p - 1) + k + p := by
            have hp_le : p ≤ n - 1 := by omega
            rw [substZeroAfterMap_ge (ρ := ρ) (k := k) hp_le]
            rw [show n - 1 - p = n - p - 1 by
              rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 p]]
          have hBefore :
              substZeroBeforeMap p k ρ n =
                ρ (n - p - 1) + k + p + 1 :=
            substZeroBeforeMap_gt (ρ := ρ) (k := k) hgt
          have hBeforeGt : k + p < substZeroBeforeMap p k ρ n := by
            rw [hBefore]
            omega
          have hslot :
              insertAt (k+p) termVal e (substZeroBeforeMap p k ρ n) =
                e (substZeroAfterMap p k ρ (n - 1)) := by
            rw [insertAt_gt hBeforeGt, hBefore, hAfter]
            congr
          constructor
          · intro h
            change e out = e (substZeroAfterMap p k ρ (n - 1)) at h
            change insertAt (k+p) termVal e out =
              insertAt (k+p) termVal e (substZeroBeforeMap p k ρ n)
            rw [insertAt_lt houtSlot, hslot]
            exact h
          · intro h
            change insertAt (k+p) termVal e out =
              insertAt (k+p) termVal e (substZeroBeforeMap p k ρ n) at h
            change e out = e (substZeroAfterMap p k ρ (n - 1))
            rwa [insertAt_lt houtSlot, hslot] at h
  | zero =>
      intro p k ρ out termVal e hout _hfree _hterm
      have houtSlot : out < k + p := by omega
      constructor
      · intro h
        have houtEmpty : e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty
            M.toFirstOrderAdjunctionModel e out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty
          M.toFirstOrderAdjunctionModel (insertAt (k+p) termVal e) out).mpr
        rw [insertAt_lt houtSlot]
        exact houtEmpty
      · intro h
        have houtEmpty : insertAt (k+p) termVal e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty
            M.toFirstOrderAdjunctionModel (insertAt (k+p) termVal e) out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty
          M.toFirstOrderAdjunctionModel e out).mpr
        rwa [insertAt_lt houtSlot] at houtEmpty
  | succ s ih =>
      intro p k ρ out termVal e hout hfree hterm
      constructor
      · intro h
        rcases h with ⟨x, hs, hsucc⟩
        refine ⟨x, ?_, ?_⟩
        · have hsMap : Sat M.mem (scons x e)
              (termGraphAt (substZeroAfterMap p (k+1) ρ) 0
                (PA.Term.subst (PA.Formula.substTermAt p replacement) s)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) s)
              (ρ := fun n => substZeroAfterMap p k ρ n + 1)
              (σ := substZeroAfterMap p (k+1) ρ) (out := 0)
              (substZeroAfterMap_add p k 1 ρ)
            rwa [← hEq]
          have hfree' : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem ((scons x e) (ρ n + (k+1) + p)) := by
            intro n hn
            have hslot : (scons x e) (ρ n + (k+1) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+1) + p = ρ n + k + p + 1 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have htermX : Sat M.mem
              (insertAt ((k+1)+p) termVal (scons x e))
              (termGraphAt (fun n => ρ n + (k+1) + p + 1)
                ((k+1)+p) replacement) :=
            Sat_termGraphAt_insertAt_shift_prefix replacement p k ρ
              termVal x e hterm
          have hsIns := (ih p (k+1) ρ 0 termVal (scons x e)
            (by omega) hfree' htermX).mp hsMap
          have henv : ∀ n,
              scons x (insertAt (k+p) termVal e) n =
                insertAt ((k+1)+p) termVal (scons x e) n :=
            scons_insertAt_prefix p k termVal x e
          have hsEnv : Sat M.mem (scons x (insertAt (k+p) termVal e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 s) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 s)
              (scons x (insertAt (k+p) termVal e))
              (insertAt ((k+1)+p) termVal (scons x e)) henv).mpr hsIns
          have hEq := termGraphAt_map_ext s
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          rwa [hEq] at hsEnv
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec
            M.toFirstOrderAdjunctionModel (scons x e) (out+1) 0).mp hsucc
          apply (FirstOrderAdjunctionModel.HF_succAt_spec
            M.toFirstOrderAdjunctionModel
            (scons x (insertAt (k+p) termVal e)) (out+1) 0).mpr
          change insertAt (k+p) termVal e out = M.adjoin x x
          rwa [insertAt_lt (by omega : out < k + p)]
      · intro h
        rcases h with ⟨x, hs, hsucc⟩
        refine ⟨x, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext s
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          have hsMap : Sat M.mem (scons x (insertAt (k+p) termVal e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 s) := by
            rw [hEq]
            exact hs
          have henv : ∀ n,
              scons x (insertAt (k+p) termVal e) n =
                insertAt ((k+1)+p) termVal (scons x e) n :=
            scons_insertAt_prefix p k termVal x e
          have hsIns : Sat M.mem
              (insertAt ((k+1)+p) termVal (scons x e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 s) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 s)
              (scons x (insertAt (k+p) termVal e))
              (insertAt ((k+1)+p) termVal (scons x e)) henv).mp hsMap
          have hfree' : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem ((scons x e) (ρ n + (k+1) + p)) := by
            intro n hn
            have hslot : (scons x e) (ρ n + (k+1) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+1) + p = ρ n + k + p + 1 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have htermX : Sat M.mem
              (insertAt ((k+1)+p) termVal (scons x e))
              (termGraphAt (fun n => ρ n + (k+1) + p + 1)
                ((k+1)+p) replacement) :=
            Sat_termGraphAt_insertAt_shift_prefix replacement p k ρ
              termVal x e hterm
          have hsSub := (ih p (k+1) ρ 0 termVal (scons x e)
            (by omega) hfree' htermX).mpr hsIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) s)
            (ρ := fun n => substZeroAfterMap p k ρ n + 1)
            (σ := substZeroAfterMap p (k+1) ρ) (out := 0)
            (substZeroAfterMap_add p k 1 ρ)
          rwa [← hEqSub] at hsSub
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec
            M.toFirstOrderAdjunctionModel
            (scons x (insertAt (k+p) termVal e)) (out+1) 0).mp hsucc
          apply (FirstOrderAdjunctionModel.HF_succAt_spec
            M.toFirstOrderAdjunctionModel (scons x e) (out+1) 0).mpr
          change e out = M.adjoin x x
          change insertAt (k+p) termVal e out = M.adjoin x x at hsVal
          rwa [insertAt_lt (by omega : out < k + p)] at hsVal
  | add a b iha ihb =>
      intro p k ρ out termVal e hout hfree hterm
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p (k+2) ρ) 1
                (PA.Term.subst (PA.Formula.substTermAt p replacement) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
              (ρ := fun n => substZeroAfterMap p k ρ n + 2)
              (σ := substZeroAfterMap p (k+2) ρ) (out := 1)
              (substZeroAfterMap_add p k 2 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal x e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + (k+2) + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + (k+2) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+2) + p = ρ n + k + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haIns := (iha p (k+2) ρ 1 termVal
            (scons y (scons x e)) (by omega) hfree2 hterm2).mp haMap
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) termVal e)) n =
                insertAt ((k+2)+p) termVal (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k termVal x y e
          have haEnv : Sat M.mem
              (scons y (scons x (insertAt (k+p) termVal e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (insertAt (k+p) termVal e)))
              (insertAt ((k+2)+p) termVal (scons y (scons x e))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p (k+2) ρ) 0
                (PA.Term.subst (PA.Formula.substTermAt p replacement) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
              (ρ := fun n => substZeroAfterMap p k ρ n + 2)
              (σ := substZeroAfterMap p (k+2) ρ) (out := 0)
              (substZeroAfterMap_add p k 2 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal x e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + (k+2) + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + (k+2) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+2) + p = ρ n + k + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbIns := (ihb p (k+2) ρ 0 termVal
            (scons y (scons x e)) (by omega) hfree2 hterm2).mp hbMap
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) termVal e)) n =
                insertAt ((k+2)+p) termVal (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k termVal x y e
          have hbEnv : Sat M.mem
              (scons y (scons x (insertAt (k+p) termVal e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (insertAt (k+p) termVal e)))
              (insertAt ((k+2)+p) termVal (scons y (scons x e))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at hbEnv
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt (k+p) termVal e))) ?_).mp hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt (by omega : out < k + p)]
          · rfl
          · rfl
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have haMap : Sat M.mem
              (scons y (scons x (insertAt (k+p) termVal e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) termVal e)) n =
                insertAt ((k+2)+p) termVal (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k termVal x y e
          have haIns : Sat M.mem
              (insertAt ((k+2)+p) termVal (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (insertAt (k+p) termVal e)))
              (insertAt ((k+2)+p) termVal (scons y (scons x e))) henv).mp haMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal x e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + (k+2) + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + (k+2) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+2) + p = ρ n + k + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haSub := (iha p (k+2) ρ 1 termVal
            (scons y (scons x e)) (by omega) hfree2 hterm2).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
            (ρ := fun n => substZeroAfterMap p k ρ n + 2)
            (σ := substZeroAfterMap p (k+2) ρ) (out := 1)
            (substZeroAfterMap_add p k 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have hbMap : Sat M.mem
              (scons y (scons x (insertAt (k+p) termVal e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) termVal e)) n =
                insertAt ((k+2)+p) termVal (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k termVal x y e
          have hbIns : Sat M.mem
              (insertAt ((k+2)+p) termVal (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (insertAt (k+p) termVal e)))
              (insertAt ((k+2)+p) termVal (scons y (scons x e))) henv).mp hbMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal x e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + (k+2) + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + (k+2) + p) =
                e (ρ n + k + p) := by
              rw [show ρ n + (k+2) + p = ρ n + k + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbSub := (ihb p (k+2) ρ 0 termVal
            (scons y (scons x e)) (by omega) hfree2 hterm2).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
            (ρ := fun n => substZeroAfterMap p k ρ n + 2)
            (σ := substZeroAfterMap p (k+2) ρ) (out := 0)
            (substZeroAfterMap_add p k 2 ρ)
          rwa [← hEqSub] at hbSub
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt (k+p) termVal e))) ?_).mpr hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt (by omega : out < k + p)]
          · rfl
          · rfl
  | mul a b iha ihb =>
      intro p k ρ out termVal e hout hfree hterm
      constructor
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroAfterMap p (k+3) ρ) 1
                (PA.Term.subst (PA.Formula.substTermAt p replacement) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
              (ρ := fun n => substZeroAfterMap p k ρ n + 3)
              (σ := substZeroAfterMap p (k+3) ρ) (out := 1)
              (substZeroAfterMap_add p k 3 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal y e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal x (scons y e) hterm1
          have hterm3 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+2) ρ termVal z (scons x (scons y e)) hterm2
          have hfree3 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons z (scons x (scons y e))) (ρ n + (k+3) + p)) := by
            intro n hn
            have hslot : (scons z (scons x (scons y e)))
                (ρ n + (k+3) + p) = e (ρ n + k + p) := by
              rw [show ρ n + (k+3) + p = ρ n + k + p + 3 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haIns := (iha p (k+3) ρ 1 termVal
            (scons z (scons x (scons y e))) (by omega)
            hfree3 hterm3).mp haMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) termVal e))) n =
                insertAt ((k+3)+p) termVal
                  (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k termVal y x z e
          have haEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e)))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroAfterMap p (k+3) ρ) 2
                (PA.Term.subst (PA.Formula.substTermAt p replacement) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
              (ρ := fun n => substZeroAfterMap p k ρ n + 3)
              (σ := substZeroAfterMap p (k+3) ρ) (out := 2)
              (substZeroAfterMap_add p k 3 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal y e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal x (scons y e) hterm1
          have hterm3 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+2) ρ termVal z (scons x (scons y e)) hterm2
          have hfree3 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons z (scons x (scons y e))) (ρ n + (k+3) + p)) := by
            intro n hn
            have hslot : (scons z (scons x (scons y e)))
                (ρ n + (k+3) + p) = e (ρ n + k + p) := by
              rw [show ρ n + (k+3) + p = ρ n + k + p + 3 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbIns := (ihb p (k+3) ρ 2 termVal
            (scons z (scons x (scons y e))) (by omega)
            hfree3 hterm3).mp hbMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) termVal e))) n =
                insertAt ((k+3)+p) termVal
                  (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k termVal y x z e
          have hbEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e)))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at hbEnv
        · change z = insertAt (k+p) termVal e out
          rw [insertAt_lt (by omega : out < k + p)]
          exact hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt (k+p) termVal e)))) ?_).mp hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have haMap : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) termVal e))) n =
                insertAt ((k+3)+p) termVal
                  (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k termVal y x z e
          have haIns : Sat M.mem
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e)))) henv).mp haMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal y e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal x (scons y e) hterm1
          have hterm3 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+2) ρ termVal z (scons x (scons y e)) hterm2
          have hfree3 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons z (scons x (scons y e))) (ρ n + (k+3) + p)) := by
            intro n hn
            have hslot : (scons z (scons x (scons y e)))
                (ρ n + (k+3) + p) = e (ρ n + k + p) := by
              rw [show ρ n + (k+3) + p = ρ n + k + p + 3 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haSub := (iha p (k+3) ρ 1 termVal
            (scons z (scons x (scons y e))) (by omega)
            hfree3 hterm3).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
            (ρ := fun n => substZeroAfterMap p k ρ n + 3)
            (σ := substZeroAfterMap p (k+3) ρ) (out := 1)
            (substZeroAfterMap_add p k 3 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have hbMap : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) termVal e))) n =
                insertAt ((k+3)+p) termVal
                  (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k termVal y x z e
          have hbIns : Sat M.mem
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (insertAt (k+p) termVal e))))
              (insertAt ((k+3)+p) termVal
                (scons z (scons x (scons y e)))) henv).mp hbMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p k ρ termVal y e hterm
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+1) ρ termVal x (scons y e) hterm1
          have hterm3 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p (k+2) ρ termVal z (scons x (scons y e)) hterm2
          have hfree3 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons z (scons x (scons y e))) (ρ n + (k+3) + p)) := by
            intro n hn
            have hslot : (scons z (scons x (scons y e)))
                (ρ n + (k+3) + p) = e (ρ n + k + p) := by
              rw [show ρ n + (k+3) + p = ρ n + k + p + 3 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbSub := (ihb p (k+3) ρ 2 termVal
            (scons z (scons x (scons y e))) (by omega)
            hfree3 hterm3).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
            (ρ := fun n => substZeroAfterMap p k ρ n + 3)
            (σ := substZeroAfterMap p (k+3) ρ) (out := 2)
            (substZeroAfterMap_add p k 3 ρ)
          rwa [← hEqSub] at hbSub
        · change z = e out
          change z = insertAt (k+p) termVal e out at hcopy
          rwa [insertAt_lt (by omega : out < k + p)] at hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt (k+p) termVal e)))) ?_).mpr hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl

theorem scons_replaceAt {α : Type u} (k : Nat) (x d : α) (e : Nat → α) :
    ∀ n, scons d (replaceAt k x e) n = replaceAt (k+1) x (scons d e) n := by
  intro n
  cases n with
  | zero =>
      simp [replaceAt, scons]
  | succ n =>
      simp only [scons]
      by_cases h : n = k
      · subst n
        rw [replaceAt_eq, replaceAt_eq]
      · have hs : n + 1 ≠ k + 1 := by omega
        rw [replaceAt_ne h, replaceAt_ne hs]
        rfl

theorem scons_replaceAt_prefix {α : Type u} (p k : Nat) (x d : α) (e : Nat → α) :
    ∀ n, scons d (replaceAt (k+p) x e) n =
      replaceAt ((k+1)+p) x (scons d e) n := by
  intro n
  calc
    scons d (replaceAt (k+p) x e) n =
        replaceAt ((k+p)+1) x (scons d e) n :=
      scons_replaceAt (k+p) x d e n
    _ = replaceAt ((k+1)+p) x (scons d e) n := by
      rw [show (k+p)+1 = (k+1)+p by omega]

theorem scons2_replaceAt_prefix {α : Type u}
    (p k : Nat) (x d₁ d₂ : α) (e : Nat → α) :
    ∀ n, scons d₂ (scons d₁ (replaceAt (k+p) x e)) n =
      replaceAt ((k+2)+p) x (scons d₂ (scons d₁ e)) n := by
  intro n
  calc
    scons d₂ (scons d₁ (replaceAt (k+p) x e)) n =
        scons d₂ (replaceAt ((k+1)+p) x (scons d₁ e)) n := by
          cases n with
          | zero => rfl
          | succ n => exact scons_replaceAt_prefix p k x d₁ e n
    _ = replaceAt ((((k+1)+p)+1)) x (scons d₂ (scons d₁ e)) n :=
        scons_replaceAt (((k+1)+p)) x d₂ (scons d₁ e) n
    _ = replaceAt ((k+2)+p) x (scons d₂ (scons d₁ e)) n := by
      rw [show (((k+1)+p)+1) = (k+2)+p by omega]

theorem scons3_replaceAt_prefix {α : Type u}
    (p k : Nat) (x d₁ d₂ d₃ : α) (e : Nat → α) :
    ∀ n, scons d₃ (scons d₂ (scons d₁ (replaceAt (k+p) x e))) n =
      replaceAt ((k+3)+p) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
  intro n
  calc
    scons d₃ (scons d₂ (scons d₁ (replaceAt (k+p) x e))) n =
        scons d₃ (replaceAt ((k+2)+p) x (scons d₂ (scons d₁ e))) n := by
          cases n with
          | zero => rfl
          | succ n => exact scons2_replaceAt_prefix p k x d₁ d₂ e n
    _ = replaceAt ((((k+2)+p)+1)) x (scons d₃ (scons d₂ (scons d₁ e))) n :=
        scons_replaceAt (((k+2)+p)) x d₃ (scons d₂ (scons d₁ e)) n
    _ = replaceAt ((k+3)+p) x (scons d₃ (scons d₂ (scons d₁ e))) n := by
      rw [show (((k+2)+p)+1) = (k+3)+p by omega]

theorem scons_succReplaceAt_prefix {α : Type u}
    (M : FirstOrderAdjunctionModel α) (p k : Nat) (d : α) (e : Nat → α) :
    ∀ n, scons d (succReplaceAt M (k+p) e) n =
      succReplaceAt M ((k+1)+p) (scons d e) n := by
  intro n
  unfold succReplaceAt
  have hval :
      M.adjoin (scons d e ((k+1)+p)) (scons d e ((k+1)+p)) =
        M.adjoin (e (k+p)) (e (k+p)) := by
    have hslot : scons d e ((k+1)+p) = e (k+p) := by
      rw [show (k+1)+p = (k+p)+1 by omega]
      rfl
    rw [hslot]
  rw [hval]
  exact scons_replaceAt_prefix p k (M.adjoin (e (k+p)) (e (k+p))) d e n

theorem scons2_succReplaceAt_prefix {α : Type u}
    (M : FirstOrderAdjunctionModel α) (p k : Nat) (d₁ d₂ : α) (e : Nat → α) :
    ∀ n, scons d₂ (scons d₁ (succReplaceAt M (k+p) e)) n =
      succReplaceAt M ((k+2)+p) (scons d₂ (scons d₁ e)) n := by
  intro n
  unfold succReplaceAt
  have hval :
      M.adjoin (scons d₂ (scons d₁ e) ((k+2)+p))
          (scons d₂ (scons d₁ e) ((k+2)+p)) =
        M.adjoin (e (k+p)) (e (k+p)) := by
    have hslot : scons d₂ (scons d₁ e) ((k+2)+p) = e (k+p) := by
      rw [show (k+2)+p = (k+p)+2 by omega]
      rfl
    rw [hslot]
  rw [hval]
  exact scons2_replaceAt_prefix p k (M.adjoin (e (k+p)) (e (k+p))) d₁ d₂ e n

theorem scons3_succReplaceAt_prefix {α : Type u}
    (M : FirstOrderAdjunctionModel α) (p k : Nat) (d₁ d₂ d₃ : α) (e : Nat → α) :
    ∀ n, scons d₃ (scons d₂ (scons d₁ (succReplaceAt M (k+p) e))) n =
      succReplaceAt M ((k+3)+p) (scons d₃ (scons d₂ (scons d₁ e))) n := by
  intro n
  unfold succReplaceAt
  have hval :
      M.adjoin (scons d₃ (scons d₂ (scons d₁ e)) ((k+3)+p))
          (scons d₃ (scons d₂ (scons d₁ e)) ((k+3)+p)) =
        M.adjoin (e (k+p)) (e (k+p)) := by
    have hslot : scons d₃ (scons d₂ (scons d₁ e)) ((k+3)+p) = e (k+p) := by
      rw [show (k+3)+p = (k+p)+3 by omega]
      rfl
    rw [hslot]
  rw [hval]
  exact scons3_replaceAt_prefix p k (M.adjoin (e (k+p)) (e (k+p))) d₁ d₂ d₃ e n

theorem termGraphAt_substZero_insert_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (t : PA.Term) :
    ∀ (k : Nat) (ρ : Nat → Nat) (out : Nat) (e : Nat → α),
      out < k →
        (Sat M.mem e
            (termGraphAt (fun n => ρ n + k) out
              (PA.Term.subst PA.Formula.substZero t)) ↔
          Sat M.mem (insertAt k M.empty e)
            (termGraphAt (fun n => upVarMap ρ n + k) out t)) := by
  induction t with
  | var n =>
      intro k ρ out e hout
      cases n with
      | zero =>
          constructor
          · intro h
            have houtEmpty : e out = M.empty :=
              (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mp h
            apply (termGraphAt_var_spec (mem := M.mem)
              (fun n => upVarMap ρ n + k) out 0 (insertAt k M.empty e)).mpr
            simp [upVarMap, insertAt_lt hout, houtEmpty]
          · intro h
            have hEq := (termGraphAt_var_spec (mem := M.mem)
              (fun n => upVarMap ρ n + k) out 0 (insertAt k M.empty e)).mp h
            apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mpr
            change e out = M.empty
            calc
              e out = insertAt k M.empty e out := (insertAt_lt hout).symm
              _ = insertAt k M.empty e (upVarMap ρ 0 + k) := hEq
              _ = M.empty := by
                simp [upVarMap]
      | succ n =>
          have hslot : insertAt k M.empty e (upVarMap ρ (n+1) + k) =
              e (ρ n + k) := by
            have hgt : k < upVarMap ρ (n+1) + k := by
              simp [upVarMap]
            rw [insertAt_gt hgt]
            have hpred : upVarMap ρ (n+1) + k - 1 = ρ n + k := by
              simp [upVarMap]
            rw [hpred]
          constructor
          · intro h
            change e out = e (ρ n + k) at h
            change insertAt k M.empty e out =
              insertAt k M.empty e (upVarMap ρ (n+1) + k)
            rw [insertAt_lt hout, hslot]
            exact h
          · intro h
            change insertAt k M.empty e out =
              insertAt k M.empty e (upVarMap ρ (n+1) + k) at h
            change e out = e (ρ n + k)
            rwa [insertAt_lt hout, hslot] at h
  | zero =>
      intro k ρ out e hout
      constructor
      · intro h
        have houtEmpty : e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
          (insertAt k M.empty e) out).mpr
        rw [insertAt_lt hout]
        exact houtEmpty
      · intro h
        have houtEmpty : insertAt k M.empty e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M
            (insertAt k M.empty e) out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mpr
        rwa [insertAt_lt hout] at houtEmpty
  | succ t ih =>
      intro k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have htMap : Sat M.mem (scons x e)
              (termGraphAt (fun n => ρ n + (k+1)) 0
                (PA.Term.subst PA.Formula.substZero t)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst PA.Formula.substZero t)
              (ρ := fun n => ρ n + k + 1)
              (σ := fun n => ρ n + (k+1)) (out := 0)
              (fun n => by omega)
            rwa [← hEq]
          have htIns := (ih (k+1) ρ 0 (scons x e) (by omega)).mp htMap
          have henv : ∀ n,
              scons x (insertAt k M.empty e) n =
                insertAt (k+1) M.empty (scons x e) n :=
            scons_insertAt k M.empty x e
          have htEnv : Sat M.mem (scons x (insertAt k M.empty e))
              (termGraphAt (fun n => upVarMap ρ n + (k+1)) 0 t) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+1)) 0 t)
              (scons x (insertAt k M.empty e))
              (insertAt (k+1) M.empty (scons x e)) henv).mpr htIns
          have hEq := termGraphAt_map_ext t
            (ρ := fun n => upVarMap ρ n + (k+1))
            (σ := fun n => upVarMap ρ n + k + 1) (out := 0)
            (fun n => by omega)
          rwa [hEq] at htEnv
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (insertAt k M.empty e)) (out+1) 0).mpr
          change insertAt k M.empty e out = M.adjoin x x
          rwa [insertAt_lt hout]
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext t
            (ρ := fun n => upVarMap ρ n + (k+1))
            (σ := fun n => upVarMap ρ n + k + 1) (out := 0)
            (fun n => by omega)
          have htMap : Sat M.mem (scons x (insertAt k M.empty e))
              (termGraphAt (fun n => upVarMap ρ n + (k+1)) 0 t) := by
            rw [hEq]
            exact ht
          have henv : ∀ n,
              scons x (insertAt k M.empty e) n =
                insertAt (k+1) M.empty (scons x e) n :=
            scons_insertAt k M.empty x e
          have htIns : Sat M.mem (insertAt (k+1) M.empty (scons x e))
              (termGraphAt (fun n => upVarMap ρ n + (k+1)) 0 t) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+1)) 0 t)
              (scons x (insertAt k M.empty e))
              (insertAt (k+1) M.empty (scons x e)) henv).mp htMap
          have htSub := (ih (k+1) ρ 0 (scons x e) (by omega)).mpr htIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst PA.Formula.substZero t)
            (ρ := fun n => ρ n + k + 1)
            (σ := fun n => ρ n + (k+1)) (out := 0)
            (fun n => by omega)
          rwa [← hEqSub] at htSub
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (insertAt k M.empty e)) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mpr
          change e out = M.adjoin x x
          change insertAt k M.empty e out = M.adjoin x x at hsVal
          rwa [insertAt_lt hout] at hsVal
  | add a b iha ihb =>
      intro k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (fun n => ρ n + (k+2)) 1
                (PA.Term.subst PA.Formula.substZero a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst PA.Formula.substZero a)
              (ρ := fun n => ρ n + k + 2)
              (σ := fun n => ρ n + (k+2)) (out := 1)
              (fun n => by omega)
            rwa [← hEq]
          have haIns := (iha (k+2) ρ 1 (scons y (scons x e)) (by omega)).mp haMap
          have henv : ∀ n,
              scons y (scons x (insertAt k M.empty e)) n =
                insertAt (k+2) M.empty (scons y (scons x e)) n :=
            scons2_insertAt k M.empty x y e
          have haEnv : Sat M.mem (scons y (scons x (insertAt k M.empty e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 1 a) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+2)) 1 a)
              (scons y (scons x (insertAt k M.empty e)))
              (insertAt (k+2) M.empty (scons y (scons x e))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := fun n => upVarMap ρ n + (k+2))
            (σ := fun n => upVarMap ρ n + k + 2) (out := 1)
            (fun n => by omega)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (fun n => ρ n + (k+2)) 0
                (PA.Term.subst PA.Formula.substZero b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst PA.Formula.substZero b)
              (ρ := fun n => ρ n + k + 2)
              (σ := fun n => ρ n + (k+2)) (out := 0)
              (fun n => by omega)
            rwa [← hEq]
          have hbIns := (ihb (k+2) ρ 0 (scons y (scons x e)) (by omega)).mp hbMap
          have henv : ∀ n,
              scons y (scons x (insertAt k M.empty e)) n =
                insertAt (k+2) M.empty (scons y (scons x e)) n :=
            scons2_insertAt k M.empty x y e
          have hbEnv : Sat M.mem (scons y (scons x (insertAt k M.empty e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 0 b) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+2)) 0 b)
              (scons y (scons x (insertAt k M.empty e)))
              (insertAt (k+2) M.empty (scons y (scons x e))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := fun n => upVarMap ρ n + (k+2))
            (σ := fun n => upVarMap ρ n + k + 2) (out := 0)
            (fun n => by omega)
          rwa [hEq] at hbEnv
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt k M.empty e))) ?_).mp hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt hout]
          · rfl
          · rfl
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := fun n => upVarMap ρ n + (k+2))
            (σ := fun n => upVarMap ρ n + k + 2) (out := 1)
            (fun n => by omega)
          have haMap : Sat M.mem (scons y (scons x (insertAt k M.empty e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (insertAt k M.empty e)) n =
                insertAt (k+2) M.empty (scons y (scons x e)) n :=
            scons2_insertAt k M.empty x y e
          have haIns : Sat M.mem
              (insertAt (k+2) M.empty (scons y (scons x e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 1 a) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+2)) 1 a)
              (scons y (scons x (insertAt k M.empty e)))
              (insertAt (k+2) M.empty (scons y (scons x e))) henv).mp haMap
          have haSub := (iha (k+2) ρ 1 (scons y (scons x e)) (by omega)).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst PA.Formula.substZero a)
            (ρ := fun n => ρ n + k + 2)
            (σ := fun n => ρ n + (k+2)) (out := 1)
            (fun n => by omega)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := fun n => upVarMap ρ n + (k+2))
            (σ := fun n => upVarMap ρ n + k + 2) (out := 0)
            (fun n => by omega)
          have hbMap : Sat M.mem (scons y (scons x (insertAt k M.empty e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (insertAt k M.empty e)) n =
                insertAt (k+2) M.empty (scons y (scons x e)) n :=
            scons2_insertAt k M.empty x y e
          have hbIns : Sat M.mem
              (insertAt (k+2) M.empty (scons y (scons x e)))
              (termGraphAt (fun n => upVarMap ρ n + (k+2)) 0 b) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+2)) 0 b)
              (scons y (scons x (insertAt k M.empty e)))
              (insertAt (k+2) M.empty (scons y (scons x e))) henv).mp hbMap
          have hbSub := (ihb (k+2) ρ 0 (scons y (scons x e)) (by omega)).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst PA.Formula.substZero b)
            (ρ := fun n => ρ n + k + 2)
            (σ := fun n => ρ n + (k+2)) (out := 0)
            (fun n => by omega)
          rwa [← hEqSub] at hbSub
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt k M.empty e))) ?_).mpr hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt hout]
          · rfl
          · rfl
  | mul a b iha ihb =>
      intro k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (fun n => ρ n + (k+3)) 1
                (PA.Term.subst PA.Formula.substZero a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst PA.Formula.substZero a)
              (ρ := fun n => ρ n + k + 3)
              (σ := fun n => ρ n + (k+3)) (out := 1)
              (fun n => by omega)
            rwa [← hEq]
          have haIns := (iha (k+3) ρ 1
            (scons z (scons x (scons y e))) (by omega)).mp haMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt k M.empty e))) n =
                insertAt (k+3) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt k M.empty y x z e
          have haEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 1 a) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+3)) 1 a)
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (insertAt (k+3) M.empty (scons z (scons x (scons y e)))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := fun n => upVarMap ρ n + (k+3))
            (σ := fun n => upVarMap ρ n + k + 3) (out := 1)
            (fun n => by omega)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (fun n => ρ n + (k+3)) 2
                (PA.Term.subst PA.Formula.substZero b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst PA.Formula.substZero b)
              (ρ := fun n => ρ n + k + 3)
              (σ := fun n => ρ n + (k+3)) (out := 2)
              (fun n => by omega)
            rwa [← hEq]
          have hbIns := (ihb (k+3) ρ 2
            (scons z (scons x (scons y e))) (by omega)).mp hbMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt k M.empty e))) n =
                insertAt (k+3) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt k M.empty y x z e
          have hbEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 2 b) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+3)) 2 b)
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (insertAt (k+3) M.empty (scons z (scons x (scons y e)))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := fun n => upVarMap ρ n + (k+3))
            (σ := fun n => upVarMap ρ n + k + 3) (out := 2)
            (fun n => by omega)
          rwa [hEq] at hbEnv
        · change z = insertAt k M.empty e out
          rw [insertAt_lt hout]
          exact hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt k M.empty e)))) ?_).mp hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := fun n => upVarMap ρ n + (k+3))
            (σ := fun n => upVarMap ρ n + k + 3) (out := 1)
            (fun n => by omega)
          have haMap : Sat M.mem
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt k M.empty e))) n =
                insertAt (k+3) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt k M.empty y x z e
          have haIns : Sat M.mem
              (insertAt (k+3) M.empty (scons z (scons x (scons y e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 1 a) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+3)) 1 a)
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (insertAt (k+3) M.empty (scons z (scons x (scons y e)))) henv).mp haMap
          have haSub := (iha (k+3) ρ 1
            (scons z (scons x (scons y e))) (by omega)).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst PA.Formula.substZero a)
            (ρ := fun n => ρ n + k + 3)
            (σ := fun n => ρ n + (k+3)) (out := 1)
            (fun n => by omega)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := fun n => upVarMap ρ n + (k+3))
            (σ := fun n => upVarMap ρ n + k + 3) (out := 2)
            (fun n => by omega)
          have hbMap : Sat M.mem
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 2 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt k M.empty e))) n =
                insertAt (k+3) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt k M.empty y x z e
          have hbIns : Sat M.mem
              (insertAt (k+3) M.empty (scons z (scons x (scons y e))))
              (termGraphAt (fun n => upVarMap ρ n + (k+3)) 2 b) :=
            (Sat_ext (termGraphAt (fun n => upVarMap ρ n + (k+3)) 2 b)
              (scons z (scons x (scons y (insertAt k M.empty e))))
              (insertAt (k+3) M.empty (scons z (scons x (scons y e)))) henv).mp hbMap
          have hbSub := (ihb (k+3) ρ 2
            (scons z (scons x (scons y e))) (by omega)).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst PA.Formula.substZero b)
            (ρ := fun n => ρ n + k + 3)
            (σ := fun n => ρ n + (k+3)) (out := 2)
            (fun n => by omega)
          rwa [← hEqSub] at hbSub
        · change z = e out
          change z = insertAt k M.empty e out at hcopy
          rwa [insertAt_lt hout] at hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt k M.empty e)))) ?_).mpr hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl

theorem termGraphAt_substZeroAt_insert_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (t : PA.Term) :
    ∀ (p k : Nat) (ρ : Nat → Nat) (out : Nat) (e : Nat → α),
      out < k →
        (Sat M.mem e
            (termGraphAt (substZeroAfterMap p k ρ) out
              (PA.Term.subst (PA.Formula.substZeroAt p) t)) ↔
          Sat M.mem (insertAt (k+p) M.empty e)
            (termGraphAt (substZeroBeforeMap p k ρ) out t)) := by
  induction t with
  | var n =>
      intro p k ρ out e hout
      by_cases hlt : n < p
      · simp only [PA.Term.subst]
        rw [PA.Formula.substZeroAt_lt hlt]
        have houtSlot : out < k + p := by omega
        have hnSlot : substZeroBeforeMap p k ρ n < k + p := by
          rw [substZeroBeforeMap_lt hlt]
          omega
        constructor
        · intro h
          change e out = e (substZeroAfterMap p k ρ n) at h
          change insertAt (k+p) M.empty e out =
            insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ n)
          rw [insertAt_lt houtSlot, insertAt_lt hnSlot]
          simpa [substZeroAfterMap_lt hlt, substZeroBeforeMap_lt hlt] using h
        · intro h
          change insertAt (k+p) M.empty e out =
            insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ n) at h
          change e out = e (substZeroAfterMap p k ρ n)
          rw [insertAt_lt houtSlot, insertAt_lt hnSlot] at h
          simpa [substZeroAfterMap_lt hlt, substZeroBeforeMap_lt hlt] using h
      · by_cases heq : n = p
        · subst n
          simp only [PA.Term.subst]
          rw [PA.Formula.substZeroAt_eq]
          have houtSlot : out < k + p := by omega
          constructor
          · intro h
            have houtEmpty : e out = M.empty :=
              (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mp h
            apply (termGraphAt_var_spec (mem := M.mem)
              (substZeroBeforeMap p k ρ) out p
              (insertAt (k+p) M.empty e)).mpr
            change insertAt (k+p) M.empty e out =
              insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ p)
            rw [insertAt_lt houtSlot, substZeroBeforeMap_eq, insertAt_eq]
            exact houtEmpty
          · intro h
            have hEq := (termGraphAt_var_spec (mem := M.mem)
              (substZeroBeforeMap p k ρ) out p
              (insertAt (k+p) M.empty e)).mp h
            apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mpr
            change e out = M.empty
            calc
              e out = insertAt (k+p) M.empty e out := (insertAt_lt houtSlot).symm
              _ = insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ p) := hEq
              _ = M.empty := by
                rw [substZeroBeforeMap_eq, insertAt_eq]
        · have hgt : p < n := by omega
          simp only [PA.Term.subst]
          rw [PA.Formula.substZeroAt_gt hgt]
          have houtSlot : out < k + p := by omega
          have hAfter :
              substZeroAfterMap p k ρ (n - 1) =
                ρ (n - p - 1) + k + p := by
            have hp_le : p ≤ n - 1 := by omega
            rw [substZeroAfterMap_ge (ρ := ρ) (k := k) hp_le]
            rw [show n - 1 - p = n - p - 1 by
              rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 p]]
          have hBefore :
              substZeroBeforeMap p k ρ n =
                ρ (n - p - 1) + k + p + 1 :=
            substZeroBeforeMap_gt (ρ := ρ) (k := k) hgt
          have hBeforeGt : k + p < substZeroBeforeMap p k ρ n := by
            rw [hBefore]
            omega
          have hslot :
              insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ n) =
                e (substZeroAfterMap p k ρ (n - 1)) := by
            rw [insertAt_gt hBeforeGt, hBefore, hAfter]
            congr
          constructor
          · intro h
            change e out = e (substZeroAfterMap p k ρ (n - 1)) at h
            change insertAt (k+p) M.empty e out =
              insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ n)
            rw [insertAt_lt houtSlot, hslot]
            exact h
          · intro h
            change insertAt (k+p) M.empty e out =
              insertAt (k+p) M.empty e (substZeroBeforeMap p k ρ n) at h
            change e out = e (substZeroAfterMap p k ρ (n - 1))
            rwa [insertAt_lt houtSlot, hslot] at h
  | zero =>
      intro p k ρ out e hout
      simp only [PA.Term.subst]
      have houtSlot : out < k + p := by omega
      constructor
      · intro h
        have houtEmpty : e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
          (insertAt (k+p) M.empty e) out).mpr
        rw [insertAt_lt houtSlot]
        exact houtEmpty
      · intro h
        have houtEmpty : insertAt (k+p) M.empty e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M
            (insertAt (k+p) M.empty e) out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mpr
        rwa [insertAt_lt houtSlot] at houtEmpty
  | succ t ih =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have htMap : Sat M.mem (scons x e)
              (termGraphAt (substZeroAfterMap p (k+1) ρ) 0
                (PA.Term.subst (PA.Formula.substZeroAt p) t)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) t)
              (ρ := fun n => substZeroAfterMap p k ρ n + 1)
              (σ := substZeroAfterMap p (k+1) ρ) (out := 0)
              (substZeroAfterMap_add p k 1 ρ)
            rwa [← hEq]
          have htIns := (ih p (k+1) ρ 0 (scons x e) (by omega)).mp htMap
          have henv : ∀ n,
              scons x (insertAt (k+p) M.empty e) n =
                insertAt ((k+1)+p) M.empty (scons x e) n :=
            scons_insertAt_prefix p k M.empty x e
          have htEnv : Sat M.mem (scons x (insertAt (k+p) M.empty e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t)
              (scons x (insertAt (k+p) M.empty e))
              (insertAt ((k+1)+p) M.empty (scons x e)) henv).mpr htIns
          have hEq := termGraphAt_map_ext t
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          rwa [hEq] at htEnv
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (insertAt (k+p) M.empty e)) (out+1) 0).mpr
          change insertAt (k+p) M.empty e out = M.adjoin x x
          rwa [insertAt_lt (by omega)]
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext t
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          have htMap : Sat M.mem (scons x (insertAt (k+p) M.empty e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) := by
            rw [hEq]
            exact ht
          have henv : ∀ n,
              scons x (insertAt (k+p) M.empty e) n =
                insertAt ((k+1)+p) M.empty (scons x e) n :=
            scons_insertAt_prefix p k M.empty x e
          have htIns : Sat M.mem (insertAt ((k+1)+p) M.empty (scons x e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t)
              (scons x (insertAt (k+p) M.empty e))
              (insertAt ((k+1)+p) M.empty (scons x e)) henv).mp htMap
          have htSub := (ih p (k+1) ρ 0 (scons x e) (by omega)).mpr htIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) t)
            (ρ := fun n => substZeroAfterMap p k ρ n + 1)
            (σ := substZeroAfterMap p (k+1) ρ) (out := 0)
            (substZeroAfterMap_add p k 1 ρ)
          rwa [← hEqSub] at htSub
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (insertAt (k+p) M.empty e)) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mpr
          change e out = M.adjoin x x
          change insertAt (k+p) M.empty e out = M.adjoin x x at hsVal
          rwa [insertAt_lt (by omega)] at hsVal
  | add a b iha ihb =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p (k+2) ρ) 1
                (PA.Term.subst (PA.Formula.substZeroAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) a)
              (ρ := fun n => substZeroAfterMap p k ρ n + 2)
              (σ := substZeroAfterMap p (k+2) ρ) (out := 1)
              (substZeroAfterMap_add p k 2 ρ)
            rwa [← hEq]
          have haIns := (iha p (k+2) ρ 1 (scons y (scons x e)) (by omega)).mp haMap
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) M.empty e)) n =
                insertAt ((k+2)+p) M.empty (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k M.empty x y e
          have haEnv : Sat M.mem (scons y (scons x (insertAt (k+p) M.empty e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (insertAt (k+p) M.empty e)))
              (insertAt ((k+2)+p) M.empty (scons y (scons x e))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p (k+2) ρ) 0
                (PA.Term.subst (PA.Formula.substZeroAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) b)
              (ρ := fun n => substZeroAfterMap p k ρ n + 2)
              (σ := substZeroAfterMap p (k+2) ρ) (out := 0)
              (substZeroAfterMap_add p k 2 ρ)
            rwa [← hEq]
          have hbIns := (ihb p (k+2) ρ 0 (scons y (scons x e)) (by omega)).mp hbMap
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) M.empty e)) n =
                insertAt ((k+2)+p) M.empty (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k M.empty x y e
          have hbEnv : Sat M.mem (scons y (scons x (insertAt (k+p) M.empty e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (insertAt (k+p) M.empty e)))
              (insertAt ((k+2)+p) M.empty (scons y (scons x e))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at hbEnv
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt (k+p) M.empty e))) ?_).mp hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt (by omega : out < k + p)]
          · rfl
          · rfl
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have haMap : Sat M.mem (scons y (scons x (insertAt (k+p) M.empty e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) M.empty e)) n =
                insertAt ((k+2)+p) M.empty (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k M.empty x y e
          have haIns : Sat M.mem
              (insertAt ((k+2)+p) M.empty (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (insertAt (k+p) M.empty e)))
              (insertAt ((k+2)+p) M.empty (scons y (scons x e))) henv).mp haMap
          have haSub := (iha p (k+2) ρ 1 (scons y (scons x e)) (by omega)).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (ρ := fun n => substZeroAfterMap p k ρ n + 2)
            (σ := substZeroAfterMap p (k+2) ρ) (out := 1)
            (substZeroAfterMap_add p k 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have hbMap : Sat M.mem (scons y (scons x (insertAt (k+p) M.empty e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (insertAt (k+p) M.empty e)) n =
                insertAt ((k+2)+p) M.empty (scons y (scons x e)) n :=
            scons2_insertAt_prefix p k M.empty x y e
          have hbIns : Sat M.mem
              (insertAt ((k+2)+p) M.empty (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (insertAt (k+p) M.empty e)))
              (insertAt ((k+2)+p) M.empty (scons y (scons x e))) henv).mp hbMap
          have hbSub := (ihb p (k+2) ρ 0 (scons y (scons x e)) (by omega)).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) b)
            (ρ := fun n => substZeroAfterMap p k ρ n + 2)
            (σ := substZeroAfterMap p (k+2) ρ) (out := 0)
            (substZeroAfterMap_add p k 2 ρ)
          rwa [← hEqSub] at hbSub
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (insertAt (k+p) M.empty e))) ?_).mpr hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, insertAt_lt (by omega : out < k + p)]
          · rfl
          · rfl
  | mul a b iha ihb =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroAfterMap p (k+3) ρ) 1
                (PA.Term.subst (PA.Formula.substZeroAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) a)
              (ρ := fun n => substZeroAfterMap p k ρ n + 3)
              (σ := substZeroAfterMap p (k+3) ρ) (out := 1)
              (substZeroAfterMap_add p k 3 ρ)
            rwa [← hEq]
          have haIns := (iha p (k+3) ρ 1 (scons z (scons x (scons y e))) (by omega)).mp haMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) M.empty e))) n =
                insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k M.empty y x z e
          have haEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e)))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroAfterMap p (k+3) ρ) 2
                (PA.Term.subst (PA.Formula.substZeroAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) b)
              (ρ := fun n => substZeroAfterMap p k ρ n + 3)
              (σ := substZeroAfterMap p (k+3) ρ) (out := 2)
              (substZeroAfterMap_add p k 3 ρ)
            rwa [← hEq]
          have hbIns := (ihb p (k+3) ρ 2 (scons z (scons x (scons y e))) (by omega)).mp hbMap
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) M.empty e))) n =
                insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k M.empty y x z e
          have hbEnv : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e)))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at hbEnv
        · change z = insertAt (k+p) M.empty e out
          change z = e out at hcopy
          rwa [insertAt_lt (by omega : out < k + p)]
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt (k+p) M.empty e)))) ?_).mp hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have haMap : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) M.empty e))) n =
                insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k M.empty y x z e
          have haIns : Sat M.mem
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e)))) henv).mp haMap
          have haSub := (iha p (k+3) ρ 1 (scons z (scons x (scons y e))) (by omega)).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (ρ := fun n => substZeroAfterMap p k ρ n + 3)
            (σ := substZeroAfterMap p (k+3) ρ) (out := 1)
            (substZeroAfterMap_add p k 3 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have hbMap : Sat M.mem
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons z (scons x (scons y (insertAt (k+p) M.empty e))) n =
                insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))) n :=
            scons3_insertAt_prefix p k M.empty y x z e
          have hbIns : Sat M.mem
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (insertAt (k+p) M.empty e))))
              (insertAt ((k+3)+p) M.empty (scons z (scons x (scons y e)))) henv).mp hbMap
          have hbSub := (ihb p (k+3) ρ 2 (scons z (scons x (scons y e))) (by omega)).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) b)
            (ρ := fun n => substZeroAfterMap p k ρ n + 3)
            (σ := substZeroAfterMap p (k+3) ρ) (out := 2)
            (substZeroAfterMap_add p k 3 ρ)
          rwa [← hEqSub] at hbSub
        · change z = e out
          change z = insertAt (k+p) M.empty e out at hcopy
          rwa [insertAt_lt (by omega : out < k + p)] at hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (insertAt (k+p) M.empty e)))) ?_).mpr hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl

theorem termGraphAt_substSuccAt_replace_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (t : PA.Term) :
    ∀ (p k : Nat) (ρ : Nat → Nat) (out : Nat) (e : Nat → α),
      out < k →
        (Sat M.mem e
            (termGraphAt (substZeroBeforeMap p k ρ) out
              (PA.Term.subst (PA.Formula.substSuccAt p) t)) ↔
          Sat M.mem (succReplaceAt M (k+p) e)
            (termGraphAt (substZeroBeforeMap p k ρ) out t)) := by
  induction t with
  | var n =>
      intro p k ρ out e hout
      by_cases heq : n = p
      · subst n
        simp only [PA.Term.subst]
        rw [PA.Formula.substSuccAt_eq]
        have houtSlot : out ≠ k + p := by omega
        constructor
        · intro h
          rcases h with ⟨x, hx, hs⟩
          have hxVal : x = e (k+p) := by
            change x = scons x e (substZeroBeforeMap p k ρ p + 1) at hx
            rw [substZeroBeforeMap_eq] at hx
            simpa [scons] using hx
          have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mp hs
          change e out = M.adjoin x x at hsVal
          apply (termGraphAt_var_spec (mem := M.mem)
            (substZeroBeforeMap p k ρ) out p
            (succReplaceAt M (k+p) e)).mpr
          change succReplaceAt M (k+p) e out =
            succReplaceAt M (k+p) e (substZeroBeforeMap p k ρ p)
          rw [succReplaceAt_ne M e houtSlot, substZeroBeforeMap_eq,
            succReplaceAt_eq, hsVal, hxVal]
        · intro h
          have hEq := (termGraphAt_var_spec (mem := M.mem)
            (substZeroBeforeMap p k ρ) out p
            (succReplaceAt M (k+p) e)).mp h
          have hOut : e out = M.adjoin (e (k+p)) (e (k+p)) := by
            change succReplaceAt M (k+p) e out =
              succReplaceAt M (k+p) e (substZeroBeforeMap p k ρ p) at hEq
            rwa [succReplaceAt_ne M e houtSlot, substZeroBeforeMap_eq,
              succReplaceAt_eq] at hEq
          refine ⟨e (k+p), ?_, ?_⟩
          · change e (k+p) = scons (e (k+p)) e
              (substZeroBeforeMap p k ρ p + 1)
            rw [substZeroBeforeMap_eq]
            rfl
          · apply (FirstOrderAdjunctionModel.HF_succAt_spec M
              (scons (e (k+p)) e) (out+1) 0).mpr
            change e out = M.adjoin (e (k+p)) (e (k+p))
            exact hOut
      · simp only [PA.Term.subst]
        rw [PA.Formula.substSuccAt_ne heq]
        have houtSlot : out ≠ k + p := by omega
        have hnSlot : substZeroBeforeMap p k ρ n ≠ k + p :=
          substZeroBeforeMap_ne_replaced_slot (ρ := ρ) (k := k) heq
        constructor
        · intro h
          change e out = e (substZeroBeforeMap p k ρ n) at h
          change succReplaceAt M (k+p) e out =
            succReplaceAt M (k+p) e (substZeroBeforeMap p k ρ n)
          rw [succReplaceAt_ne M e houtSlot, succReplaceAt_ne M e hnSlot]
          exact h
        · intro h
          change succReplaceAt M (k+p) e out =
            succReplaceAt M (k+p) e (substZeroBeforeMap p k ρ n) at h
          change e out = e (substZeroBeforeMap p k ρ n)
          rwa [succReplaceAt_ne M e houtSlot, succReplaceAt_ne M e hnSlot] at h
  | zero =>
      intro p k ρ out e hout
      simp only [PA.Term.subst]
      have houtSlot : out ≠ k + p := by omega
      constructor
      · intro h
        have houtEmpty : e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
          (succReplaceAt M (k+p) e) out).mpr
        rwa [succReplaceAt_ne M e houtSlot]
      · intro h
        have houtEmpty : succReplaceAt M (k+p) e out = M.empty :=
          (FirstOrderAdjunctionModel.HF_emptyAt_empty M
            (succReplaceAt M (k+p) e) out).mp h
        apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M e out).mpr
        rwa [succReplaceAt_ne M e houtSlot] at houtEmpty
  | succ t ih =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have htMap : Sat M.mem (scons x e)
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0
                (PA.Term.subst (PA.Formula.substSuccAt p) t)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) t)
              (ρ := fun n => substZeroBeforeMap p k ρ n + 1)
              (σ := substZeroBeforeMap p (k+1) ρ) (out := 0)
              (substZeroBeforeMap_add p k 1 ρ)
            rwa [← hEq]
          have htRep := (ih p (k+1) ρ 0 (scons x e) (by omega)).mp htMap
          have henv : ∀ n,
              scons x (succReplaceAt M (k+p) e) n =
                succReplaceAt M ((k+1)+p) (scons x e) n :=
            scons_succReplaceAt_prefix M p k x e
          have htEnv : Sat M.mem (scons x (succReplaceAt M (k+p) e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t)
              (scons x (succReplaceAt M (k+p) e))
              (succReplaceAt M ((k+1)+p) (scons x e)) henv).mpr htRep
          have hEq := termGraphAt_map_ext t
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          rwa [hEq] at htEnv
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (succReplaceAt M (k+p) e)) (out+1) 0).mpr
          change succReplaceAt M (k+p) e out = M.adjoin x x
          rwa [succReplaceAt_ne M e (by omega : out ≠ k + p)]
      · intro h
        rcases h with ⟨x, ht, hs⟩
        refine ⟨x, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext t
            (ρ := substZeroBeforeMap p (k+1) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 1) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 1 ρ n).symm)
          have htMap : Sat M.mem (scons x (succReplaceAt M (k+p) e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) := by
            rw [hEq]
            exact ht
          have henv : ∀ n,
              scons x (succReplaceAt M (k+p) e) n =
                succReplaceAt M ((k+1)+p) (scons x e) n :=
            scons_succReplaceAt_prefix M p k x e
          have htRep : Sat M.mem (succReplaceAt M ((k+1)+p) (scons x e))
              (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+1) ρ) 0 t)
              (scons x (succReplaceAt M (k+p) e))
              (succReplaceAt M ((k+1)+p) (scons x e)) henv).mp htMap
          have htSub := (ih p (k+1) ρ 0 (scons x e) (by omega)).mpr htRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) t)
            (ρ := fun n => substZeroBeforeMap p k ρ n + 1)
            (σ := substZeroBeforeMap p (k+1) ρ) (out := 0)
            (substZeroBeforeMap_add p k 1 ρ)
          rwa [← hEqSub] at htSub
        · have hsVal := (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x (succReplaceAt M (k+p) e)) (out+1) 0).mp hs
          apply (FirstOrderAdjunctionModel.HF_succAt_spec M
            (scons x e) (out+1) 0).mpr
          change e out = M.adjoin x x
          change succReplaceAt M (k+p) e out = M.adjoin x x at hsVal
          rwa [succReplaceAt_ne M e (by omega : out ≠ k + p)] at hsVal
  | add a b iha ihb =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1
                (PA.Term.subst (PA.Formula.substSuccAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) a)
              (ρ := fun n => substZeroBeforeMap p k ρ n + 2)
              (σ := substZeroBeforeMap p (k+2) ρ) (out := 1)
              (substZeroBeforeMap_add p k 2 ρ)
            rwa [← hEq]
          have haRep := (iha p (k+2) ρ 1 (scons y (scons x e)) (by omega)).mp haMap
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M (k+p) e)) n =
                succReplaceAt M ((k+2)+p) (scons y (scons x e)) n :=
            scons2_succReplaceAt_prefix M p k x y e
          have haEnv : Sat M.mem (scons y (scons x (succReplaceAt M (k+p) e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (succReplaceAt M (k+p) e)))
              (succReplaceAt M ((k+2)+p) (scons y (scons x e))) henv).mpr haRep
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0
                (PA.Term.subst (PA.Formula.substSuccAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) b)
              (ρ := fun n => substZeroBeforeMap p k ρ n + 2)
              (σ := substZeroBeforeMap p (k+2) ρ) (out := 0)
              (substZeroBeforeMap_add p k 2 ρ)
            rwa [← hEq]
          have hbRep := (ihb p (k+2) ρ 0 (scons y (scons x e)) (by omega)).mp hbMap
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M (k+p) e)) n =
                succReplaceAt M ((k+2)+p) (scons y (scons x e)) n :=
            scons2_succReplaceAt_prefix M p k x y e
          have hbEnv : Sat M.mem (scons y (scons x (succReplaceAt M (k+p) e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (succReplaceAt M (k+p) e)))
              (succReplaceAt M ((k+2)+p) (scons y (scons x e))) henv).mpr hbRep
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          rwa [hEq] at hbEnv
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (succReplaceAt M (k+p) e))) ?_).mp hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, succReplaceAt_ne M e (by omega : out ≠ k+p)]
          · rfl
          · rfl
      · intro h
        rcases h with ⟨x, y, ha, hb, hg⟩
        refine ⟨x, y, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have haMap : Sat M.mem (scons y (scons x (succReplaceAt M (k+p) e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M (k+p) e)) n =
                succReplaceAt M ((k+2)+p) (scons y (scons x e)) n :=
            scons2_succReplaceAt_prefix M p k x y e
          have haRep : Sat M.mem
              (succReplaceAt M ((k+2)+p) (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 1 a)
              (scons y (scons x (succReplaceAt M (k+p) e)))
              (succReplaceAt M ((k+2)+p) (scons y (scons x e))) henv).mp haMap
          have haSub := (iha p (k+2) ρ 1 (scons y (scons x e)) (by omega)).mpr haRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) a)
            (ρ := fun n => substZeroBeforeMap p k ρ n + 2)
            (σ := substZeroBeforeMap p (k+2) ρ) (out := 1)
            (substZeroBeforeMap_add p k 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+2) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p k 2 ρ n).symm)
          have hbMap : Sat M.mem (scons y (scons x (succReplaceAt M (k+p) e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M (k+p) e)) n =
                succReplaceAt M ((k+2)+p) (scons y (scons x e)) n :=
            scons2_succReplaceAt_prefix M p k x y e
          have hbRep : Sat M.mem
              (succReplaceAt M ((k+2)+p) (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+2) ρ) 0 b)
              (scons y (scons x (succReplaceAt M (k+p) e)))
              (succReplaceAt M ((k+2)+p) (scons y (scons x e))) henv).mp hbMap
          have hbSub := (ihb p (k+2) ρ 0 (scons y (scons x e)) (by omega)).mpr hbRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) b)
            (ρ := fun n => substZeroBeforeMap p k ρ n + 2)
            (σ := substZeroBeforeMap p (k+2) ρ) (out := 0)
            (substZeroBeforeMap_add p k 2 ρ)
          rwa [← hEqSub] at hbSub
        · apply (Sat_ext_free (addGraphAt (out+2) 1 0)
            (scons y (scons x e))
            (scons y (scons x (succReplaceAt M (k+p) e))) ?_).mpr hg
          intro n hn
          rcases addGraphAt_free hn with rfl | rfl | rfl
          · simp [scons, succReplaceAt_ne M e (by omega : out ≠ k+p)]
          · rfl
          · rfl
  | mul a b iha ihb =>
      intro p k ρ out e hout
      constructor
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have haMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1
                (PA.Term.subst (PA.Formula.substSuccAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) a)
              (ρ := fun n => substZeroBeforeMap p k ρ n + 3)
              (σ := substZeroBeforeMap p (k+3) ρ) (out := 1)
              (substZeroBeforeMap_add p k 3 ρ)
            rwa [← hEq]
          have haRep := (iha p (k+3) ρ 1 (scons z (scons x (scons y e))) (by omega)).mp haMap
          have henv : ∀ n,
              scons z (scons x (scons y (succReplaceAt M (k+p) e))) n =
                succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))) n :=
            scons3_succReplaceAt_prefix M p k y x z e
          have haEnv : Sat M.mem
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e)))) henv).mpr haRep
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons z (scons x (scons y e)))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2
                (PA.Term.subst (PA.Formula.substSuccAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) b)
              (ρ := fun n => substZeroBeforeMap p k ρ n + 3)
              (σ := substZeroBeforeMap p (k+3) ρ) (out := 2)
              (substZeroBeforeMap_add p k 3 ρ)
            rwa [← hEq]
          have hbRep := (ihb p (k+3) ρ 2 (scons z (scons x (scons y e))) (by omega)).mp hbMap
          have henv : ∀ n,
              scons z (scons x (scons y (succReplaceAt M (k+p) e))) n =
                succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))) n :=
            scons3_succReplaceAt_prefix M p k y x z e
          have hbEnv : Sat M.mem
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e)))) henv).mpr hbRep
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          rwa [hEq] at hbEnv
        · change z = succReplaceAt M (k+p) e out
          change z = e out at hcopy
          rwa [succReplaceAt_ne M e (by omega : out ≠ k+p)]
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (succReplaceAt M (k+p) e)))) ?_).mp hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl
      · intro h
        rcases h with ⟨y, x, z, ha, hb, hcopy, hg⟩
        refine ⟨y, x, z, ?_, ?_, ?_, ?_⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 1)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have haMap : Sat M.mem
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons z (scons x (scons y (succReplaceAt M (k+p) e))) n =
                succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))) n :=
            scons3_succReplaceAt_prefix M p k y x z e
          have haRep : Sat M.mem
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 1 a)
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e)))) henv).mp haMap
          have haSub := (iha p (k+3) ρ 1 (scons z (scons x (scons y e))) (by omega)).mpr haRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) a)
            (ρ := fun n => substZeroBeforeMap p k ρ n + 3)
            (σ := substZeroBeforeMap p (k+3) ρ) (out := 1)
            (substZeroBeforeMap_add p k 3 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p (k+3) ρ)
            (σ := fun n => substZeroBeforeMap p k ρ n + 3) (out := 2)
            (fun n => (substZeroBeforeMap_add p k 3 ρ n).symm)
          have hbMap : Sat M.mem
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons z (scons x (scons y (succReplaceAt M (k+p) e))) n =
                succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))) n :=
            scons3_succReplaceAt_prefix M p k y x z e
          have hbRep : Sat M.mem
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e))))
              (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p (k+3) ρ) 2 b)
              (scons z (scons x (scons y (succReplaceAt M (k+p) e))))
              (succReplaceAt M ((k+3)+p) (scons z (scons x (scons y e)))) henv).mp hbMap
          have hbSub := (ihb p (k+3) ρ 2 (scons z (scons x (scons y e))) (by omega)).mpr hbRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) b)
            (ρ := fun n => substZeroBeforeMap p k ρ n + 3)
            (σ := substZeroBeforeMap p (k+3) ρ) (out := 2)
            (substZeroBeforeMap_add p k 3 ρ)
          rwa [← hEqSub] at hbSub
        · change z = e out
          change z = succReplaceAt M (k+p) e out at hcopy
          rwa [succReplaceAt_ne M e (by omega : out ≠ k+p)] at hcopy
        · apply (Sat_ext_free mulGraph
            (scons z (scons x (scons y e)))
            (scons z (scons x (scons y (succReplaceAt M (k+p) e)))) ?_).mpr hg
          intro n hn
          rcases mulGraph_free hn with rfl | rfl | rfl
          · rfl
          · rfl
          · rfl

/-- Translate PA formulas to HF formulas, using `ρ` to identify the HF slots
that hold the current PA variables.  Quantifiers are explicitly relativized to
the finite-ordinal domain formula. -/
def formulaAt (ρ : Nat → Nat) : PA.Formula → Form
  | PA.Formula.eq a b =>
      fEx (fEx (fAnd
        (termGraphAt (fun n => ρ n + 2) 1 a)
        (fAnd
          (termGraphAt (fun n => ρ n + 2) 0 b)
          (fEq 1 0))))
  | PA.Formula.bot => fBot
  | PA.Formula.imp a b => fImp (formulaAt ρ a) (formulaAt ρ b)
  | PA.Formula.and a b => fAnd (formulaAt ρ a) (formulaAt ρ b)
  | PA.Formula.or a b => fOr (formulaAt ρ a) (formulaAt ρ b)
  | PA.Formula.all a => fAll (fImp domainForm (formulaAt (upVarMap ρ) a))
  | PA.Formula.ex a => fEx (fAnd domainForm (formulaAt (upVarMap ρ) a))

/-- PA-formula translation only depends on the slot map at variables free in
the formula. -/
theorem formulaAt_map_ext_free (phi : PA.Formula) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, PA.Formula.Free n phi → ρ n = σ n) →
        formulaAt ρ phi = formulaAt σ phi := by
  induction phi with
  | eq a b =>
      intro ρ σ h
      simp only [formulaAt]
      rw [termGraphAt_map_ext_free a
        (ρ := fun n => ρ n + 2) (σ := fun n => σ n + 2) (out := 1)
        (fun n hn => by rw [h n (Or.inl hn)])]
      rw [termGraphAt_map_ext_free b
        (ρ := fun n => ρ n + 2) (σ := fun n => σ n + 2) (out := 0)
        (fun n hn => by rw [h n (Or.inr hn)])]
  | bot =>
      intro ρ σ h
      rfl
  | imp a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha (fun n hn => h n (Or.inl hn))]
      rw [ihb (fun n hn => h n (Or.inr hn))]
  | and a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha (fun n hn => h n (Or.inl hn))]
      rw [ihb (fun n hn => h n (Or.inr hn))]
  | or a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha (fun n hn => h n (Or.inl hn))]
      rw [ihb (fun n hn => h n (Or.inr hn))]
  | all a ih =>
      intro ρ σ h
      simp only [formulaAt]
      rw [@ih (upVarMap ρ) (upVarMap σ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [upVarMap]
            exact h n hn)]
  | ex a ih =>
      intro ρ σ h
      simp only [formulaAt]
      rw [@ih (upVarMap ρ) (upVarMap σ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [upVarMap]
            exact h n hn)]

theorem formulaAt_map_ext (phi : PA.Formula) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, ρ n = σ n) → formulaAt ρ phi = formulaAt σ phi := by
  induction phi with
  | eq a b =>
      intro ρ σ h
      simp only [formulaAt]
      rw [termGraphAt_map_ext a (ρ := fun n => ρ n + 2)
        (σ := fun n => σ n + 2) (out := 1) (fun n => by rw [h n])]
      rw [termGraphAt_map_ext b (ρ := fun n => ρ n + 2)
        (σ := fun n => σ n + 2) (out := 0) (fun n => by rw [h n])]
  | bot =>
      intro ρ σ h
      rfl
  | imp a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha h, ihb h]
  | and a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha h, ihb h]
  | or a b iha ihb =>
      intro ρ σ h
      simp only [formulaAt]
      rw [iha h, ihb h]
  | all a ih =>
      intro ρ σ h
      simp only [formulaAt]
      rw [@ih (upVarMap ρ) (upVarMap σ)
        (fun n => by cases n <;> simp [upVarMap, h])]
  | ex a ih =>
      intro ρ σ h
      simp only [formulaAt]
      rw [@ih (upVarMap ρ) (upVarMap σ)
        (fun n => by cases n <;> simp [upVarMap, h])]

/-- Translating a renamed PA formula composes the slot map with the PA
renaming. -/
theorem formulaAt_PA_rename (phi : PA.Formula) :
    ∀ {ρ r : Nat → Nat},
      formulaAt ρ (PA.Formula.rename r phi) =
        formulaAt (fun n => ρ (r n)) phi := by
  induction phi with
  | eq a b =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [termGraphAt_PA_rename a]
      rw [termGraphAt_PA_rename b]
  | bot =>
      intro ρ r
      rfl
  | imp a b iha ihb =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [iha, ihb]
  | and a b iha ihb =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [iha, ihb]
  | or a b iha ihb =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [iha, ihb]
  | all a ih =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [@ih (upVarMap ρ) (SetTheory.up r)]
      rw [formulaAt_map_ext a
        (ρ := fun n => upVarMap ρ (SetTheory.up r n))
        (σ := upVarMap (fun n => ρ (r n)))
        (fun n => by cases n <;> simp [upVarMap, SetTheory.up])]
  | ex a ih =>
      intro ρ r
      simp only [PA.Formula.rename, formulaAt]
      rw [@ih (upVarMap ρ) (SetTheory.up r)]
      rw [formulaAt_map_ext a
        (ρ := fun n => upVarMap ρ (SetTheory.up r n))
        (σ := upVarMap (fun n => ρ (r n)))
        (fun n => by cases n <;> simp [upVarMap, SetTheory.up])]

/-- Renaming one level under a binder leaves the PA-in-HF domain formula
unchanged. -/
theorem rename_domainForm_up (r : Nat → Nat) :
    rename (SetTheory.up r) domainForm = domainForm := by
  exact rename_ext_free domainForm (SetTheory.up r) (fun n => n)
    (fun n hn => by
      have hn0 := domainForm_free hn
      subst n
      rfl)

/-- HF-renaming a translated PA formula composes the PA-variable slot map with
the HF renaming. -/
theorem formulaAt_rename (phi : PA.Formula) :
    ∀ {ρ r : Nat → Nat},
      rename r (formulaAt ρ phi) =
        formulaAt (fun n => r (ρ n)) phi := by
  induction phi with
  | eq a b =>
      intro ρ r
      simp [formulaAt, rename, SetTheory.up, termGraphAt_rename]
  | bot =>
      intro ρ r
      rfl
  | imp a b iha ihb =>
      intro ρ r
      simp [formulaAt, rename, iha, ihb]
  | and a b iha ihb =>
      intro ρ r
      simp [formulaAt, rename, iha, ihb]
  | or a b iha ihb =>
      intro ρ r
      simp [formulaAt, rename, iha, ihb]
  | all a ih =>
      intro ρ r
      simp only [formulaAt, rename]
      rw [rename_domainForm_up r]
      rw [@ih (upVarMap ρ) (SetTheory.up r)]
      rw [formulaAt_map_ext a
        (ρ := fun n => SetTheory.up r (upVarMap ρ n))
        (σ := upVarMap (fun n => r (ρ n)))
        (fun n => by cases n <;> simp [upVarMap, SetTheory.up])]
  | ex a ih =>
      intro ρ r
      simp only [formulaAt, rename]
      rw [rename_domainForm_up r]
      rw [@ih (upVarMap ρ) (SetTheory.up r)]
      rw [formulaAt_map_ext a
        (ρ := fun n => SetTheory.up r (upVarMap ρ n))
        (σ := upVarMap (fun n => r (ρ n)))
        (fun n => by cases n <;> simp [upVarMap, SetTheory.up])]

/-- Shifting PA variables below a translated binder is the same as shifting the
already-translated HF formula. -/
theorem formulaAt_rename_succ_upVarMap (phi : PA.Formula) (ρ : Nat → Nat) :
    formulaAt (upVarMap ρ) (PA.Formula.rename Nat.succ phi) =
      rename Nat.succ (formulaAt ρ phi) := by
  calc
    formulaAt (upVarMap ρ) (PA.Formula.rename Nat.succ phi)
        = formulaAt (fun n => upVarMap ρ (Nat.succ n)) phi := by
            exact formulaAt_PA_rename phi
    _ = formulaAt (fun n => Nat.succ (ρ n)) phi := by
            exact formulaAt_map_ext phi (fun n => by simp [upVarMap])
    _ = rename Nat.succ (formulaAt ρ phi) := by
            exact (formulaAt_rename phi).symm

/-- Translating PA substitution of de Bruijn 0 by a PA variable agrees with
instantiating the translated body at the corresponding HF slot. -/
theorem formulaAt_subst_instTerm_var (phi : PA.Formula) (ρ : Nat → Nat)
    (k : Nat) :
    formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) phi) =
      rename (inst (ρ k)) (formulaAt (upVarMap ρ) phi) := by
  calc
    formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) phi)
        = formulaAt ρ (PA.Formula.rename (SetTheory.inst k) phi) := by
            rw [PA.Formula.subst_instTerm_var]
    _ = formulaAt (fun n => ρ (SetTheory.inst k n)) phi := by
            exact formulaAt_PA_rename phi
    _ = formulaAt (fun n => SetTheory.inst (ρ k) (upVarMap ρ n)) phi := by
            exact formulaAt_map_ext phi
              (fun n => by cases n <;> simp [SetTheory.inst, upVarMap])
    _ = rename (inst (ρ k)) (formulaAt (upVarMap ρ) phi) := by
            exact (formulaAt_rename phi).symm

theorem domainForm_scons_insertAt {α : Type u} {mem : α → α → Prop}
    (p : Nat) (x d : α) (e : Nat → α) :
    Sat mem (scons d (insertAt p x e)) domainForm ↔
      Sat mem (scons d e) domainForm :=
  Sat_ext_free domainForm (scons d (insertAt p x e)) (scons d e)
    (fun n hn => by
      have hn0 := domainForm_free hn
      subst n
      rfl)

theorem domainForm_scons_succReplaceAt {α : Type u}
    (M : FirstOrderAdjunctionModel α) (p : Nat) (d : α) (e : Nat → α) :
    Sat M.mem (scons d (succReplaceAt M p e)) domainForm ↔
      Sat M.mem (scons d e) domainForm :=
  Sat_ext_free domainForm (scons d (succReplaceAt M p e)) (scons d e)
    (fun n hn => by
      have hn0 := domainForm_free hn
      subst n
      rfl)

theorem formulaAt_substZeroAt_insert_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (phi : PA.Formula) :
    ∀ (p : Nat) (ρ : Nat → Nat) (e : Nat → α),
      (Sat M.mem e
          (formulaAt (substZeroAfterMap p 0 ρ)
            (PA.Formula.subst (PA.Formula.substZeroAt p) phi)) ↔
        Sat M.mem (insertAt p M.empty e)
          (formulaAt (substZeroBeforeMap p 0 ρ) phi)) := by
  induction phi with
  | eq a b =>
      intro p ρ e
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p 2 ρ) 1
                (PA.Term.subst (PA.Formula.substZeroAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) a)
              (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
              (σ := substZeroAfterMap p 2 ρ) (out := 1)
              (substZeroAfterMap_add p 0 2 ρ)
            rwa [← hEq]
          have haIns := (termGraphAt_substZeroAt_insert_model M a
            p 2 ρ 1 (scons y (scons x e)) (by omega)).mp haMap
          have henv : ∀ n,
              scons y (scons x (insertAt p M.empty e)) n =
                insertAt (2+p) M.empty (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 M.empty x y e n
          have haEnv : Sat M.mem (scons y (scons x (insertAt p M.empty e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (insertAt p M.empty e)))
              (insertAt (2+p) M.empty (scons y (scons x e))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p 2 ρ) 0
                (PA.Term.subst (PA.Formula.substZeroAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substZeroAt p) b)
              (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
              (σ := substZeroAfterMap p 2 ρ) (out := 0)
              (substZeroAfterMap_add p 0 2 ρ)
            rwa [← hEq]
          have hbIns := (termGraphAt_substZeroAt_insert_model M b
            p 2 ρ 0 (scons y (scons x e)) (by omega)).mp hbMap
          have henv : ∀ n,
              scons y (scons x (insertAt p M.empty e)) n =
                insertAt (2+p) M.empty (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 M.empty x y e n
          have hbEnv : Sat M.mem (scons y (scons x (insertAt p M.empty e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (insertAt p M.empty e)))
              (insertAt (2+p) M.empty (scons y (scons x e))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at hbEnv
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have haMap : Sat M.mem (scons y (scons x (insertAt p M.empty e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (insertAt p M.empty e)) n =
                insertAt (2+p) M.empty (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 M.empty x y e n
          have haIns : Sat M.mem
              (insertAt (2+p) M.empty (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (insertAt p M.empty e)))
              (insertAt (2+p) M.empty (scons y (scons x e))) henv).mp haMap
          have haSub := (termGraphAt_substZeroAt_insert_model M a
            p 2 ρ 1 (scons y (scons x e)) (by omega)).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) a)
            (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
            (σ := substZeroAfterMap p 2 ρ) (out := 1)
            (substZeroAfterMap_add p 0 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have hbMap : Sat M.mem (scons y (scons x (insertAt p M.empty e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (insertAt p M.empty e)) n =
                insertAt (2+p) M.empty (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 M.empty x y e n
          have hbIns : Sat M.mem
              (insertAt (2+p) M.empty (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (insertAt p M.empty e)))
              (insertAt (2+p) M.empty (scons y (scons x e))) henv).mp hbMap
          have hbSub := (termGraphAt_substZeroAt_insert_model M b
            p 2 ρ 0 (scons y (scons x e)) (by omega)).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substZeroAt p) b)
            (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
            (σ := substZeroAfterMap p 2 ρ) (out := 0)
            (substZeroAfterMap_add p 0 2 ρ)
          rwa [← hEqSub] at hbSub
  | bot =>
      intro p ρ e
      rfl
  | imp a b iha ihb =>
      intro p ρ e
      constructor
      · intro h ha
        exact (ihb p ρ e).mp (h ((iha p ρ e).mpr ha))
      · intro h ha
        exact (ihb p ρ e).mpr (h ((iha p ρ e).mp ha))
  | and a b iha ihb =>
      intro p ρ e
      exact and_congr (iha p ρ e) (ihb p ρ e)
  | or a b iha ihb =>
      intro p ρ e
      exact or_congr (iha p ρ e) (ihb p ρ e)
  | all a ih =>
      intro p ρ e
      constructor
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d e) domainForm :=
          (domainForm_scons_insertAt (mem := M.mem) p M.empty d e).mp hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d e)
            (formulaAt (substZeroAfterMap (p+1) 0 ρ)
              (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)) := by
          rw [PA.Formula.upSubst_substZeroAt p] at hbody
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)
            (ρ := upVarMap (substZeroAfterMap p 0 ρ))
            (σ := substZeroAfterMap (p+1) 0 ρ)
            (upVarMap_substZeroAfterMap_zero p ρ)
          rwa [hEq] at hbody
        have hbodyIns := (ih (p+1) ρ (scons d e)).mp hbodyNorm
        have henv : ∀ n,
            scons d (insertAt p M.empty e) n =
              insertAt (p+1) M.empty (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_insertAt_prefix p 0 M.empty d e n
        have hbodyEnv : Sat M.mem (scons d (insertAt p M.empty e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (insertAt p M.empty e))
            (insertAt (p+1) M.empty (scons d e)) henv).mpr hbodyIns
        have hEq := formulaAt_map_ext a
          (ρ := substZeroBeforeMap (p+1) 0 ρ)
          (σ := upVarMap (substZeroBeforeMap p 0 ρ))
          (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
        rwa [hEq] at hbodyEnv
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d (insertAt p M.empty e)) domainForm :=
          (domainForm_scons_insertAt (mem := M.mem) p M.empty d e).mpr hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d (insertAt p M.empty e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq]
        have henv : ∀ n,
            scons d (insertAt p M.empty e) n =
              insertAt (p+1) M.empty (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_insertAt_prefix p 0 M.empty d e n
        have hbodyIns : Sat M.mem
            (insertAt (p+1) M.empty (scons d e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (insertAt p M.empty e))
            (insertAt (p+1) M.empty (scons d e)) henv).mp hbodyNorm
        have hbodyAfter := (ih (p+1) ρ (scons d e)).mpr hbodyIns
        have hbodyActual : Sat M.mem (scons d e)
            (formulaAt (upVarMap (substZeroAfterMap p 0 ρ))
              (PA.Formula.subst (PA.Term.upSubst (PA.Formula.substZeroAt p)) a)) := by
          rw [PA.Formula.upSubst_substZeroAt p]
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)
            (ρ := upVarMap (substZeroAfterMap p 0 ρ))
            (σ := substZeroAfterMap (p+1) 0 ρ)
            (upVarMap_substZeroAfterMap_zero p ρ)
          rwa [hEq]
        exact hbodyActual
  | ex a ih =>
      intro p ρ e
      constructor
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_insertAt (mem := M.mem) p M.empty d e).mpr hdDomain
        · have hbodyNorm : Sat M.mem (scons d e)
              (formulaAt (substZeroAfterMap (p+1) 0 ρ)
                (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)) := by
            rw [PA.Formula.upSubst_substZeroAt p] at hbody
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)
              (ρ := upVarMap (substZeroAfterMap p 0 ρ))
              (σ := substZeroAfterMap (p+1) 0 ρ)
              (upVarMap_substZeroAfterMap_zero p ρ)
            rwa [hEq] at hbody
          have hbodyIns := (ih (p+1) ρ (scons d e)).mp hbodyNorm
          have henv : ∀ n,
              scons d (insertAt p M.empty e) n =
                insertAt (p+1) M.empty (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_insertAt_prefix p 0 M.empty d e n
          have hbodyEnv : Sat M.mem (scons d (insertAt p M.empty e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (insertAt p M.empty e))
              (insertAt (p+1) M.empty (scons d e)) henv).mpr hbodyIns
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq] at hbodyEnv
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_insertAt (mem := M.mem) p M.empty d e).mp hdDomain
        · have hbodyNorm : Sat M.mem (scons d (insertAt p M.empty e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
            have hEq := formulaAt_map_ext a
              (ρ := substZeroBeforeMap (p+1) 0 ρ)
              (σ := upVarMap (substZeroBeforeMap p 0 ρ))
              (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
            rwa [hEq]
          have henv : ∀ n,
              scons d (insertAt p M.empty e) n =
                insertAt (p+1) M.empty (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_insertAt_prefix p 0 M.empty d e n
          have hbodyIns : Sat M.mem
              (insertAt (p+1) M.empty (scons d e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (insertAt p M.empty e))
              (insertAt (p+1) M.empty (scons d e)) henv).mp hbodyNorm
          have hbodyAfter := (ih (p+1) ρ (scons d e)).mpr hbodyIns
          have hbodyActual : Sat M.mem (scons d e)
              (formulaAt (upVarMap (substZeroAfterMap p 0 ρ))
                (PA.Formula.subst (PA.Term.upSubst (PA.Formula.substZeroAt p)) a)) := by
            rw [PA.Formula.upSubst_substZeroAt p]
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substZeroAt (p+1)) a)
              (ρ := upVarMap (substZeroAfterMap p 0 ρ))
              (σ := substZeroAfterMap (p+1) 0 ρ)
              (upVarMap_substZeroAfterMap_zero p ρ)
            rwa [hEq]
          exact hbodyActual

theorem formulaAt_substZero_insert_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (phi : PA.Formula)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ (PA.Formula.subst PA.Formula.substZero phi)) ↔
      Sat M.mem (insertAt 0 M.empty e) (formulaAt (upVarMap ρ) phi) := by
  constructor
  · intro h
    have hNormL : Sat M.mem e
        (formulaAt (substZeroAfterMap 0 0 ρ)
          (PA.Formula.subst (PA.Formula.substZeroAt 0) phi)) := by
      rw [PA.Formula.substZeroAt_zero]
      have hEq := formulaAt_map_ext (PA.Formula.subst PA.Formula.substZero phi)
        (ρ := substZeroAfterMap 0 0 ρ) (σ := ρ)
        (substZeroAfterMap_zero_zero ρ)
      rwa [hEq]
    have hNormR := (formulaAt_substZeroAt_insert_model M phi 0 ρ e).mp hNormL
    have hEq := formulaAt_map_ext phi
      (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
      (substZeroBeforeMap_zero_zero ρ)
    rwa [hEq] at hNormR
  · intro h
    have hNormR : Sat M.mem (insertAt 0 M.empty e)
        (formulaAt (substZeroBeforeMap 0 0 ρ) phi) := by
      have hEq := formulaAt_map_ext phi
        (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
        (substZeroBeforeMap_zero_zero ρ)
      rwa [hEq]
    have hNormL := (formulaAt_substZeroAt_insert_model M phi 0 ρ e).mpr hNormR
    rw [PA.Formula.substZeroAt_zero] at hNormL
    have hEq := formulaAt_map_ext (PA.Formula.subst PA.Formula.substZero phi)
      (ρ := substZeroAfterMap 0 0 ρ) (σ := ρ)
      (substZeroAfterMap_zero_zero ρ)
    rwa [hEq] at hNormL

theorem formulaAt_substZero_scons_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (phi : PA.Formula)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ (PA.Formula.subst PA.Formula.substZero phi)) ↔
      Sat M.mem (scons M.empty e) (formulaAt (upVarMap ρ) phi) := by
  have h := formulaAt_substZero_insert_model M phi ρ e
  exact h.trans
    (Sat_ext (formulaAt (upVarMap ρ) phi)
      (insertAt 0 M.empty e) (scons M.empty e) (insertAt_zero M.empty e))

/-- Shift a replacement-term graph through the one fresh local witness introduced
by a translated PA quantifier. -/
theorem Sat_termGraphAt_insertAt_shift_formula_prefix {α : Type u}
    {mem : α → α → Prop} (t : PA.Term) (p : Nat)
    (ρ : Nat → Nat) (termVal d : α) (e : Nat → α)
    (h : Sat mem (insertAt p termVal e)
      (termGraphAt (fun n => ρ n + p + 1) p t)) :
    Sat mem (insertAt (p+1) termVal (scons d e))
      (termGraphAt (fun n => ρ n + (p+1) + 1) (p+1) t) := by
  have h0 : Sat mem (insertAt (0+p) termVal e)
      (termGraphAt (fun n => ρ n + 0 + p + 1) (0+p) t) := by
    simpa [Nat.zero_add] using h
  have hraw := Sat_termGraphAt_insertAt_shift_prefix t p 0 ρ termVal d e h0
  have hslot : (0 + 1) + p = p + 1 := by omega
  rw [hslot] at hraw
  have hEq := termGraphAt_map_ext t
    (ρ := fun n => ρ n + (0 + 1) + p + 1)
    (σ := fun n => ρ n + (p+1) + 1) (out := p+1)
    (fun n => by omega)
  rwa [hEq] at hraw

/-- Transport translated PA formulas across arbitrary PA-term substitution.

The replacement term is represented by an explicit translated term graph at the
inserted HF slot.  This keeps term totality as a semantic hypothesis, rather
than baking it into the substitution map. -/
theorem formulaAt_substTermAt_insert_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (phi : PA.Formula)
    (replacement : PA.Term) :
    ∀ (p : Nat) (ρ : Nat → Nat) (termVal : α) (e : Nat → α),
      (∀ n, PA.Term.Free n replacement →
        OrdinalLike M.mem (e (ρ n + p))) →
      Sat M.mem (insertAt p termVal e)
        (termGraphAt (fun n => ρ n + p + 1) p replacement) →
      (Sat M.mem e
          (formulaAt (substZeroAfterMap p 0 ρ)
            (PA.Formula.subst (PA.Formula.substTermAt p replacement) phi)) ↔
        Sat M.mem (insertAt p termVal e)
          (formulaAt (substZeroBeforeMap p 0 ρ) phi)) := by
  induction phi with
  | eq a b =>
      intro p ρ termVal e hfree hterm
      have hterm0 : Sat M.mem (insertAt (0+p) termVal e)
          (termGraphAt (fun n => ρ n + 0 + p + 1) (0+p) replacement) := by
        simpa [Nat.zero_add] using hterm
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p 2 ρ) 1
                (PA.Term.subst (PA.Formula.substTermAt p replacement) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
              (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
              (σ := substZeroAfterMap p 2 ρ) (out := 1)
              (substZeroAfterMap_add p 0 2 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 0 ρ termVal x e hterm0
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 1 ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + 2 + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + 2 + p) =
                e (ρ n + p) := by
              rw [show ρ n + 2 + p = ρ n + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haIns := (termGraphAt_substTermAt_insert_model M replacement a
            p 2 ρ 1 termVal (scons y (scons x e)) (by omega)
            hfree2 hterm2).mp haMap
          have henv : ∀ n,
              scons y (scons x (insertAt p termVal e)) n =
                insertAt (2+p) termVal (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 termVal x y e n
          have haEnv : Sat M.mem (scons y (scons x (insertAt p termVal e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (insertAt p termVal e)))
              (insertAt (2+p) termVal (scons y (scons x e))) henv).mpr haIns
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroAfterMap p 2 ρ) 0
                (PA.Term.subst (PA.Formula.substTermAt p replacement) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
              (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
              (σ := substZeroAfterMap p 2 ρ) (out := 0)
              (substZeroAfterMap_add p 0 2 ρ)
            rwa [← hEq]
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 0 ρ termVal x e hterm0
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 1 ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + 2 + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + 2 + p) =
                e (ρ n + p) := by
              rw [show ρ n + 2 + p = ρ n + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbIns := (termGraphAt_substTermAt_insert_model M replacement b
            p 2 ρ 0 termVal (scons y (scons x e)) (by omega)
            hfree2 hterm2).mp hbMap
          have henv : ∀ n,
              scons y (scons x (insertAt p termVal e)) n =
                insertAt (2+p) termVal (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 termVal x y e n
          have hbEnv : Sat M.mem (scons y (scons x (insertAt p termVal e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (insertAt p termVal e)))
              (insertAt (2+p) termVal (scons y (scons x e))) henv).mpr hbIns
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at hbEnv
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have haMap : Sat M.mem (scons y (scons x (insertAt p termVal e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (insertAt p termVal e)) n =
                insertAt (2+p) termVal (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 termVal x y e n
          have haIns : Sat M.mem
              (insertAt (2+p) termVal (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (insertAt p termVal e)))
              (insertAt (2+p) termVal (scons y (scons x e))) henv).mp haMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 0 ρ termVal x e hterm0
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 1 ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + 2 + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + 2 + p) =
                e (ρ n + p) := by
              rw [show ρ n + 2 + p = ρ n + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have haSub := (termGraphAt_substTermAt_insert_model M replacement a
            p 2 ρ 1 termVal (scons y (scons x e)) (by omega)
            hfree2 hterm2).mpr haIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) a)
            (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
            (σ := substZeroAfterMap p 2 ρ) (out := 1)
            (substZeroAfterMap_add p 0 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have hbMap : Sat M.mem (scons y (scons x (insertAt p termVal e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (insertAt p termVal e)) n =
                insertAt (2+p) termVal (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using scons2_insertAt_prefix p 0 termVal x y e n
          have hbIns : Sat M.mem
              (insertAt (2+p) termVal (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (insertAt p termVal e)))
              (insertAt (2+p) termVal (scons y (scons x e))) henv).mp hbMap
          have hterm1 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 0 ρ termVal x e hterm0
          have hterm2 := Sat_termGraphAt_insertAt_shift_prefix replacement
            p 1 ρ termVal y (scons x e) hterm1
          have hfree2 : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem
                ((scons y (scons x e)) (ρ n + 2 + p)) := by
            intro n hn
            have hslot : (scons y (scons x e)) (ρ n + 2 + p) =
                e (ρ n + p) := by
              rw [show ρ n + 2 + p = ρ n + p + 2 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hbSub := (termGraphAt_substTermAt_insert_model M replacement b
            p 2 ρ 0 termVal (scons y (scons x e)) (by omega)
            hfree2 hterm2).mpr hbIns
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substTermAt p replacement) b)
            (ρ := fun n => substZeroAfterMap p 0 ρ n + 2)
            (σ := substZeroAfterMap p 2 ρ) (out := 0)
            (substZeroAfterMap_add p 0 2 ρ)
          rwa [← hEqSub] at hbSub
  | bot =>
      intro p ρ termVal e hfree hterm
      rfl
  | imp a b iha ihb =>
      intro p ρ termVal e hfree hterm
      constructor
      · intro h ha
        exact (ihb p ρ termVal e hfree hterm).mp
          (h ((iha p ρ termVal e hfree hterm).mpr ha))
      · intro h ha
        exact (ihb p ρ termVal e hfree hterm).mpr
          (h ((iha p ρ termVal e hfree hterm).mp ha))
  | and a b iha ihb =>
      intro p ρ termVal e hfree hterm
      exact and_congr (iha p ρ termVal e hfree hterm)
        (ihb p ρ termVal e hfree hterm)
  | or a b iha ihb =>
      intro p ρ termVal e hfree hterm
      exact or_congr (iha p ρ termVal e hfree hterm)
        (ihb p ρ termVal e hfree hterm)
  | all a ih =>
      intro p ρ termVal e hfree hterm
      constructor
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d e) domainForm :=
          (domainForm_scons_insertAt (mem := M.mem) p termVal d e).mp hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d e)
            (formulaAt (substZeroAfterMap (p+1) 0 ρ)
              (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)) := by
          rw [PA.Formula.upSubst_substTermAt p replacement] at hbody
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)
            (ρ := upVarMap (substZeroAfterMap p 0 ρ))
            (σ := substZeroAfterMap (p+1) 0 ρ)
            (upVarMap_substZeroAfterMap_zero p ρ)
          rwa [hEq] at hbody
        have hfree' : ∀ n, PA.Term.Free n replacement →
            OrdinalLike M.mem ((scons d e) (ρ n + (p+1))) := by
          intro n hn
          have hslot : (scons d e) (ρ n + (p+1)) = e (ρ n + p) := by
            rw [show ρ n + (p+1) = ρ n + p + 1 by omega]
            rfl
          rw [hslot]
          exact hfree n hn
        have hterm' := Sat_termGraphAt_insertAt_shift_formula_prefix
          replacement p ρ termVal d e hterm
        have hbodyIns := (ih (p+1) ρ termVal (scons d e)
          hfree' hterm').mp hbodyNorm
        have henv : ∀ n,
            scons d (insertAt p termVal e) n =
              insertAt (p+1) termVal (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_insertAt_prefix p 0 termVal d e n
        have hbodyEnv : Sat M.mem (scons d (insertAt p termVal e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (insertAt p termVal e))
            (insertAt (p+1) termVal (scons d e)) henv).mpr hbodyIns
        have hEq := formulaAt_map_ext a
          (ρ := substZeroBeforeMap (p+1) 0 ρ)
          (σ := upVarMap (substZeroBeforeMap p 0 ρ))
          (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
        rwa [hEq] at hbodyEnv
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d (insertAt p termVal e)) domainForm :=
          (domainForm_scons_insertAt (mem := M.mem) p termVal d e).mpr hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d (insertAt p termVal e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq]
        have henv : ∀ n,
            scons d (insertAt p termVal e) n =
              insertAt (p+1) termVal (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_insertAt_prefix p 0 termVal d e n
        have hbodyIns : Sat M.mem
            (insertAt (p+1) termVal (scons d e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (insertAt p termVal e))
            (insertAt (p+1) termVal (scons d e)) henv).mp hbodyNorm
        have hfree' : ∀ n, PA.Term.Free n replacement →
            OrdinalLike M.mem ((scons d e) (ρ n + (p+1))) := by
          intro n hn
          have hslot : (scons d e) (ρ n + (p+1)) = e (ρ n + p) := by
            rw [show ρ n + (p+1) = ρ n + p + 1 by omega]
            rfl
          rw [hslot]
          exact hfree n hn
        have hterm' := Sat_termGraphAt_insertAt_shift_formula_prefix
          replacement p ρ termVal d e hterm
        have hbodyAfter := (ih (p+1) ρ termVal (scons d e)
          hfree' hterm').mpr hbodyIns
        have hbodyActual : Sat M.mem (scons d e)
            (formulaAt (upVarMap (substZeroAfterMap p 0 ρ))
              (PA.Formula.subst
                (PA.Term.upSubst (PA.Formula.substTermAt p replacement)) a)) := by
          rw [PA.Formula.upSubst_substTermAt p replacement]
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)
            (ρ := upVarMap (substZeroAfterMap p 0 ρ))
            (σ := substZeroAfterMap (p+1) 0 ρ)
            (upVarMap_substZeroAfterMap_zero p ρ)
          rwa [hEq]
        exact hbodyActual
  | ex a ih =>
      intro p ρ termVal e hfree hterm
      constructor
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_insertAt (mem := M.mem) p termVal d e).mpr hdDomain
        · have hbodyNorm : Sat M.mem (scons d e)
              (formulaAt (substZeroAfterMap (p+1) 0 ρ)
                (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)) := by
            rw [PA.Formula.upSubst_substTermAt p replacement] at hbody
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)
              (ρ := upVarMap (substZeroAfterMap p 0 ρ))
              (σ := substZeroAfterMap (p+1) 0 ρ)
              (upVarMap_substZeroAfterMap_zero p ρ)
            rwa [hEq] at hbody
          have hfree' : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem ((scons d e) (ρ n + (p+1))) := by
            intro n hn
            have hslot : (scons d e) (ρ n + (p+1)) = e (ρ n + p) := by
              rw [show ρ n + (p+1) = ρ n + p + 1 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hterm' := Sat_termGraphAt_insertAt_shift_formula_prefix
            replacement p ρ termVal d e hterm
          have hbodyIns := (ih (p+1) ρ termVal (scons d e)
            hfree' hterm').mp hbodyNorm
          have henv : ∀ n,
              scons d (insertAt p termVal e) n =
                insertAt (p+1) termVal (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_insertAt_prefix p 0 termVal d e n
          have hbodyEnv : Sat M.mem (scons d (insertAt p termVal e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (insertAt p termVal e))
              (insertAt (p+1) termVal (scons d e)) henv).mpr hbodyIns
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq] at hbodyEnv
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_insertAt (mem := M.mem) p termVal d e).mp hdDomain
        · have hbodyNorm : Sat M.mem (scons d (insertAt p termVal e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
            have hEq := formulaAt_map_ext a
              (ρ := substZeroBeforeMap (p+1) 0 ρ)
              (σ := upVarMap (substZeroBeforeMap p 0 ρ))
              (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
            rwa [hEq]
          have henv : ∀ n,
              scons d (insertAt p termVal e) n =
                insertAt (p+1) termVal (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_insertAt_prefix p 0 termVal d e n
          have hbodyIns : Sat M.mem
              (insertAt (p+1) termVal (scons d e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (insertAt p termVal e))
              (insertAt (p+1) termVal (scons d e)) henv).mp hbodyNorm
          have hfree' : ∀ n, PA.Term.Free n replacement →
              OrdinalLike M.mem ((scons d e) (ρ n + (p+1))) := by
            intro n hn
            have hslot : (scons d e) (ρ n + (p+1)) = e (ρ n + p) := by
              rw [show ρ n + (p+1) = ρ n + p + 1 by omega]
              rfl
            rw [hslot]
            exact hfree n hn
          have hterm' := Sat_termGraphAt_insertAt_shift_formula_prefix
            replacement p ρ termVal d e hterm
          have hbodyAfter := (ih (p+1) ρ termVal (scons d e)
            hfree' hterm').mpr hbodyIns
          have hbodyActual : Sat M.mem (scons d e)
              (formulaAt (upVarMap (substZeroAfterMap p 0 ρ))
                (PA.Formula.subst
                  (PA.Term.upSubst (PA.Formula.substTermAt p replacement)) a)) := by
            rw [PA.Formula.upSubst_substTermAt p replacement]
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substTermAt (p+1) replacement) a)
              (ρ := upVarMap (substZeroAfterMap p 0 ρ))
              (σ := substZeroAfterMap (p+1) 0 ρ)
              (upVarMap_substZeroAfterMap_zero p ρ)
            rwa [hEq]
          exact hbodyActual

/-- Top-level instance of arbitrary PA-term substitution into translated
formulas.  The replacement term graph is supplied at the new front slot. -/
theorem formulaAt_subst_instTerm_of_termGraph_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (phi : PA.Formula)
    (replacement : PA.Term) (ρ : Nat → Nat) (termVal : α)
    (e : Nat → α)
    (hfree : ∀ n, PA.Term.Free n replacement →
      OrdinalLike M.mem (e (ρ n)))
    (hterm : Sat M.mem (scons termVal e)
      (termGraphAt (fun n => ρ n + 1) 0 replacement)) :
    Sat M.mem e
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm replacement) phi)) ↔
    Sat M.mem (scons termVal e) (formulaAt (upVarMap ρ) phi) := by
  have hfree0 : ∀ n, PA.Term.Free n replacement →
      OrdinalLike M.mem (e (ρ n + 0)) := by
    intro n hn
    simpa using hfree n hn
  have hterm0 : Sat M.mem (insertAt 0 termVal e)
      (termGraphAt (fun n => ρ n + 0 + 1) 0 replacement) := by
    have hSat : Sat M.mem (insertAt 0 termVal e)
        (termGraphAt (fun n => ρ n + 1) 0 replacement) :=
      (Sat_ext (termGraphAt (fun n => ρ n + 1) 0 replacement)
        (insertAt 0 termVal e) (scons termVal e)
        (insertAt_zero termVal e)).mpr hterm
    simpa [Nat.zero_add] using hSat
  have hmain := formulaAt_substTermAt_insert_model M phi replacement
    0 ρ termVal e hfree0 hterm0
  constructor
  · intro h
    have hNormL : Sat M.mem e
        (formulaAt (substZeroAfterMap 0 0 ρ)
          (PA.Formula.subst (PA.Formula.substTermAt 0 replacement) phi)) := by
      rw [PA.Formula.substTermAt_zero replacement]
      have hEq := formulaAt_map_ext
        (PA.Formula.subst (PA.Formula.instTerm replacement) phi)
        (ρ := substZeroAfterMap 0 0 ρ) (σ := ρ)
        (substZeroAfterMap_zero_zero ρ)
      rwa [hEq]
    have hNormR := hmain.mp hNormL
    have hEnv : Sat M.mem (scons termVal e)
        (formulaAt (substZeroBeforeMap 0 0 ρ) phi) :=
      (Sat_ext (formulaAt (substZeroBeforeMap 0 0 ρ) phi)
        (insertAt 0 termVal e) (scons termVal e)
        (insertAt_zero termVal e)).mp hNormR
    have hEq := formulaAt_map_ext phi
      (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
      (substZeroBeforeMap_zero_zero ρ)
    rwa [hEq] at hEnv
  · intro h
    have hNormR : Sat M.mem (insertAt 0 termVal e)
        (formulaAt (substZeroBeforeMap 0 0 ρ) phi) := by
      have hEnv : Sat M.mem (scons termVal e)
          (formulaAt (substZeroBeforeMap 0 0 ρ) phi) := by
        have hEq := formulaAt_map_ext phi
          (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
          (substZeroBeforeMap_zero_zero ρ)
        rwa [hEq]
      exact (Sat_ext (formulaAt (substZeroBeforeMap 0 0 ρ) phi)
        (insertAt 0 termVal e) (scons termVal e)
        (insertAt_zero termVal e)).mpr hEnv
    have hNormL := hmain.mpr hNormR
    rw [PA.Formula.substTermAt_zero replacement] at hNormL
    have hEq := formulaAt_map_ext
      (PA.Formula.subst (PA.Formula.instTerm replacement) phi)
      (ρ := substZeroAfterMap 0 0 ρ) (σ := ρ)
      (substZeroAfterMap_zero_zero ρ)
    rwa [hEq] at hNormL

theorem formulaAt_substSuccAt_replace_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (phi : PA.Formula) :
    ∀ (p : Nat) (ρ : Nat → Nat) (e : Nat → α),
      (Sat M.mem e
          (formulaAt (substZeroBeforeMap p 0 ρ)
            (PA.Formula.subst (PA.Formula.substSuccAt p) phi)) ↔
        Sat M.mem (succReplaceAt M p e)
          (formulaAt (substZeroBeforeMap p 0 ρ) phi)) := by
  induction phi with
  | eq a b =>
      intro p ρ e
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have haMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1
                (PA.Term.subst (PA.Formula.substSuccAt p) a)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) a)
              (ρ := fun n => substZeroBeforeMap p 0 ρ n + 2)
              (σ := substZeroBeforeMap p 2 ρ) (out := 1)
              (substZeroBeforeMap_add p 0 2 ρ)
            rwa [← hEq]
          have haRep := (termGraphAt_substSuccAt_replace_model M a
            p 2 ρ 1 (scons y (scons x e)) (by omega)).mp haMap
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M p e)) n =
                succReplaceAt M (2+p) (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using
              scons2_succReplaceAt_prefix M p 0 x y e n
          have haEnv : Sat M.mem (scons y (scons x (succReplaceAt M p e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (succReplaceAt M p e)))
              (succReplaceAt M (2+p) (scons y (scons x e))) henv).mpr haRep
          have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at haEnv
        · have hbMap : Sat M.mem (scons y (scons x e))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0
                (PA.Term.subst (PA.Formula.substSuccAt p) b)) := by
            have hEq := termGraphAt_map_ext
              (PA.Term.subst (PA.Formula.substSuccAt p) b)
              (ρ := fun n => substZeroBeforeMap p 0 ρ n + 2)
              (σ := substZeroBeforeMap p 2 ρ) (out := 0)
              (substZeroBeforeMap_add p 0 2 ρ)
            rwa [← hEq]
          have hbRep := (termGraphAt_substSuccAt_replace_model M b
            p 2 ρ 0 (scons y (scons x e)) (by omega)).mp hbMap
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M p e)) n =
                succReplaceAt M (2+p) (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using
              scons2_succReplaceAt_prefix M p 0 x y e n
          have hbEnv : Sat M.mem (scons y (scons x (succReplaceAt M p e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (succReplaceAt M p e)))
              (succReplaceAt M (2+p) (scons y (scons x e))) henv).mpr hbRep
          have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          rwa [hEq] at hbEnv
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        refine ⟨x, y, ?_, ?_, heq⟩
        · have hEq := termGraphAt_map_ext a
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 1)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have haMap : Sat M.mem (scons y (scons x (succReplaceAt M p e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) := by
            rw [hEq]
            exact ha
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M p e)) n =
                succReplaceAt M (2+p) (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using
              scons2_succReplaceAt_prefix M p 0 x y e n
          have haRep : Sat M.mem
              (succReplaceAt M (2+p) (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 1 a)
              (scons y (scons x (succReplaceAt M p e)))
              (succReplaceAt M (2+p) (scons y (scons x e))) henv).mp haMap
          have haSub := (termGraphAt_substSuccAt_replace_model M a
            p 2 ρ 1 (scons y (scons x e)) (by omega)).mpr haRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) a)
            (ρ := fun n => substZeroBeforeMap p 0 ρ n + 2)
            (σ := substZeroBeforeMap p 2 ρ) (out := 1)
            (substZeroBeforeMap_add p 0 2 ρ)
          rwa [← hEqSub] at haSub
        · have hEq := termGraphAt_map_ext b
            (ρ := substZeroBeforeMap p 2 ρ)
            (σ := fun n => substZeroBeforeMap p 0 ρ n + 2) (out := 0)
            (fun n => (substZeroBeforeMap_add p 0 2 ρ n).symm)
          have hbMap : Sat M.mem (scons y (scons x (succReplaceAt M p e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) := by
            rw [hEq]
            exact hb
          have henv : ∀ n,
              scons y (scons x (succReplaceAt M p e)) n =
                succReplaceAt M (2+p) (scons y (scons x e)) n := by
            intro n
            simpa [Nat.zero_add] using
              scons2_succReplaceAt_prefix M p 0 x y e n
          have hbRep : Sat M.mem
              (succReplaceAt M (2+p) (scons y (scons x e)))
              (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b) :=
            (Sat_ext (termGraphAt (substZeroBeforeMap p 2 ρ) 0 b)
              (scons y (scons x (succReplaceAt M p e)))
              (succReplaceAt M (2+p) (scons y (scons x e))) henv).mp hbMap
          have hbSub := (termGraphAt_substSuccAt_replace_model M b
            p 2 ρ 0 (scons y (scons x e)) (by omega)).mpr hbRep
          have hEqSub := termGraphAt_map_ext
            (PA.Term.subst (PA.Formula.substSuccAt p) b)
            (ρ := fun n => substZeroBeforeMap p 0 ρ n + 2)
            (σ := substZeroBeforeMap p 2 ρ) (out := 0)
            (substZeroBeforeMap_add p 0 2 ρ)
          rwa [← hEqSub] at hbSub
  | bot =>
      intro p ρ e
      rfl
  | imp a b iha ihb =>
      intro p ρ e
      constructor
      · intro h ha
        exact (ihb p ρ e).mp (h ((iha p ρ e).mpr ha))
      · intro h ha
        exact (ihb p ρ e).mpr (h ((iha p ρ e).mp ha))
  | and a b iha ihb =>
      intro p ρ e
      exact and_congr (iha p ρ e) (ihb p ρ e)
  | or a b iha ihb =>
      intro p ρ e
      exact or_congr (iha p ρ e) (ihb p ρ e)
  | all a ih =>
      intro p ρ e
      constructor
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d e) domainForm :=
          (domainForm_scons_succReplaceAt M p d e).mp hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d e)
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ)
              (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)) := by
          rw [PA.Formula.upSubst_substSuccAt p] at hbody
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)
            (ρ := upVarMap (substZeroBeforeMap p 0 ρ))
            (σ := substZeroBeforeMap (p+1) 0 ρ)
            (upVarMap_substZeroBeforeMap_zero p ρ)
          rwa [hEq] at hbody
        have hbodyRep := (ih (p+1) ρ (scons d e)).mp hbodyNorm
        have henv : ∀ n,
            scons d (succReplaceAt M p e) n =
              succReplaceAt M (p+1) (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_succReplaceAt_prefix M p 0 d e n
        have hbodyEnv : Sat M.mem (scons d (succReplaceAt M p e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (succReplaceAt M p e))
            (succReplaceAt M (p+1) (scons d e)) henv).mpr hbodyRep
        have hEq := formulaAt_map_ext a
          (ρ := substZeroBeforeMap (p+1) 0 ρ)
          (σ := upVarMap (substZeroBeforeMap p 0 ρ))
          (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
        rwa [hEq] at hbodyEnv
      · intro hall d hdDomain
        have hdDomain' : Sat M.mem (scons d (succReplaceAt M p e)) domainForm :=
          (domainForm_scons_succReplaceAt M p d e).mpr hdDomain
        have hbody := hall d hdDomain'
        have hbodyNorm : Sat M.mem (scons d (succReplaceAt M p e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq]
        have henv : ∀ n,
            scons d (succReplaceAt M p e) n =
              succReplaceAt M (p+1) (scons d e) n := by
          intro n
          simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using scons_succReplaceAt_prefix M p 0 d e n
        have hbodyRep : Sat M.mem
            (succReplaceAt M (p+1) (scons d e))
            (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
          (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
            (scons d (succReplaceAt M p e))
            (succReplaceAt M (p+1) (scons d e)) henv).mp hbodyNorm
        have hbodyAfter := (ih (p+1) ρ (scons d e)).mpr hbodyRep
        have hbodyActual : Sat M.mem (scons d e)
            (formulaAt (upVarMap (substZeroBeforeMap p 0 ρ))
              (PA.Formula.subst (PA.Term.upSubst (PA.Formula.substSuccAt p)) a)) := by
          rw [PA.Formula.upSubst_substSuccAt p]
          have hEq := formulaAt_map_ext
            (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)
            (ρ := upVarMap (substZeroBeforeMap p 0 ρ))
            (σ := substZeroBeforeMap (p+1) 0 ρ)
            (upVarMap_substZeroBeforeMap_zero p ρ)
          rwa [hEq]
        exact hbodyActual
  | ex a ih =>
      intro p ρ e
      constructor
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_succReplaceAt M p d e).mpr hdDomain
        · have hbodyNorm : Sat M.mem (scons d e)
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ)
                (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)) := by
            rw [PA.Formula.upSubst_substSuccAt p] at hbody
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)
              (ρ := upVarMap (substZeroBeforeMap p 0 ρ))
              (σ := substZeroBeforeMap (p+1) 0 ρ)
              (upVarMap_substZeroBeforeMap_zero p ρ)
            rwa [hEq] at hbody
          have hbodyRep := (ih (p+1) ρ (scons d e)).mp hbodyNorm
          have henv : ∀ n,
              scons d (succReplaceAt M p e) n =
                succReplaceAt M (p+1) (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_succReplaceAt_prefix M p 0 d e n
          have hbodyEnv : Sat M.mem (scons d (succReplaceAt M p e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (succReplaceAt M p e))
              (succReplaceAt M (p+1) (scons d e)) henv).mpr hbodyRep
          have hEq := formulaAt_map_ext a
            (ρ := substZeroBeforeMap (p+1) 0 ρ)
            (σ := upVarMap (substZeroBeforeMap p 0 ρ))
            (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
          rwa [hEq] at hbodyEnv
      · intro h
        rcases h with ⟨d, hdDomain, hbody⟩
        refine ⟨d, ?_, ?_⟩
        · exact (domainForm_scons_succReplaceAt M p d e).mp hdDomain
        · have hbodyNorm : Sat M.mem (scons d (succReplaceAt M p e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) := by
            have hEq := formulaAt_map_ext a
              (ρ := substZeroBeforeMap (p+1) 0 ρ)
              (σ := upVarMap (substZeroBeforeMap p 0 ρ))
              (fun n => (upVarMap_substZeroBeforeMap_zero p ρ n).symm)
            rwa [hEq]
          have henv : ∀ n,
              scons d (succReplaceAt M p e) n =
                succReplaceAt M (p+1) (scons d e) n := by
            intro n
            simpa [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using scons_succReplaceAt_prefix M p 0 d e n
          have hbodyRep : Sat M.mem
              (succReplaceAt M (p+1) (scons d e))
              (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a) :=
            (Sat_ext (formulaAt (substZeroBeforeMap (p+1) 0 ρ) a)
              (scons d (succReplaceAt M p e))
              (succReplaceAt M (p+1) (scons d e)) henv).mp hbodyNorm
          have hbodyAfter := (ih (p+1) ρ (scons d e)).mpr hbodyRep
          have hbodyActual : Sat M.mem (scons d e)
              (formulaAt (upVarMap (substZeroBeforeMap p 0 ρ))
                (PA.Formula.subst (PA.Term.upSubst (PA.Formula.substSuccAt p)) a)) := by
            rw [PA.Formula.upSubst_substSuccAt p]
            have hEq := formulaAt_map_ext
              (PA.Formula.subst (PA.Formula.substSuccAt (p+1)) a)
              (ρ := upVarMap (substZeroBeforeMap p 0 ρ))
              (σ := substZeroBeforeMap (p+1) 0 ρ)
              (upVarMap_substZeroBeforeMap_zero p ρ)
            rwa [hEq]
          exact hbodyActual

theorem formulaAt_substSuccVar_scons_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (phi : PA.Formula)
    (ρ : Nat → Nat) (a : α) (e : Nat → α) :
    Sat M.mem (scons a e)
        (formulaAt (upVarMap ρ)
          (PA.Formula.subst PA.Formula.substSuccVar phi)) ↔
      Sat M.mem (scons (M.adjoin a a) e)
        (formulaAt (upVarMap ρ) phi) := by
  constructor
  · intro h
    have hNormL : Sat M.mem (scons a e)
        (formulaAt (substZeroBeforeMap 0 0 ρ)
          (PA.Formula.subst (PA.Formula.substSuccAt 0) phi)) := by
      rw [PA.Formula.substSuccAt_zero]
      have hEq := formulaAt_map_ext (PA.Formula.subst PA.Formula.substSuccVar phi)
        (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
        (substZeroBeforeMap_zero_zero ρ)
      rwa [hEq]
    have hNormR := (formulaAt_substSuccAt_replace_model M phi 0 ρ (scons a e)).mp hNormL
    have hEnv : ∀ n,
        succReplaceAt M 0 (scons a e) n = scons (M.adjoin a a) e n := by
      intro n
      unfold succReplaceAt
      simpa [scons] using replaceAt_zero_scons (M.adjoin a a) a e n
    have hMap := formulaAt_map_ext phi
      (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
      (substZeroBeforeMap_zero_zero ρ)
    have hSat : Sat M.mem (scons (M.adjoin a a) e)
        (formulaAt (substZeroBeforeMap 0 0 ρ) phi) :=
      (Sat_ext (formulaAt (substZeroBeforeMap 0 0 ρ) phi)
        (succReplaceAt M 0 (scons a e))
        (scons (M.adjoin a a) e) hEnv).mp hNormR
    rwa [hMap] at hSat
  · intro h
    have hMap := formulaAt_map_ext phi
      (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
      (substZeroBeforeMap_zero_zero ρ)
    have hEnv : ∀ n,
        succReplaceAt M 0 (scons a e) n = scons (M.adjoin a a) e n := by
      intro n
      unfold succReplaceAt
      simpa [scons] using replaceAt_zero_scons (M.adjoin a a) a e n
    have hNormR : Sat M.mem (succReplaceAt M 0 (scons a e))
        (formulaAt (substZeroBeforeMap 0 0 ρ) phi) := by
      apply (Sat_ext (formulaAt (substZeroBeforeMap 0 0 ρ) phi)
        (succReplaceAt M 0 (scons a e))
        (scons (M.adjoin a a) e) hEnv).mpr
      rwa [hMap]
    have hNormL := (formulaAt_substSuccAt_replace_model M phi 0 ρ (scons a e)).mpr hNormR
    rw [PA.Formula.substSuccAt_zero] at hNormL
    have hEq := formulaAt_map_ext (PA.Formula.subst PA.Formula.substSuccVar phi)
      (ρ := substZeroBeforeMap 0 0 ρ) (σ := upVarMap ρ)
      (substZeroBeforeMap_zero_zero ρ)
    rwa [hEq] at hNormL

/-- The PA induction axiom is valid under the PA-in-HF translation in every
chosen finite first-order HF adjunction model.

The finite-generation axiom is used only through
`ordinalLike_empty_or_succ`: an ordinal-like HF object is either empty or the
adjunction successor of an ordinal-like member.  The PA base and step
hypotheses are then transported by the explicit zero/successor substitution
lemmas above. -/
theorem formulaAt_induction_valid_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (phi : PA.Formula) (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ (PA.Formula.inductionForm phi)) := by
  intro hInd
  let theta : Form := fImp domainForm (formulaAt (upVarMap ρ) phi)
  have hall : ∀ a, Sat M.mem (scons a e) theta := by
    have hind := M.induction_schema theta e
    apply hind
    intro a ih
    intro haDomain
    have haOrd : OrdinalLike M.mem a :=
      (HF_ordinalLikeAt_spec (scons a e) 0).mp haDomain
    rcases FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M haOrd with
      hEmpty | ⟨p, hp, hSucc⟩
    · subst a
      exact (formulaAt_substZero_scons_model M.toFirstOrderAdjunctionModel
        phi ρ e).mp hInd.1
    · have hpOrd : OrdinalLike M.mem p := OrdinalLike.of_mem haOrd hp
      have hpDomain : Sat M.mem (scons p e) domainForm :=
        (HF_ordinalLikeAt_spec (scons p e) 0).mpr hpOrd
      have hpTheta : Sat M.mem (scons p e) theta :=
        (Sat_rename_rSkipParam theta e a p).mp (ih p hp)
      have hpPhi : Sat M.mem (scons p e) (formulaAt (upVarMap ρ) phi) :=
        hpTheta hpDomain
      have hStepSub : Sat M.mem (scons p e)
          (formulaAt (upVarMap ρ)
            (PA.Formula.subst PA.Formula.substSuccVar phi)) :=
        hInd.2 p hpDomain hpPhi
      have hStepPhi : Sat M.mem (scons (M.adjoin p p) e)
          (formulaAt (upVarMap ρ) phi) :=
        (formulaAt_substSuccVar_scons_model M.toFirstOrderAdjunctionModel
          phi ρ p e).mp hStepSub
      rw [hSucc]
      exact hStepPhi
  intro a haDomain
  exact hall a haDomain

theorem formulaAt_free (phi : PA.Formula) :
    ∀ {ρ : Nat → Nat} {i : Nat}, Free i (formulaAt ρ phi) →
      ∃ n, PA.Formula.Free n phi ∧ i = ρ n := by
  induction phi with
  | eq a b =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · have ha := termGraphAt_free a h
        rcases ha with ha | ha
        · omega
        · rcases ha with ⟨n, hn, hi⟩
          exact ⟨n, Or.inl hn, by omega⟩
      · rcases h with h | h
        · have hb := termGraphAt_free b h
          rcases hb with hb | hb
          · omega
          · rcases hb with ⟨n, hn, hi⟩
            exact ⟨n, Or.inr hn, by omega⟩
        · omega
  | bot =>
      intro ρ i h
      cases h
  | imp a b iha ihb =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | and a b iha ihb =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | or a b iha ihb =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | all a ih =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · have hd := domainForm_free h
        omega
      · rcases ih h with ⟨n, hn, hi⟩
        cases n with
        | zero =>
            simp [upVarMap] at hi
        | succ n =>
            exists n
            constructor
            · exact hn
            · simp [upVarMap] at hi
              omega
  | ex a ih =>
      intro ρ i h
      simp only [formulaAt, Free] at h
      rcases h with h | h
      · have hd := domainForm_free h
        omega
      · rcases ih h with ⟨n, hn, hi⟩
        cases n with
        | zero =>
            simp [upVarMap] at hi
        | succ n =>
            exists n
            constructor
            · exact hn
            · simp [upVarMap] at hi
              omega

/-- Translated equality between PA variables is ordinary equality between the
selected slots.  This version works over any membership relation. -/
theorem formulaAt_eq_var_spec {α : Type u} {mem : α → α → Prop}
    (ρ : Nat → Nat) (m n : Nat) (e : Nat → α) :
    Sat mem e (formulaAt ρ (PA.Formula.eq (PA.Term.var m) (PA.Term.var n))) ↔
      e (ρ m) = e (ρ n) := by
  constructor
  · intro h
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change x = y at hxy
    have hx' := (termGraphAt_var_spec (fun n => ρ n + 2) 1 m
      (scons y (scons x e)) (mem := mem)).mp hx
    have hy' := (termGraphAt_var_spec (fun n => ρ n + 2) 0 n
      (scons y (scons x e)) (mem := mem)).mp hy
    have hxv : x = e (ρ m) := by simpa [scons] using hx'
    have hyv : y = e (ρ n) := by simpa [scons] using hy'
    rw [← hxv, ← hyv]
    exact hxy
  · intro h
    refine ⟨e (ρ m), e (ρ n), ?_, ?_, ?_⟩
    · apply (termGraphAt_var_spec (fun n => ρ n + 2) 1 m
        (scons (e (ρ n)) (scons (e (ρ m)) e)) (mem := mem)).mpr
      simp [scons]
    · apply (termGraphAt_var_spec (fun n => ρ n + 2) 0 n
        (scons (e (ρ n)) (scons (e (ρ m)) e)) (mem := mem)).mpr
      simp [scons]
    · exact h

/-- The zero-is-not-successor PA axiom is valid under the PA-in-HF translation
over any membership relation.  The contradiction is already contained in the
empty and adjunction graph formulas. -/
theorem formulaAt_zeroNotSucc_valid {α : Type u} {mem : α → α → Prop}
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat mem e (formulaAt ρ PA.Formula.zeroNotSucc) := by
  intro a _ hEq
  rcases hEq with ⟨sx, z, hsx, hz, heq⟩
  change sx = z at heq
  have hsx' := (termGraphAt_succ_var_spec (fun n => upVarMap ρ n + 2) 1 0
    (scons z (scons sx (scons a e))) (mem := mem)).mp hsx
  have hz' := (termGraphAt_zero_spec (fun n => upVarMap ρ n + 2) 0
    (scons z (scons sx (scons a e))) (mem := mem)).mp hz
  have haSucc : mem a sx := by
    have hspec := hsx' a
    have : mem a sx ↔ mem a a ∨ a = a := by
      simpa [upVarMap, scons] using hspec
    exact this.mpr (Or.inr rfl)
  rw [heq] at haSucc
  exact hz' a haSucc

/-- The add-zero PA axiom is valid under the PA-in-HF translation in any
chosen first-order HF model.  The witness for `x+0` is the one-pair
successor-recursion graph `{⟨0,x⟩}`. -/
theorem formulaAt_addZero_valid_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.addZero) := by
  intro x _hxDomain
  refine ⟨x, x, ?_, ?_, rfl⟩
  · apply termGraphAt_add_var_zero_model M (fun n => upVarMap ρ n + 2) 1 0
      (scons x (scons x (scons x e)))
    rfl
  · apply (termGraphAt_var_spec (mem := M.mem) (fun n => upVarMap ρ n + 2) 0 0
      (scons x (scons x (scons x e)))).mpr
    rfl

theorem formulaAt_mulZero_valid_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.mulZero) := by
  intro x _hxDomain
  refine ⟨M.empty, M.empty, ?_, ?_, rfl⟩
  · apply termGraphAt_mul_var_zero_model M (fun n => upVarMap ρ n + 2) 1 0
      (scons M.empty (scons M.empty (scons x e)))
    rfl
  · apply (FirstOrderAdjunctionModel.HF_emptyAt_empty M
      (scons M.empty (scons M.empty (scons x e))) 0).mpr
    rfl

/-- The add-successor PA axiom is valid under the PA-in-HF translation once
successor-recursion traces are known to be total on ordinal-like right inputs.

The remaining work for `addSucc` is therefore the object-language HF-induction
proof of the `hTotal` hypothesis. -/
theorem formulaAt_addSucc_valid_model_of_succRecTotal {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hTotal : ∀ s m, OrdinalLike M.mem m →
      FirstOrderAdjunctionModel.SuccRecTotal M s m)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.addSucc) := by
  intro x _hxDomain
  intro y hyDomain
  have hyOrd : OrdinalLike M.mem y :=
    (HF_ordinalLikeAt_spec (scons y (scons x e)) 0).mp hyDomain
  rcases hTotal x y hyOrd with ⟨f, z, hf, hz⟩
  let sz := M.adjoin z z
  let σ : Nat → Nat := fun n => upVarMap (upVarMap ρ) n + 2
  let Eeq : Nat → α := scons sz (scons sz (scons y (scons x e)))
  refine ⟨sz, sz, ?_, ?_, rfl⟩
  · apply termGraphAt_add_var_succ_var_of_succRecApprox_model M σ 1 1 0 Eeq
      (f := f) (z := z)
    · simpa [σ, Eeq, scons, upVarMap] using hyOrd
    · rfl
    · simpa [σ, Eeq, scons, upVarMap] using hf
    · simpa [σ, Eeq, scons, upVarMap] using hz
  · apply termGraphAt_succ_add_var_var_of_succRecApprox_model M σ 0 1 0 Eeq
      (f := f) (z := z)
    · rfl
    · simpa [σ, Eeq, scons, upVarMap] using hf
    · simpa [σ, Eeq, scons, upVarMap] using hz

/-- The add-successor PA axiom follows from the maximal-member principle for
nonempty objects in a first-order HF model. -/
theorem formulaAt_addSucc_valid_model_of_mem_max_exists {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hMax : ∀ a, (∃ x, M.mem x a) →
      ∃ p, M.mem p a ∧ ∀ q, M.mem q a → ¬ M.mem p q)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.addSucc) := by
  apply formulaAt_addSucc_valid_model_of_succRecTotal M
  intro s m hm
  exact FirstOrderAdjunctionModel.succRecTotal_of_ordinalLike_of_mem_max_exists
    M hMax s m hm

theorem formulaAt_addSucc_valid_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.addSucc) := by
  apply formulaAt_addSucc_valid_model_of_succRecTotal M.toFirstOrderAdjunctionModel
  intro s m hm
  exact FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike M s m hm

theorem formulaAt_mulSucc_valid_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.mulSucc) := by
  intro x hxDomain
  intro y hyDomain
  have hxOrd : OrdinalLike M.mem x :=
    (HF_ordinalLikeAt_spec (scons x e) 0).mp hxDomain
  have hyOrd : OrdinalLike M.mem y :=
    (HF_ordinalLikeAt_spec (scons y (scons x e)) 0).mp hyDomain
  rcases mulRecTotal_of_ordinalLike_finite_model M x y hxOrd hyOrd with
    ⟨f, z, hf, hz⟩
  rcases FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike M z x hxOrd with
    ⟨g, w, hg, hw⟩
  let σ : Nat → Nat := fun n => upVarMap (upVarMap ρ) n + 2
  let Eeq : Nat → α := scons w (scons w (scons y (scons x e)))
  refine ⟨w, w, ?_, ?_, rfl⟩
  · apply termGraphAt_mul_var_succ_var_of_mulRecApprox_model
      M.toFirstOrderAdjunctionModel σ 1 1 0 Eeq
      (f := f) (z := z) (g := g) (y := w)
    · simpa [σ, Eeq, scons, upVarMap] using hyOrd
    · rfl
    · simpa [σ, Eeq, scons, upVarMap] using hf
    · simpa [σ, Eeq, scons, upVarMap] using hz
    · simpa [σ, Eeq, scons, upVarMap] using hg
    · simpa [σ, Eeq, scons, upVarMap] using hw
  · apply termGraphAt_add_mul_var_var_var_of_traces_model
      M.toFirstOrderAdjunctionModel σ 0 1 0 Eeq
      (f := f) (z := z) (g := g) (y := w)
    · rfl
    · simpa [σ, Eeq, scons, upVarMap] using hf
    · simpa [σ, Eeq, scons, upVarMap] using hz
    · simpa [σ, Eeq, scons, upVarMap] using hg
    · simpa [σ, Eeq, scons, upVarMap] using hw

/-- Successor-injectivity for the PA-in-HF translation follows from
irreflexivity of membership.  In semantic HF models that irreflexivity comes
from `semantic_mem_irrefl_of_HFAx_s`. -/
theorem formulaAt_succInj_of_irrefl {α : Type u} {mem : α → α → Prop}
    (hIrrefl : ∀ a, ¬ mem a a) (ρ : Nat → Nat) (e : Nat → α) :
    Sat mem e (formulaAt ρ PA.Formula.succInj) := by
  intro a ha b hb hEq
  rcases hEq with ⟨sa, sb, hsa, hsb, heq⟩
  change sa = sb at heq
  have hsa' := (termGraphAt_succ_var_spec
    (fun n => upVarMap (upVarMap ρ) n + 2) 1 1
    (scons sb (scons sa (scons b (scons a e)))) (mem := mem)).mp hsa
  have hsb' := (termGraphAt_succ_var_spec
    (fun n => upVarMap (upVarMap ρ) n + 2) 0 0
    (scons sb (scons sa (scons b (scons a e)))) (mem := mem)).mp hsb
  have hsaSpec : ∀ x, mem x sa ↔ mem x a ∨ x = a := by
    intro x
    have hx := hsa' x
    simpa [upVarMap, scons] using hx
  have hsbSpec : ∀ x, mem x sb ↔ mem x b ∨ x = b := by
    intro x
    have hx := hsb' x
    simpa [upVarMap, scons] using hx
  have haOrd : OrdinalLike mem a := by
    exact (HF_ordinalLikeAt_spec (scons a e) 0).mp ha
  have hbOrd : OrdinalLike mem b := by
    exact (HF_ordinalLikeAt_spec (scons b (scons a e)) 0).mp hb
  have hab : a = b := by
    have haSucc : mem a sb := by
      rw [← heq]
      exact (hsaSpec a).mpr (Or.inr rfl)
    rcases (hsbSpec a).mp haSucc with hab | hab
    · have hbSucc : mem b sa := by
        rw [heq]
        exact (hsbSpec b).mpr (Or.inr rfl)
      rcases (hsaSpec b).mp hbSucc with hba | hba
      · have hbb : mem b b := hbOrd.1 a hab b hba
        exact False.elim (hIrrefl b hbb)
      · exact hba.symm
    · exact hab
  apply (formulaAt_eq_var_spec (upVarMap (upVarMap ρ)) 1 0
    (scons b (scons a e)) (mem := mem)).mpr
  simpa [upVarMap, scons] using hab

/-- Harmless PA universal closures preserve validity of translated formulas
over any membership relation. -/
theorem formulaAt_closeN_valid {α : Type u} {mem : α → α → Prop}
    (phi : PA.Formula) (h : ∀ ρ (e : Nat → α), Sat mem e (formulaAt ρ phi)) :
    ∀ k ρ (e : Nat → α), Sat mem e (formulaAt ρ (PA.Formula.closeN k phi)) := by
  intro k
  induction k generalizing phi with
  | zero =>
      intro ρ e
      exact h ρ e
  | succ k ih =>
      intro ρ e
      exact ih (PA.Formula.all phi)
        (fun ρ e x _ => h (upVarMap ρ) (scons x e)) ρ e

/-- Version of `formulaAt_closeN_valid` for PA's syntactic sealing operation. -/
theorem formulaAt_sealPA_valid {α : Type u} {mem : α → α → Prop}
    (phi : PA.Formula) (h : ∀ ρ (e : Nat → α), Sat mem e (formulaAt ρ phi))
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat mem e (formulaAt ρ (PA.Formula.sealPA phi)) := by
  unfold PA.Formula.sealPA
  exact formulaAt_closeN_valid phi h (PA.Formula.bound phi) ρ e

/-- In any adjunction model, translated equality between PA variables is
ordinary equality between the selected HF slots. -/
theorem formulaAt_eq_var_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (m n : Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ (PA.Formula.eq (PA.Term.var m) (PA.Term.var n))) ↔
      e (ρ m) = e (ρ n) := by
  constructor
  · intro h
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change x = y at hxy
    have hx' := (termGraphAt_var_model M (fun n => ρ n + 2) 1 m
      (scons y (scons x e))).mp hx
    have hy' := (termGraphAt_var_model M (fun n => ρ n + 2) 0 n
      (scons y (scons x e))).mp hy
    have hxv : x = e (ρ m) := by simpa [scons] using hx'
    have hyv : y = e (ρ n) := by simpa [scons] using hy'
    rw [← hxv, ← hyv]
    exact hxy
  · intro h
    refine ⟨e (ρ m), e (ρ n), ?_, ?_, ?_⟩
    · apply (termGraphAt_var_model M (fun n => ρ n + 2) 1 m
        (scons (e (ρ n)) (scons (e (ρ m)) e))).mpr
      simp [scons]
    · apply (termGraphAt_var_model M (fun n => ρ n + 2) 0 n
        (scons (e (ρ n)) (scons (e (ρ m)) e))).mpr
      simp [scons]
    · exact h

/-- The zero-is-not-successor PA axiom is valid under the PA-in-HF
translation in every adjunction model.  This is the unsealed body; use
`translated_zeroNotSucc_sat_model` for the closed PA axiom. -/
theorem formulaAt_zeroNotSucc_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.zeroNotSucc) := by
  intro a _ hEq
  rcases hEq with ⟨sx, z, hsx, hz, heq⟩
  change sx = z at heq
  have hsx' := (termGraphAt_succ_var_model M (fun n => upVarMap ρ n + 2) 1 0
    (scons z (scons sx (scons a e)))).mp hsx
  have hz' := (termGraphAt_zero_model M (fun n => upVarMap ρ n + 2) 0
    (scons z (scons sx (scons a e)))).mp hz
  have hsxv : sx = M.adjoin a a := by
    simpa [upVarMap, scons] using hsx'
  have hzv : z = M.empty := by
    simpa [scons] using hz'
  rw [hsxv, hzv] at heq
  exact adjoin_self_ne_empty_model M a heq

/-- The successor-injectivity PA axiom is valid under the PA-in-HF translation
in every adjunction model.  This is the unsealed body; use
`translated_succInj_sat_model` for the closed PA axiom. -/
theorem formulaAt_succInj_model {α : Type} (M : AdjunctionModel α)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ PA.Formula.succInj) := by
  intro a ha b hb hEq
  rcases hEq with ⟨sa, sb, hsa, hsb, heq⟩
  change sa = sb at heq
  have hsa' := (termGraphAt_succ_var_model M
    (fun n => upVarMap (upVarMap ρ) n + 2) 1 1
    (scons sb (scons sa (scons b (scons a e))))).mp hsa
  have hsb' := (termGraphAt_succ_var_model M
    (fun n => upVarMap (upVarMap ρ) n + 2) 0 0
    (scons sb (scons sa (scons b (scons a e))))).mp hsb
  have hsav : sa = M.adjoin a a := by
    simpa [upVarMap, scons] using hsa'
  have hsbv : sb = M.adjoin b b := by
    simpa [upVarMap, scons] using hsb'
  have haOrd : OrdinalLike M.mem a := by
    exact (HF_ordinalLikeAt_spec (scons a e) 0).mp ha
  have hbOrd : OrdinalLike M.mem b := by
    exact (HF_ordinalLikeAt_spec (scons b (scons a e)) 0).mp hb
  have hab : a = b := by
    apply adjoin_self_injective_on_ordinalLike_model M haOrd hbOrd
    rw [← hsav, ← hsbv]
    exact heq
  apply (formulaAt_eq_var_model M (upVarMap (upVarMap ρ)) 1 0
    (scons b (scons a e))).mpr
  simpa [upVarMap, scons] using hab

/-- Harmless PA universal closures preserve model-validity of a translated PA
formula, provided the unclosed translation is valid for every slot map and
environment. -/
theorem formulaAt_closeN_valid_model {α : Type} (M : AdjunctionModel α)
    (phi : PA.Formula) (h : ∀ ρ (e : Nat → α), Sat M.mem e (formulaAt ρ phi)) :
    ∀ k ρ (e : Nat → α), Sat M.mem e (formulaAt ρ (PA.Formula.closeN k phi)) := by
  intro k
  induction k generalizing phi with
  | zero =>
      intro ρ e
      exact h ρ e
  | succ k ih =>
      intro ρ e
      exact ih (PA.Formula.all phi)
        (fun ρ e x _ => h (upVarMap ρ) (scons x e)) ρ e

/-- Version of `formulaAt_closeN_valid_model` for PA's syntactic sealing
operation. -/
theorem formulaAt_sealPA_valid_model {α : Type} (M : AdjunctionModel α)
    (phi : PA.Formula) (h : ∀ ρ (e : Nat → α), Sat M.mem e (formulaAt ρ phi))
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat M.mem e (formulaAt ρ (PA.Formula.sealPA phi)) := by
  unfold PA.Formula.sealPA
  exact formulaAt_closeN_valid_model M phi h (PA.Formula.bound phi) ρ e

theorem formulaAt_exact (phi : PA.Formula) :
    ∀ (ρ : Nat → Nat) (v e),
      (∀ n, e (ρ n) = ordinalCode (v n)) →
        (Sat Mem e (formulaAt ρ phi) ↔ PA.Formula.Sat PA.natModel v phi) := by
  induction phi with
  | eq a b =>
      intro ρ v e hρ
      constructor
      · intro h
        rcases h with ⟨x, y, ha, hb, heq⟩
        have hρ' : ∀ n, scons y (scons x e) (ρ n + 2) = ordinalCode (v n) := by
          intro n
          simpa [scons] using hρ n
        have hx := (termGraphAt_exact a (fun n => ρ n + 2) 1 v
          (scons y (scons x e)) hρ').mp ha
        have hy := (termGraphAt_exact b (fun n => ρ n + 2) 0 v
          (scons y (scons x e)) hρ').mp hb
        change x = ordinalCode (PA.Term.eval PA.natModel v a) at hx
        change y = ordinalCode (PA.Term.eval PA.natModel v b) at hy
        apply ordinalCode_injective
        rw [← hx, ← hy]
        exact heq
      · intro h
        let x := ordinalCode (PA.Term.eval PA.natModel v a)
        let y := ordinalCode (PA.Term.eval PA.natModel v b)
        refine ⟨x, y, ?_, ?_, ?_⟩
        · apply (termGraphAt_exact a (fun n => ρ n + 2) 1 v
            (scons y (scons x e)) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · apply (termGraphAt_exact b (fun n => ρ n + 2) 0 v
            (scons y (scons x e)) ?_).mpr
          · rfl
          · intro n
            simpa [scons] using hρ n
        · change x = y
          simp only [x, y]
          rw [h]
  | bot =>
      intro ρ v e hρ
      exact Iff.rfl
  | imp a b iha ihb =>
      intro ρ v e hρ
      simp only [formulaAt, PA.Formula.Sat]
      exact ⟨fun hab ha => (ihb ρ v e hρ).mp (hab ((iha ρ v e hρ).mpr ha)),
             fun hab ha => (ihb ρ v e hρ).mpr (hab ((iha ρ v e hρ).mp ha))⟩
  | and a b iha ihb =>
      intro ρ v e hρ
      simp only [formulaAt, PA.Formula.Sat]
      exact and_congr (iha ρ v e hρ) (ihb ρ v e hρ)
  | or a b iha ihb =>
      intro ρ v e hρ
      simp only [formulaAt, PA.Formula.Sat]
      exact or_congr (iha ρ v e hρ) (ihb ρ v e hρ)
  | all a ih =>
      intro ρ v e hρ
      constructor
      · intro h n
        have hdom : Sat Mem (scons (ordinalCode n) e) domainForm :=
          domain_ordinalCode n e
        have hρ' : ∀ k, scons (ordinalCode n) e (upVarMap ρ k) =
            ordinalCode (scons n v k) := by
          intro k
          cases k with
          | zero => rfl
          | succ k =>
              simp [upVarMap, scons]
              exact hρ k
        exact (ih (upVarMap ρ) (scons n v) (scons (ordinalCode n) e) hρ').mp
          (h (ordinalCode n) hdom)
      · intro h x hxdom
        rcases (domain_exact (scons x e)).mp hxdom with ⟨n, hn⟩
        have hx : x = ordinalCode n := hn.symm
        have hρ' : ∀ k, scons x e (upVarMap ρ k) =
            ordinalCode (scons n v k) := by
          intro k
          cases k with
          | zero =>
              exact hx
          | succ k =>
              simp [upVarMap, scons]
              exact hρ k
        exact (ih (upVarMap ρ) (scons n v) (scons x e) hρ').mpr (h n)
  | ex a ih =>
      intro ρ v e hρ
      constructor
      · intro h
        rcases h with ⟨x, hxdom, hbody⟩
        rcases (domain_exact (scons x e)).mp hxdom with ⟨n, hn⟩
        have hx : x = ordinalCode n := hn.symm
        have hρ' : ∀ k, scons x e (upVarMap ρ k) =
            ordinalCode (scons n v k) := by
          intro k
          cases k with
          | zero =>
              exact hx
          | succ k =>
              simp [upVarMap, scons]
              exact hρ k
        exact ⟨n, (ih (upVarMap ρ) (scons n v) (scons x e) hρ').mp hbody⟩
      · intro h
        rcases h with ⟨n, hn⟩
        refine ⟨ordinalCode n, domain_ordinalCode n e, ?_⟩
        have hρ' : ∀ k, scons (ordinalCode n) e (upVarMap ρ k) =
            ordinalCode (scons n v k) := by
          intro k
          cases k with
          | zero => rfl
          | succ k =>
              simp [upVarMap, scons]
              exact hρ k
        exact (ih (upVarMap ρ) (scons n v) (scons (ordinalCode n) e) hρ').mpr hn

/-- The default PA-in-HF translation reads PA variable `n` from HF slot `n`. -/
def translateFormula (phi : PA.Formula) : Form :=
  formulaAt (fun n : Nat => n) phi

/-- Closed zero-is-not-successor axiom, semantically valid under the PA-in-HF
translation over any membership relation. -/
theorem translated_zeroNotSucc_sat {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)) :=
  formulaAt_sealPA_valid PA.Formula.zeroNotSucc
    (fun ρ e => formulaAt_zeroNotSucc_valid ρ e) (fun n : Nat => n) e

/-- Closed successor-injectivity axiom, semantically valid under the PA-in-HF
translation whenever membership is irreflexive. -/
theorem translated_succInj_sat_of_irrefl {α : Type u} {mem : α → α → Prop}
    (hIrrefl : ∀ a, ¬ mem a a) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.succInj)) :=
  formulaAt_sealPA_valid PA.Formula.succInj
    (fun ρ e => formulaAt_succInj_of_irrefl hIrrefl ρ e) (fun n : Nat => n) e

/-- Closed successor-injectivity axiom, semantically valid in every semantic
model of the sealed HF theory. -/
theorem translated_succInj_sat_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.succInj)) :=
  translated_succInj_sat_of_irrefl (semantic_mem_irrefl_of_HFAx_s v hHF) e

/-- Closed add-zero axiom, semantically valid in every semantic model of the
sealed HF theory. -/
theorem translated_addZero_sat_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.addZero)) := by
  let M := firstOrderAdjunctionModel_of_HFAx_s v hHF
  change Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.addZero))
  exact formulaAt_sealPA_valid PA.Formula.addZero
    (fun ρ e => formulaAt_addZero_valid_model M ρ e) (fun n : Nat => n) e

/-- Closed mul-zero axiom, semantically valid in every semantic model of the
sealed HF theory. -/
theorem translated_mulZero_sat_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)) := by
  let M := firstOrderAdjunctionModel_of_HFAx_s v hHF
  change Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulZero))
  exact formulaAt_sealPA_valid PA.Formula.mulZero
    (fun ρ e => formulaAt_mulZero_valid_model M ρ e) (fun n : Nat => n) e

/-- Closed add-successor axiom, semantically valid in every semantic model of
the strengthened hereditary-finite theory. -/
theorem translated_addSucc_sat_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.addSucc)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.addSucc))
  exact formulaAt_sealPA_valid PA.Formula.addSucc
    (fun ρ e => formulaAt_addSucc_valid_finite_model M ρ e) (fun n : Nat => n) e

/-- Closed multiplication-successor axiom, semantically valid in every
semantic model of the strengthened hereditary-finite theory. -/
theorem translated_mulSucc_sat_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulSucc)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.mulSucc))
  exact formulaAt_sealPA_valid PA.Formula.mulSucc
    (fun ρ e => formulaAt_mulSucc_valid_finite_model M ρ e) (fun n : Nat => n) e

/-- Closed PA induction axiom instances are semantically valid under the
PA-in-HF translation in every model of the strengthened hereditary-finite
theory. -/
theorem translated_induction_sat_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (phi : PA.Formula) (e : Nat → α) :
    Sat mem e (translateFormula (PA.Formula.sealPA (PA.Formula.inductionForm phi))) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e
    (translateFormula (PA.Formula.sealPA (PA.Formula.inductionForm phi)))
  exact formulaAt_sealPA_valid (PA.Formula.inductionForm phi)
    (fun ρ e => formulaAt_induction_valid_finite_model M phi ρ e)
    (fun n : Nat => n) e

/-- Closed zero-is-not-successor axiom, semantically validated in every
adjunction model under the PA-in-HF translation. -/
theorem translated_zeroNotSucc_sat_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)) :=
  formulaAt_sealPA_valid_model M PA.Formula.zeroNotSucc
    (fun ρ e => formulaAt_zeroNotSucc_model M ρ e) (fun n : Nat => n) e

/-- Closed successor-injectivity axiom, semantically validated in every
adjunction model under the PA-in-HF translation. -/
theorem translated_succInj_sat_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem e (translateFormula (PA.Formula.sealPA PA.Formula.succInj)) :=
  formulaAt_sealPA_valid_model M PA.Formula.succInj
    (fun ρ e => formulaAt_succInj_model M ρ e) (fun n : Nat => n) e

theorem translateFormula_exact (phi : PA.Formula) (v : Nat → Nat) :
    Sat Mem (fun n => ordinalCode (v n)) (translateFormula phi) ↔
      PA.Formula.Sat PA.natModel v phi :=
  formulaAt_exact phi (fun n : Nat => n) v (fun n => ordinalCode (v n)) (fun _ => rfl)

theorem translated_PA_axiom_sat_codes (phi : PA.Formula)
    (hphi : PA.Formula.Ax_s phi) (v : Nat → Nat) :
    Sat Mem (fun n => ordinalCode (v n)) (translateFormula phi) :=
  (translateFormula_exact phi v).mpr
    (PA.Formula.sat_axiom_s PA.natModel v phi hphi)

theorem formulaAt_sentence_of_PA_sentence (phi : PA.Formula) (ρ : Nat → Nat)
    (hphi : PA.Formula.Sentence phi) : Sentence (formulaAt ρ phi) := by
  intro i hi
  rcases formulaAt_free phi hi with ⟨n, hn, _⟩
  exact hphi n hn

theorem translateFormula_sentence_of_PA_sentence (phi : PA.Formula)
    (hphi : PA.Formula.Sentence phi) : Sentence (translateFormula phi) :=
  formulaAt_sentence_of_PA_sentence phi (fun n : Nat => n) hphi

/-- Closed PA formulas have the same HF translation under every slot map. -/
theorem formulaAt_eq_translateFormula_of_PA_sentence (phi : PA.Formula)
    (ρ : Nat → Nat) (hphi : PA.Formula.Sentence phi) :
    formulaAt ρ phi = translateFormula phi := by
  unfold translateFormula
  exact formulaAt_map_ext_free phi
    (fun n hn => False.elim (hphi n hn))

theorem translated_PA_axiom_sentence (phi : PA.Formula)
    (hphi : PA.Formula.Ax_s phi) : Sentence (translateFormula phi) :=
  translateFormula_sentence_of_PA_sentence phi (PA.Formula.sentence_ax_s hphi)

/-- HF proves the PA-in-HF translation of PA's zero-is-not-successor axiom. -/
theorem BProv_HF_translated_zeroNotSucc :
    BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)) := by
  apply completeness_inf HFAx_s
  · exact Sentences_HF
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_zeroNotSucc
  · intro Dom mem v _hHF
    exact translated_zeroNotSucc_sat (mem := mem) v

/-- HF proves the PA-in-HF translation of PA's successor-injectivity axiom. -/
theorem BProv_HF_translated_succInj :
    BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.succInj)) := by
  apply completeness_inf HFAx_s
  · exact Sentences_HF
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_succInj
  · intro Dom mem v hHF
    exact translated_succInj_sat_of_HFAx_s v hHF v

/-- HF proves the PA-in-HF translation of PA's add-zero axiom. -/
theorem BProv_HF_translated_addZero :
    BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addZero)) := by
  apply completeness_inf HFAx_s
  · exact Sentences_HF
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_addZero
  · intro Dom mem v hHF
    exact translated_addZero_sat_of_HFAx_s v hHF v

theorem BProv_HF_translated_mulZero :
    BProv HFAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)) := by
  apply completeness_inf HFAx_s
  · exact Sentences_HF
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_mulZero
  · intro Dom mem v hHF
    exact translated_mulZero_sat_of_HFAx_s v hHF v

theorem BProv_HFFin_translated_zeroNotSucc :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.zeroNotSucc)) := by
  exact BProv_theory_mono (fun g hg => HFFinAx_s_of_HFAx_s hg)
    BProv_HF_translated_zeroNotSucc

theorem BProv_HFFin_translated_succInj :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.succInj)) := by
  exact BProv_theory_mono (fun g hg => HFFinAx_s_of_HFAx_s hg)
    BProv_HF_translated_succInj

theorem BProv_HFFin_translated_addZero :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addZero)) := by
  exact BProv_theory_mono (fun g hg => HFFinAx_s_of_HFAx_s hg)
    BProv_HF_translated_addZero

theorem BProv_HFFin_translated_mulZero :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulZero)) := by
  exact BProv_theory_mono (fun g hg => HFFinAx_s_of_HFAx_s hg)
    BProv_HF_translated_mulZero

theorem BProv_HFFin_translated_addSucc :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.addSucc)) := by
  apply completeness_inf HFFinAx_s
  · exact Sentences_HFFin
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_addSucc
  · intro Dom mem v hHF
    exact translated_addSucc_sat_of_HFFinAx_s v hHF v

theorem BProv_HFFin_translated_mulSucc :
    BProv HFFinAx_s [] (translateFormula (PA.Formula.sealPA PA.Formula.mulSucc)) := by
  apply completeness_inf HFFinAx_s
  · exact Sentences_HFFin
  · exact translated_PA_axiom_sentence _ PA.Formula.Ax_s_mulSucc
  · intro Dom mem v hHF
    exact translated_mulSucc_sat_of_HFFinAx_s v hHF v

theorem BProv_HFFin_translated_induction (phi : PA.Formula) :
    BProv HFFinAx_s []
      (translateFormula (PA.Formula.sealPA (PA.Formula.inductionForm phi))) := by
  apply completeness_inf HFFinAx_s
  · exact Sentences_HFFin
  · exact translated_PA_axiom_sentence _ (PA.Formula.Ax_s_induction phi)
  · intro Dom mem v hHF
    exact translated_induction_sat_of_HFFinAx_s v hHF phi v

theorem BProv_HFFin_translated_PA_axiom {phi : PA.Formula}
    (hphi : PA.Formula.Ax_s phi) :
    BProv HFFinAx_s [] (translateFormula phi) := by
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | ⟨psi, rfl⟩
  · exact BProv_HFFin_translated_succInj
  · exact BProv_HFFin_translated_zeroNotSucc
  · exact BProv_HFFin_translated_addZero
  · exact BProv_HFFin_translated_addSucc
  · exact BProv_HFFin_translated_mulZero
  · exact BProv_HFFin_translated_mulSucc
  · exact BProv_HFFin_translated_induction psi

/-- The HF-side theory consisting of syntactic translations of the sealed PA
axiom-scheme instances. -/
def translatedPAAx (g : Form) : Prop :=
  ∃ phi, PA.Formula.Ax_s phi ∧ g = translateFormula phi

theorem translatedPAAx_intro {phi : PA.Formula} (hphi : PA.Formula.Ax_s phi) :
    translatedPAAx (translateFormula phi) :=
  ⟨phi, hphi, rfl⟩

theorem Sentences_translatedPAAx : Sentences translatedPAAx := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_PA_axiom_sentence phi hphi

/-- Renaming does not change a sentence. -/
theorem rename_eq_of_sentence {g : Form} (hg : Sentence g) (r : Nat → Nat) :
    rename r g = g := by
  calc
    rename r g = rename (fun n => n) g := by
      apply rename_ext_free
      intro n hn
      exact False.elim (hg n hn)
    _ = g := rename_id g

theorem BProv_translatedPAAx_of_PAAx {phi : PA.Formula}
    (hphi : PA.Formula.Ax_s phi) :
    BProv translatedPAAx [] (translateFormula phi) :=
  BProv_ax (translatedPAAx_intro hphi)

/-- Translate a finite PA context pointwise into the HF language. -/
def translateContext (G : List PA.Formula) : List Form :=
  G.map translateFormula

/-- Translate a finite PA context using an explicit PA-variable-to-HF-slot
map.  This is the context-level counterpart of `formulaAt`; the identity
specialization is `translateContext`. -/
def translateContextAt (ρ : Nat → Nat) (G : List PA.Formula) : List Form :=
  G.map (formulaAt ρ)

/-- Domain assumptions for the first `n` PA variables under an explicit slot
map.  The list is ordered from PA variable `0` upward, so extending a de Bruijn
context exposes the newest variable as the head assumption. -/
def domainContextAt (ρ : Nat → Nat) : Nat → List Form
  | 0 => []
  | n+1 => rename (inst (ρ 0)) domainForm ::
      domainContextAt (fun k => ρ (k+1)) n

theorem translateContextAt_id (G : List PA.Formula) :
    translateContextAt (fun n : Nat => n) G = translateContext G := by
  simp [translateContextAt, translateContext, translateFormula]

/-- Renaming an instantiated PA-domain formula only changes the instantiated
slot; the domain formula itself has no free variables except `0`. -/
theorem rename_domainForm_inst (r : Nat → Nat) (k : Nat) :
    rename r (rename (inst k) domainForm) =
      rename (inst (r k)) domainForm := by
  rw [rename_comp]
  exact rename_ext_free domainForm _ _ (fun n hn => by
    have hn0 := domainForm_free hn
    subst n
    rfl)

/-- Instantiating the PA-domain formula at its own slot leaves it unchanged. -/
theorem rename_domainForm_inst_zero :
    rename (inst 0) domainForm = domainForm := by
  calc
    rename (inst 0) domainForm = rename (fun n => n) domainForm := by
      exact rename_ext_free domainForm _ _ (fun n hn => by
        have hn0 := domainForm_free hn
        subst n
        rfl)
    _ = domainForm := rename_id domainForm

/-- Domain contexts are stable under HF renaming by composing the slot map. -/
theorem domainContextAt_rename (ρ r : Nat → Nat) :
    ∀ n, (domainContextAt ρ n).map (rename r) =
      domainContextAt (fun k => r (ρ k)) n
  | 0 => rfl
  | n+1 => by
      simp [domainContextAt, rename_domainForm_inst,
        domainContextAt_rename (fun k => ρ (k+1)) r n]

/-- The `k`th PA variable-domain assumption is present whenever `k < n`. -/
theorem mem_domainContextAt {ρ : Nat → Nat} :
    ∀ {n k : Nat}, k < n →
      rename (inst (ρ k)) domainForm ∈ domainContextAt ρ n
  | 0, k, hk => by omega
  | n+1, 0, _ => by simp [domainContextAt]
  | n+1, k+1, hk => by
      exact List.mem_cons.mpr
        (Or.inr (mem_domainContextAt
          (ρ := fun j => ρ (j+1)) (n := n) (k := k) (by omega)))

/-- Enlarging the explicit PA-domain prefix preserves every existing domain
assumption. -/
theorem mem_domainContextAt_mono {ρ : Nat → Nat} :
    ∀ {n m : Nat} {g : Form}, n ≤ m →
      g ∈ domainContextAt ρ n → g ∈ domainContextAt ρ m
  | 0, _m, _g, _hnm, hg => by simp [domainContextAt] at hg
  | n+1, 0, _g, hnm, _hg => by omega
  | n+1, m+1, g, hnm, hg => by
      simp only [domainContextAt, List.mem_cons] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl hg
      · exact Or.inr
          (mem_domainContextAt_mono
            (ρ := fun k => ρ (k+1)) (n := n) (m := m)
            (g := g) (by omega) hg)

/-- A relative proof using a finite PA-domain prefix remains valid with a
larger domain prefix. -/
theorem BProv_mono_domainContextAt {B : Form → Prop} {ρ : Nat → Nat}
    {n m : Nat} {G : List Form} {phi : Form}
    (hnm : n ≤ m)
    (h : BProv B (domainContextAt ρ n ++ G) phi) :
    BProv B (domainContextAt ρ m ++ G) phi :=
  BProv_mono B _ _ phi (fun x hx => by
    rw [List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (mem_domainContextAt_mono (ρ := ρ) hnm hx)
    · exact Or.inr hx) h

/-- Under a translated PA binder, the domain context splits into the new
variable-domain assumption followed by the shifted old domain context. -/
theorem domainContextAt_upVarMap_succ (ρ : Nat → Nat) (n : Nat) :
    domainContextAt (upVarMap ρ) (n+1) =
      domainForm :: (domainContextAt ρ n).map (rename Nat.succ) := by
  simp [domainContextAt, upVarMap, domainContextAt_rename,
    rename_domainForm_inst_zero]

/-- Translating a PA context after shifting PA variables below a binder agrees
with shifting the already-translated HF context. -/
theorem translateContextAt_rename_succ_upVarMap (ρ : Nat → Nat)
    (G : List PA.Formula) :
    translateContextAt (upVarMap ρ) (G.map (PA.Formula.rename Nat.succ)) =
      (translateContextAt ρ G).map (rename Nat.succ) := by
  simp [translateContextAt, formulaAt_rename_succ_upVarMap]

theorem mem_translateContext_of_mem {G : List PA.Formula} {phi : PA.Formula}
    (hphi : phi ∈ G) : translateFormula phi ∈ translateContext G :=
  List.mem_map_of_mem (f := translateFormula) hphi

/-- Context membership is preserved by explicit-slot PA-in-HF translation. -/
theorem mem_translateContextAt_of_mem {ρ : Nat → Nat} {G : List PA.Formula}
    {phi : PA.Formula} (hphi : phi ∈ G) :
    formulaAt ρ phi ∈ translateContextAt ρ G :=
  List.mem_map_of_mem (f := formulaAt ρ) hphi

/-- Translated PA assumptions are available as assumptions in the translated
finite context. -/
theorem BProv_translate_ass {G : List PA.Formula} {phi : PA.Formula}
    (hphi : phi ∈ G) :
    BProv translatedPAAx (translateContext G) (translateFormula phi) :=
  BProv_of_Prov (B := translatedPAAx)
    (Prov.P_ass (translateContext G) (translateFormula phi)
      (mem_translateContext_of_mem hphi))

/-- Translated PA assumptions are available under any explicit slot map. -/
theorem BProv_formulaAt_ass {ρ : Nat → Nat} {G : List PA.Formula}
    {phi : PA.Formula} (hphi : phi ∈ G) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ phi) :=
  BProv_of_Prov (B := translatedPAAx)
    (Prov.P_ass (translateContextAt ρ G) (formulaAt ρ phi)
      (mem_translateContextAt_of_mem hphi))

/-- A domain assumption recorded in `domainContextAt` is available over any
additional HF context tail. -/
theorem BProv_domainContextAt_var {ρ : Nat → Nat} {n k : Nat}
    {G : List Form} (hk : k < n) :
    BProv translatedPAAx (domainContextAt ρ n ++ G)
      (rename (inst (ρ k)) domainForm) :=
  BProv_of_Prov (B := translatedPAAx)
    (Prov.P_ass (domainContextAt ρ n ++ G)
      (rename (inst (ρ k)) domainForm)
      (List.mem_append.mpr (Or.inl (mem_domainContextAt (ρ := ρ) hk))))

/-- Instantiating the domain formula at an HF slot says exactly that the slot
is ordinal-like. -/
theorem Sat_rename_inst_domainForm_ordinalLike {α : Type u}
    {mem : α → α → Prop} (e : Nat → α) (k : Nat) :
    Sat mem e (rename (inst k) domainForm) ↔ OrdinalLike mem (e k) := by
  have hrename := Sat_rename (mem := mem) domainForm (inst k) e
  rw [hrename]
  change Sat mem (fun n => e (inst k n)) (HF_ordinalLikeAt 0) ↔
    OrdinalLike mem (e k)
  simpa [inst] using
    (HF_ordinalLikeAt_spec (mem := mem) (fun n => e (inst k n)) 0)

/-- The explicit PA-domain context semantically supplies ordinal-like values
for every PA variable below its bound. -/
theorem Sat_domainContextAt_ordinalLike {α : Type u}
    {mem : α → α → Prop} {ρ : Nat → Nat} {n : Nat} {e : Nat → α}
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g) :
    ∀ k, k < n → OrdinalLike mem (e (ρ k)) := by
  intro k hk
  exact (Sat_rename_inst_domainForm_ordinalLike e (ρ k)).mp
    (hctx _ (mem_domainContextAt (ρ := ρ) hk))

/-- Conversely, ordinal-likeness for every selected PA variable makes the
explicit PA-domain context true. -/
theorem Sat_domainContextAt_of_ordinalLike {α : Type u}
    {mem : α → α → Prop} {ρ : Nat → Nat} {n : Nat} {e : Nat → α}
    (hord : ∀ k, k < n → OrdinalLike mem (e (ρ k))) :
    ∀ g, g ∈ domainContextAt ρ n → Sat mem e g := by
  induction n generalizing ρ with
  | zero =>
      intro g hg
      simp [domainContextAt] at hg
  | succ n ih =>
      intro g hg
      simp only [domainContextAt, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact (Sat_rename_inst_domainForm_ordinalLike e (ρ 0)).mpr
          (hord 0 (by omega))
      · exact ih (ρ := fun k => ρ (k+1))
          (fun k hk => hord (k+1) (by omega)) g hg

/-- A PA axiom, translated into HF, is an axiom of the intermediate
`translatedPAAx` theory. -/
theorem BProv_translate_ax {phi : PA.Formula} (hphi : PA.Formula.Ax_s phi) :
    BProv translatedPAAx [] (translateFormula phi) :=
  BProv_translatedPAAx_of_PAAx hphi

/-- A PA axiom translated under any slot map is an axiom of the intermediate
`translatedPAAx` theory, because PA axiom instances are closed. -/
theorem BProv_formulaAt_ax {ρ : Nat → Nat} {phi : PA.Formula}
    (hphi : PA.Formula.Ax_s phi) :
    BProv translatedPAAx [] (formulaAt ρ phi) := by
  rw [formulaAt_eq_translateFormula_of_PA_sentence phi ρ
    (PA.Formula.sentence_ax_s hphi)]
  exact BProv_translate_ax hphi

/-- A relative HF proof may ignore one extra finite-context assumption. -/
theorem BProv_context_cons {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G b) : BProv B (a :: G) b :=
  BProv_mono B G (a :: G) b
    (fun _ hx => List.mem_cons.mpr (Or.inr hx)) h

/-- Relative HF provability is closed under implication introduction. -/
theorem BProv_impI {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B (a :: G) b) : BProv B G (fImp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl hx)))
  · rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · exact List.mem_cons.mpr (Or.inl hx)
    · exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx)))

/-- Implication introduction with a fixed prefix of assumptions.

This is the context-shaping form needed when an object-language assumption is
discharged behind explicit domain hypotheses. -/
theorem BProv_impI_after_prefix {B : Form → Prop} {Γ Δ : List Form}
    {a b : Form}
    (h : BProv B (Γ ++ a :: Δ) b) :
    BProv B (Γ ++ Δ) (fImp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  grind

/-- Relative HF provability is closed under conjunction introduction. -/
theorem BProv_andI {B : Form → Prop} {G : List Form} {a b : Form}
    (ha : BProv B G a) (hb : BProv B G b) : BProv B G (fAnd a b) := by
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨La ++ Lb, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hLa x hx
    · exact hLb x hx
  · apply Prov.P_andI
    · apply Prov_weaken hpa
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inl hx))
      · exact Or.inr hx
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inr hx))
      · exact Or.inr hx

/-- Relative HF provability is closed under bottom elimination. -/
theorem BProv_botE {B : Form → Prop} {G : List Form} {a : Form}
    (hbot : BProv B G fBot) : BProv B G a := by
  rcases hbot with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_botE _ a hp⟩

/-- Relative HF provability is closed under the first conjunction projection. -/
theorem BProv_andE1 {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fAnd a b)) : BProv B G a := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE1 _ a b hp⟩

/-- Relative HF provability is closed under the second conjunction projection. -/
theorem BProv_andE2 {B : Form → Prop} {G : List Form} {a b : Form}
    (h : BProv B G (fAnd a b)) : BProv B G b := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE2 _ a b hp⟩

/-- Relative HF provability is closed under left disjunction introduction. -/
theorem BProv_orI1 {B : Form → Prop} {G : List Form} {a b : Form}
    (ha : BProv B G a) : BProv B G (fOr a b) := by
  rcases ha with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI1 _ a b hp⟩

/-- Relative HF provability is closed under right disjunction introduction. -/
theorem BProv_orI2 {B : Form → Prop} {G : List Form} {a b : Form}
    (hb : BProv B G b) : BProv B G (fOr a b) := by
  rcases hb with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI2 _ a b hp⟩

/-- Relative HF provability is closed under disjunction elimination. -/
theorem BProv_orE {B : Form → Prop} {G : List Form} {a b c : Form}
    (hor : BProv B G (fOr a b))
    (ha : BProv B (a :: G) c)
    (hb : BProv B (b :: G) c) : BProv B G c := by
  rcases hor with ⟨Lo, hLo, hpo⟩
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨Lo ++ La ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_orE _ a b c
    · apply Prov_weaken hpo
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpa
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind

/-- Disjunction elimination with a fixed prefix of assumptions before each
branch assumption. -/
theorem BProv_orE_after_prefix {B : Form → Prop} {Γ Δ : List Form}
    {a b c : Form}
    (hor : BProv B (Γ ++ Δ) (fOr a b))
    (ha : BProv B (Γ ++ a :: Δ) c)
    (hb : BProv B (Γ ++ b :: Δ) c) :
    BProv B (Γ ++ Δ) c := by
  rcases hor with ⟨Lo, hLo, hpo⟩
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨Lo ++ La ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_orE _ a b c
    · apply Prov_weaken hpo
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpa
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind

/-- Relative HF provability is closed under universal elimination. -/
theorem BProv_allE {B : Form → Prop} {G : List Form} {a : Form} {k : Nat}
    (h : BProv B G (fAll a)) : BProv B G (rename (inst k) a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_allE _ _ k hp⟩

/-- Relative HF provability is closed under existential introduction. -/
theorem BProv_exI {B : Form → Prop} {G : List Form} {a : Form} {k : Nat}
    (h : BProv B G (rename (inst k) a)) : BProv B G (fEx a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_exI _ _ k hp⟩

/-- Universal introduction for relative HF proofs whose theory axioms are
sentences.  The sentence premise keeps the finite list of used theory axioms
stable under the binder shift. -/
theorem BProv_allI_of_sentences {B : Form → Prop} (hB : Sentences B)
    {G : List Form} {a : Form}
    (h : BProv B (G.map (rename Nat.succ)) a) : BProv B G (fAll a) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename Nat.succ) = L := by
    calc
      L.map (rename Nat.succ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hL x hx)) Nat.succ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  apply Prov.P_allI
  apply Prov_weaken hp
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Existential elimination for relative HF proofs whose theory axioms are
sentences.  The sentence premise keeps the finite list of used theory axioms
stable under the binder shift. -/
theorem BProv_exE_of_sentences {B : Form → Prop} (hB : Sentences B)
    {G : List Form} {a c : Form}
    (hex : BProv B G (fEx a))
    (hbody : BProv B (a :: G.map (rename Nat.succ))
      (rename Nat.succ c)) :
    BProv B G c := by
  rcases hex with ⟨Le, hLe, hpe⟩
  rcases hbody with ⟨Lb, hLb, hpb⟩
  have hLbmap : Lb.map (rename Nat.succ) = Lb := by
    calc
      Lb.map (rename Nat.succ) = Lb.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hLb x hx)) Nat.succ
      _ = Lb := by simp
  refine ⟨Le ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_exE _ a c
    · apply Prov_weaken hpe
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · apply List.mem_cons.mpr
        apply Or.inr
        simp only [List.map_append, List.mem_append]
        apply Or.inl
        exact Or.inr (by simpa [hLbmap] using hx)
      · rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · apply List.mem_cons.mpr
          apply Or.inr
          simp only [List.map_append, List.mem_append]
          exact Or.inr hx

/-- Translated implication introduction for the PA-in-HF translation. -/
theorem BProv_translate_impI {G : List PA.Formula} {a b : PA.Formula}
    (h : BProv translatedPAAx
      (translateFormula a :: translateContext G) (translateFormula b)) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.imp a b)) := by
  change BProv translatedPAAx (translateContext G)
    (fImp (translateFormula a) (translateFormula b))
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl hx)))
  · rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · exact List.mem_cons.mpr (Or.inl hx)
    · exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx)))

/-- Translated implication elimination for the PA-in-HF translation. -/
theorem BProv_translate_impE {G : List PA.Formula} {a b : PA.Formula}
    (hab : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.imp a b)))
    (ha : BProv translatedPAAx (translateContext G) (translateFormula a)) :
    BProv translatedPAAx (translateContext G) (translateFormula b) := by
  exact BProv_mp translatedPAAx (translateContext G)
    (translateFormula a) (translateFormula b)
    (by simpa [translateFormula, formulaAt] using hab) ha

/-- Translated bottom elimination for the PA-in-HF translation. -/
theorem BProv_translate_botE {G : List PA.Formula} {a : PA.Formula}
    (hbot : BProv translatedPAAx (translateContext G) fBot) :
    BProv translatedPAAx (translateContext G) (translateFormula a) := by
  rcases hbot with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_botE _ (translateFormula a) hp⟩

/-- Translated law of excluded middle for the PA-in-HF translation. -/
theorem BProv_translate_lem (G : List PA.Formula) (a : PA.Formula) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.or a (PA.Formula.imp a PA.Formula.bot))) := by
  change BProv translatedPAAx (translateContext G)
    (fOr (translateFormula a) (fImp (translateFormula a) fBot))
  exact BProv_of_Prov (B := translatedPAAx) (Prov.P_lem _ _)

/-- Translated conjunction introduction for the PA-in-HF translation. -/
theorem BProv_translate_andI {G : List PA.Formula} {a b : PA.Formula}
    (ha : BProv translatedPAAx (translateContext G) (translateFormula a))
    (hb : BProv translatedPAAx (translateContext G) (translateFormula b)) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.and a b)) := by
  change BProv translatedPAAx (translateContext G)
    (fAnd (translateFormula a) (translateFormula b))
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨La ++ Lb, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hLa x hx
    · exact hLb x hx
  · apply Prov.P_andI
    · apply Prov_weaken hpa
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inl hx))
      · exact Or.inr hx
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inr hx))
      · exact Or.inr hx

/-- First translated conjunction projection for the PA-in-HF translation. -/
theorem BProv_translate_andE1 {G : List PA.Formula} {a b : PA.Formula}
    (h : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.and a b))) :
    BProv translatedPAAx (translateContext G) (translateFormula a) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_andE1 _ (translateFormula a) (translateFormula b)
  simpa [translateFormula, formulaAt] using hp

/-- Second translated conjunction projection for the PA-in-HF translation. -/
theorem BProv_translate_andE2 {G : List PA.Formula} {a b : PA.Formula}
    (h : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.and a b))) :
    BProv translatedPAAx (translateContext G) (translateFormula b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_andE2 _ (translateFormula a) (translateFormula b)
  simpa [translateFormula, formulaAt] using hp

/-- Left translated disjunction introduction for the PA-in-HF translation. -/
theorem BProv_translate_orI1 {G : List PA.Formula} {a b : PA.Formula}
    (ha : BProv translatedPAAx (translateContext G) (translateFormula a)) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.or a b)) := by
  rcases ha with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContext G)
    (fOr (translateFormula a) (translateFormula b))
  exact Prov.P_orI1 _ _ _ hp

/-- Right translated disjunction introduction for the PA-in-HF translation. -/
theorem BProv_translate_orI2 {G : List PA.Formula} {a b : PA.Formula}
    (hb : BProv translatedPAAx (translateContext G) (translateFormula b)) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.or a b)) := by
  rcases hb with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContext G)
    (fOr (translateFormula a) (translateFormula b))
  exact Prov.P_orI2 _ _ _ hp

/-- Translated disjunction elimination for the PA-in-HF translation. -/
theorem BProv_translate_orE {G : List PA.Formula} {a b c : PA.Formula}
    (hor : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.or a b)))
    (ha : BProv translatedPAAx
      (translateFormula a :: translateContext G) (translateFormula c))
    (hb : BProv translatedPAAx
      (translateFormula b :: translateContext G) (translateFormula c)) :
    BProv translatedPAAx (translateContext G) (translateFormula c) := by
  rcases hor with ⟨Lo, hLo, hpo⟩
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨Lo ++ La ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_orE _ (translateFormula a) (translateFormula b) (translateFormula c)
    · apply Prov_weaken hpo
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpa
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind

/-- Translated implication introduction for an explicit PA-variable-to-HF-slot
map. -/
theorem BProv_formulaAt_impI {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (h : BProv translatedPAAx
      (formulaAt ρ a :: translateContextAt ρ G) (formulaAt ρ b)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.imp a b)) := by
  change BProv translatedPAAx (translateContextAt ρ G)
    (fImp (formulaAt ρ a) (formulaAt ρ b))
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl hx)))
  · rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · exact List.mem_cons.mpr (Or.inl hx)
    · exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx)))

/-- Translated implication elimination for an explicit PA-variable-to-HF-slot
map. -/
theorem BProv_formulaAt_impE {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (hab : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.imp a b)))
    (ha : BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ a)) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ b) := by
  exact BProv_mp translatedPAAx (translateContextAt ρ G)
    (formulaAt ρ a) (formulaAt ρ b)
    (by simpa [formulaAt] using hab) ha

/-- Translated bottom elimination for an explicit PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_botE {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula}
    (hbot : BProv translatedPAAx (translateContextAt ρ G) fBot) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ a) := by
  rcases hbot with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_botE _ (formulaAt ρ a) hp⟩

/-- Translated law of excluded middle for an explicit PA-variable-to-HF-slot
map. -/
theorem BProv_formulaAt_lem (ρ : Nat → Nat) (G : List PA.Formula)
    (a : PA.Formula) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.or a (PA.Formula.imp a PA.Formula.bot))) := by
  change BProv translatedPAAx (translateContextAt ρ G)
    (fOr (formulaAt ρ a) (fImp (formulaAt ρ a) fBot))
  exact BProv_of_Prov (B := translatedPAAx) (Prov.P_lem _ _)

/-- Reflexivity of equality for a PA variable term under an arbitrary HF
context.  This is the base equality bridge that needs no term-totality proof:
the graph of a PA variable is just HF equality to its assigned slot. -/
theorem BProv_formulaAt_eqRefl_var {B : Form → Prop} {G : List Form}
    (ρ : Nat → Nat) (k : Nat) :
    BProv B G
      (formulaAt ρ (PA.Formula.eq (PA.Term.var k) (PA.Term.var k))) := by
  refine BProv_of_Prov (B := B) ?_
  change Prov G
    (fEx (fEx (fAnd (fEq 1 (ρ k + 2))
      (fAnd (fEq 0 (ρ k + 2)) (fEq 1 0)))))
  apply Prov.P_exI _ _ (ρ k)
  apply Prov.P_exI _ _ (ρ k)
  change Prov G (fAnd (fEq (ρ k) (ρ k))
    (fAnd (fEq (ρ k) (ρ k)) (fEq (ρ k) (ρ k))))
  apply Prov.P_andI
  · exact Prov.P_eqRefl _ (ρ k)
  · apply Prov.P_andI
    · exact Prov.P_eqRefl _ (ρ k)
    · exact Prov.P_eqRefl _ (ρ k)

/-- In every model of finite HF, the PA-in-HF translation of `0 = 0` is
semantically valid.  The witness is the chosen HF empty object supplied by the
target theory; no existence claim is hidden in the syntax of `zero`. -/
theorem formulaAt_eqRefl_zero_valid_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (e : Nat → α) :
    Sat mem e (formulaAt ρ (PA.Formula.eq PA.Term.zero PA.Term.zero)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e (formulaAt ρ (PA.Formula.eq PA.Term.zero PA.Term.zero))
  refine ⟨M.empty, M.empty, ?_, ?_, rfl⟩
  · exact (FirstOrderAdjunctionModel.HF_emptyAt_empty
      M.toFirstOrderAdjunctionModel
      (scons M.empty (scons M.empty e)) 1).mpr rfl
  · exact (FirstOrderAdjunctionModel.HF_emptyAt_empty
      M.toFirstOrderAdjunctionModel
      (scons M.empty (scons M.empty e)) 0).mpr rfl

/-- Finite HF proves the PA-in-HF translation of zero reflexivity. -/
theorem BProv_HFFin_formulaAt_eqRefl_zero_nil (ρ : Nat → Nat) :
    BProv HFFinAx_s []
      (formulaAt ρ (PA.Formula.eq PA.Term.zero PA.Term.zero)) := by
  apply completeness_inf HFFinAx_s
  · exact Sentences_HFFin
  · exact formulaAt_sentence_of_PA_sentence
      (PA.Formula.eq PA.Term.zero PA.Term.zero) ρ
      (by
        intro n hn
        rcases hn with h | h <;> cases h)
  · intro Dom mem v hHF
    exact formulaAt_eqRefl_zero_valid_of_HFFinAx_s v hHF ρ v

/-- Finite HF proves zero reflexivity over any additional finite context. -/
theorem BProv_HFFin_formulaAt_eqRefl_zero {G : List Form} (ρ : Nat → Nat) :
    BProv HFFinAx_s G
      (formulaAt ρ (PA.Formula.eq PA.Term.zero PA.Term.zero)) :=
  BProv_mono HFFinAx_s [] G _
    (fun _ h => by cases h)
    (BProv_HFFin_formulaAt_eqRefl_zero_nil ρ)

/-- In every model of finite HF, domain assumptions for the free variables of
`t` validate the PA-in-HF translation of `t = t`.

The proof first obtains a genuine term-graph witness from
`termGraphAt_total_of_ordinalLike`, then uses the same witness for both sides
of the translated equality. -/
theorem formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (t : PA.Term) (e : Nat → α)
    (hctx : ∀ g, g ∈ domainContextAt ρ t.bound → Sat mem e g) :
    Sat mem e (formulaAt ρ (PA.Formula.eq t t)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e (formulaAt ρ (PA.Formula.eq t t))
  have hfree : ∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := t.bound)
      (e := e) hctx n (PA.Term.free_lt_bound t n hn)
  rcases termGraphAt_total_of_ordinalLike M t ρ e hfree with
    ⟨x, _hxOrd, hxGraph⟩
  let E : Nat → α := scons x (scons x e)
  have hxLeft : Sat M.mem E
      (termGraphAt (fun n => ρ n + 2) 1 t) := by
    have h := Sat_termGraphAt_shift_front t (fun n => ρ n + 1) 0
      (scons x e) x hxGraph
    simpa [E, Nat.add_assoc] using h
  have hxRight : Sat M.mem E
      (termGraphAt (fun n => ρ n + 2) 0 t) := by
    have h := Sat_termGraphAt_insert_after_output t ρ e x x hxGraph
    simpa [E, Nat.add_assoc] using h
  refine ⟨x, x, ?_, ?_, ?_⟩
  · exact hxLeft
  · exact hxRight
  · rfl

/-- In every model of finite HF, the explicit domain assumptions for a PA term
yield an ordinal-like value satisfying that term's translated graph. -/
theorem termGraphAt_exists_valid_of_HFFinAx_s_domainContext {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (t : PA.Term) (e : Nat → α)
    (hctx : ∀ g, g ∈ domainContextAt ρ t.bound → Sat mem e g) :
    Sat mem e
      (fEx (fAnd domainForm (termGraphAt (fun n => ρ n + 1) 0 t))) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e
    (fEx (fAnd domainForm (termGraphAt (fun n => ρ n + 1) 0 t)))
  have hfree : ∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := t.bound)
      (e := e) hctx n (PA.Term.free_lt_bound t n hn)
  rcases termGraphAt_total_of_ordinalLike M t ρ e hfree with
    ⟨x, hxOrd, hxGraph⟩
  refine ⟨x, ?_, ?_⟩
  · exact (HF_ordinalLikeAt_spec (scons x e) 0).mpr hxOrd
  · exact hxGraph

/-- Finite HF proves translated reflexivity for an arbitrary PA term from
explicit domain assumptions for all free variables of the term. -/
theorem BProv_HFFin_formulaAt_eqRefl_domainContext {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) :
    BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (formulaAt ρ (PA.Formula.eq t t)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    exact formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext v hHF ρ t v
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))

/-- The semantic reflexivity rule for arbitrary PA terms is monotone in the
explicit domain prefix. -/
theorem formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext_le {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (t : PA.Term) (e : Nat → α) {n : Nat}
    (hbound : t.bound ≤ n)
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g) :
    Sat mem e (formulaAt ρ (PA.Formula.eq t t)) :=
  formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext v hHF ρ t e
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) hbound hg))

/-- Finite HF proves translated reflexivity for an arbitrary PA term from any
domain prefix large enough to cover the term's free variables. -/
theorem BProv_HFFin_formulaAt_eqRefl_domainContext_le {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) {n : Nat} (hbound : t.bound ≤ n) :
    BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.eq t t)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    exact formulaAt_eqRefl_valid_of_HFFinAx_s_domainContext_le v hHF
      ρ t v hbound
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))

/-- Finite HF proves that an arbitrary PA term has an ordinal-like translated
graph value from explicit domain assumptions for all free variables of the
term. -/
theorem BProv_HFFin_termGraphAt_exists_domainContext {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) :
    BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (fEx (fAnd domainForm (termGraphAt (fun n => ρ n + 1) 0 t))) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    exact termGraphAt_exists_valid_of_HFFinAx_s_domainContext v hHF ρ t v
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))

/-- The semantic term-graph existence rule is monotone in the explicit domain
prefix. -/
theorem termGraphAt_exists_valid_of_HFFinAx_s_domainContext_le {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (t : PA.Term) (e : Nat → α) {n : Nat}
    (hbound : t.bound ≤ n)
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g) :
    Sat mem e
      (fEx (fAnd domainForm (termGraphAt (fun n => ρ n + 1) 0 t))) :=
  termGraphAt_exists_valid_of_HFFinAx_s_domainContext v hHF ρ t e
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) hbound hg))

/-- Finite HF proves term-graph existence from any domain prefix large enough
to cover the term's free variables. -/
theorem BProv_HFFin_termGraphAt_exists_domainContext_le {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) {n : Nat} (hbound : t.bound ≤ n) :
    BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (fEx (fAnd domainForm (termGraphAt (fun n => ρ n + 1) 0 t))) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    exact termGraphAt_exists_valid_of_HFFinAx_s_domainContext_le v hHF
      ρ t v hbound
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))

/-- In every model of finite HF, universal elimination by an arbitrary PA term
is valid once the free variables of that term are known to lie in the PA
domain. -/
theorem formulaAt_allE_valid_of_HFFinAx_s_domainContext {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term) (e : Nat → α)
    (hctx : ∀ g, g ∈ domainContextAt ρ t.bound → Sat mem e g)
    (hall : Sat mem e (formulaAt ρ (PA.Formula.all a))) :
    Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e
    (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))
  change Sat M.mem e (formulaAt ρ (PA.Formula.all a)) at hall
  have hfree : ∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := t.bound)
      (e := e) hctx n (PA.Term.free_lt_bound t n hn)
  rcases termGraphAt_total_of_ordinalLike M t ρ e hfree with
    ⟨x, hxOrd, hxGraph⟩
  have hbody : Sat M.mem (scons x e) (formulaAt (upVarMap ρ) a) :=
    hall x ((HF_ordinalLikeAt_spec (scons x e) 0).mpr hxOrd)
  exact (formulaAt_subst_instTerm_of_termGraph_model M a t ρ x e
    hfree hxGraph).mpr hbody

/-- The semantic universal-elimination rule for arbitrary PA terms is monotone
in the explicit domain prefix. -/
theorem formulaAt_allE_valid_of_HFFinAx_s_domainContext_le {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term)
    (e : Nat → α) {n : Nat} (hbound : t.bound ≤ n)
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g)
    (hall : Sat mem e (formulaAt ρ (PA.Formula.all a))) :
    Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) :=
  formulaAt_allE_valid_of_HFFinAx_s_domainContext v hHF ρ a t e
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) hbound hg))
    hall

/-- In every model of finite HF, existential introduction by an arbitrary PA
term is valid once the free variables of that term are known to lie in the PA
domain. -/
theorem formulaAt_exI_valid_of_HFFinAx_s_domainContext {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term) (e : Nat → α)
    (hctx : ∀ g, g ∈ domainContextAt ρ t.bound → Sat mem e g)
    (hbody : Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))) :
    Sat mem e (formulaAt ρ (PA.Formula.ex a)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e (formulaAt ρ (PA.Formula.ex a))
  change Sat M.mem e
    (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) at hbody
  have hfree : ∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := t.bound)
      (e := e) hctx n (PA.Term.free_lt_bound t n hn)
  rcases termGraphAt_total_of_ordinalLike M t ρ e hfree with
    ⟨x, hxOrd, hxGraph⟩
  have hbody' : Sat M.mem (scons x e) (formulaAt (upVarMap ρ) a) :=
    (formulaAt_subst_instTerm_of_termGraph_model M a t ρ x e
      hfree hxGraph).mp hbody
  exact ⟨x, (HF_ordinalLikeAt_spec (scons x e) 0).mpr hxOrd, hbody'⟩

/-- The semantic existential-introduction rule for arbitrary PA terms is
monotone in the explicit domain prefix. -/
theorem formulaAt_exI_valid_of_HFFinAx_s_domainContext_le {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term)
    (e : Nat → α) {n : Nat} (hbound : t.bound ≤ n)
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g)
    (hbody : Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))) :
    Sat mem e (formulaAt ρ (PA.Formula.ex a)) :=
  formulaAt_exI_valid_of_HFFinAx_s_domainContext v hHF ρ a t e
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) hbound hg))
    hbody

/-- Finite HF proves universal elimination by an arbitrary PA term from
explicit domain assumptions for that term's free variables. -/
theorem BProv_HFFin_formulaAt_allE_term_domainContext {G : List Form}
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term)
    (hall : BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (formulaAt ρ (PA.Formula.all a))) :
    BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have hallSat : Sat mem v (formulaAt ρ (PA.Formula.all a)) :=
      soundness_BProv hall v hHF hctx
    exact formulaAt_allE_valid_of_HFFinAx_s_domainContext v hHF ρ a t v
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg))) hallSat

/-- Finite HF proves universal elimination by an arbitrary PA term from any
domain prefix large enough to cover the term's free variables. -/
theorem BProv_HFFin_formulaAt_allE_term_domainContext_le {G : List Form}
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term) {n : Nat}
    (hbound : t.bound ≤ n)
    (hall : BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.all a))) :
    BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have hallSat : Sat mem v (formulaAt ρ (PA.Formula.all a)) :=
      soundness_BProv hall v hHF hctx
    exact formulaAt_allE_valid_of_HFFinAx_s_domainContext_le v hHF
      ρ a t v hbound
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg))) hallSat

/-- Finite HF proves existential introduction by an arbitrary PA term from
explicit domain assumptions for that term's free variables. -/
theorem BProv_HFFin_formulaAt_exI_term_domainContext {G : List Form}
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term)
    (hbody : BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))) :
    BProv HFFinAx_s (domainContextAt ρ t.bound ++ G)
      (formulaAt ρ (PA.Formula.ex a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have hbodySat : Sat mem v
        (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) :=
      soundness_BProv hbody v hHF hctx
    exact formulaAt_exI_valid_of_HFFinAx_s_domainContext v hHF ρ a t v
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg))) hbodySat

/-- Finite HF proves existential introduction by an arbitrary PA term from any
domain prefix large enough to cover the term's free variables. -/
theorem BProv_HFFin_formulaAt_exI_term_domainContext_le {G : List Form}
    (ρ : Nat → Nat) (a : PA.Formula) (t : PA.Term) {n : Nat}
    (hbound : t.bound ≤ n)
    (hbody : BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))) :
    BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.ex a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have hbodySat : Sat mem v
        (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) :=
      soundness_BProv hbody v hHF hctx
    exact formulaAt_exI_valid_of_HFFinAx_s_domainContext_le v hHF
      ρ a t v hbound
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg))) hbodySat

/-- In every model of finite HF, equality elimination by arbitrary PA terms is
valid when the free variables of both terms are known to lie in the PA domain.

The translated equality supplies graph witnesses for the two term values; the
formula-substitution bridge turns substitution by the left term into the body
at the left witness slot, transports that body across the witnessed equality,
and turns the result back into substitution by the right term. -/
theorem formulaAt_eqElim_valid_of_HFFinAx_s_domainContext {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (s t : PA.Term) (a : PA.Formula) (e : Nat → α)
    (hsctx : ∀ g, g ∈ domainContextAt ρ s.bound → Sat mem e g)
    (htctx : ∀ g, g ∈ domainContextAt ρ t.bound → Sat mem e g)
    (heq : Sat mem e (formulaAt ρ (PA.Formula.eq s t)))
    (hbody : Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a))) :
    Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change Sat M.mem e
    (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a))
  change Sat M.mem e (formulaAt ρ (PA.Formula.eq s t)) at heq
  change Sat M.mem e
    (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a)) at hbody
  have hsfree : ∀ n, PA.Term.Free n s → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := s.bound)
      (e := e) hsctx n (PA.Term.free_lt_bound s n hn)
  have htfree : ∀ n, PA.Term.Free n t → OrdinalLike M.mem (e (ρ n)) := by
    intro n hn
    exact Sat_domainContextAt_ordinalLike (ρ := ρ) (n := t.bound)
      (e := e) htctx n (PA.Term.free_lt_bound t n hn)
  rcases heq with ⟨x, y, hsGraphShift, htGraphShift, hxy⟩
  have hsGraph : Sat M.mem (scons x e)
      (termGraphAt (fun n => ρ n + 1) 0 s) :=
    Sat_termGraphAt_shift_front_inv s (fun n => ρ n + 1) 0
      (scons x e) y hsGraphShift
  have htGraph : Sat M.mem (scons y e)
      (termGraphAt (fun n => ρ n + 1) 0 t) :=
    Sat_termGraphAt_insert_after_output_inv t ρ e y x htGraphShift
  have hbodyX : Sat M.mem (scons x e) (formulaAt (upVarMap ρ) a) :=
    (formulaAt_subst_instTerm_of_termGraph_model M a s ρ x e
      hsfree hsGraph).mp hbody
  have henv : ∀ n, scons x e n = scons y e n := by
    intro n
    cases n with
    | zero => exact hxy
    | succ n => rfl
  have hbodyY : Sat M.mem (scons y e) (formulaAt (upVarMap ρ) a) :=
    (Sat_ext (formulaAt (upVarMap ρ) a)
      (scons x e) (scons y e) henv).mp hbodyX
  exact (formulaAt_subst_instTerm_of_termGraph_model M a t ρ y e
    htfree htGraph).mpr hbodyY

/-- The semantic equality-elimination rule for arbitrary PA terms is monotone
in a shared explicit domain prefix large enough for both terms. -/
theorem formulaAt_eqElim_valid_of_HFFinAx_s_domainContext_le {α : Type u}
    {mem : α → α → Prop} (v : Nat → α)
    (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (ρ : Nat → Nat) (s t : PA.Term) (a : PA.Formula)
    (e : Nat → α) {n : Nat}
    (hsbound : s.bound ≤ n) (htbound : t.bound ≤ n)
    (hctx : ∀ g, g ∈ domainContextAt ρ n → Sat mem e g)
    (heq : Sat mem e (formulaAt ρ (PA.Formula.eq s t)))
    (hbody : Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a))) :
    Sat mem e
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) :=
  formulaAt_eqElim_valid_of_HFFinAx_s_domainContext v hHF ρ s t a e
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) hsbound hg))
    (fun g hg => hctx g
      (mem_domainContextAt_mono (ρ := ρ) htbound hg))
    heq hbody

/-- Finite HF proves equality elimination for arbitrary PA terms from explicit
domain assumptions for the free variables of both terms. -/
theorem BProv_HFFin_formulaAt_eqElim_term_domainContext {G : List Form}
    (ρ : Nat → Nat) (s t : PA.Term) (a : PA.Formula)
    (heq : BProv HFFinAx_s
      (domainContextAt ρ s.bound ++ (domainContextAt ρ t.bound ++ G))
      (formulaAt ρ (PA.Formula.eq s t)))
    (hbody : BProv HFFinAx_s
      (domainContextAt ρ s.bound ++ (domainContextAt ρ t.bound ++ G))
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a))) :
    BProv HFFinAx_s
      (domainContextAt ρ s.bound ++ (domainContextAt ρ t.bound ++ G))
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have heqSat : Sat mem v (formulaAt ρ (PA.Formula.eq s t)) :=
      soundness_BProv heq v hHF hctx
    have hbodySat : Sat mem v
        (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a)) :=
      soundness_BProv hbody v hHF hctx
    exact formulaAt_eqElim_valid_of_HFFinAx_s_domainContext v hHF ρ s t a v
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))
      (fun g hg => hctx g
        (List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inl hg)))))
      heqSat hbodySat

/-- Finite HF proves equality elimination for arbitrary PA terms from any
shared domain prefix large enough to cover the free variables of both terms. -/
theorem BProv_HFFin_formulaAt_eqElim_term_domainContext_le {G : List Form}
    (ρ : Nat → Nat) (s t : PA.Term) (a : PA.Formula) {n : Nat}
    (hsbound : s.bound ≤ n) (htbound : t.bound ≤ n)
    (heq : BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.eq s t)))
    (hbody : BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a))) :
    BProv HFFinAx_s (domainContextAt ρ n ++ G)
      (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm t) a)) := by
  apply completeness_inf_context HFFinAx_s
  · exact Sentences_HFFin
  · intro Dom mem v hHF hctx
    have heqSat : Sat mem v (formulaAt ρ (PA.Formula.eq s t)) :=
      soundness_BProv heq v hHF hctx
    have hbodySat : Sat mem v
        (formulaAt ρ (PA.Formula.subst (PA.Formula.instTerm s) a)) :=
      soundness_BProv hbody v hHF hctx
    exact formulaAt_eqElim_valid_of_HFFinAx_s_domainContext_le v hHF
      ρ s t a v hsbound htbound
      (fun g hg => hctx g (List.mem_append.mpr (Or.inl hg)))
      heqSat hbodySat

/-- An HF equality proof between the slots assigned to two PA variables yields
the PA-in-HF translation of equality between those PA variables. -/
theorem BProv_formulaAt_eq_var_of_eq {B : Form → Prop} {G : List Form} (ρ : Nat → Nat)
    (m n : Nat)
    (h : BProv B G (fEq (ρ m) (ρ n))) :
    BProv B G
      (formulaAt ρ (PA.Formula.eq (PA.Term.var m) (PA.Term.var n))) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ G)
    (fEx (fEx (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)))))
  apply Prov.P_exI _ _ (ρ m)
  apply Prov.P_exI _ _ (ρ n)
  change Prov (L ++ G) (fAnd (fEq (ρ m) (ρ m))
    (fAnd (fEq (ρ n) (ρ n)) (fEq (ρ m) (ρ n))))
  apply Prov.P_andI
  · exact Prov.P_eqRefl _ (ρ m)
  · apply Prov.P_andI
    · exact Prov.P_eqRefl _ (ρ n)
    · exact hp

/-- Explicit term-graph witnesses for two PA terms, together with equality of
their value slots, yield the PA-in-HF translation of equality between those
terms.

All computational content stays in the premises: the theorem only packages
already-supplied graph and equality proofs into the translated PA equality
formula. -/
theorem BProv_formulaAt_eq_of_termGraphsAt {B : Form → Prop} {G : List Form}
    (ρ : Nat → Nat) (s t : PA.Term) (i j : Nat)
    (hs : BProv B G (termGraphAt ρ i s))
    (ht : BProv B G (termGraphAt ρ j t))
    (heq : BProv B G (fEq i j)) :
    BProv B G (formulaAt ρ (PA.Formula.eq s t)) := by
  have hconj : BProv B G
      (fAnd (termGraphAt ρ i s)
        (fAnd (termGraphAt ρ j t) (fEq i j))) :=
    BProv_andI hs (BProv_andI ht heq)
  rcases hconj with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ G)
    (fEx (fEx (fAnd (termGraphAt (fun n => ρ n + 2) 1 s)
      (fAnd (termGraphAt (fun n => ρ n + 2) 0 t) (fEq 1 0)))))
  apply Prov.P_exI _ _ i
  apply Prov.P_exI _ _ j
  simpa [rename, termGraphAt_rename, SetTheory.up, inst] using hp

/-- Term-graph witnesses can be transported across equality of their output
slots.

This is the graph-level equality-elimination rule needed by later arbitrary
PA-term substitution proofs. -/
theorem BProv_termGraphAt_eqElim_out {B : Form → Prop} {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) {i j : Nat}
    (heq : BProv B G (fEq i j))
    (hgraph : BProv B G (termGraphAt ρ i t)) :
    BProv B G (termGraphAt ρ j t) := by
  have hinst : BProv B G
      (rename (inst i) (termGraphAt (fun n => ρ n + 1) 0 t)) := by
    simpa [termGraphAt_inst_out] using hgraph
  have htarget : BProv B G
      (rename (inst j) (termGraphAt (fun n => ρ n + 1) 0 t)) :=
    BProv_eqElim heq hinst
  simpa [termGraphAt_inst_out] using htarget

/-- A concrete HF slot realizing a PA term graph yields the PA-in-HF
translation of reflexivity for that PA term.

The term graph witness is an explicit premise: this lemma does not assert that
arbitrary PA terms are total in the interpreted HF domain. -/
theorem BProv_formulaAt_eqRefl_of_termGraphAt {B : Form → Prop} {G : List Form}
    (ρ : Nat → Nat) (t : PA.Term) (k : Nat)
    (h : BProv B G (termGraphAt ρ k t)) :
    BProv B G (formulaAt ρ (PA.Formula.eq t t)) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ G)
    (fEx (fEx (fAnd (termGraphAt (fun n => ρ n + 2) 1 t)
      (fAnd (termGraphAt (fun n => ρ n + 2) 0 t) (fEq 1 0)))))
  apply Prov.P_exI _ _ k
  apply Prov.P_exI _ _ k
  have hconj : Prov (L ++ G)
      (fAnd (termGraphAt ρ k t)
        (fAnd (termGraphAt ρ k t) (fEq k k))) := by
    apply Prov.P_andI
    · exact hp
    · apply Prov.P_andI
      · exact hp
      · exact Prov.P_eqRefl _ k
  simpa [rename, termGraphAt_rename, SetTheory.up, inst] using hconj

/-- The PA-in-HF translation of equality between two PA variables entails the
underlying HF equality between their assigned slots. -/
theorem BProv_eq_of_formulaAt_eq_var {B : Form → Prop} {G : List Form} (ρ : Nat → Nat)
    (m n : Nat)
    (h : BProv B G
      (formulaAt ρ (PA.Formula.eq (PA.Term.var m) (PA.Term.var n)))) :
    BProv B G (fEq (ρ m) (ρ n)) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  let H : List Form := L ++ G
  change Prov H (fEq (ρ m) (ρ n))
  change Prov H
    (fEx (fEx (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0))))) at hp
  apply Prov.P_exE H
    (fEx (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0))))
    (fEq (ρ m) (ρ n)) hp
  change Prov
    (fEx (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0))) :: H.map (rename Nat.succ))
    (fEq (ρ m + 1) (ρ n + 1))
  let H1 : List Form :=
    fEx (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0))) :: H.map (rename Nat.succ)
  have hinner : Prov H1
      (fEx (fAnd (fEq 1 (ρ m + 2))
        (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)))) :=
    Prov.P_ass H1 _ (by simp [H1])
  apply Prov.P_exE H1
    (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)))
    (fEq (ρ m + 1) (ρ n + 1)) hinner
  change Prov
    (fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)) ::
        H1.map (rename Nat.succ))
    (fEq (ρ m + 2) (ρ n + 2))
  let H2 : List Form :=
    fAnd (fEq 1 (ρ m + 2))
      (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)) ::
        H1.map (rename Nat.succ)
  have hconj : Prov H2
      (fAnd (fEq 1 (ρ m + 2))
        (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0))) :=
    Prov.P_ass H2 _ (by simp [H2])
  have hx : Prov H2 (fEq 1 (ρ m + 2)) :=
    Prov.P_andE1 H2 _ _ hconj
  have hyx : Prov H2 (fAnd (fEq 0 (ρ n + 2)) (fEq 1 0)) :=
    Prov.P_andE2 H2 _ _ hconj
  have hy : Prov H2 (fEq 0 (ρ n + 2)) :=
    Prov.P_andE1 H2 _ _ hyx
  have hxy : Prov H2 (fEq 1 0) :=
    Prov.P_andE2 H2 _ _ hyx
  have hmx : Prov H2 (fEq (ρ m + 2) 1) :=
    Prov_eq_sym H2 1 (ρ m + 2) hx
  have hm0 : Prov H2 (fEq (ρ m + 2) 0) :=
    Prov_eq_trans H2 (ρ m + 2) 1 0 hmx hxy
  exact Prov_eq_trans H2 (ρ m + 2) 0 (ρ n + 2) hm0 hy

/-- PA-in-HF Leibniz equality elimination for equality between PA variables.

The term-totality issue is explicit in the shape of this lemma: it applies only
to variable terms, whose translated term graphs are just equality to their HF
slots. -/
theorem BProv_formulaAt_eqElim_var {B : Form → Prop} {Γ : List Form} {ρ : Nat → Nat}
    {m n : Nat} {a : PA.Formula}
    (heq : BProv B Γ
      (formulaAt ρ (PA.Formula.eq (PA.Term.var m) (PA.Term.var n))))
    (ha : BProv B Γ
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var m)) a))) :
    BProv B Γ
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var n)) a)) := by
  have hslot : BProv B Γ (fEq (ρ m) (ρ n)) :=
    BProv_eq_of_formulaAt_eq_var ρ m n heq
  have ha' : BProv B Γ
      (rename (inst (ρ m)) (formulaAt (upVarMap ρ) a)) := by
    simpa [formulaAt_subst_instTerm_var] using ha
  have htarget : BProv B Γ
      (rename (inst (ρ n)) (formulaAt (upVarMap ρ) a)) :=
    BProv_eqElim hslot ha'
  simpa [formulaAt_subst_instTerm_var] using htarget

/-- Translated conjunction introduction for an explicit
PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_andI {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (ha : BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ a))
    (hb : BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ b)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.and a b)) := by
  change BProv translatedPAAx (translateContextAt ρ G)
    (fAnd (formulaAt ρ a) (formulaAt ρ b))
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨La ++ Lb, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hLa x hx
    · exact hLb x hx
  · apply Prov.P_andI
    · apply Prov_weaken hpa
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inl hx))
      · exact Or.inr hx
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inr hx))
      · exact Or.inr hx

/-- First translated conjunction projection for an explicit
PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_andE1 {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (h : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.and a b))) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ a) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_andE1 _ (formulaAt ρ a) (formulaAt ρ b)
  simpa [formulaAt] using hp

/-- Second translated conjunction projection for an explicit
PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_andE2 {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (h : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.and a b))) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_andE2 _ (formulaAt ρ a) (formulaAt ρ b)
  simpa [formulaAt] using hp

/-- Left translated disjunction introduction for an explicit
PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_orI1 {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (ha : BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ a)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.or a b)) := by
  rcases ha with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContextAt ρ G)
    (fOr (formulaAt ρ a) (formulaAt ρ b))
  exact Prov.P_orI1 _ _ _ hp

/-- Right translated disjunction introduction for an explicit
PA-variable-to-HF-slot map. -/
theorem BProv_formulaAt_orI2 {ρ : Nat → Nat} {G : List PA.Formula}
    {a b : PA.Formula}
    (hb : BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ b)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.or a b)) := by
  rcases hb with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContextAt ρ G)
    (fOr (formulaAt ρ a) (formulaAt ρ b))
  exact Prov.P_orI2 _ _ _ hp

/-- Translated disjunction elimination for an explicit PA-variable-to-HF-slot
map. -/
theorem BProv_formulaAt_orE {ρ : Nat → Nat} {G : List PA.Formula}
    {a b c : PA.Formula}
    (hor : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.or a b)))
    (ha : BProv translatedPAAx
      (formulaAt ρ a :: translateContextAt ρ G) (formulaAt ρ c))
    (hb : BProv translatedPAAx
      (formulaAt ρ b :: translateContextAt ρ G) (formulaAt ρ c)) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ c) := by
  rcases hor with ⟨Lo, hLo, hpo⟩
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨Lo ++ La ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_orE _ (formulaAt ρ a) (formulaAt ρ b) (formulaAt ρ c)
    · apply Prov_weaken hpo
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpa
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind

/-- Raw translated universal introduction.

This is the HF natural-deduction rule for the relativized translation shape:
to prove `∀ x ∈ domain, A`, it is enough to prove the relativized body in the
shifted translated context.  A later PA-proof translation lemma is responsible
for turning a PA premise over `G.map rename Nat.succ` into this shifted HF
premise. -/
theorem BProv_translate_allI_raw {G : List PA.Formula} {a : PA.Formula}
    (h : BProv translatedPAAx ((translateContext G).map (rename Nat.succ))
      (fImp domainForm (formulaAt (upVarMap (fun n => n)) a))) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.all a)) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename Nat.succ) = L := by
    calc
      L.map (rename Nat.succ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (Sentences_translatedPAAx x (hL x hx)) Nat.succ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContext G)
    (fAll (fImp domainForm (formulaAt (upVarMap (fun n => n)) a)))
  apply Prov.P_allI
  apply Prov_weaken hp
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Raw translated universal elimination by an HF variable instance. -/
theorem BProv_translate_allE_raw {G : List PA.Formula} {a : PA.Formula} {k : Nat}
    (h : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.all a))) :
    BProv translatedPAAx (translateContext G)
      (rename (inst k)
        (fImp domainForm (formulaAt (upVarMap (fun n => n)) a))) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContext G)
    (rename (inst k)
      (fImp domainForm (formulaAt (upVarMap (fun n => n)) a)))
  exact Prov.P_allE _ _ k hp

/-- Raw translated existential introduction by an HF variable witness. -/
theorem BProv_translate_exI_raw {G : List PA.Formula} {a : PA.Formula} {k : Nat}
    (h : BProv translatedPAAx (translateContext G)
      (rename (inst k)
        (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a)))) :
    BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.ex a)) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContext G)
    (fEx (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a)))
  exact Prov.P_exI _ _ k hp

/-- Raw translated existential elimination.

The branch premise is stated in the shifted HF context and proves the shifted
conclusion, exactly matching the generic set-theory natural-deduction rule.
The PA-level rule still needs the separate syntactic bridge that turns a PA
renamed context into this shifted translated context. -/
theorem BProv_translate_exE_raw {G : List PA.Formula} {a c : PA.Formula}
    (hex : BProv translatedPAAx (translateContext G)
      (translateFormula (PA.Formula.ex a)))
    (hbody : BProv translatedPAAx
      (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a) ::
        (translateContext G).map (rename Nat.succ))
      (rename Nat.succ (translateFormula c))) :
    BProv translatedPAAx (translateContext G) (translateFormula c) := by
  rcases hex with ⟨Le, hLe, hpe⟩
  rcases hbody with ⟨Lb, hLb, hpb⟩
  have hLbmap : Lb.map (rename Nat.succ) = Lb := by
    calc
      Lb.map (rename Nat.succ) = Lb.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (Sentences_translatedPAAx x (hLb x hx)) Nat.succ
      _ = Lb := by simp
  refine ⟨Le ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_exE _ (fAnd domainForm (formulaAt (upVarMap (fun n => n)) a))
      (translateFormula c)
    · apply Prov_weaken hpe
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · apply List.mem_cons.mpr
        apply Or.inr
        simp only [List.map_append, List.mem_append]
        apply Or.inl
        exact Or.inr (by simpa [hLbmap] using hx)
      · rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · apply List.mem_cons.mpr
          apply Or.inr
          simp only [List.map_append, List.mem_append]
          exact Or.inr hx

/-- Raw translated universal introduction under an explicit slot map. -/
theorem BProv_formulaAt_allI_raw {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula}
    (h : BProv translatedPAAx ((translateContextAt ρ G).map (rename Nat.succ))
      (fImp domainForm (formulaAt (upVarMap ρ) a))) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a)) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename Nat.succ) = L := by
    calc
      L.map (rename Nat.succ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (Sentences_translatedPAAx x (hL x hx)) Nat.succ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContextAt ρ G)
    (fAll (fImp domainForm (formulaAt (upVarMap ρ) a)))
  apply Prov.P_allI
  apply Prov_weaken hp
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Translated universal introduction in the PA proof-rule shape.

The premise is the recursive translation of PA's `allI` premise over
`G.map (PA.Formula.rename Nat.succ)`.  The theorem inserts the relativizing
domain antecedent and uses the context-renaming bridge to reach the raw HF
rule. -/
theorem BProv_formulaAt_allI {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula}
    (h : BProv translatedPAAx
      (translateContextAt (upVarMap ρ) (G.map (PA.Formula.rename Nat.succ)))
      (formulaAt (upVarMap ρ) a)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a)) := by
  have hshift : BProv translatedPAAx
      ((translateContextAt ρ G).map (rename Nat.succ))
      (formulaAt (upVarMap ρ) a) := by
    simpa [translateContextAt_rename_succ_upVarMap] using h
  exact BProv_formulaAt_allI_raw
    (BProv_impI (BProv_context_cons hshift))

/-- Translated universal introduction while carrying explicit domain
assumptions for the currently available PA variables. -/
theorem BProv_formulaAt_allI_domainContext {ρ : Nat → Nat}
    {n : Nat} {G : List PA.Formula} {a : PA.Formula}
    (h : BProv translatedPAAx
      (domainContextAt (upVarMap ρ) (n+1) ++
        translateContextAt (upVarMap ρ) (G.map (PA.Formula.rename Nat.succ)))
      (formulaAt (upVarMap ρ) a)) :
    BProv translatedPAAx
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a)) := by
  have hshift : BProv translatedPAAx
      (domainForm ::
        ((domainContextAt ρ n ++ translateContextAt ρ G).map
          (rename Nat.succ)))
      (formulaAt (upVarMap ρ) a) := by
    simpa [domainContextAt_upVarMap_succ,
      translateContextAt_rename_succ_upVarMap, List.map_append,
      List.cons_append] using h
  change BProv translatedPAAx
    (domainContextAt ρ n ++ translateContextAt ρ G)
    (fAll (fImp domainForm (formulaAt (upVarMap ρ) a)))
  exact BProv_allI_of_sentences Sentences_translatedPAAx
    (BProv_impI hshift)

/-- Universal introduction under explicit PA-domain assumptions for any
sentence theory of HF formulas. -/
theorem BProv_formulaAt_allI_domainContext_of_sentences {B : Form → Prop}
    (hB : Sentences B) {ρ : Nat → Nat}
    {n : Nat} {G : List PA.Formula} {a : PA.Formula}
    (h : BProv B
      (domainContextAt (upVarMap ρ) (n+1) ++
        translateContextAt (upVarMap ρ) (G.map (PA.Formula.rename Nat.succ)))
      (formulaAt (upVarMap ρ) a)) :
    BProv B
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a)) := by
  have hshift : BProv B
      (domainForm ::
        ((domainContextAt ρ n ++ translateContextAt ρ G).map
          (rename Nat.succ)))
      (formulaAt (upVarMap ρ) a) := by
    simpa [domainContextAt_upVarMap_succ,
      translateContextAt_rename_succ_upVarMap, List.map_append,
      List.cons_append] using h
  change BProv B
    (domainContextAt ρ n ++ translateContextAt ρ G)
    (fAll (fImp domainForm (formulaAt (upVarMap ρ) a)))
  exact BProv_allI_of_sentences hB (BProv_impI hshift)

/-- Raw translated universal elimination by an HF variable instance under an
explicit slot map. -/
theorem BProv_formulaAt_allE_raw {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula} {k : Nat}
    (h : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a))) :
    BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst k)
        (fImp domainForm (formulaAt (upVarMap ρ) a))) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContextAt ρ G)
    (rename (inst k)
      (fImp domainForm (formulaAt (upVarMap ρ) a)))
  exact Prov.P_allE _ _ k hp

/-- Translated universal elimination when PA instantiates by a variable.

The domain premise is explicit: because PA quantifiers are interpreted by the
finite-ordinal domain in HF, using a free PA variable as a witness requires a
proof that the corresponding HF slot is in the interpreted domain. -/
theorem BProv_formulaAt_allE_var {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula} {k : Nat}
    (hall : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a)))
    (hdom : BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst (ρ k)) domainForm)) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a)) := by
  have himp : BProv translatedPAAx (translateContextAt ρ G)
      (fImp (rename (inst (ρ k)) domainForm)
        (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a))) := by
    simpa [rename] using
      (BProv_formulaAt_allE_raw (ρ := ρ) (G := G) (a := a) (k := ρ k) hall)
  have hbody : BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a)) :=
    BProv_mp translatedPAAx (translateContextAt ρ G)
      (rename (inst (ρ k)) domainForm)
      (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a)) himp hdom
  rwa [formulaAt_subst_instTerm_var]

/-- Translated universal elimination at an arbitrary HF slot.

The slot is not assumed to come from a PA variable; the caller supplies the
domain proof for the concrete slot used as the quantified value. -/
theorem BProv_formulaAt_allE_slot_context {Γ : List Form} {ρ : Nat → Nat}
    {a : PA.Formula} {k : Nat}
    (hall : BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.all a)))
    (hdom : BProv translatedPAAx Γ
      (rename (inst k) domainForm)) :
    BProv translatedPAAx Γ
      (rename (inst k) (formulaAt (upVarMap ρ) a)) := by
  have himp : BProv translatedPAAx Γ
      (fImp (rename (inst k) domainForm)
        (rename (inst k) (formulaAt (upVarMap ρ) a))) := by
    simpa [formulaAt, rename] using
      (BProv_allE (B := translatedPAAx) (G := Γ)
        (a := fImp domainForm (formulaAt (upVarMap ρ) a))
        (k := k) hall)
  exact BProv_mp translatedPAAx Γ
    (rename (inst k) domainForm)
    (rename (inst k) (formulaAt (upVarMap ρ) a)) himp hdom

/-- Equality of HF slots transports a translated PA body instantiated at one
slot to the same body instantiated at the other slot. -/
theorem BProv_formulaAt_slot_eqElim_context {Γ : List Form} {ρ : Nat → Nat}
    {a : PA.Formula} {i j : Nat}
    (heq : BProv translatedPAAx Γ (fEq i j))
    (hbody : BProv translatedPAAx Γ
      (rename (inst i) (formulaAt (upVarMap ρ) a))) :
    BProv translatedPAAx Γ
      (rename (inst j) (formulaAt (upVarMap ρ) a)) :=
  BProv_eqElim heq hbody

/-- Universal elimination may instantiate at one explicit domain slot and then
transport the resulting body across an equality of HF slots. -/
theorem BProv_formulaAt_allE_equal_slot_context {Γ : List Form}
    {ρ : Nat → Nat} {a : PA.Formula} {i j : Nat}
    (hall : BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.all a)))
    (hdom : BProv translatedPAAx Γ (rename (inst i) domainForm))
    (heq : BProv translatedPAAx Γ (fEq i j)) :
    BProv translatedPAAx Γ
      (rename (inst j) (formulaAt (upVarMap ρ) a)) :=
  BProv_formulaAt_slot_eqElim_context (ρ := ρ) (a := a) heq
    (BProv_formulaAt_allE_slot_context (ρ := ρ) (a := a)
      (k := i) hall hdom)

/-- Translated universal elimination by a PA variable over an arbitrary HF
context, with the variable-domain proof kept explicit. -/
theorem BProv_formulaAt_allE_var_context {Γ : List Form} {ρ : Nat → Nat}
    {a : PA.Formula} {k : Nat}
    (hall : BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.all a)))
    (hdom : BProv translatedPAAx Γ
      (rename (inst (ρ k)) domainForm)) :
    BProv translatedPAAx Γ
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a)) := by
  have hbody : BProv translatedPAAx Γ
      (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a)) :=
    BProv_formulaAt_allE_slot_context (ρ := ρ) (a := a)
      (k := ρ k) hall hdom
  rwa [formulaAt_subst_instTerm_var]

/-- Translated universal elimination by a PA variable available in the explicit
domain context. -/
theorem BProv_formulaAt_allE_var_domainContext {ρ : Nat → Nat}
    {n : Nat} {G : List PA.Formula} {a : PA.Formula} {k : Nat}
    (hk : k < n)
    (hall : BProv translatedPAAx
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.all a))) :
    BProv translatedPAAx
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a)) :=
  BProv_formulaAt_allE_var_context hall
    (BProv_domainContextAt_var (ρ := ρ) (n := n) (k := k)
      (G := translateContextAt ρ G) hk)

/-- Raw translated existential introduction by an HF variable witness under an
explicit slot map. -/
theorem BProv_formulaAt_exI_raw {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula} {k : Nat}
    (h : BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst k)
        (fAnd domainForm (formulaAt (upVarMap ρ) a)))) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  change Prov (L ++ translateContextAt ρ G)
    (fEx (fAnd domainForm (formulaAt (upVarMap ρ) a)))
  exact Prov.P_exI _ _ k hp

/-- Translated existential introduction when PA supplies a variable witness.

As for universal elimination, the domain proof is a separate premise rather
than being hidden in the translation of formulas or contexts. -/
theorem BProv_formulaAt_exI_var {ρ : Nat → Nat} {G : List PA.Formula}
    {a : PA.Formula} {k : Nat}
    (hdom : BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst (ρ k)) domainForm))
    (hbody : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a))) :
    BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)) := by
  have hbody' : BProv translatedPAAx (translateContextAt ρ G)
      (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a)) := by
    rwa [formulaAt_subst_instTerm_var] at hbody
  have hand : BProv translatedPAAx (translateContextAt ρ G)
      (fAnd (rename (inst (ρ k)) domainForm)
        (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a))) :=
    BProv_andI hdom hbody'
  exact BProv_formulaAt_exI_raw (ρ := ρ) (G := G) (a := a) (k := ρ k)
    (by simpa [rename] using hand)

/-- Translated existential introduction at an arbitrary HF slot.

This is the slot-level companion to `BProv_formulaAt_allE_slot_context`: the
witness slot and its domain proof are explicit, independent of whether the
slot is syntactically assigned to a PA variable. -/
theorem BProv_formulaAt_exI_slot_context {Γ : List Form} {ρ : Nat → Nat}
    {a : PA.Formula} {k : Nat}
    (hdom : BProv translatedPAAx Γ
      (rename (inst k) domainForm))
    (hbody : BProv translatedPAAx Γ
      (rename (inst k) (formulaAt (upVarMap ρ) a))) :
    BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.ex a)) := by
  have hand : BProv translatedPAAx Γ
      (fAnd (rename (inst k) domainForm)
        (rename (inst k) (formulaAt (upVarMap ρ) a))) :=
    BProv_andI hdom hbody
  have hex : BProv translatedPAAx Γ
      (fEx (fAnd domainForm (formulaAt (upVarMap ρ) a))) :=
    BProv_exI (B := translatedPAAx) (G := Γ)
      (a := fAnd domainForm (formulaAt (upVarMap ρ) a))
      (k := k) (by simpa [rename] using hand)
  simpa [formulaAt] using hex

/-- Existential introduction may transport a translated PA body across an
equality of HF slots before using the explicit domain witness slot. -/
theorem BProv_formulaAt_exI_equal_slot_context {Γ : List Form}
    {ρ : Nat → Nat} {a : PA.Formula} {i j : Nat}
    (hdom : BProv translatedPAAx Γ (rename (inst j) domainForm))
    (heq : BProv translatedPAAx Γ (fEq i j))
    (hbody : BProv translatedPAAx Γ
      (rename (inst i) (formulaAt (upVarMap ρ) a))) :
    BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.ex a)) :=
  BProv_formulaAt_exI_slot_context (ρ := ρ) (a := a) (k := j)
    hdom (BProv_formulaAt_slot_eqElim_context (ρ := ρ) (a := a)
      heq hbody)

/-- Translated existential introduction by a PA variable over an arbitrary HF
context, with the variable-domain proof kept explicit. -/
theorem BProv_formulaAt_exI_var_context {Γ : List Form} {ρ : Nat → Nat}
    {a : PA.Formula} {k : Nat}
    (hdom : BProv translatedPAAx Γ
      (rename (inst (ρ k)) domainForm))
    (hbody : BProv translatedPAAx Γ
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a))) :
    BProv translatedPAAx Γ
      (formulaAt ρ (PA.Formula.ex a)) := by
  have hbodySlot : BProv translatedPAAx Γ
      (rename (inst (ρ k)) (formulaAt (upVarMap ρ) a)) := by
    rwa [formulaAt_subst_instTerm_var] at hbody
  exact BProv_formulaAt_exI_slot_context (ρ := ρ) (a := a)
    (k := ρ k) hdom hbodySlot

/-- Translated existential introduction by a PA variable available in the
explicit domain context. -/
theorem BProv_formulaAt_exI_var_domainContext {ρ : Nat → Nat}
    {n : Nat} {G : List PA.Formula} {a : PA.Formula} {k : Nat}
    (hk : k < n)
    (hbody : BProv translatedPAAx
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ
        (PA.Formula.subst (PA.Formula.instTerm (PA.Term.var k)) a))) :
    BProv translatedPAAx
      (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)) :=
  BProv_formulaAt_exI_var_context
    (BProv_domainContextAt_var (ρ := ρ) (n := n) (k := k)
      (G := translateContextAt ρ G) hk)
    hbody

/-- Raw translated existential elimination under an explicit slot map. -/
theorem BProv_formulaAt_exE_raw {ρ : Nat → Nat} {G : List PA.Formula}
    {a c : PA.Formula}
    (hex : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)))
    (hbody : BProv translatedPAAx
      (fAnd domainForm (formulaAt (upVarMap ρ) a) ::
        (translateContextAt ρ G).map (rename Nat.succ))
      (rename Nat.succ (formulaAt ρ c))) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ c) := by
  rcases hex with ⟨Le, hLe, hpe⟩
  rcases hbody with ⟨Lb, hLb, hpb⟩
  have hLbmap : Lb.map (rename Nat.succ) = Lb := by
    calc
      Lb.map (rename Nat.succ) = Lb.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (Sentences_translatedPAAx x (hLb x hx)) Nat.succ
      _ = Lb := by simp
  refine ⟨Le ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_exE _ (fAnd domainForm (formulaAt (upVarMap ρ) a))
      (formulaAt ρ c)
    · apply Prov_weaken hpe
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · apply List.mem_cons.mpr
        apply Or.inr
        simp only [List.map_append, List.mem_append]
        apply Or.inl
        exact Or.inr (by simpa [hLbmap] using hx)
      · rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · apply List.mem_cons.mpr
          apply Or.inr
          simp only [List.map_append, List.mem_append]
          exact Or.inr hx

/-- Translated existential elimination in the PA proof-rule shape.

The branch premise is the recursive translation of PA's `exE` branch over
`a :: G.map (PA.Formula.rename Nat.succ)`.  The raw HF rule expects the branch
assumption to include the relativizing domain conjunct, so the proof cuts the
plain translated assumption out of that conjunction before applying the raw
rule. -/
theorem BProv_formulaAt_exE {ρ : Nat → Nat} {G : List PA.Formula}
    {a c : PA.Formula}
    (hex : BProv translatedPAAx (translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)))
    (hbody : BProv translatedPAAx
      (formulaAt (upVarMap ρ) a ::
        translateContextAt (upVarMap ρ)
          (G.map (PA.Formula.rename Nat.succ)))
      (formulaAt (upVarMap ρ) (PA.Formula.rename Nat.succ c))) :
    BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ c) := by
  let body : Form := formulaAt (upVarMap ρ) a
  let shiftedContext : List Form :=
    (translateContextAt ρ G).map (rename Nat.succ)
  let rawAssumption : Form := fAnd domainForm body
  let rawContext : List Form := rawAssumption :: shiftedContext
  have hbodyShift : BProv translatedPAAx (body :: shiftedContext)
      (rename Nat.succ (formulaAt ρ c)) := by
    simpa [body, shiftedContext, translateContextAt_rename_succ_upVarMap,
      formulaAt_rename_succ_upVarMap] using hbody
  have hraw : BProv translatedPAAx rawContext
      (rename Nat.succ (formulaAt ρ c)) := by
    apply BProv_lift hbodyShift
    · intro b hb
      exact BProv_ax (G := rawContext) hb
    · intro g hg
      rw [List.mem_cons] at hg
      rcases hg with hg | hg
      · subst g
        exact BProv_of_Prov (B := translatedPAAx)
          (Prov.P_andE2 rawContext domainForm body
            (Prov.P_ass rawContext rawAssumption (by simp [rawContext])))
      · exact BProv_of_Prov (B := translatedPAAx)
          (Prov.P_ass rawContext g (by simp [rawContext, shiftedContext, hg]))
  exact BProv_formulaAt_exE_raw hex hraw

/-- Existential elimination under explicit PA-domain assumptions for any
sentence theory of HF formulas. -/
theorem BProv_formulaAt_exE_domainContext_of_sentences {B : Form → Prop}
    (hB : Sentences B) {ρ : Nat → Nat} {n : Nat}
    {G : List PA.Formula} {a c : PA.Formula}
    (hex : BProv B (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ (PA.Formula.ex a)))
    (hbody : BProv B
      (domainContextAt (upVarMap ρ) (n+1) ++
        translateContextAt (upVarMap ρ)
          (a :: G.map (PA.Formula.rename Nat.succ)))
      (formulaAt (upVarMap ρ) (PA.Formula.rename Nat.succ c))) :
    BProv B (domainContextAt ρ n ++ translateContextAt ρ G)
      (formulaAt ρ c) := by
  let body : Form := formulaAt (upVarMap ρ) a
  let shiftedDomain : List Form :=
    (domainContextAt ρ n).map (rename Nat.succ)
  let shiftedContext : List Form :=
    translateContextAt (upVarMap ρ) (G.map (PA.Formula.rename Nat.succ))
  let rawAssumption : Form := fAnd domainForm body
  let rawContext : List Form := rawAssumption ::
    ((domainContextAt ρ n ++ translateContextAt ρ G).map (rename Nat.succ))
  have hbodyShift : BProv B
      (domainForm :: (shiftedDomain ++ body :: shiftedContext))
      (rename Nat.succ (formulaAt ρ c)) := by
    simpa [body, shiftedDomain, shiftedContext,
      domainContextAt_upVarMap_succ,
      formulaAt_rename_succ_upVarMap, translateContextAt, List.map_append,
      List.cons_append, Function.comp_apply] using hbody
  have hrawAssumption : BProv B rawContext rawAssumption :=
    BProv_of_Prov (B := B)
      (Prov.P_ass rawContext rawAssumption (by simp [rawContext]))
  have hraw : BProv B rawContext (rename Nat.succ (formulaAt ρ c)) := by
    apply BProv_lift hbodyShift
    · intro b hb
      exact BProv_ax (G := rawContext) hb
    · intro g hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with hg | hg
      · subst g
        exact BProv_andE1 hrawAssumption
      · rcases hg with hgDomain | hg
        · exact BProv_of_Prov (B := B)
            (Prov.P_ass rawContext g (by
              simp [rawContext, shiftedDomain, List.mem_append, hgDomain]))
        · rcases hg with hg | hgContext
          · subst g
            exact BProv_andE2 hrawAssumption
          · exact BProv_of_Prov (B := B)
              (Prov.P_ass rawContext g (by
                have hgContext' :
                    g ∈ (translateContextAt ρ G).map (rename Nat.succ) := by
                  simpa [shiftedContext,
                    translateContextAt_rename_succ_upVarMap] using hgContext
                simp [rawContext, List.mem_append, hgContext']))
  exact BProv_exE_of_sentences hB hex hraw

/-- Structural PA-proof translation into the explicit-slot PA-in-HF
translation, with the genuinely term-sensitive proof rules left as explicit
parameters.

The four hypotheses are exactly the rules whose PA version mentions arbitrary
terms.  This theorem discharges the remaining propositional and quantifier
plumbing once and for all without hiding term-totality proofs in a definition. -/
theorem BProv_formulaAt_of_Prov_with_term_rules
    (hAllE : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {a : PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.all a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)))
    (hExI : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {a : PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.ex a)))
    (hEqRefl : ∀ {ρ : Nat → Nat} {G : List PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.eq t t)))
    (hEqElim : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {s t : PA.Term} {a : PA.Formula},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.eq s t)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm s) a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)))
    {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.Prov G phi) :
    ∀ ρ : Nat → Nat,
      BProv translatedPAAx (translateContextAt ρ G) (formulaAt ρ phi) := by
  induction h with
  | P_ass G a hin =>
      intro ρ
      exact BProv_formulaAt_ass (ρ := ρ) hin
  | P_impI G a b _ ih =>
      intro ρ
      exact BProv_formulaAt_impI (ρ := ρ) (ih ρ)
  | P_impE G a b _ _ ihab iha =>
      intro ρ
      exact BProv_formulaAt_impE (ρ := ρ) (ihab ρ) (iha ρ)
  | P_botE G a _ ih =>
      intro ρ
      exact BProv_formulaAt_botE (ρ := ρ) (ih ρ)
  | P_lem G a =>
      intro ρ
      exact BProv_formulaAt_lem ρ G a
  | P_andI G a b _ _ iha ihb =>
      intro ρ
      exact BProv_formulaAt_andI (ρ := ρ) (iha ρ) (ihb ρ)
  | P_andE1 G a b _ ih =>
      intro ρ
      exact BProv_formulaAt_andE1 (ρ := ρ) (ih ρ)
  | P_andE2 G a b _ ih =>
      intro ρ
      exact BProv_formulaAt_andE2 (ρ := ρ) (ih ρ)
  | P_orI1 G a b _ ih =>
      intro ρ
      exact BProv_formulaAt_orI1 (ρ := ρ) (a := a) (b := b) (ih ρ)
  | P_orI2 G a b _ ih =>
      intro ρ
      exact BProv_formulaAt_orI2 (ρ := ρ) (a := a) (b := b) (ih ρ)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro ρ
      exact BProv_formulaAt_orE (ρ := ρ) (ihor ρ) (iha ρ) (ihb ρ)
  | P_allI G a _ ih =>
      intro ρ
      exact BProv_formulaAt_allI (ρ := ρ) (ih (upVarMap ρ))
  | P_allE G a t _ ih =>
      intro ρ
      exact hAllE (ih ρ)
  | P_exI G a t _ ih =>
      intro ρ
      exact hExI (ih ρ)
  | P_exE G a c _ _ ihex ihbody =>
      intro ρ
      exact BProv_formulaAt_exE (ρ := ρ) (ihex ρ) (ihbody (upVarMap ρ))
  | P_eqRefl G t =>
      intro ρ
      exact hEqRefl
  | P_eqElim G s t a _ _ iheq iha =>
      intro ρ
      exact hEqElim (iheq ρ) (iha ρ)

/-- Structural PA-proof translation directly into finite HF, carrying explicit
domain assumptions for a finite prefix of PA variables.

The existentially returned bound is proof-structural: it is large enough for
every arbitrary-term rule used in the PA derivation.  The translated context is
not strengthened by definition; the domain assumptions remain visible in the
finite HF context. -/
theorem BProv_HFFin_formulaAt_of_Prov_domainContext
    {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.Prov G phi) :
    ∃ n, ∀ ρ : Nat → Nat,
      BProv HFFinAx_s
        (domainContextAt ρ n ++ translateContextAt ρ G)
        (formulaAt ρ phi) := by
  induction h with
  | P_ass G a hin =>
      refine ⟨0, ?_⟩
      intro ρ
      exact BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass (domainContextAt ρ 0 ++ translateContextAt ρ G)
          (formulaAt ρ a) (by
            simp [domainContextAt]
            exact mem_translateContextAt_of_mem (ρ := ρ) hin))
  | P_impI G a b _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      have hbody : BProv HFFinAx_s
          (domainContextAt ρ n ++ formulaAt ρ a :: translateContextAt ρ G)
          (formulaAt ρ b) := by
        simpa [translateContextAt] using ih ρ
      simpa [formulaAt] using
        (BProv_impI_after_prefix
          (B := HFFinAx_s) (Γ := domainContextAt ρ n)
          (Δ := translateContextAt ρ G)
          (a := formulaAt ρ a) (b := formulaAt ρ b) hbody)
  | P_impE G a b _ _ ihab iha =>
      rcases ihab with ⟨nab, ihab⟩
      rcases iha with ⟨na, iha⟩
      refine ⟨nab + na, ?_⟩
      intro ρ
      have hab' : BProv HFFinAx_s
          (domainContextAt ρ (nab + na) ++ translateContextAt ρ G)
          (formulaAt ρ (PA.Formula.imp a b)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := nab)
          (m := nab + na) (by omega) (ihab ρ)
      have ha' : BProv HFFinAx_s
          (domainContextAt ρ (nab + na) ++ translateContextAt ρ G)
          (formulaAt ρ a) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := na)
          (m := nab + na) (by omega) (iha ρ)
      exact BProv_mp HFFinAx_s
        (domainContextAt ρ (nab + na) ++ translateContextAt ρ G)
        (formulaAt ρ a) (formulaAt ρ b)
        (by simpa [formulaAt] using hab') ha'
  | P_botE G a _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      exact BProv_botE (B := HFFinAx_s) (a := formulaAt ρ a) (ih ρ)
  | P_lem G a =>
      refine ⟨0, ?_⟩
      intro ρ
      change BProv HFFinAx_s
        (domainContextAt ρ 0 ++ translateContextAt ρ G)
        (fOr (formulaAt ρ a) (fImp (formulaAt ρ a) fBot))
      simpa [domainContextAt] using
        (BProv_of_Prov (B := HFFinAx_s)
          (Prov.P_lem (translateContextAt ρ G) (formulaAt ρ a)))
  | P_andI G a b _ _ iha ihb =>
      rcases iha with ⟨na, iha⟩
      rcases ihb with ⟨nb, ihb⟩
      refine ⟨na + nb, ?_⟩
      intro ρ
      have ha' : BProv HFFinAx_s
          (domainContextAt ρ (na + nb) ++ translateContextAt ρ G)
          (formulaAt ρ a) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := na)
          (m := na + nb) (by omega) (iha ρ)
      have hb' : BProv HFFinAx_s
          (domainContextAt ρ (na + nb) ++ translateContextAt ρ G)
          (formulaAt ρ b) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := nb)
          (m := na + nb) (by omega) (ihb ρ)
      simpa [formulaAt] using BProv_andI ha' hb'
  | P_andE1 G a b _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      exact BProv_andE1 (a := formulaAt ρ a) (b := formulaAt ρ b)
        (by simpa [formulaAt] using ih ρ)
  | P_andE2 G a b _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      exact BProv_andE2 (a := formulaAt ρ a) (b := formulaAt ρ b)
        (by simpa [formulaAt] using ih ρ)
  | P_orI1 G a b _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      simpa [formulaAt] using
        (BProv_orI1 (B := HFFinAx_s) (b := formulaAt ρ b) (ih ρ))
  | P_orI2 G a b _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      simpa [formulaAt] using
        (BProv_orI2 (B := HFFinAx_s) (a := formulaAt ρ a) (ih ρ))
  | P_orE G a b c _ _ _ ihor iha ihb =>
      rcases ihor with ⟨no, ihor⟩
      rcases iha with ⟨na, iha⟩
      rcases ihb with ⟨nb, ihb⟩
      refine ⟨no + na + nb, ?_⟩
      intro ρ
      have hor' : BProv HFFinAx_s
          (domainContextAt ρ (no + na + nb) ++ translateContextAt ρ G)
          (formulaAt ρ (PA.Formula.or a b)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := no)
          (m := no + na + nb) (by omega) (ihor ρ)
      have ha' : BProv HFFinAx_s
          (domainContextAt ρ (no + na + nb) ++
            formulaAt ρ a :: translateContextAt ρ G)
          (formulaAt ρ c) := by
        simpa [translateContextAt] using
          (BProv_mono_domainContextAt (ρ := ρ) (n := na)
            (m := no + na + nb) (by omega) (iha ρ))
      have hb' : BProv HFFinAx_s
          (domainContextAt ρ (no + na + nb) ++
            formulaAt ρ b :: translateContextAt ρ G)
          (formulaAt ρ c) := by
        simpa [translateContextAt] using
          (BProv_mono_domainContextAt (ρ := ρ) (n := nb)
            (m := no + na + nb) (by omega) (ihb ρ))
      exact BProv_orE_after_prefix
        (B := HFFinAx_s) (Γ := domainContextAt ρ (no + na + nb))
        (Δ := translateContextAt ρ G)
        (a := formulaAt ρ a) (b := formulaAt ρ b)
        (c := formulaAt ρ c) (by simpa [formulaAt] using hor') ha' hb'
  | P_allI G a _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n, ?_⟩
      intro ρ
      have hbody : BProv HFFinAx_s
          (domainContextAt (upVarMap ρ) (n+1) ++
            translateContextAt (upVarMap ρ)
              (G.map (PA.Formula.rename Nat.succ)))
          (formulaAt (upVarMap ρ) a) :=
        BProv_mono_domainContextAt (ρ := upVarMap ρ) (n := n)
          (m := n+1) (by omega) (ih (upVarMap ρ))
      exact BProv_formulaAt_allI_domainContext_of_sentences
        Sentences_HFFin hbody
  | P_allE G a t _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n + t.bound, ?_⟩
      intro ρ
      have hall : BProv HFFinAx_s
          (domainContextAt ρ (n + t.bound) ++ translateContextAt ρ G)
          (formulaAt ρ (PA.Formula.all a)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := n)
          (m := n + t.bound) (by omega) (ih ρ)
      exact BProv_HFFin_formulaAt_allE_term_domainContext_le
        (G := translateContextAt ρ G) ρ a t (by omega) hall
  | P_exI G a t _ ih =>
      rcases ih with ⟨n, ih⟩
      refine ⟨n + t.bound, ?_⟩
      intro ρ
      have hbody : BProv HFFinAx_s
          (domainContextAt ρ (n + t.bound) ++ translateContextAt ρ G)
          (formulaAt ρ
            (PA.Formula.subst (PA.Formula.instTerm t) a)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := n)
          (m := n + t.bound) (by omega) (ih ρ)
      exact BProv_HFFin_formulaAt_exI_term_domainContext_le
        (G := translateContextAt ρ G) ρ a t (by omega) hbody
  | P_exE G a c _ _ ihex ihbody =>
      rcases ihex with ⟨nex, ihex⟩
      rcases ihbody with ⟨nbody, ihbody⟩
      refine ⟨nex + nbody, ?_⟩
      intro ρ
      have hex' : BProv HFFinAx_s
          (domainContextAt ρ (nex + nbody) ++ translateContextAt ρ G)
          (formulaAt ρ (PA.Formula.ex a)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := nex)
          (m := nex + nbody) (by omega) (ihex ρ)
      have hbody' : BProv HFFinAx_s
          (domainContextAt (upVarMap ρ) (nex + nbody + 1) ++
            translateContextAt (upVarMap ρ)
              (a :: G.map (PA.Formula.rename Nat.succ)))
          (formulaAt (upVarMap ρ) (PA.Formula.rename Nat.succ c)) :=
        BProv_mono_domainContextAt (ρ := upVarMap ρ) (n := nbody)
          (m := nex + nbody + 1) (by omega) (ihbody (upVarMap ρ))
      exact BProv_formulaAt_exE_domainContext_of_sentences
        Sentences_HFFin hex' hbody'
  | P_eqRefl G t =>
      refine ⟨t.bound, ?_⟩
      intro ρ
      exact BProv_HFFin_formulaAt_eqRefl_domainContext_le
        (G := translateContextAt ρ G) ρ t (by omega)
  | P_eqElim G s t a _ _ iheq iha =>
      rcases iheq with ⟨neq, iheq⟩
      rcases iha with ⟨na, iha⟩
      refine ⟨neq + na + s.bound + t.bound, ?_⟩
      intro ρ
      have heq' : BProv HFFinAx_s
          (domainContextAt ρ (neq + na + s.bound + t.bound) ++
            translateContextAt ρ G)
          (formulaAt ρ (PA.Formula.eq s t)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := neq)
          (m := neq + na + s.bound + t.bound) (by omega) (iheq ρ)
      have ha' : BProv HFFinAx_s
          (domainContextAt ρ (neq + na + s.bound + t.bound) ++
            translateContextAt ρ G)
          (formulaAt ρ
            (PA.Formula.subst (PA.Formula.instTerm s) a)) :=
        BProv_mono_domainContextAt (ρ := ρ) (n := na)
          (m := neq + na + s.bound + t.bound) (by omega) (iha ρ)
      exact BProv_HFFin_formulaAt_eqElim_term_domainContext_le
        (G := translateContextAt ρ G) ρ s t a
        (by omega) (by omega) heq' ha'

/-- Relative PA proofs translate once the term-sensitive PA rules have been
supplied explicitly.

This is the `BProv`-level companion to
`BProv_formulaAt_of_Prov_with_term_rules`: finite PA axiom lists are translated
and then cut away using `BProv_formulaAt_ax`, while the four arbitrary-term
rules remain visible premises. -/
theorem BProv_formulaAt_of_PA_BProv_with_term_rules
    (hAllE : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {a : PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.all a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)))
    (hExI : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {a : PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.ex a)))
    (hEqRefl : ∀ {ρ : Nat → Nat} {G : List PA.Formula} {t : PA.Term},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.eq t t)))
    (hEqElim : ∀ {ρ : Nat → Nat} {G : List PA.Formula}
      {s t : PA.Term} {a : PA.Formula},
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ (PA.Formula.eq s t)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm s) a)) →
      BProv translatedPAAx (translateContextAt ρ G)
        (formulaAt ρ
          (PA.Formula.subst (PA.Formula.instTerm t) a)))
    {phi : PA.Formula}
    (h : PA.Formula.BProv PA.Formula.Ax_s [] phi) :
    ∀ ρ : Nat → Nat,
      BProv translatedPAAx [] (formulaAt ρ phi) := by
  rcases h with ⟨L, hL, hp⟩
  intro ρ
  have htranslated : BProv translatedPAAx
      (translateContextAt ρ L) (formulaAt ρ phi) := by
    simpa using BProv_formulaAt_of_Prov_with_term_rules
      (hAllE := @hAllE) (hExI := @hExI)
      (hEqRefl := @hEqRefl) (hEqElim := @hEqElim)
      hp ρ
  exact BProv_cut htranslated (fun g hg => by
    simp only [translateContextAt, List.mem_map] at hg
    rcases hg with ⟨psi, hpsi, rfl⟩
    exact BProv_formulaAt_ax (ρ := ρ) (hL psi hpsi))

/-- Relative PA proofs translate directly into finite HF while carrying an
explicit PA-domain prefix.

Finite PA axiom uses are cut away using their already-established HFFin
translations; ordinary PA context assumptions remain visible as the translated
finite context. -/
theorem BProv_HFFin_formulaAt_of_PA_BProv_domainContext
    {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.BProv PA.Formula.Ax_s G phi) :
    ∃ n, ∀ ρ : Nat → Nat,
      BProv HFFinAx_s
        (domainContextAt ρ n ++ translateContextAt ρ G)
        (formulaAt ρ phi) := by
  rcases h with ⟨L, hL, hp⟩
  rcases BProv_HFFin_formulaAt_of_Prov_domainContext hp with
    ⟨n, htranslated⟩
  refine ⟨n, ?_⟩
  intro ρ
  exact BProv_cut (htranslated ρ) (fun g hg => by
    rw [List.mem_append] at hg
    rcases hg with hgDomain | hgTranslated
    · exact BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass
          (domainContextAt ρ n ++ translateContextAt ρ G)
          g (List.mem_append.mpr (Or.inl hgDomain)))
    · simp only [translateContextAt, List.map_append, List.mem_append,
        List.mem_map] at hgTranslated
      rcases hgTranslated with hgAx | hgCtx
      · rcases hgAx with ⟨psi, hpsi, rfl⟩
        have haxTranslated : BProv translatedPAAx [] (formulaAt ρ psi) :=
          BProv_formulaAt_ax (ρ := ρ) (hL psi hpsi)
        have haxHF : BProv HFFinAx_s [] (formulaAt ρ psi) :=
          BProv_lift haxTranslated
            (fun _ hg => by
              rcases hg with ⟨theta, htheta, rfl⟩
              exact BProv_HFFin_translated_PA_axiom htheta)
            (fun _ hg => nomatch hg)
        exact BProv_mono HFFinAx_s []
          (domainContextAt ρ n ++ translateContextAt ρ G)
          (formulaAt ρ psi) (fun _ hnil => by cases hnil) haxHF
      · rcases hgCtx with ⟨psi, hpsi, rfl⟩
        exact BProv_of_Prov (B := HFFinAx_s)
          (Prov.P_ass
            (domainContextAt ρ n ++ translateContextAt ρ G)
            (formulaAt ρ psi)
            (List.mem_append.mpr
              (Or.inr (mem_translateContextAt_of_mem (ρ := ρ) hpsi)))))

/-- Closed PA theorems translate to finite HF theorems.

The relative translator above keeps an explicit finite PA-domain prefix.  For a
closed PA theorem, that prefix is discharged semantically: in any model of
`HFFinAx_s`, the chosen HF empty object is ordinal-like, so a constant-empty
assignment satisfies every formula in the prefix; sentence invariance then
moves the conclusion back to the arbitrary assignment required by
completeness. -/
theorem BProv_HFFin_translateFormula_of_PA_BProv {phi : PA.Formula}
    (hphi : PA.Formula.Sentence phi)
    (h : PA.Formula.BProv PA.Formula.Ax_s [] phi) :
    BProv HFFinAx_s [] (translateFormula phi) := by
  rcases BProv_HFFin_formulaAt_of_PA_BProv_domainContext h with
    ⟨n, htranslated⟩
  apply completeness_inf HFFinAx_s
  · exact Sentences_HFFin
  · exact translateFormula_sentence_of_PA_sentence phi hphi
  · intro Dom mem v hHF
    let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    let e0 : Nat → Dom := fun _ => M.empty
    have hEmptyOrd : OrdinalLike mem M.empty := by
      change OrdinalLike M.mem M.empty
      exact FirstOrderAdjunctionModel.ordinalLike_empty
        M.toFirstOrderAdjunctionModel
    have hdomain :
        ∀ g, g ∈ domainContextAt (fun k : Nat => k) n →
          Sat mem e0 g :=
      Sat_domainContextAt_of_ordinalLike
        (ρ := fun k : Nat => k) (n := n) (e := e0)
        (fun _ _ => hEmptyOrd)
    have hcontext :
        ∀ g,
          g ∈ domainContextAt (fun k : Nat => k) n ++
              translateContextAt (fun k : Nat => k) [] →
          Sat mem e0 g := by
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hdomain g hg
      · simp [translateContextAt] at hg
    have hHF_e0 : ∀ g, HFFinAx_s g → Sat mem e0 g := by
      intro g hg
      exact (Sat_sentence_inv g (Sentences_HFFin g hg) v e0).mp
        (hHF g hg)
    have hsatFormulaAt :
        Sat mem e0 (formulaAt (fun k : Nat => k) phi) :=
      soundness_BProv (htranslated (fun k : Nat => k)) e0 hHF_e0
        hcontext
    have hsatTranslate :
        Sat mem e0 (translateFormula phi) := by
      simpa [formulaAt_eq_translateFormula_of_PA_sentence phi
        (fun k : Nat => k) hphi] using hsatFormulaAt
    exact (Sat_sentence_inv (translateFormula phi)
      (translateFormula_sentence_of_PA_sentence phi hphi) e0 v).mp hsatTranslate

theorem BProv_lift_translatedPAAx_to_HF
    (hAx : ∀ g, translatedPAAx g → BProv HFAx_s [] g)
    {g : Form} (h : BProv translatedPAAx [] g) : BProv HFAx_s [] g :=
  BProv_lift h hAx (fun _ hf => nomatch hf)

theorem BProv_lift_translatedPAAx_to_HFFin
    (hAx : ∀ g, translatedPAAx g → BProv HFFinAx_s [] g)
    {g : Form} (h : BProv translatedPAAx [] g) : BProv HFFinAx_s [] g :=
  BProv_lift h hAx (fun _ hf => nomatch hf)

theorem BProv_HFFin_of_translatedPAAx {g : Form}
    (hg : translatedPAAx g) : BProv HFFinAx_s [] g := by
  rcases hg with ⟨phi, hphi, rfl⟩
  exact BProv_HFFin_translated_PA_axiom hphi

/-- Lift a relative proof over translated PA axioms into finite HF without
discarding its explicit finite context. -/
theorem BProv_HFFin_of_BProv_translatedPAAx_context {G : List Form} {g : Form}
    (h : BProv translatedPAAx G g) : BProv HFFinAx_s G g :=
  BProv_lift h
    (fun _ hg => BProv_mono HFFinAx_s [] G _
      (fun _ hnil => by cases hnil)
      (BProv_HFFin_of_translatedPAAx hg))
    (fun a ha => BProv_of_Prov (B := HFFinAx_s)
      (Prov.P_ass G a ha))

/-- Any derivation over the intermediate translated-PA axiom theory can be cut
down to a derivation over the strengthened finite-HF theory. -/
theorem BProv_HFFin_of_BProv_translatedPAAx {g : Form}
    (h : BProv translatedPAAx [] g) : BProv HFFinAx_s [] g :=
  BProv_HFFin_of_BProv_translatedPAAx_context h

theorem standard_sat_translatedPAAx (e : Nat → Nat) :
    ∀ g, translatedPAAx g → Sat Mem e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  have hsent := translated_PA_axiom_sentence phi hphi
  have hcoded := translated_PA_axiom_sat_codes phi hphi (fun _ => 0)
  exact (Sat_sentence_inv (translateFormula phi) hsent
    (fun _ => ordinalCode 0) e).mp hcoded

end PAInHF

/-! ## The HF-in-PA-in-HF round trip -/

/-- Isomorphism of adjunction-style HF models. -/
structure AdjunctionIso {α : Type} {β : Type}
    (M : AdjunctionModel α) (N : AdjunctionModel β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_mem : ∀ a b, N.mem (toFun a) (toFun b) ↔ M.mem a b
  map_empty : toFun M.empty = N.empty
  map_adjoin : ∀ a b, toFun (M.adjoin a b) = N.adjoin (toFun a) (toFun b)

/-- A shallow semantic bi-interpretation checkpoint: a PA model, an HF model,
the PA model obtained by interpreting PA in HF, the HF model obtained by going
back through that PA interpretation, and explicit round-trip isomorphisms.

This is intentionally a semantic record.  It does not claim, by definition, that
the operations or relations are first-order definable; later syntactic
interpretation records should refine this shape with formulas and translation
theorems. -/
structure ShallowBiInterpretation where
  paModel : PA.Model Nat
  hfModel : AdjunctionModel Nat
  paInHf : PA.Model OrdinalHF
  hfInPaInHf : AdjunctionModel OrdinalHF
  paRoundTrip : PA.Iso paModel paInHf
  hfRoundTrip : AdjunctionIso hfModel hfInPaInHf

/-- A syntax-level interpretation of one first-order theory in another.
It records sentence preservation, theorem transfer, and the concrete fact that
every source axiom translates to a theorem of the target theory. -/
structure TheoryInterpretation
    (Src Tgt : Type)
    (SrcSentence : Src → Prop) (TgtSentence : Tgt → Prop)
    (SrcAx : Src → Prop) (TgtAx : Tgt → Prop)
    (SrcProv : (Src → Prop) → List Src → Src → Prop)
    (TgtProv : (Tgt → Prop) → List Tgt → Tgt → Prop) where
  translate : Src → Tgt
  maps_sentence : ∀ {phi}, SrcSentence phi → TgtSentence (translate phi)
  maps_axiom : ∀ {phi}, SrcAx phi → TgtProv TgtAx [] (translate phi)
  maps_theorem : ∀ {phi}, SrcSentence phi →
    SrcProv SrcAx [] phi → TgtProv TgtAx [] (translate phi)

/-- Compose two theory interpretations.

The additional premise records that source axioms are source sentences, which
is needed only for the composed `maps_axiom` field: the first interpretation
turns a source axiom into a theorem of the middle theory, and the second
interpretation transfers middle-theory theorems only for middle sentences. -/
def TheoryInterpretation.comp
    {Src Mid Tgt : Type}
    {SrcSentence : Src → Prop} {MidSentence : Mid → Prop}
    {TgtSentence : Tgt → Prop}
    {SrcAx : Src → Prop} {MidAx : Mid → Prop} {TgtAx : Tgt → Prop}
    {SrcProv : (Src → Prop) → List Src → Src → Prop}
    {MidProv : (Mid → Prop) → List Mid → Mid → Prop}
    {TgtProv : (Tgt → Prop) → List Tgt → Tgt → Prop}
    (I : TheoryInterpretation Src Mid
      SrcSentence MidSentence SrcAx MidAx SrcProv MidProv)
    (J : TheoryInterpretation Mid Tgt
      MidSentence TgtSentence MidAx TgtAx MidProv TgtProv)
    (hSrcAxSentence : ∀ {phi}, SrcAx phi → SrcSentence phi) :
    TheoryInterpretation Src Tgt
      SrcSentence TgtSentence SrcAx TgtAx SrcProv TgtProv where
  translate := fun phi => J.translate (I.translate phi)
  maps_sentence := by
    intro phi hphi
    exact J.maps_sentence (I.maps_sentence hphi)
  maps_axiom := by
    intro phi hphi
    exact J.maps_theorem (I.maps_sentence (hSrcAxSentence hphi))
      (I.maps_axiom hphi)
  maps_theorem := by
    intro phi hphi hprov
    exact J.maps_theorem (I.maps_sentence hphi)
      (I.maps_theorem hphi hprov)

/-- Build an identity interpretation between two set-theory theories once each
source axiom has been proved from the target theory.  This is the assembly
lemma used after axiom-discharge work; it does not hide any axiom proof. -/
def setTheoryIdentityInterpretationOfAxiomProofs
    (SrcAx TgtAx : Form → Prop)
    (hAx : ∀ phi, SrcAx phi → BProv TgtAx [] phi) :
    TheoryInterpretation Form Form Sentence Sentence SrcAx TgtAx BProv BProv where
  translate := id
  maps_sentence := by
    intro phi hphi
    exact hphi
  maps_axiom := by
    intro phi hphi
    exact hAx phi hphi
  maps_theorem := by
    intro phi _ h
    exact BProv_lift h hAx (fun g hg => nomatch hg)

/-- The intermediate set-theory of translated PA axioms is deductively
interpretable in the strengthened finite-HF theory by the identity translation.

This record packages the axiom-discharge theorem
`PAInHF.BProv_HFFin_of_translatedPAAx` at the theory level.  The still-open
PA-in-HF proof-translation task can target `PAInHF.translatedPAAx` first and
compose with this interpretation. -/
def translatedPATheoryInHFFinInterpretation :
    TheoryInterpretation Form Form Sentence Sentence
      PAInHF.translatedPAAx HFFinAx_s BProv BProv :=
  setTheoryIdentityInterpretationOfAxiomProofs
    PAInHF.translatedPAAx HFFinAx_s
    (fun _ hg => PAInHF.BProv_HFFin_of_translatedPAAx hg)

/-- Compose a future PA-to-`translatedPAAx` interpretation with the established
deductive bridge from `translatedPAAx` into `HFFinAx_s`.

This keeps the remaining PA proof-translation theorem honest: the caller must
still supply the interpretation into the intermediate translated-axiom theory. -/
def paInHFFinOfTranslatedPATheoryInterpretation
    (I : TheoryInterpretation PA.Formula Form
      PA.Formula.Sentence Sentence
      PA.Formula.Ax_s PAInHF.translatedPAAx
      PA.Formula.BProv BProv) :
    TheoryInterpretation PA.Formula Form
      PA.Formula.Sentence Sentence
      PA.Formula.Ax_s HFFinAx_s
      PA.Formula.BProv BProv :=
  TheoryInterpretation.comp I translatedPATheoryInHFFinInterpretation
    (fun {phi} hphi => PA.Formula.sentence_ax_s (f := phi) hphi)

/-- Direct deductive interpretation of PA in strengthened finite HF using the
Ackermann finite-ordinal translation. -/
def paInHFFinTheoryInterpretation :
    TheoryInterpretation PA.Formula Form
      PA.Formula.Sentence Sentence
      PA.Formula.Ax_s HFFinAx_s
      PA.Formula.BProv BProv where
  translate := PAInHF.translateFormula
  maps_sentence := by
    intro phi hphi
    exact PAInHF.translateFormula_sentence_of_PA_sentence phi hphi
  maps_axiom := by
    intro phi hphi
    exact PAInHF.BProv_HFFin_translated_PA_axiom hphi
  maps_theorem := by
    intro phi hphi hprov
    exact PAInHF.BProv_HFFin_translateFormula_of_PA_BProv hphi hprov

/-- Deductive interpretation of strengthened finite HF in the PA-side theory
whose axioms are exactly the translated finite-HF axioms.

This is the reverse analogue of the translated-PA bridge: it is a structural
proof translation and deliberately does not claim yet that PA proves every
translated finite-HF axiom. -/
def hfInTranslatedHFFinTheoryInterpretation :
    TheoryInterpretation Form PA.Formula
      Sentence PA.Formula.Sentence
      HFFinAx_s PA.Formula.translatedHFFinAx
      BProv PA.Formula.BProv where
  translate := PA.Formula.translateHFFormula
  maps_sentence := by
    intro phi hphi
    exact PA.Formula.translateHFFormula_sentence_of_HF_sentence phi hphi
  maps_axiom := by
    intro phi hphi
    exact PA.Formula.BProv_translatedHFFinAx_of_HFFinAx hphi
  maps_theorem := by
    intro phi _hphi hprov
    exact PA.Formula.BProv_translateHFFormula_of_BProv_HFFin hprov

/-- Compose the reverse finite-HF proof translation with a future discharge of
the translated finite-HF axiom theory into PA proper. -/
def hfInPAOfTranslatedHFFinTheoryInterpretation
    (I : TheoryInterpretation PA.Formula PA.Formula
      PA.Formula.Sentence PA.Formula.Sentence
      PA.Formula.translatedHFFinAx PA.Formula.Ax_s
      PA.Formula.BProv PA.Formula.BProv) :
    TheoryInterpretation Form PA.Formula
      Sentence PA.Formula.Sentence
      HFFinAx_s PA.Formula.Ax_s
      BProv PA.Formula.BProv :=
  TheoryInterpretation.comp hfInTranslatedHFFinTheoryInterpretation I
    (fun {phi} hphi => Sentences_HFFin phi hphi)

/-- PA analogue of `setTheoryIdentityInterpretationOfAxiomProofs`. -/
def paIdentityInterpretationOfAxiomProofs
    (SrcAx TgtAx : PA.Formula → Prop)
    (hAx : ∀ phi, SrcAx phi → PA.Formula.BProv TgtAx [] phi) :
    TheoryInterpretation PA.Formula PA.Formula
      PA.Formula.Sentence PA.Formula.Sentence
      SrcAx TgtAx PA.Formula.BProv PA.Formula.BProv where
  translate := id
  maps_sentence := by
    intro phi hphi
    exact hphi
  maps_axiom := by
    intro phi hphi
    exact hAx phi hphi
  maps_theorem := by
    intro phi _ h
    exact PA.Formula.BProv_lift h hAx (fun g hg => nomatch hg)

/-- Identity interpretation from translated finite-HF axioms into PA, once the
caller supplies explicit PA proofs of those translated axioms. -/
def translatedHFFinTheoryInPAInterpretationOfAxiomProofs
    (hAx : ∀ phi, PA.Formula.translatedHFFinAx phi →
      PA.Formula.BProv PA.Formula.Ax_s [] phi) :
    TheoryInterpretation PA.Formula PA.Formula
      PA.Formula.Sentence PA.Formula.Sentence
      PA.Formula.translatedHFFinAx PA.Formula.Ax_s
      PA.Formula.BProv PA.Formula.BProv :=
  paIdentityInterpretationOfAxiomProofs
    PA.Formula.translatedHFFinAx PA.Formula.Ax_s hAx

/-- Identity interpretation from translated finite-HF axioms into PA, assembled
from the named per-axiom proof obligations. -/
def translatedHFFinTheoryInPAInterpretationOfProofs
    (P : PA.Formula.TranslatedHFFinAxiomProofs) :
    TheoryInterpretation PA.Formula PA.Formula
      PA.Formula.Sentence PA.Formula.Sentence
      PA.Formula.translatedHFFinAx PA.Formula.Ax_s
      PA.Formula.BProv PA.Formula.BProv :=
  translatedHFFinTheoryInPAInterpretationOfAxiomProofs
    (fun _ hphi =>
      PA.Formula.BProv_Ax_s_of_translatedHFFinAx_of_proofs P hphi)

/-- Reverse interpretation of finite HF in PA from explicit PA proofs of every
translated finite-HF axiom. -/
def hfInPAInterpretationOfTranslatedHFFinAxiomProofs
    (hAx : ∀ phi, PA.Formula.translatedHFFinAx phi →
      PA.Formula.BProv PA.Formula.Ax_s [] phi) :
    TheoryInterpretation Form PA.Formula
      Sentence PA.Formula.Sentence
      HFFinAx_s PA.Formula.Ax_s
      BProv PA.Formula.BProv :=
  hfInPAOfTranslatedHFFinTheoryInterpretation
    (translatedHFFinTheoryInPAInterpretationOfAxiomProofs hAx)

/-- Reverse interpretation of finite HF in PA from the structured translated
finite-HF axiom proof obligations. -/
def hfInPAInterpretationOfTranslatedHFFinProofs
    (P : PA.Formula.TranslatedHFFinAxiomProofs) :
    TheoryInterpretation Form PA.Formula
      Sentence PA.Formula.Sentence
      HFFinAx_s PA.Formula.Ax_s
      BProv PA.Formula.BProv :=
  hfInPAOfTranslatedHFFinTheoryInterpretation
    (translatedHFFinTheoryInPAInterpretationOfProofs P)

abbrev PAProvability :=
  (PA.Formula → Prop) → List PA.Formula → PA.Formula → Prop

/-- The exact target for a deductive PA/HF bi-interpretability theorem.

Unlike `StandardModelInterpretationCertificate`, this record is not inhabited
in this file.  It states the remaining proof obligations at the theory level:
both syntactic translations must transfer theorems between the PA axiom theory
and the chosen HF-side axiom theory, and the two composites must be provably
equivalent to the identity translations on sentences. -/
structure DeductiveBiInterpretationCertificate
    (HFAxTarget : Form → Prop) (PAProv : PAProvability) where
  paInHf : TheoryInterpretation PA.Formula Form
    PA.Formula.Sentence Sentence
    PA.Formula.Ax_s HFAxTarget
    PAProv BProv
  hfInPa : TheoryInterpretation Form PA.Formula
    Sentence PA.Formula.Sentence
    HFAxTarget PA.Formula.Ax_s
    BProv PAProv
  pa_roundTrip : ∀ (phi : PA.Formula), phi.Sentence →
    PAProv PA.Formula.Ax_s []
      (PA.Formula.iffForm phi (hfInPa.translate (paInHf.translate phi)))
  hf_roundTrip : ∀ (phi : Form), Sentence phi →
    BProv HFAxTarget []
      (fIff phi (paInHf.translate (hfInPa.translate phi)))

/-- The concrete deductive target using the PA natural-deduction calculus
defined above, for the foundation-style HF theory. -/
abbrev PAHFDeductiveBiInterpretationCertificate : Type :=
  DeductiveBiInterpretationCertificate HFAx_s PA.Formula.BProv

/-- The concrete deductive target for PA and the strengthened hereditary-finite
set theory `HFFinAx_s`.  This is the target relevant to the PA/HF theorem:
`HFAx_s` alone still has infinite ZF-style models. -/
abbrev PAHFFinDeductiveBiInterpretationCertificate : Type :=
  DeductiveBiInterpretationCertificate HFFinAx_s PA.Formula.BProv

/-- A standard-model interpretation certificate with the actual syntactic
translations attached, parameterized by the HF-side axiom theory and its
PA-side translated axiom theory.

The exactness fields say that the translations have the intended semantics in
the standard PA and Ackermann-HF models; the axiom fields say that each
translated axiom theory is satisfied by the opposite standard model; the
`shallow` field carries the two round-trip isomorphisms. -/
structure StandardModelInterpretationCertificateFor
    (HFAxTarget : Form → Prop)
    (TranslatedHFAxTarget : PA.Formula → Prop) where
  shallow : ShallowBiInterpretation
  paToHf : PA.Formula → Form
  hfToPa : Form → PA.Formula
  paToHf_exact : ∀ (phi : PA.Formula) (v : Nat → Nat),
    Sat Mem (fun n => ordinalCode (v n)) (paToHf phi) ↔
      PA.Formula.Sat PA.natModel v phi
  hfToPa_exact : ∀ (phi : Form) (v : Nat → Nat),
    PA.Formula.Sat PA.natModel v (hfToPa phi) ↔ Sat Mem v phi
  paAxiom_sat : ∀ (phi : PA.Formula), PA.Formula.Ax_s phi → ∀ (v : Nat → Nat),
    Sat Mem (fun n => ordinalCode (v n)) (paToHf phi)
  hfAxiom_sat : ∀ (phi : Form), HFAxTarget phi → ∀ (v : Nat → Nat),
    PA.Formula.Sat PA.natModel v (hfToPa phi)
  translatedPA_sat : ∀ (e : Nat → Nat) (g : Form),
    PAInHF.translatedPAAx g → Sat Mem e g
  translatedHF_sat : ∀ (e : Nat → Nat) (f : PA.Formula),
    TranslatedHFAxTarget f → PA.Formula.Sat PA.natModel e f

/-- Standard-model certificate for the foundation-style HF theory. -/
abbrev StandardModelInterpretationCertificate : Type :=
  StandardModelInterpretationCertificateFor HFAx_s PA.Formula.translatedHFAx

/-- Standard-model certificate for the strengthened finite-HF theory. -/
abbrev StandardModelFiniteInterpretationCertificate : Type :=
  StandardModelInterpretationCertificateFor HFFinAx_s PA.Formula.translatedHFFinAx

/-- The HF model obtained after interpreting PA inside Ackermann HF and then
running Ackermann's HF interpretation in that interpreted PA model. -/
noncomputable def ordinalHFModel : AdjunctionModel OrdinalHF where
  mem a b := Mem (natOfOrdinal a) (natOfOrdinal b)
  empty := ordinalOfNat empty
  adjoin a b := ordinalOfNat (adjoin (natOfOrdinal a) (natOfOrdinal b))
  extensional := by
    intro a b h
    apply ordinal_eq_of_natOfOrdinal_eq
    apply ext
    intro x
    have hx := h (ordinalOfNat x)
    simpa [natOfOrdinal_ordinalOfNat] using hx
  empty_spec := by
    intro x
    simpa [natOfOrdinal_ordinalOfNat] using
      (mem_empty (natOfOrdinal x))
  adjoin_spec := by
    intro x a b
    constructor
    · intro h
      have h' : Mem (natOfOrdinal x) (adjoin (natOfOrdinal a) (natOfOrdinal b)) := by
        simpa [natOfOrdinal_ordinalOfNat] using h
      have hm := (mem_adjoin (natOfOrdinal x) (natOfOrdinal a) (natOfOrdinal b)).mp h'
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (ordinal_eq_of_natOfOrdinal_eq hm)
    · intro h
      have h' : Mem (natOfOrdinal x) (adjoin (natOfOrdinal a) (natOfOrdinal b)) := by
        apply (mem_adjoin (natOfOrdinal x) (natOfOrdinal a) (natOfOrdinal b)).mpr
        rcases h with h | h
        · exact Or.inl h
        · subst h
          exact Or.inr rfl
      simpa [natOfOrdinal_ordinalOfNat] using h'
  set_induction := by
    intro P step a
    have hnat : ∀ n, P (ordinalOfNat n) := by
      intro n
      exact Nat.strongRecOn n (fun n ih =>
        step (ordinalOfNat n) (fun x hx =>
          have hx' : Mem (natOfOrdinal x) n := by
            simpa [natOfOrdinal_ordinalOfNat] using hx
          have hxlt : natOfOrdinal x < n := mem_lt hx'
          have hpx : P (ordinalOfNat (natOfOrdinal x)) := ih (natOfOrdinal x) hxlt
          by simpa [ordinalOfNat_natOfOrdinal x] using hpx))
    simpa [ordinalOfNat_natOfOrdinal a] using hnat (natOfOrdinal a)

theorem ordinalHF_sat_HF (v : Nat → OrdinalHF) :
    ∀ g, HFAx_s g → Sat ordinalHFModel.mem v g :=
  sat_HF_model ordinalHFModel v

/-- The second round trip of the bi-interpretability construction: starting
from Ackermann HF, interpreting arithmetic as finite ordinals, and then
interpreting HF back by Ackermann coding gives an HF model isomorphic to the
original one. -/
noncomputable def hfRoundTripIso : AdjunctionIso standardModel ordinalHFModel where
  toFun := ordinalOfNat
  invFun := natOfOrdinal
  left_inv := natOfOrdinal_ordinalOfNat
  right_inv := ordinalOfNat_natOfOrdinal
  map_mem := by
    intro a b
    simp only [ordinalHFModel, standardModel, natOfOrdinal_ordinalOfNat]
  map_empty := rfl
  map_adjoin := by
    intro a b
    apply ordinal_eq_of_natOfOrdinal_eq
    simp only [standardModel, ordinalHFModel, natOfOrdinal_ordinalOfNat]

/-- The standard semantic PA/HF bi-interpretability datum: PA on `Nat` and HF
under Ackermann coding, with the two round trips witnessed by `ordinalCode`. -/
noncomputable def standardShallowBiInterpretation : ShallowBiInterpretation where
  paModel := PA.natModel
  hfModel := standardModel
  paInHf := ordinalPAModel
  hfInPaInHf := ordinalHFModel
  paRoundTrip := paRoundTripIso
  hfRoundTrip := hfRoundTripIso

/-- The standard-model syntactic/semantic certificate for the PA/HF
interpretations.  This is not yet a deductive bi-interpretability theorem for
the two axiom theories; it records the exact standard-model semantics and the
semantic round-trip isomorphisms that the theory-level proof must internalize. -/
noncomputable def standardModelInterpretation : StandardModelInterpretationCertificate where
  shallow := standardShallowBiInterpretation
  paToHf := PAInHF.translateFormula
  hfToPa := PA.Formula.translateHFFormula
  paToHf_exact := PAInHF.translateFormula_exact
  hfToPa_exact := PA.Formula.translateHFFormula_exact
  paAxiom_sat := PAInHF.translated_PA_axiom_sat_codes
  hfAxiom_sat := PA.Formula.translated_HF_axiom_sat_nat
  translatedPA_sat := PAInHF.standard_sat_translatedPAAx
  translatedHF_sat := PA.Formula.standard_sat_translatedHFAx

/-- The same standard-model certificate, but with the strengthened finite-HF
axiom theory on the HF side. -/
noncomputable def standardModelFiniteInterpretation :
    StandardModelFiniteInterpretationCertificate where
  shallow := standardShallowBiInterpretation
  paToHf := PAInHF.translateFormula
  hfToPa := PA.Formula.translateHFFormula
  paToHf_exact := PAInHF.translateFormula_exact
  hfToPa_exact := PA.Formula.translateHFFormula_exact
  paAxiom_sat := PAInHF.translated_PA_axiom_sat_codes
  hfAxiom_sat := PA.Formula.translated_HFFin_axiom_sat_nat
  translatedPA_sat := PAInHF.standard_sat_translatedPAAx
  translatedHF_sat := PA.Formula.standard_sat_translatedHFFinAx

theorem PA_standard_model_interpretable_with_HF :
    Nonempty StandardModelInterpretationCertificate :=
  ⟨standardModelInterpretation⟩

theorem PA_standard_model_interpretable_with_HFFin :
    Nonempty StandardModelFiniteInterpretationCertificate :=
  ⟨standardModelFiniteInterpretation⟩

theorem PA_biinterpretable_with_HF_standard :
    Nonempty (PA.Iso PA.natModel ordinalPAModel) ∧
      Nonempty (AdjunctionIso standardModel ordinalHFModel) :=
  ⟨⟨standardShallowBiInterpretation.paRoundTrip⟩,
   ⟨standardShallowBiInterpretation.hfRoundTrip⟩⟩

theorem PA_biinterpretable_with_HFFin_standard :
    Nonempty (PA.Iso PA.natModel ordinalPAModel) ∧
      Nonempty (AdjunctionIso standardModel ordinalHFModel) :=
  PA_biinterpretable_with_HF_standard

end AckermannHF

end SetTheory
