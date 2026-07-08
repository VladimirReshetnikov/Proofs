/-
  PAHF.lean

  Peano arithmetic and hereditary finite sets.

  This module starts the formalization of the classical bi-interpretability
  route:

  * interpret hereditary finite sets in arithmetic by Ackermann's bit coding;
  * interpret arithmetic in hereditary finite sets by the finite von Neumann
    ordinals;
  * prove the round trips by explicit isomorphisms.

  The first section below is intentionally modest and reusable: it builds the
  Ackermann membership relation on `Nat` and proves the finite-set axioms that
  only need bit arithmetic.  Later sections use these lemmas as the semantic
  core of the interpretation data.
-/
import SetTheory.Completeness

namespace SetTheory

/-! ## Ackermann-coded hereditary finite sets -/

namespace AckermannHF

open Form

/-- `Mem x y` means: in Ackermann's coding, the set coded by `x` is an element
of the set coded by `y`.  Equivalently, the `x`-th binary digit of `y` is set. -/
def Mem (x y : Nat) : Prop := y.testBit x = true

/-- The empty set is coded by `0`. -/
def empty : Nat := 0

/-- Adjunction/insert: add the element coded by `x` to the set coded by `a`. -/
def adjoin (a x : Nat) : Nat := a ||| 2 ^ x

theorem mem_empty (x : Nat) : ¬ Mem x empty := by
  simp [Mem, empty, Nat.zero_testBit]

theorem mem_adjoin (x a b : Nat) : Mem x (adjoin a b) ↔ Mem x a ∨ x = b := by
  unfold Mem adjoin
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((of_decide_eq_true h).symm)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (decide_eq_true h.symm)

theorem ext {a b : Nat} (h : ∀ x, Mem x a ↔ Mem x b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro x
  have hx := h x
  cases ha : a.testBit x <;> cases hb : b.testBit x <;>
    simp [Mem, ha, hb] at hx ⊢

theorem two_pow_le_of_mem {x y : Nat} (h : Mem x y) : 2 ^ x ≤ y := by
  apply Nat.le_of_testBit
  intro i hi
  rw [Nat.testBit_two_pow] at hi
  have hix : x = i := of_decide_eq_true hi
  subst hix
  exact h

theorem mem_lt {x y : Nat} (h : Mem x y) : x < y :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (two_pow_le_of_mem h)

/-- Set induction for the Ackermann-coded HF membership relation. -/
theorem induction (P : Nat → Prop)
    (step : ∀ a, (∀ x, Mem x a → P x) → P a) :
    ∀ a, P a := by
  intro a
  exact Nat.strongRecOn a (fun a ih =>
    step a (fun x hx => ih x (mem_lt hx)))

theorem eq_empty_iff_no_mem (a : Nat) : a = empty ↔ ∀ x, ¬ Mem x a := by
  constructor
  · intro h x
    rw [h]
    exact mem_empty x
  · intro h
    apply ext
    intro x
    constructor
    · exact fun hx => False.elim (h x hx)
    · exact fun hx => False.elim (mem_empty x hx)

theorem exists_mem_of_ne_empty {a : Nat} (ha : a ≠ empty) : ∃ x, Mem x a := by
  apply Classical.byContradiction
  intro h
  apply ha
  exact (eq_empty_iff_no_mem a).mpr (fun x hx => h ⟨x, hx⟩)

/-- Search for the largest member of `a` below `n`.  The default value at
`n = 0` is irrelevant; callers use the accompanying existence lemmas. -/
def maxMemberBelow (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if a.testBit n then n else maxMemberBelow a n

theorem le_maxMemberBelow_of_lt {a y n : Nat}
    (hy : y < n) (hmem : Mem y a) : y ≤ maxMemberBelow a n := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn : Mem n a
      · have hbit : a.testBit n = true := hn
        simp [maxMemberBelow, hbit]
        exact Nat.lt_succ_iff.mp hy
      · have hbit : a.testBit n = false := by
          cases hb : a.testBit n <;> simp [Mem, hb] at hn ⊢
        simp [maxMemberBelow, hbit]
        have hyle : y ≤ n := Nat.lt_succ_iff.mp hy
        rcases Nat.lt_or_eq_of_le hyle with hylt | hyeq
        · exact ih hylt
        · subst hyeq
          exact False.elim (hn hmem)

theorem maxMemberBelow_mem_of_exists {a n : Nat}
    (hex : ∃ y, y < n ∧ Mem y a) : Mem (maxMemberBelow a n) a := by
  induction n with
  | zero =>
      rcases hex with ⟨y, hy, _⟩
      omega
  | succ n ih =>
      by_cases hn : Mem n a
      · have hbit : a.testBit n = true := hn
        simp [maxMemberBelow, hbit, Mem]
      · have hbit : a.testBit n = false := by
          cases hb : a.testBit n <;> simp [Mem, hb] at hn ⊢
        simp [maxMemberBelow, hbit]
        apply ih
        rcases hex with ⟨y, hy, hmem⟩
        have hyle : y ≤ n := Nat.lt_succ_iff.mp hy
        rcases Nat.lt_or_eq_of_le hyle with hylt | hyeq
        · exact ⟨y, hylt, hmem⟩
        · subst hyeq
          exact False.elim (hn hmem)

theorem exists_max_mem_of_ne_empty {a : Nat} (ha : a ≠ empty) :
    ∃ m, Mem m a ∧ ∀ y, Mem y a → y ≤ m := by
  obtain ⟨y, hy⟩ := exists_mem_of_ne_empty ha
  refine ⟨maxMemberBelow a a, ?_, ?_⟩
  · apply maxMemberBelow_mem_of_exists
    exact ⟨y, mem_lt hy, hy⟩
  · intro z hz
    exact le_maxMemberBelow_of_lt (mem_lt hz) hz

/-- A compact semantic bundle for the usual adjunction presentation of HF. -/
structure AdjunctionModel (α : Type) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional :
    ∀ {a b}, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec :
    ∀ x, ¬ mem x empty
  adjoin_spec :
    ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b
  set_induction :
    ∀ P : α → Prop, (∀ a, (∀ x, mem x a → P x) → P a) → ∀ a, P a

/-- The standard Ackermann-coded model of hereditary finite sets. -/
def standardModel : AdjunctionModel Nat where
  mem := Mem
  empty := empty
  adjoin := adjoin
  extensional := by
    intro a b h
    exact ext h
  empty_spec := mem_empty
  adjoin_spec := mem_adjoin
  set_induction := induction

/-- Membership in any adjunction model is irreflexive. -/
theorem AdjunctionModel.mem_irrefl {α : Type} (M : AdjunctionModel α) (a : α) :
    ¬ M.mem a a := by
  refine M.set_induction (fun x => ¬ M.mem x x) ?_ a
  intro x ih hxx
  exact ih x hxx hxx

/-! ## First-order HF axioms over the one-relation language -/

/-- A renaming used under two binders: keep the current object variable in
slot `0`, and move every parameter past the two locally-bound variables. -/
def rSkipParam : Nat → Nat
  | 0 => 0
  | n+1 => n+2

theorem Sat_rename_rSkipParam {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (x y : α) :
    Sat mem (scons y (scons x e)) (rename rSkipParam phi) ↔
      Sat mem (scons y e) phi := by
  rw [Sat_rename]
  exact Sat_ext phi _ _ (fun n => by cases n <;> rfl)

/-- In the finite-generation induction step, read `phi` at the old set slot
under the local binders for `a`, `b`, and `c = a ∪ {b}`. -/
def rAdjStepOld : Nat → Nat
  | 0 => 2
  | n+1 => n+3

/-- In the finite-generation induction step, read `phi` at the new adjunction
slot under the local binders for `a`, `b`, and `c = a ∪ {b}`. -/
def rAdjStepNew : Nat → Nat
  | 0 => 0
  | n+1 => n+3

theorem Sat_rename_rAdjStepOld {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (a b c : α) :
    Sat mem (scons c (scons b (scons a e))) (rename rAdjStepOld phi) ↔
      Sat mem (scons a e) phi := by
  rw [Sat_rename]
  exact Sat_ext phi _ _ (fun n => by cases n <;> rfl)

theorem Sat_rename_rAdjStepNew {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) (a b c : α) :
    Sat mem (scons c (scons b (scons a e))) (rename rAdjStepNew phi) ↔
      Sat mem (scons c e) phi := by
  rw [Sat_rename]
  exact Sat_ext phi _ _ (fun n => by cases n <;> rfl)

/-- Under the local binders for a subset witness and its candidate element,
read a predicate at the candidate element while preserving the old parameters. -/
def rSepParam : Nat → Nat
  | 0 => 0
  | n+1 => n+2

theorem Sat_rename_rSepParam {α : Type u} {mem : α → α → Prop}
    (psi : Form) (e : Nat → α) (s x : α) :
    Sat mem (scons x (scons s e)) (rename rSepParam psi) ↔
      Sat mem (scons x e) psi := by
  rw [Sat_rename]
  exact Sat_ext psi _ _ (fun n => by cases n <;> rfl)

/-- The first-order empty-set axiom: some set has no elements. -/
def HF_empty_form : Form :=
  fEx (fAll (fImp (fMem 0 1) fBot))

/-- The first-order extensionality axiom. -/
def HF_extensionality_form : Form :=
  fAll (fAll
    (fImp
      (fAll (fIff (fMem 0 2) (fMem 0 1)))
      (fEq 1 0)))

/-- The first-order adjunction axiom:
for all `a b`, there is `c = a ∪ {b}`. -/
def HF_adjoin_form : Form :=
  fAll (fAll (fEx (fAll
    (fIff (fMem 0 1) (fOr (fMem 0 3) (fEq 0 2))))))

/-- Formula macro: slot `i` is empty. -/
def HF_emptyAt (i : Nat) : Form :=
  fAll (fImp (fMem 0 (i+1)) fBot)

theorem HF_emptyAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (i : Nat) :
    Sat mem e (HF_emptyAt i) ↔ ∀ x, ¬ mem x (e i) :=
  Iff.rfl

theorem HF_emptyAt_empty {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i : Nat) :
    Sat M.mem e (HF_emptyAt i) ↔ e i = M.empty := by
  constructor
  · intro h
    apply M.extensional
    intro x
    constructor
    · exact fun hx => False.elim (h x hx)
    · exact fun hx => False.elim (M.empty_spec x hx)
  · intro h x hx
    have hx' : M.mem x (e i) := by
      simpa [Sat, scons] using hx
    rw [h] at hx'
    exact M.empty_spec x hx'

/-- Formula macro: slot `c` is the adjunction `a ∪ {b}`. -/
def HF_adjoinAt (c a b : Nat) : Form :=
  fAll (fIff (fMem 0 (c+1)) (fOr (fMem 0 (a+1)) (fEq 0 (b+1))))

theorem HF_adjoinAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (c a b : Nat) :
    Sat mem e (HF_adjoinAt c a b) ↔
      ∀ x, mem x (e c) ↔ mem x (e a) ∨ x = e b := by
  constructor
  · intro h x
    exact (Sat_fIff (mem := mem)).mp (h x)
  · intro h x
    exact (Sat_fIff (mem := mem)).mpr (h x)

theorem HF_adjoinAt_adjoin {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (c a b : Nat) :
    Sat M.mem e (HF_adjoinAt c a b) ↔ e c = M.adjoin (e a) (e b) := by
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [(HF_adjoinAt_spec e c a b).mp h x, M.adjoin_spec x (e a) (e b)]
  · intro h
    apply (HF_adjoinAt_spec e c a b).mpr
    intro x
    rw [h, M.adjoin_spec x (e a) (e b)]

/-- Formula macro: slot `s` is the finite-ordinal successor of slot `a`,
that is, `s = a ∪ {a}`. -/
def HF_succAt (s a : Nat) : Form := HF_adjoinAt s a a

theorem HF_succAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (s a : Nat) :
    Sat M.mem e (HF_succAt s a) ↔ e s = M.adjoin (e a) (e a) :=
  HF_adjoinAt_adjoin M e s a a

/-! ### HF-internal pair coding -/

/-- Singleton inside any adjunction-style HF model. -/
def single {α : Type} (M : AdjunctionModel α) (a : α) : α :=
  M.adjoin M.empty a

theorem single_spec {α : Type} (M : AdjunctionModel α) (a x : α) :
    M.mem x (single M a) ↔ x = a := by
  rw [single, M.adjoin_spec]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (M.empty_spec x h)
    · exact h
  · intro h
    exact Or.inr h

/-- Unordered pair inside any adjunction-style HF model. -/
def upair {α : Type} (M : AdjunctionModel α) (a b : α) : α :=
  M.adjoin (single M a) b

theorem upair_spec {α : Type} (M : AdjunctionModel α) (a b x : α) :
    M.mem x (upair M a b) ↔ x = a ∨ x = b := by
  rw [upair, M.adjoin_spec, single_spec]

/-- Kuratowski ordered pair inside any adjunction-style HF model. -/
def kpair {α : Type} (M : AdjunctionModel α) (a b : α) : α :=
  upair M (single M a) (upair M a b)

theorem kpair_mem {α : Type} (M : AdjunctionModel α) (a b q : α) :
    M.mem q (kpair M a b) ↔ q = single M a ∨ q = upair M a b := by
  unfold kpair
  rw [upair_spec]

theorem single_injective {α : Type} (M : AdjunctionModel α) {a b : α}
    (h : single M a = single M b) : a = b := by
  have ha : M.mem a (single M a) := (single_spec M a a).mpr rfl
  rw [h] at ha
  exact (single_spec M b a).mp ha

theorem upair_eq_single {α : Type} (M : AdjunctionModel α) {a b c : α}
    (h : upair M a b = single M c) : a = c ∧ b = c := by
  constructor
  · have ha : M.mem a (upair M a b) := (upair_spec M a b a).mpr (Or.inl rfl)
    rw [h] at ha
    exact (single_spec M c a).mp ha
  · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
    rw [h] at hb
    exact (single_spec M c b).mp hb

theorem kpair_injective {α : Type} (M : AdjunctionModel α) {a b c d : α}
    (h : kpair M a b = kpair M c d) : a = c ∧ b = d := by
  have hac : a = c := by
    have hs : M.mem (single M a) (kpair M a b) :=
      (kpair_mem M a b (single M a)).mpr (Or.inl rfl)
    rw [h] at hs
    rcases (kpair_mem M c d (single M a)).mp hs with hs | hs
    · exact single_injective M hs
    · exact ((upair_eq_single M hs.symm).1).symm
  subst c
  constructor
  · rfl
  · have h1 : M.mem (upair M a b) (kpair M a b) :=
      (kpair_mem M a b (upair M a b)).mpr (Or.inr rfl)
    rw [h] at h1
    rcases (kpair_mem M a d (upair M a b)).mp h1 with h1 | h1
    · have hba : b = a := (upair_eq_single M h1).2
      have h2 : M.mem (upair M a d) (kpair M a d) :=
        (kpair_mem M a d (upair M a d)).mpr (Or.inr rfl)
      rw [← h] at h2
      rcases (kpair_mem M a b (upair M a d)).mp h2 with h2 | h2
      · have hda : d = a := (upair_eq_single M h2).2
        rw [hba, hda]
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [h2] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hba, hd]
        · exact hd.symm
    · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
      rw [h1] at hb
      rcases (upair_spec M a d b).mp hb with hb | hb
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [← h1] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hb, hd]
        · exact hd.symm
      · exact hb

/-- Formula macro: slot `i` is the singleton of slot `j`. -/
def HF_singleAt (i j : Nat) : Form :=
  fAll (fIff (fMem 0 (i+1)) (fEq 0 (j+1)))

theorem HF_singleAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i j : Nat) :
    Sat M.mem e (HF_singleAt i j) ↔ e i = single M (e j) := by
  show (∀ x, (M.mem x (e i) → x = e j) ∧ (x = e j → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [single_spec M (e j) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, single_spec M (e j) x]
    exact ⟨id, id⟩

/-- Formula macro: slot `i` is the unordered pair of slots `j` and `k`. -/
def HF_upairAt (i j k : Nat) : Form :=
  fAll (fIff (fMem 0 (i+1)) (fOr (fEq 0 (j+1)) (fEq 0 (k+1))))

theorem HF_upairAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (i j k : Nat) :
    Sat M.mem e (HF_upairAt i j k) ↔ e i = upair M (e j) (e k) := by
  show (∀ x, (M.mem x (e i) → (x = e j ∨ x = e k)) ∧
             ((x = e j ∨ x = e k) → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [upair_spec M (e j) (e k) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, upair_spec M (e j) (e k) x]
    exact ⟨id, id⟩

/-- Formula macro: slot `p` is the Kuratowski ordered pair of slots `a` and
`b`. -/
def HF_kpairAt (p a b : Nat) : Form :=
  fAll (fIff (fMem 0 (p+1))
    (fOr (HF_singleAt 0 (a+1)) (HF_upairAt 0 (a+1) (b+1))))

theorem HF_kpairAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (p a b : Nat) :
    Sat M.mem e (HF_kpairAt p a b) ↔ e p = kpair M (e a) (e b) := by
  have hq : ∀ q : α,
      (Sat M.mem (scons q e) (HF_singleAt 0 (a+1)) ∨
       Sat M.mem (scons q e) (HF_upairAt 0 (a+1) (b+1)))
        ↔ (q = single M (e a) ∨ q = upair M (e a) (e b)) := by
    intro q
    rw [HF_singleAt_spec M (scons q e) 0 (a+1),
        HF_upairAt_spec M (scons q e) 0 (a+1) (b+1)]
    exact Iff.rfl
  constructor
  · intro h
    apply M.extensional
    intro q
    rw [kpair_mem M (e a) (e b) q, ← hq q]
    exact ⟨(h q).1, (h q).2⟩
  · intro h q
    constructor
    · intro hq'
      have hqmem : M.mem q (e p) := hq'
      rw [h] at hqmem
      exact (hq q).mpr ((kpair_mem M (e a) (e b) q).mp hqmem)
    · intro hs
      show M.mem q (e p)
      rw [h]
      exact (kpair_mem M (e a) (e b) q).mpr ((hq q).mp hs)

/-- Formula macro: the ordered pair of slots `a` and `b` is a member of slot
`r`. -/
def HF_pairMemAt (a b r : Nat) : Form :=
  fEx (fAnd (HF_kpairAt 0 (a+1) (b+1)) (fMem 0 (r+1)))

theorem HF_pairMemAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (a b r : Nat) :
    Sat M.mem e (HF_pairMemAt a b r) ↔
      M.mem (kpair M (e a) (e b)) (e r) := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hmem⟩
    have hp' : p = kpair M (e a) (e b) :=
      (HF_kpairAt_spec M (scons p e) 0 (a+1) (b+1)).mp hp
    have hmem' : M.mem p (e r) := hmem
    rwa [hp'] at hmem'
  · intro h
    refine ⟨kpair M (e a) (e b), ?_, ?_⟩
    · exact (HF_kpairAt_spec M (scons (kpair M (e a) (e b)) e)
        0 (a+1) (b+1)).mpr rfl
    · exact h

/-- A set of ordered pairs is single-valued in its second component. -/
def PairFunctional {α : Type} (M : AdjunctionModel α) (f : α) : Prop :=
  ∀ k y y', M.mem (kpair M k y) f → M.mem (kpair M k y') f → y = y'

/-- Every first component of a pair in `f` is a member of `m ∪ {m}`. -/
def PairKeysBelowSucc {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  ∀ k y, M.mem (kpair M k y) f → M.mem k m ∨ k = m

/-- Every element of `m ∪ {m}` appears as the first component of some pair in
`f`. -/
def PairTotalBelowSucc {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  ∀ k, M.mem k m ∨ k = m → ∃ y, M.mem (kpair M k y) f

/-- Successor-recursion step for a pair set `f` on the proper members of
`m`: if `f(k)=t`, then `f(k+1)=t+1`. -/
def PairSuccStep {α : Type} (M : AdjunctionModel α) (f m : α) : Prop :=
  ∀ k t y,
    M.mem k m →
    M.mem (kpair M k t) f →
    M.mem (kpair M (M.adjoin k k) y) f →
    y = M.adjoin t t

/-- Formula macro: slot `f` is a single-valued relation represented by
Kuratowski pairs. -/
def HF_pairFunctionalAt (f : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fAnd (HF_pairMemAt 2 1 (f+3)) (HF_pairMemAt 2 0 (f+3)))
      (fEq 1 0))))

theorem HF_pairFunctionalAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairFunctionalAt f) ↔ PairFunctional M (e f) := by
  constructor
  · intro h k y y' hky hky'
    exact h k y y'
      ⟨(HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 1 (f+3)).mpr hky,
       (HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 0 (f+3)).mpr hky'⟩
  · intro h k y y' hpairs
    exact h k y y'
      ((HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 1 (f+3)).mp hpairs.1)
      ((HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 0 (f+3)).mp hpairs.2)

/-- Formula macro: every key in relation slot `f` is in `m ∪ {m}`. -/
def HF_pairKeysBelowSuccAt (f m : Nat) : Form :=
  fAll (fAll
    (fImp
      (HF_pairMemAt 1 0 (f+2))
      (fOr (fMem 1 (m+2)) (fEq 1 (m+2)))))

theorem HF_pairKeysBelowSuccAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairKeysBelowSuccAt f m) ↔
      PairKeysBelowSucc M (e f) (e m) := by
  constructor
  · intro h k y hky
    exact h k y
      ((HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mpr hky)
  · intro h k y hky
    exact h k y
      ((HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mp hky)

/-- Formula macro: every key in `m ∪ {m}` occurs in relation slot `f`. -/
def HF_pairTotalBelowSuccAt (f m : Nat) : Form :=
  fAll
    (fImp
      (fOr (fMem 0 (m+1)) (fEq 0 (m+1)))
      (fEx (HF_pairMemAt 1 0 (f+2))))

theorem HF_pairTotalBelowSuccAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairTotalBelowSuccAt f m) ↔
      PairTotalBelowSucc M (e f) (e m) := by
  constructor
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mp hy⟩
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mpr hy⟩

/-- Formula macro: the represented relation advances by ordinal successor at
successive keys below `m`. -/
def HF_pairSuccStepAt (f m : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fMem 2 (m+3))
      (fImp
        (HF_pairMemAt 2 1 (f+3))
        (fAll
          (fImp
            (HF_succAt 0 3)
            (fImp
              (HF_pairMemAt 0 1 (f+4))
              (HF_succAt 1 2))))))))

theorem HF_pairSuccStepAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairSuccStepAt f m) ↔ PairSuccStep M (e f) (e m) := by
  constructor
  · intro h k t y hkm hkt hsy
    have hs := h k t y hkm
      ((HF_pairMemAt_spec M (scons y (scons t (scons k e))) 2 1 (f+3)).mpr hkt)
      (M.adjoin k k)
      ((HF_succAt_spec M
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 3).mpr rfl)
      ((HF_pairMemAt_spec M
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 1 (f+4)).mpr hsy)
    exact (HF_succAt_spec M
      (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 1 2).mp hs
  · intro h k t y hkm hkt sk hsk hsky
    have hsk' : sk = M.adjoin k k :=
      (HF_succAt_spec M (scons sk (scons y (scons t (scons k e)))) 0 3).mp hsk
    have hsky' : M.mem (kpair M (M.adjoin k k) y) (e f) := by
      have hpair := (HF_pairMemAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 1 (f+4)).mp hsky
      rwa [hsk'] at hpair
    apply (HF_succAt_spec M
      (scons sk (scons y (scons t (scons k e)))) 1 2).mpr
    exact h k t y hkm
      ((HF_pairMemAt_spec M (scons y (scons t (scons k e))) 2 1 (f+3)).mp hkt)
      hsky'

/-- The base clause for successor recursion: `f(0)=s`. -/
def HF_pairBaseAt (f s : Nat) : Form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 (s+1) (f+1)))

theorem HF_pairBaseAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f s : Nat) :
    Sat M.mem e (HF_pairBaseAt f s) ↔
      M.mem (kpair M M.empty (e s)) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (HF_emptyAt_empty M (scons z e) 0).mp hz
    have hpair' := (HF_pairMemAt_spec M (scons z e) 0 (s+1) (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (HF_emptyAt_empty M (scons M.empty e) 0).mpr rfl
    · exact (HF_pairMemAt_spec M (scons M.empty e) 0 (s+1) (f+1)).mpr h

/-- The base clause for zero-start recursion: `f(0)=0`. -/
def HF_pairZeroBaseAt (f : Nat) : Form :=
  fEx (fAnd (HF_emptyAt 0) (HF_pairMemAt 0 0 (f+1)))

theorem HF_pairZeroBaseAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairZeroBaseAt f) ↔
      M.mem (kpair M M.empty M.empty) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (HF_emptyAt_empty M (scons z e) 0).mp hz
    have hpair' := (HF_pairMemAt_spec M (scons z e) 0 0 (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (HF_emptyAt_empty M (scons M.empty e) 0).mpr rfl
    · exact (HF_pairMemAt_spec M (scons M.empty e) 0 0 (f+1)).mpr h

/-- Semantic package for a finite successor-recursion trace from `s` through
the segment `m ∪ {m}`. -/
def SuccRecApprox {α : Type} (M : AdjunctionModel α) (s f m : α) : Prop :=
  PairFunctional M f ∧
  PairKeysBelowSucc M f m ∧
  M.mem (kpair M M.empty s) f ∧
  PairTotalBelowSucc M f m ∧
  PairSuccStep M f m

/-- Formula macro for `SuccRecApprox`: slot `f` is the graph of successor
iteration starting at slot `s`, defined on keys up to slot `m`. -/
def HF_succRecApproxAt (f s m : Nat) : Form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairBaseAt f s)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (HF_pairSuccStepAt f m))))

/-- Formula macro: successor-recursion from slot `s` is total through slot `m`.
It existentially packages a recursion graph and its value at key `m`. -/
def HF_succRecTotalAt (s m : Nat) : Form :=
  fEx (fEx (fAnd
    (HF_succRecApproxAt 1 (s+2) (m+2))
    (HF_pairMemAt (m+2) 0 1)))

theorem HF_succRecApproxAt_spec {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) (f s m : Nat) :
    Sat M.mem e (HF_succRecApproxAt f s m) ↔
      SuccRecApprox M (e s) (e f) (e m) := by
  change
    (Sat M.mem e (HF_pairFunctionalAt f) ∧
      (Sat M.mem e (HF_pairKeysBelowSuccAt f m) ∧
        (Sat M.mem e (HF_pairBaseAt f s) ∧
          (Sat M.mem e (HF_pairTotalBelowSuccAt f m) ∧
            Sat M.mem e (HF_pairSuccStepAt f m))))) ↔
      PairFunctional M (e f) ∧
        PairKeysBelowSucc M (e f) (e m) ∧
          M.mem (kpair M M.empty (e s)) (e f) ∧
            PairTotalBelowSucc M (e f) (e m) ∧
              PairSuccStep M (e f) (e m)
  rw [
    HF_pairFunctionalAt_spec M e f,
    HF_pairKeysBelowSuccAt_spec M e f m,
    HF_pairBaseAt_spec M e f s,
    HF_pairTotalBelowSuccAt_spec M e f m,
    HF_pairSuccStepAt_spec M e f m]

/-- Formula macro: slot `a` is a subset of slot `b`. -/
def HF_subsetAt (a b : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1)) (fMem 0 (b+1)))

theorem HF_subsetAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a b : Nat) :
    Sat mem e (HF_subsetAt a b) ↔ ∀ x, mem x (e a) → mem x (e b) :=
  Iff.rfl

/-- Formula macro: there is a subset of slot `a` containing exactly the
members satisfying `psi`.  The predicate `psi` reads its candidate element in
slot `0` and its old parameters from slots `1,2,...`; the subset witness is a
local implementation detail, skipped by `rSepParam`. -/
def HF_sepByAt (psi : Form) (a : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fAnd (fMem 0 (a+2)) (rename rSepParam psi))))

theorem HF_sepByAt_spec {α : Type u} {mem : α → α → Prop}
    (psi : Form) (e : Nat → α) (a : Nat) :
    Sat mem e (HF_sepByAt psi a) ↔
      ∃ s, ∀ x, mem x s ↔ mem x (e a) ∧ Sat mem (scons x e) psi := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, fun x => ?_⟩
    have hx := (Sat_fIff (mem := mem)
      (e := scons x (scons s e))).mp (hs x)
    constructor
    · intro hxs
      have hbody := hx.mp hxs
      exact ⟨hbody.1, (Sat_rename_rSepParam psi e s x).mp hbody.2⟩
    · intro hxbody
      exact hx.mpr ⟨hxbody.1, (Sat_rename_rSepParam psi e s x).mpr hxbody.2⟩
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, fun x => ?_⟩
    apply (Sat_fIff (mem := mem) (e := scons x (scons s e))).mpr
    constructor
    · intro hxs
      exact ⟨(hs x).mp hxs |>.1,
        (Sat_rename_rSepParam psi e s x).mpr ((hs x).mp hxs |>.2)⟩
    · intro hbody
      exact (hs x).mpr
        ⟨hbody.1, (Sat_rename_rSepParam psi e s x).mp hbody.2⟩

/-- Formula macro: slots `a` and `b` have a binary union. -/
def HF_binUnionAt (a b : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fOr (fMem 0 (a+2)) (fMem 0 (b+2)))))

theorem HF_binUnionAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a b : Nat) :
    Sat mem e (HF_binUnionAt a b) ↔
      ∃ u, ∀ x, mem x u ↔ mem x (e a) ∨ mem x (e b) := by
  constructor
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mp (hu x)
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mpr (hu x)

/-- Formula macro: slot `a` has an object union. -/
def HF_unionAt (a : Nat) : Form :=
  fEx (fAll
    (fIff
      (fMem 0 1)
      (fEx (fAnd (fMem 0 (a+3)) (fMem 1 0)))))

theorem HF_unionAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_unionAt a) ↔
      ∃ u, ∀ x, mem x u ↔ ∃ v, mem v (e a) ∧ mem x v := by
  constructor
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mp (hu x)
  · intro h
    rcases h with ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact (Sat_fIff (mem := mem) (e := scons x (scons u e))).mpr (hu x)

/-- Semantic reading of transitivity for one object. -/
def TransitiveObj {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  ∀ y, mem y a → ∀ x, mem x y → mem x a

/-- Formula macro: slot `a` is transitive. -/
def HF_transitiveAt (a : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1))
    (fAll (fImp (fMem 0 1) (fMem 0 (a+2)))))

theorem HF_transitiveAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_transitiveAt a) ↔ TransitiveObj mem (e a) := by
  constructor
  · intro h y hy x hx
    exact h y hy x hx
  · intro h y hy x hx
    exact h y hy x hx

/-- Semantic reading of membership-totality on the elements of one object. -/
def MemTotalOn {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  ∀ y, mem y a → ∀ z, mem z a → mem y z ∨ y = z ∨ mem z y

/-- Semantic reading of a finite membership chain: every element is
transitive, and membership is total on the elements.  Unlike `OrdinalLike`,
the chain object itself need not be transitive, so final segments of finite
ordinals are chain-like. -/
def ChainLike {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  (∀ y, mem y a → TransitiveObj mem y) ∧ MemTotalOn mem a

/-- Formula macro: membership linearly orders the elements of slot `a`.
This is only the totality component; well-foundedness comes from HF induction. -/
def HF_memTotalOnAt (a : Nat) : Form :=
  fAll (fImp (fMem 0 (a+1))
    (fAll (fImp (fMem 0 (a+2))
      (fOr (fMem 1 0) (fOr (fEq 1 0) (fMem 0 1))))))

theorem HF_memTotalOnAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_memTotalOnAt a) ↔ MemTotalOn mem (e a) := by
  constructor
  · intro h y hy z hz
    exact h y hy z hz
  · intro h y hy z hz
    exact h y hy z hz

/-- Formula macro: slot `a` is chain-like. -/
def HF_chainLikeAt (a : Nat) : Form :=
  fAnd
    (fAll (fImp (fMem 0 (a+1)) (HF_transitiveAt 0)))
    (HF_memTotalOnAt a)

theorem HF_chainLikeAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_chainLikeAt a) ↔ ChainLike mem (e a) := by
  constructor
  · intro h
    exact ⟨(fun y hy =>
      (HF_transitiveAt_spec (scons y e) 0).mp (h.1 y hy)),
      (HF_memTotalOnAt_spec e a).mp h.2⟩
  · intro h
    exact ⟨(fun y hy =>
      (HF_transitiveAt_spec (scons y e) 0).mpr (h.1 y hy)),
      (HF_memTotalOnAt_spec e a).mpr h.2⟩

/-- Semantic reading of the finite-ordinal domain formula used by the
PA-in-HF interpretation. -/
def OrdinalLike {α : Type u} (mem : α → α → Prop) (a : α) : Prop :=
  TransitiveObj mem a ∧ (∀ y, mem y a → TransitiveObj mem y) ∧ MemTotalOn mem a

theorem OrdinalLike.of_mem {α : Type u} {mem : α → α → Prop}
    {a y : α} (ha : OrdinalLike mem a) (hy : mem y a) :
    OrdinalLike mem y := by
  refine ⟨ha.2.1 y hy, ?_, ?_⟩
  · intro z hz
    exact ha.2.1 z (ha.1 y hy z hz)
  · intro u hu z hz
    exact ha.2.2 u (ha.1 y hy u hu) z (ha.1 y hy z hz)

theorem OrdinalLike.empty {α : Type} (M : AdjunctionModel α) :
    OrdinalLike M.mem M.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)

theorem OrdinalLike.adjoin_self {α : Type} (M : AdjunctionModel α)
    {a s : α} (ha : OrdinalLike M.mem a) (hs : s = M.adjoin a a) :
    OrdinalLike M.mem s := by
  subst s
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    apply (M.adjoin_spec x a a).mpr
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact Or.inl (ha.1 y hyin x hx)
    · rw [hyeq] at hx
      exact Or.inl hx
  · intro y hy
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact ha.2.1 y hyin
    · rw [hyeq]
      exact ha.1
  · intro y hy z hz
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact ha.2.2 y hyin z hzin
      · exact Or.inl (by rw [hzeq]; exact hyin)
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact Or.inr (Or.inr (by rw [hyeq]; exact hzin))
      · exact Or.inr (Or.inl (by rw [hyeq, hzeq]))

/-- Formula macro: slot `a` is ordinal-like.  Over HF, where membership is
well-founded by set induction, this is intended to define the finite von
Neumann ordinals. -/
def HF_ordinalLikeAt (a : Nat) : Form :=
  fAnd (HF_transitiveAt a)
    (fAnd
      (fAll (fImp (fMem 0 (a+1)) (HF_transitiveAt 0)))
      (HF_memTotalOnAt a))

/-- Formula macro: successor-recursion from slot `s` is total through slot `m`
whenever slot `m` is ordinal-like. -/
def HF_succRecTotalOnOrdinalAt (s m : Nat) : Form :=
  fImp (HF_ordinalLikeAt m) (HF_succRecTotalAt s m)

/-- Formula macro: every nonempty object in slot `a` has a membership-maximal
member.  Maximal means no other member of `a` contains it. -/
def HF_memMaxAt (a : Nat) : Form :=
  fImp
    (fEx (fMem 0 (a+1)))
    (fEx
      (fAnd
        (fMem 0 (a+1))
        (fAll
          (fImp
            (fMem 0 (a+2))
            (fImp (fMem 1 0) fBot)))))

/-- Formula macro: every nonempty chain-like subset of slot `a` has a
membership-maximal member. -/
def HF_chainSubsetsMaxAt (a : Nat) : Form :=
  fAll
    (fImp
      (HF_subsetAt 0 (a+1))
      (fImp (HF_chainLikeAt 0) (HF_memMaxAt 0)))

theorem HF_ordinalLikeAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_ordinalLikeAt a) ↔ OrdinalLike mem (e a) := by
  constructor
  · intro h
    exact ⟨(HF_transitiveAt_spec e a).mp h.1,
      (fun y hy => (HF_transitiveAt_spec (scons y e) 0).mp (h.2.1 y hy)),
      (HF_memTotalOnAt_spec e a).mp h.2.2⟩
  · intro h
    exact ⟨(HF_transitiveAt_spec e a).mpr h.1,
      (fun y hy => (HF_transitiveAt_spec (scons y e) 0).mpr (h.2.1 y hy)),
      (HF_memTotalOnAt_spec e a).mpr h.2.2⟩

theorem HF_memMaxAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_memMaxAt a) ↔
      ((∃ x, mem x (e a)) →
        ∃ p, mem p (e a) ∧ ∀ q, mem q (e a) → ¬ mem p q) := by
  constructor
  · intro h hne
    rcases hne with ⟨x, hx⟩
    rcases h ⟨x, hx⟩ with ⟨p, hp, hmax⟩
    exact ⟨p, hp, fun q hq hpq => hmax q hq hpq⟩
  · intro h hneSat
    rcases hneSat with ⟨x, hx⟩
    rcases h ⟨x, hx⟩ with ⟨p, hp, hmax⟩
    exact ⟨p, hp, fun q hq hpq => hmax q hq hpq⟩

theorem HF_chainSubsetsMaxAt_spec {α : Type u} {mem : α → α → Prop}
    (e : Nat → α) (a : Nat) :
    Sat mem e (HF_chainSubsetsMaxAt a) ↔
      ∀ s, (∀ x, mem x s → mem x (e a)) →
        ChainLike mem s →
          ((∃ x, mem x s) →
            ∃ p, mem p s ∧ ∀ q, mem q s → ¬ mem p q) := by
  constructor
  · intro h s hsSub hsChain
    have hsSat := h s
    have hsSubSat : Sat mem (scons s e) (HF_subsetAt 0 (a+1)) :=
      (HF_subsetAt_spec (scons s e) 0 (a+1)).mpr hsSub
    have hChainSat : Sat mem (scons s e) (HF_chainLikeAt 0) :=
      (HF_chainLikeAt_spec (scons s e) 0).mpr hsChain
    exact (HF_memMaxAt_spec (scons s e) 0).mp (hsSat hsSubSat hChainSat)
  · intro h s hsSubSat hsChainSat
    have hsSub : ∀ x, mem x s → mem x (e a) :=
      (HF_subsetAt_spec (scons s e) 0 (a+1)).mp hsSubSat
    have hsChain : ChainLike mem s :=
      (HF_chainLikeAt_spec (scons s e) 0).mp hsChainSat
    exact (HF_memMaxAt_spec (scons s e) 0).mpr (h s hsSub hsChain)

/-! ### Free-variable support of the HF macros -/

theorem HF_emptyAt_free {i a : Nat} (h : Free i (HF_emptyAt a)) : i = a := by
  simp only [HF_emptyAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_adjoinAt_free {i c a b : Nat} (h : Free i (HF_adjoinAt c a b)) :
    i = c ∨ i = a ∨ i = b := by
  simp only [HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_succAt_free {i s a : Nat} (h : Free i (HF_succAt s a)) :
    i = s ∨ i = a := by
  simp only [HF_succAt, HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_singleAt_free {i a b : Nat} (h : Free i (HF_singleAt a b)) :
    i = a ∨ i = b := by
  simp only [HF_singleAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_upairAt_free {i a b c : Nat} (h : Free i (HF_upairAt a b c)) :
    i = a ∨ i = b ∨ i = c := by
  simp only [HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_kpairAt_free {i p a b : Nat} (h : Free i (HF_kpairAt p a b)) :
    i = p ∨ i = a ∨ i = b := by
  simp only [HF_kpairAt, HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairMemAt_free {i a b r : Nat} (h : Free i (HF_pairMemAt a b r)) :
    i = a ∨ i = b ∨ i = r := by
  simp only [HF_pairMemAt, HF_kpairAt, HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairFunctionalAt_free {i f : Nat} (h : Free i (HF_pairFunctionalAt f)) :
    i = f := by
  simp only [HF_pairFunctionalAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairKeysBelowSuccAt_free {i f m : Nat}
    (h : Free i (HF_pairKeysBelowSuccAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairKeysBelowSuccAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairTotalBelowSuccAt_free {i f m : Nat}
    (h : Free i (HF_pairTotalBelowSuccAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairTotalBelowSuccAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairSuccStepAt_free {i f m : Nat}
    (h : Free i (HF_pairSuccStepAt f m)) : i = f ∨ i = m := by
  simp only [HF_pairSuccStepAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, HF_succAt, HF_adjoinAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairBaseAt_free {i f s : Nat} (h : Free i (HF_pairBaseAt f s)) :
    i = f ∨ i = s := by
  simp only [HF_pairBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt, HF_singleAt,
    HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_pairZeroBaseAt_free {i f : Nat} (h : Free i (HF_pairZeroBaseAt f)) :
    i = f := by
  simp only [HF_pairZeroBaseAt, HF_emptyAt, HF_pairMemAt, HF_kpairAt,
    HF_singleAt, HF_upairAt, fIff, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_succRecApproxAt_free {i f s m : Nat}
    (h : Free i (HF_succRecApproxAt f s m)) : i = f ∨ i = s ∨ i = m := by
  simp only [HF_succRecApproxAt, Free] at h
  rcases h with h | h
  · have hf := HF_pairFunctionalAt_free h
    omega
  · rcases h with h | h
    · have hfm := HF_pairKeysBelowSuccAt_free h
      omega
    · rcases h with h | h
      · have hfs := HF_pairBaseAt_free h
        omega
      · rcases h with h | h
        · have hfm := HF_pairTotalBelowSuccAt_free h
          omega
        · have hfm := HF_pairSuccStepAt_free h
          omega

theorem HF_subsetAt_free {i a b : Nat} (h : Free i (HF_subsetAt a b)) :
    i = a ∨ i = b := by
  simp only [HF_subsetAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_transitiveAt_free {i a : Nat} (h : Free i (HF_transitiveAt a)) :
    i = a := by
  simp only [HF_transitiveAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_memTotalOnAt_free {i a : Nat} (h : Free i (HF_memTotalOnAt a)) :
    i = a := by
  simp only [HF_memTotalOnAt, Free] at h
  repeat first | omega | rcases h with h | h

theorem HF_ordinalLikeAt_free {i a : Nat} (h : Free i (HF_ordinalLikeAt a)) :
    i = a := by
  simp only [HF_ordinalLikeAt, HF_transitiveAt, HF_memTotalOnAt, Free] at h
  repeat first | omega | rcases h with h | h

/-- The first-order set-induction schema instance for `phi`, where `phi`
uses slot `0` as the element being proved and slots `1,2,...` as parameters. -/
def HF_induction_form (phi : Form) : Form :=
  fImp
    (fAll
      (fImp
        (fAll (fImp (fMem 0 1) (rename rSkipParam phi)))
        phi))
    (fAll phi)

/-- The finite-generation induction schema for hereditary finite sets.

If `phi` holds for every empty object and is preserved by one-point
adjunction, then `phi` holds for every object.  This is the finiteness content
missing from pure foundation-style set induction: ZF models satisfy
`HF_induction_form`, but not this schema. -/
def HF_finite_induction_form (phi : Form) : Form :=
  fImp
    (fAnd
      (fAll (fImp (HF_emptyAt 0) phi))
      (fAll (fAll (fAll
        (fImp
          (HF_adjoinAt 0 2 1)
          (fImp (rename rAdjStepOld phi) (rename rAdjStepNew phi)))))))
    (fAll phi)

theorem HF_finite_induction_form_spec {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) :
    Sat mem e (HF_finite_induction_form phi) ↔
      (((∀ z, (∀ x, ¬ mem x z) → Sat mem (scons z e) phi) ∧
        (∀ a b c, (∀ x, mem x c ↔ mem x a ∨ x = b) →
          Sat mem (scons a e) phi → Sat mem (scons c e) phi)) →
        ∀ a, Sat mem (scons a e) phi) := by
  constructor
  · intro h hgen
    apply h
    constructor
    · intro z hz
      exact hgen.1 z ((HF_emptyAt_spec (scons z e) 0).mp hz)
    · intro a b c hc hOld
      have hc' :
          ∀ x, mem x c ↔ mem x a ∨ x = b :=
        (HF_adjoinAt_spec (scons c (scons b (scons a e))) 0 2 1).mp hc
      have hOld' : Sat mem (scons a e) phi :=
        (Sat_rename_rAdjStepOld phi e a b c).mp hOld
      exact (Sat_rename_rAdjStepNew phi e a b c).mpr
        (hgen.2 a b c hc' hOld')
  · intro h hsyn
    apply h
    constructor
    · intro z hz
      exact hsyn.1 z ((HF_emptyAt_spec (scons z e) 0).mpr hz)
    · intro a b c hc hOld
      have hcSat :
          Sat mem (scons c (scons b (scons a e))) (HF_adjoinAt 0 2 1) :=
        (HF_adjoinAt_spec (scons c (scons b (scons a e))) 0 2 1).mpr hc
      have hOldSat :
          Sat mem (scons c (scons b (scons a e))) (rename rAdjStepOld phi) :=
        (Sat_rename_rAdjStepOld phi e a b c).mpr hOld
      have hNewSat := hsyn.2 a b c hcSat hOldSat
      exact (Sat_rename_rAdjStepNew phi e a b c).mp hNewSat

/-- The unsealed HF axiom schema. -/
def HFAx (f : Form) : Prop :=
  f = HF_empty_form ∨
  f = HF_extensionality_form ∨
  f = HF_adjoin_form ∨
  ∃ phi, f = HF_induction_form phi

/-- The sentence theory of HF, with every schema instance universally closed. -/
def HFAx_s (f : Form) : Prop :=
  f = sealF HF_empty_form ∨
  f = sealF HF_extensionality_form ∨
  f = sealF HF_adjoin_form ∨
  ∃ phi, f = sealF (HF_induction_form phi)

/-- The sentence theory of hereditary finite sets.

`HFAx_s` contains the extensionality/empty/adjunction axioms and
foundation-style set induction.  The additional finite-generation schema below
excludes infinite sets and is the axiom needed for the PA interpretation over
finite von Neumann ordinals. -/
def HFFinAx_s (f : Form) : Prop :=
  HFAx_s f ∨ ∃ phi, f = sealF (HF_finite_induction_form phi)

theorem Sentences_HF : Sentences HFAx_s := by
  intro f hf
  rcases hf with rfl | rfl | rfl | ⟨phi, rfl⟩ <;> exact Sentence_seal _

theorem Sentences_HFFin : Sentences HFFinAx_s := by
  intro f hf
  rcases hf with hf | ⟨phi, rfl⟩
  · exact Sentences_HF f hf
  · exact Sentence_seal _

theorem sat_HF_empty {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_empty_form :=
  ⟨M.empty, fun x hx => M.empty_spec x hx⟩

theorem sat_HF_extensionality {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_extensionality_form := by
  intro a b h
  apply M.extensional
  intro x
  exact (Sat_fIff (mem := M.mem)
    (e := scons x (scons b (scons a e)))).mp (h x)

theorem sat_HF_adjoin {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_adjoin_form := by
  intro a b
  refine ⟨M.adjoin a b, fun x => ?_⟩
  exact (Sat_fIff (mem := M.mem)).mpr (M.adjoin_spec x a b)

theorem sat_HF_induction {α : Type} (M : AdjunctionModel α)
    (phi : Form) (e : Nat → α) :
    Sat M.mem e (HF_induction_form phi) := by
  intro hstep a
  exact M.set_induction (fun x => Sat M.mem (scons x e) phi)
    (fun x ih => hstep x (fun y hy =>
      (Sat_rename_rSkipParam phi e x y).mpr (ih y hy)))
    a

theorem sat_HF_model {α : Type} (M : AdjunctionModel α) (v : Nat → α) :
    ∀ g, HFAx_s g → Sat M.mem v g := by
  intro g hg
  rcases hg with rfl | rfl | rfl | ⟨phi, rfl⟩
  · exact (seal_valid (mem := M.mem) HF_empty_form).mpr (sat_HF_empty M) v
  · exact (seal_valid (mem := M.mem) HF_extensionality_form).mpr
      (sat_HF_extensionality M) v
  · exact (seal_valid (mem := M.mem) HF_adjoin_form).mpr (sat_HF_adjoin M) v
  · exact (seal_valid (mem := M.mem) (HF_induction_form phi)).mpr
      (sat_HF_induction M phi) v

theorem standard_sat_HF (v : Nat → Nat) :
    ∀ g, HFAx_s g → Sat Mem v g :=
  sat_HF_model standardModel v

/-- The finite prefix of the Ackermann-coded set `a` using only candidate
elements below `n`.  This gives an explicit adjunction construction of every
standard HF object, independent of any formula being interpreted. -/
def prefixBelow (a : Nat) : Nat → Nat
  | 0 => empty
  | n+1 => if a.testBit n then adjoin (prefixBelow a n) n else prefixBelow a n

theorem prefixBelow_succ_of_mem {a n : Nat} (h : Mem n a) :
    prefixBelow a (n+1) = adjoin (prefixBelow a n) n := by
  have hbit : a.testBit n = true := h
  simp [prefixBelow, hbit]

theorem prefixBelow_succ_of_not_mem {a n : Nat} (h : ¬ Mem n a) :
    prefixBelow a (n+1) = prefixBelow a n := by
  have hbit : a.testBit n = false := by
    cases hb : a.testBit n <;> simp [Mem, hb] at h ⊢
  simp [prefixBelow, hbit]

theorem mem_prefixBelow_iff {x a n : Nat} :
    Mem x (prefixBelow a n) ↔ x < n ∧ Mem x a := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim (mem_empty x h)
      · intro h
        omega
  | succ n ih =>
      by_cases hn : Mem n a
      · rw [prefixBelow_succ_of_mem hn, mem_adjoin, ih]
        constructor
        · intro h
          rcases h with h | h
          · exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
          · subst x
            exact ⟨Nat.lt_succ_self n, hn⟩
        · intro h
          have hle : x ≤ n := Nat.lt_succ_iff.mp h.1
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · exact Or.inl ⟨hlt, h.2⟩
          · exact Or.inr heq
      · rw [prefixBelow_succ_of_not_mem hn, ih]
        constructor
        · intro h
          exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
        · intro h
          have hle : x ≤ n := Nat.lt_succ_iff.mp h.1
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · exact ⟨hlt, h.2⟩
          · exact False.elim (hn (by simpa [heq] using h.2))

theorem prefixBelow_self_eq (a : Nat) : prefixBelow a a = a := by
  apply ext
  intro x
  rw [mem_prefixBelow_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨mem_lt h, h⟩

theorem sat_HF_finite_induction_standard (phi : Form) (e : Nat → Nat) :
    Sat Mem e (HF_finite_induction_form phi) := by
  apply (HF_finite_induction_form_spec phi e).mpr
  intro hgen a
  have hpref : ∀ n, Sat Mem (scons (prefixBelow a n) e) phi := by
    intro n
    induction n with
    | zero =>
        exact hgen.1 (prefixBelow a 0) (fun x hx => mem_empty x hx)
    | succ n ih =>
        by_cases hn : Mem n a
        · have hAdj :
            ∀ x, Mem x (prefixBelow a (n+1)) ↔
              Mem x (prefixBelow a n) ∨ x = n := by
            intro x
            rw [prefixBelow_succ_of_mem hn, mem_adjoin]
          exact hgen.2 (prefixBelow a n) n (prefixBelow a (n+1)) hAdj ih
        · simpa [prefixBelow_succ_of_not_mem hn] using ih
  simpa [prefixBelow_self_eq a] using hpref a

theorem standard_sat_HFFin (v : Nat → Nat) :
    ∀ g, HFFinAx_s g → Sat Mem v g := by
  intro g hg
  rcases hg with hg | ⟨phi, rfl⟩
  · exact standard_sat_HF v g hg
  · exact (seal_valid (mem := Mem) (HF_finite_induction_form phi)).mpr
      (sat_HF_finite_induction_standard phi) v

/-- Named membership of the sealed empty-set axiom in the HF theory. -/
theorem HFAx_s_empty : HFAx_s (sealF HF_empty_form) :=
  Or.inl rfl

/-- Named membership of the sealed extensionality axiom in the HF theory. -/
theorem HFAx_s_extensionality : HFAx_s (sealF HF_extensionality_form) :=
  Or.inr (Or.inl rfl)

/-- Named membership of the sealed adjunction axiom in the HF theory. -/
theorem HFAx_s_adjoin : HFAx_s (sealF HF_adjoin_form) :=
  Or.inr (Or.inr (Or.inl rfl))

/-- Named membership of a sealed set-induction instance in the HF theory. -/
theorem HFAx_s_induction (phi : Form) : HFAx_s (sealF (HF_induction_form phi)) :=
  Or.inr (Or.inr (Or.inr ⟨phi, rfl⟩))

theorem HFFinAx_s_of_HFAx_s {f : Form} (hf : HFAx_s f) : HFFinAx_s f :=
  Or.inl hf

/-- Named membership of a sealed finite-generation induction instance in the
hereditary-finite theory. -/
theorem HFFinAx_s_finite_induction (phi : Form) :
    HFFinAx_s (sealF (HF_finite_induction_form phi)) :=
  Or.inr ⟨phi, rfl⟩

theorem semantic_empty_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∃ e, ∀ x, ¬ mem x e :=
  extract HFAx_s v HF_empty_form hHF HFAx_s_empty v

theorem semantic_extensionality_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b := by
  have hExt : ∀ e, Sat mem e HF_extensionality_form :=
    extract HFAx_s v HF_extensionality_form hHF HFAx_s_extensionality
  intro a b hab
  exact hExt v a b (fun x =>
    (Sat_fIff (mem := mem) (e := scons x (scons b (scons a v)))).mpr (hab x))

theorem semantic_adjoin_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b := by
  have hAdj : ∀ e, Sat mem e HF_adjoin_form :=
    extract HFAx_s v HF_adjoin_form hHF HFAx_s_adjoin
  intro a b
  rcases hAdj v a b with ⟨c, hc⟩
  exact ⟨c, fun x =>
    (Sat_fIff (mem := mem) (e := scons x (scons c (scons b (scons a v))))).mp (hc x)⟩

theorem semantic_induction_schema_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_induction_form phi) :=
  extract HFAx_s v (HF_induction_form phi) hHF (HFAx_s_induction phi)

theorem semantic_finite_induction_schema_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_finite_induction_form phi) :=
  extract HFFinAx_s v (HF_finite_induction_form phi) hHF
    (HFFinAx_s_finite_induction phi)

theorem semantic_empty_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∃ e, ∀ x, ¬ mem x e :=
  semantic_empty_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_extensionality_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b :=
  semantic_extensionality_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_adjoin_of_HFFinAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b :=
  semantic_adjoin_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg))

theorem semantic_induction_schema_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) (phi : Form) :
    ∀ e, Sat mem e (HF_induction_form phi) :=
  semantic_induction_schema_of_HFAx_s v
    (fun g hg => hHF g (HFFinAx_s_of_HFAx_s hg)) phi

/-- First-order HF induction rules out self-membership in every semantic model
of the sealed HF theory. -/
theorem semantic_mem_irrefl_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    ∀ a, ¬ mem a a := by
  let phi : Form := fImp (fMem 0 0) fBot
  have hind := semantic_induction_schema_of_HFAx_s v hHF phi v
  have hall : ∀ a, Sat mem (scons a v) phi := by
    apply hind
    intro a ih haa
    exact ih a haa haa
  intro a haa
  exact hall a haa

/-- First-order semantic content of the sealed HF theory, without pretending
that first-order induction gives the second-order `AdjunctionModel.set_induction`
field. -/
structure FirstOrderHFModel (α : Type u) where
  mem : α → α → Prop
  extensional : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  empty_exists : ∃ e, ∀ x, ¬ mem x e
  adjoin_exists : ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b
  induction_schema : ∀ phi e, Sat mem e (HF_induction_form phi)

/-- First-order HF model with chosen empty and adjunction witnesses.

This is deliberately weaker than `AdjunctionModel`: it carries the first-order
induction schema as a semantic axiom, not a meta-level set-induction principle.
It is the right bundle for constructing witnesses while discharging translated
axioms by completeness. -/
structure FirstOrderAdjunctionModel (α : Type u) where
  mem : α → α → Prop
  empty : α
  adjoin : α → α → α
  extensional : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  empty_spec : ∀ x, ¬ mem x empty
  adjoin_spec : ∀ x a b, mem x (adjoin a b) ↔ mem x a ∨ x = b
  induction_schema : ∀ phi e, Sat mem e (HF_induction_form phi)

/-- Chosen first-order HF model carrying the finite-generation induction
schema of hereditary finite sets. -/
structure FirstOrderFiniteAdjunctionModel (α : Type u) extends
    FirstOrderAdjunctionModel α where
  finite_induction_schema : ∀ phi e, Sat mem e (HF_finite_induction_form phi)

namespace FirstOrderAdjunctionModel

/-- First-order HF induction rules out self-membership in a chosen first-order
HF model. -/
theorem mem_irrefl {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) :
    ¬ M.mem a a := by
  let phi : Form := fImp (fMem 0 0) fBot
  have hind := M.induction_schema phi (fun _ => a)
  have hall : ∀ a, Sat M.mem (scons a (fun _ => a)) phi := by
    apply hind
    intro a ih haa
    exact ih a haa haa
  exact hall a

/-- First-order HF induction rules out two-cycles of membership. -/
theorem mem_asymm {α : Type u} (M : FirstOrderAdjunctionModel α) {a b : α}
    (hab : M.mem a b) : ¬ M.mem b a := by
  let phi : Form :=
    fAll (fImp (fMem 0 1) (fImp (fMem 1 0) fBot))
  let tail : Nat → α := fun _ => a
  have hind := M.induction_schema phi tail
  have hall : ∀ x, Sat M.mem (scons x tail) phi := by
    apply hind
    intro x ih y hyx hxy
    have hySat : Sat M.mem (scons y tail) phi :=
      (Sat_rename_rSkipParam phi tail x y).mp (ih y hyx)
    exact hySat x hxy hyx
  exact hall b a hab

theorem adjoin_self_mem {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) :
    M.mem a (M.adjoin a a) :=
  (M.adjoin_spec a a a).mpr (Or.inr rfl)

theorem adjoin_self_ne_self {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a : α) : M.adjoin a a ≠ a := by
  intro h
  have ha : M.mem a (M.adjoin a a) := adjoin_self_mem M a
  rw [h] at ha
  exact mem_irrefl M a ha

theorem adjoin_self_not_mem_of_ordinalLike {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a : α}
    (ha : OrdinalLike M.mem a) : ¬ M.mem (M.adjoin a a) a := by
  intro hsucc
  have ha_in_succ : M.mem a (M.adjoin a a) := adjoin_self_mem M a
  have haa : M.mem a a := ha.1 (M.adjoin a a) hsucc a ha_in_succ
  exact mem_irrefl M a haa

theorem adjoin_self_injective_on_ordinalLike {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a b : α}
    (_ha : OrdinalLike M.mem a) (hb : OrdinalLike M.mem b)
    (h : M.adjoin a a = M.adjoin b b) : a = b := by
  have hasucc : M.mem a (M.adjoin b b) := by
    have : M.mem a (M.adjoin a a) := adjoin_self_mem M a
    simpa [h] using this
  rcases (M.adjoin_spec a b b).mp hasucc with hab | hab
  · have hbsucc : M.mem b (M.adjoin a a) := by
      have : M.mem b (M.adjoin b b) := adjoin_self_mem M b
      simpa [← h] using this
    rcases (M.adjoin_spec b a a).mp hbsucc with hba | hba
    · have hbb : M.mem b b := hb.1 a hab b hba
      exact False.elim (mem_irrefl M b hbb)
    · exact hba.symm
  · exact hab

/-- The chosen empty object is ordinal-like in every first-order adjunction
model. -/
theorem ordinalLike_empty {α : Type u} (M : FirstOrderAdjunctionModel α) :
    OrdinalLike M.mem M.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)
  · intro y hy
    exact False.elim (M.empty_spec y hy)

/-- Self-adjunction preserves ordinal-likeness in every first-order adjunction
model. -/
theorem ordinalLike_adjoin_self {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a s : α}
    (ha : OrdinalLike M.mem a) (hs : s = M.adjoin a a) :
    OrdinalLike M.mem s := by
  subst s
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    apply (M.adjoin_spec x a a).mpr
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact Or.inl (ha.1 y hyin x hx)
    · rw [hyeq] at hx
      exact Or.inl hx
  · intro y hy
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · exact ha.2.1 y hyin
    · rw [hyeq]
      exact ha.1
  · intro y hy z hz
    rcases (M.adjoin_spec y a a).mp hy with hyin | hyeq
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact ha.2.2 y hyin z hzin
      · exact Or.inl (by rw [hzeq]; exact hyin)
    · rcases (M.adjoin_spec z a a).mp hz with hzin | hzeq
      · exact Or.inr (Or.inr (by rw [hyeq]; exact hzin))
      · exact Or.inr (Or.inl (by rw [hyeq, hzeq]))

/-- A membership-maximal element of an ordinal-like object is its predecessor. -/
theorem ordinalLike_eq_succ_of_mem_max {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a p : α}
    (ha : OrdinalLike M.mem a)
    (hp : M.mem p a)
    (hmax : ∀ q, M.mem q a → ¬ M.mem p q) :
    a = M.adjoin p p := by
  apply M.extensional
  intro x
  constructor
  · intro hx
    apply (M.adjoin_spec x p p).mpr
    rcases ha.2.2 x hx p hp with hxp | hxp | hpx
    · exact Or.inl hxp
    · exact Or.inr hxp
    · exact False.elim (hmax x hx hpx)
  · intro hx
    rcases (M.adjoin_spec x p p).mp hx with hxp | hxp
    · exact ha.1 p hp x hxp
    · rw [hxp]
      exact hp

/-- If every nonempty object has a membership-maximal element, then every
ordinal-like object is either empty or a successor of one of its members. -/
theorem ordinalLike_empty_or_succ_of_mem_max_exists {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hMax : ∀ a, (∃ x, M.mem x a) →
      ∃ p, M.mem p a ∧ ∀ q, M.mem q a → ¬ M.mem p q)
    {a : α} (ha : OrdinalLike M.mem a) :
    a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p := by
  by_cases hne : ∃ x, M.mem x a
  · rcases hMax a hne with ⟨p, hp, hmax⟩
    exact Or.inr ⟨p, hp, ordinalLike_eq_succ_of_mem_max M ha hp hmax⟩
  · left
    apply M.extensional
    intro x
    constructor
    · intro hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro hx
      exact False.elim (M.empty_spec x hx)

/-- Singleton inside a chosen first-order HF model. -/
def single {α : Type u} (M : FirstOrderAdjunctionModel α) (a : α) : α :=
  M.adjoin M.empty a

theorem single_spec {α : Type u} (M : FirstOrderAdjunctionModel α) (a x : α) :
    M.mem x (single M a) ↔ x = a := by
  rw [single, M.adjoin_spec]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (M.empty_spec x h)
    · exact h
  · intro h
    exact Or.inr h

/-- Unordered pair inside a chosen first-order HF model. -/
def upair {α : Type u} (M : FirstOrderAdjunctionModel α) (a b : α) : α :=
  M.adjoin (single M a) b

theorem upair_spec {α : Type u} (M : FirstOrderAdjunctionModel α) (a b x : α) :
    M.mem x (upair M a b) ↔ x = a ∨ x = b := by
  rw [upair, M.adjoin_spec, single_spec]

/-- Kuratowski ordered pair inside a chosen first-order HF model. -/
def kpair {α : Type u} (M : FirstOrderAdjunctionModel α) (a b : α) : α :=
  upair M (single M a) (upair M a b)

theorem kpair_mem {α : Type u} (M : FirstOrderAdjunctionModel α) (a b q : α) :
    M.mem q (kpair M a b) ↔ q = single M a ∨ q = upair M a b := by
  rw [kpair, upair_spec]

theorem single_injective {α : Type u} (M : FirstOrderAdjunctionModel α) {a b : α}
    (h : single M a = single M b) : a = b := by
  have ha : M.mem a (single M a) := (single_spec M a a).mpr rfl
  rw [h] at ha
  exact (single_spec M b a).mp ha

theorem upair_eq_single {α : Type u} (M : FirstOrderAdjunctionModel α) {a b c : α}
    (h : upair M a b = single M c) : a = c ∧ b = c := by
  constructor
  · have ha : M.mem a (upair M a b) := (upair_spec M a b a).mpr (Or.inl rfl)
    rw [h] at ha
    exact (single_spec M c a).mp ha
  · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
    rw [h] at hb
    exact (single_spec M c b).mp hb

theorem kpair_injective {α : Type u} (M : FirstOrderAdjunctionModel α) {a b c d : α}
    (h : kpair M a b = kpair M c d) : a = c ∧ b = d := by
  have hac : a = c := by
    have hs : M.mem (single M a) (kpair M a b) :=
      (kpair_mem M a b (single M a)).mpr (Or.inl rfl)
    rw [h] at hs
    rcases (kpair_mem M c d (single M a)).mp hs with hs | hs
    · exact single_injective M hs
    · exact ((upair_eq_single M hs.symm).1).symm
  subst c
  constructor
  · rfl
  · have h1 : M.mem (upair M a b) (kpair M a b) :=
      (kpair_mem M a b (upair M a b)).mpr (Or.inr rfl)
    rw [h] at h1
    rcases (kpair_mem M a d (upair M a b)).mp h1 with h1 | h1
    · have hba : b = a := (upair_eq_single M h1).2
      have h2 : M.mem (upair M a d) (kpair M a d) :=
        (kpair_mem M a d (upair M a d)).mpr (Or.inr rfl)
      rw [← h] at h2
      rcases (kpair_mem M a b (upair M a d)).mp h2 with h2 | h2
      · have hda : d = a := (upair_eq_single M h2).2
        rw [hba, hda]
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [h2] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hba, hd]
        · exact hd.symm
    · have hb : M.mem b (upair M a b) := (upair_spec M a b b).mpr (Or.inr rfl)
      rw [h1] at hb
      rcases (upair_spec M a d b).mp hb with hb | hb
      · have hd : M.mem d (upair M a d) := (upair_spec M a d d).mpr (Or.inr rfl)
        rw [← h1] at hd
        rcases (upair_spec M a b d).mp hd with hd | hd
        · rw [hb, hd]
        · exact hd.symm
      · exact hb

theorem HF_emptyAt_empty {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i : Nat) :
    Sat M.mem e (HF_emptyAt i) ↔ e i = M.empty := by
  constructor
  · intro h
    apply M.extensional
    intro x
    constructor
    · exact fun hx => False.elim (h x hx)
    · exact fun hx => False.elim (M.empty_spec x hx)
  · intro h x hx
    have hx' : M.mem x (e i) := by
      simpa [Sat, scons] using hx
    rw [h] at hx'
    exact M.empty_spec x hx'

theorem HF_adjoinAt_adjoin {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (c a b : Nat) :
    Sat M.mem e (HF_adjoinAt c a b) ↔ e c = M.adjoin (e a) (e b) := by
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [(HF_adjoinAt_spec e c a b).mp h x, M.adjoin_spec x (e a) (e b)]
  · intro h
    apply (HF_adjoinAt_spec e c a b).mpr
    intro x
    rw [h, M.adjoin_spec x (e a) (e b)]

theorem HF_succAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (s a : Nat) :
    Sat M.mem e (HF_succAt s a) ↔ e s = M.adjoin (e a) (e a) :=
  HF_adjoinAt_adjoin M e s a a

theorem HF_singleAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i j : Nat) :
    Sat M.mem e (HF_singleAt i j) ↔ e i = single M (e j) := by
  show (∀ x, (M.mem x (e i) → x = e j) ∧ (x = e j → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [single_spec M (e j) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, single_spec M (e j) x]
    exact ⟨id, id⟩

theorem HF_upairAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (i j k : Nat) :
    Sat M.mem e (HF_upairAt i j k) ↔ e i = upair M (e j) (e k) := by
  show (∀ x, (M.mem x (e i) → (x = e j ∨ x = e k)) ∧
             ((x = e j ∨ x = e k) → M.mem x (e i))) ↔ _
  constructor
  · intro h
    apply M.extensional
    intro x
    rw [upair_spec M (e j) (e k) x]
    exact ⟨(h x).1, (h x).2⟩
  · intro h x
    rw [h, upair_spec M (e j) (e k) x]
    exact ⟨id, id⟩

theorem HF_kpairAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (p a b : Nat) :
    Sat M.mem e (HF_kpairAt p a b) ↔ e p = kpair M (e a) (e b) := by
  have hq : ∀ q : α,
      (Sat M.mem (scons q e) (HF_singleAt 0 (a+1)) ∨
       Sat M.mem (scons q e) (HF_upairAt 0 (a+1) (b+1)))
        ↔ (q = single M (e a) ∨ q = upair M (e a) (e b)) := by
    intro q
    rw [HF_singleAt_spec M (scons q e) 0 (a+1),
        HF_upairAt_spec M (scons q e) 0 (a+1) (b+1)]
    exact Iff.rfl
  constructor
  · intro h
    apply M.extensional
    intro q
    rw [kpair_mem M (e a) (e b) q, ← hq q]
    exact ⟨(h q).1, (h q).2⟩
  · intro h q
    constructor
    · intro hq'
      have hqmem : M.mem q (e p) := hq'
      rw [h] at hqmem
      exact (hq q).mpr ((kpair_mem M (e a) (e b) q).mp hqmem)
    · intro hs
      show M.mem q (e p)
      rw [h]
      exact (kpair_mem M (e a) (e b) q).mpr ((hq q).mp hs)

theorem HF_pairMemAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (a b r : Nat) :
    Sat M.mem e (HF_pairMemAt a b r) ↔
      M.mem (kpair M (e a) (e b)) (e r) := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hmem⟩
    have hp' : p = kpair M (e a) (e b) :=
      (HF_kpairAt_spec M (scons p e) 0 (a+1) (b+1)).mp hp
    have hmem' : M.mem p (e r) := hmem
    rwa [hp'] at hmem'
  · intro h
    refine ⟨kpair M (e a) (e b), ?_, ?_⟩
    · exact (HF_kpairAt_spec M (scons (kpair M (e a) (e b)) e)
        0 (a+1) (b+1)).mpr rfl
    · exact h

/-- A set of first-order-model ordered pairs is single-valued in its second
component. -/
def PairFunctional {α : Type u} (M : FirstOrderAdjunctionModel α) (f : α) : Prop :=
  ∀ k y y', M.mem (kpair M k y) f → M.mem (kpair M k y') f → y = y'

/-- Every first component of a pair in `f` is a member of `m ∪ {m}`. -/
def PairKeysBelowSucc {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  ∀ k y, M.mem (kpair M k y) f → M.mem k m ∨ k = m

/-- Every element of `m ∪ {m}` appears as the first component of some pair in
`f`. -/
def PairTotalBelowSucc {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  ∀ k, M.mem k m ∨ k = m → ∃ y, M.mem (kpair M k y) f

/-- Successor-recursion step for a first-order-model pair set `f`. -/
def PairSuccStep {α : Type u} (M : FirstOrderAdjunctionModel α) (f m : α) : Prop :=
  ∀ k t y,
    M.mem k m →
    M.mem (kpair M k t) f →
    M.mem (kpair M (M.adjoin k k) y) f →
    y = M.adjoin t t

theorem HF_pairFunctionalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairFunctionalAt f) ↔ PairFunctional M (e f) := by
  constructor
  · intro h k y y' hky hky'
    exact h k y y'
      ⟨(HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 1 (f+3)).mpr hky,
       (HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 0 (f+3)).mpr hky'⟩
  · intro h k y y' hpairs
    exact h k y y'
      ((HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 1 (f+3)).mp hpairs.1)
      ((HF_pairMemAt_spec M (scons y' (scons y (scons k e))) 2 0 (f+3)).mp hpairs.2)

theorem HF_pairKeysBelowSuccAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairKeysBelowSuccAt f m) ↔
      PairKeysBelowSucc M (e f) (e m) := by
  constructor
  · intro h k y hky
    exact h k y
      ((HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mpr hky)
  · intro h k y hky
    exact h k y
      ((HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mp hky)

theorem HF_pairTotalBelowSuccAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairTotalBelowSuccAt f m) ↔
      PairTotalBelowSucc M (e f) (e m) := by
  constructor
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mp hy⟩
  · intro h k hk
    rcases h k hk with ⟨y, hy⟩
    exact ⟨y, (HF_pairMemAt_spec M (scons y (scons k e)) 1 0 (f+2)).mpr hy⟩

theorem HF_pairSuccStepAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f m : Nat) :
    Sat M.mem e (HF_pairSuccStepAt f m) ↔ PairSuccStep M (e f) (e m) := by
  constructor
  · intro h k t y hkm hkt hsy
    have hs := h k t y hkm
      ((HF_pairMemAt_spec M (scons y (scons t (scons k e))) 2 1 (f+3)).mpr hkt)
      (M.adjoin k k)
      ((HF_succAt_spec M
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 3).mpr rfl)
      ((HF_pairMemAt_spec M
        (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 0 1 (f+4)).mpr hsy)
    exact (HF_succAt_spec M
      (scons (M.adjoin k k) (scons y (scons t (scons k e)))) 1 2).mp hs
  · intro h k t y hkm hkt sk hsk hsky
    have hsk' : sk = M.adjoin k k :=
      (HF_succAt_spec M (scons sk (scons y (scons t (scons k e)))) 0 3).mp hsk
    have hsky' : M.mem (kpair M (M.adjoin k k) y) (e f) := by
      have hpair := (HF_pairMemAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 1 (f+4)).mp hsky
      rwa [hsk'] at hpair
    apply (HF_succAt_spec M
      (scons sk (scons y (scons t (scons k e)))) 1 2).mpr
    exact h k t y hkm
      ((HF_pairMemAt_spec M (scons y (scons t (scons k e))) 2 1 (f+3)).mp hkt)
      hsky'

theorem HF_pairBaseAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f s : Nat) :
    Sat M.mem e (HF_pairBaseAt f s) ↔
      M.mem (kpair M M.empty (e s)) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (HF_emptyAt_empty M (scons z e) 0).mp hz
    have hpair' := (HF_pairMemAt_spec M (scons z e) 0 (s+1) (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (HF_emptyAt_empty M (scons M.empty e) 0).mpr rfl
    · exact (HF_pairMemAt_spec M (scons M.empty e) 0 (s+1) (f+1)).mpr h

theorem HF_pairZeroBaseAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f : Nat) :
    Sat M.mem e (HF_pairZeroBaseAt f) ↔
      M.mem (kpair M M.empty M.empty) (e f) := by
  constructor
  · intro h
    rcases h with ⟨z, hz, hpair⟩
    have hz' : z = M.empty := (HF_emptyAt_empty M (scons z e) 0).mp hz
    have hpair' := (HF_pairMemAt_spec M (scons z e) 0 0 (f+1)).mp hpair
    rwa [hz'] at hpair'
  · intro h
    refine ⟨M.empty, ?_, ?_⟩
    · exact (HF_emptyAt_empty M (scons M.empty e) 0).mpr rfl
    · exact (HF_pairMemAt_spec M (scons M.empty e) 0 0 (f+1)).mpr h

/-- Semantic package for a finite successor-recursion trace in a chosen
first-order HF model. -/
def SuccRecApprox {α : Type u} (M : FirstOrderAdjunctionModel α) (s f m : α) : Prop :=
  PairFunctional M f ∧
  PairKeysBelowSucc M f m ∧
  M.mem (kpair M M.empty s) f ∧
  PairTotalBelowSucc M f m ∧
  PairSuccStep M f m

/-- Total successor-recursion data through a key `m`: a trace plus its value at
`m`. -/
def SuccRecTotal {α : Type u} (M : FirstOrderAdjunctionModel α) (s m : α) : Prop :=
  ∃ f z, SuccRecApprox M s f m ∧ M.mem (kpair M m z) f

/-- The one-pair graph `{⟨0,s⟩}` used for successor recursion through zero. -/
def zeroSuccRecGraph {α : Type u} (M : FirstOrderAdjunctionModel α) (s : α) : α :=
  single M (kpair M M.empty s)

theorem zeroSuccRecGraph_base {α : Type u} (M : FirstOrderAdjunctionModel α)
    (s : α) :
    M.mem (kpair M M.empty s) (zeroSuccRecGraph M s) :=
  (single_spec M (kpair M M.empty s) (kpair M M.empty s)).mpr rfl

theorem zeroSuccRecGraph_succRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) (s : α) :
    SuccRecApprox M s (zeroSuccRecGraph M s) M.empty := by
  refine ⟨?functional, ?keys, zeroSuccRecGraph_base M s, ?total, ?step⟩
  · intro k y y' hky hky'
    have hky_eq : kpair M k y = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y)).mp hky
    have hky'_eq : kpair M k y' = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y')).mp hky'
    have hy : y = s := (kpair_injective M hky_eq).2
    have hy' : y' = s := (kpair_injective M hky'_eq).2
    rw [hy, hy']
  · intro k y hky
    have hk_eq : kpair M k y = kpair M M.empty s :=
      (single_spec M (kpair M M.empty s) (kpair M k y)).mp hky
    exact Or.inr (kpair_injective M hk_eq).1
  · intro k hk
    rcases hk with hk | hk
    · exact False.elim (M.empty_spec k hk)
    · subst k
      exact ⟨s, zeroSuccRecGraph_base M s⟩
  · intro k _t _y hkm _ _
    exact False.elim (M.empty_spec k hkm)

/-- Successor-recursion is total through zero. -/
theorem succRecTotal_empty {α : Type u}
    (M : FirstOrderAdjunctionModel α) (s : α) :
    SuccRecTotal M s M.empty := by
  exact ⟨zeroSuccRecGraph M s, s,
    zeroSuccRecGraph_succRecApprox M s,
    zeroSuccRecGraph_base M s⟩

/-- Extend a successor-recursion graph by the next pair
`⟨m+1, z+1⟩`. -/
def succRecGraphSucc {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m z : α) : α :=
  M.adjoin f (kpair M (M.adjoin m m) (M.adjoin z z))

theorem succRecGraphSucc_old {α : Type u} (M : FirstOrderAdjunctionModel α)
    {f m z p : α} (hp : M.mem p f) :
    M.mem p (succRecGraphSucc M f m z) :=
  (M.adjoin_spec p f (kpair M (M.adjoin m m) (M.adjoin z z))).mpr (Or.inl hp)

theorem succRecGraphSucc_new {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m z : α) :
    M.mem (kpair M (M.adjoin m m) (M.adjoin z z))
      (succRecGraphSucc M f m z) :=
  (M.adjoin_spec (kpair M (M.adjoin m m) (M.adjoin z z))
    f (kpair M (M.adjoin m m) (M.adjoin z z))).mpr (Or.inr rfl)

theorem succRecGraphSucc_succRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) {s f m z : α}
    (hm : OrdinalLike M.mem m)
    (hf : SuccRecApprox M s f m)
    (hz : M.mem (kpair M m z) f) :
    SuccRecApprox M s (succRecGraphSucc M f m z) (M.adjoin m m) := by
  rcases hf with ⟨hfun, hkeys, hbase, htotal, hstep⟩
  let sm := M.adjoin m m
  let sz := M.adjoin z z
  let newPair := kpair M sm sz
  let g := succRecGraphSucc M f m z
  have hsm_not_mem : ¬ M.mem sm m := by
    simpa [sm] using adjoin_self_not_mem_of_ordinalLike M hm
  have hsm_ne_m : sm ≠ m := by
    simpa [sm] using adjoin_self_ne_self M m
  have hmem_g : ∀ p, M.mem p g ↔ M.mem p f ∨ p = newPair := by
    intro p
    exact M.adjoin_spec p f newPair
  have old_key_ne_succ :
      ∀ {k y}, M.mem (kpair M k y) f → k ≠ sm := by
    intro k y hOld hk
    have hkBound := hkeys k y hOld
    rw [hk] at hkBound
    rcases hkBound with hmem | heq
    · exact hsm_not_mem hmem
    · exact hsm_ne_m heq
  have pair_old_of_mem_key :
      ∀ {k y}, M.mem k m → M.mem (kpair M k y) g →
        M.mem (kpair M k y) f := by
    intro k y hkm hkg
    rcases (hmem_g (kpair M k y)).mp hkg with hOld | hNew
    · exact hOld
    · have hk : k = sm := (kpair_injective M hNew).1
      rw [hk] at hkm
      exact False.elim (hsm_not_mem hkm)
  refine ⟨?functional, ?keys, ?base, ?total, ?step⟩
  · intro k y y' hky hky'
    rcases (hmem_g (kpair M k y)).mp hky with hOld | hNew
    · rcases (hmem_g (kpair M k y')).mp hky' with hOld' | hNew'
      · exact hfun k y y' hOld hOld'
      · have hk : k = sm := (kpair_injective M hNew').1
        exact False.elim (old_key_ne_succ hOld hk)
    · rcases (hmem_g (kpair M k y')).mp hky' with hOld' | hNew'
      · have hk : k = sm := (kpair_injective M hNew).1
        exact False.elim (old_key_ne_succ hOld' hk)
      · have hy : y = sz := (kpair_injective M hNew).2
        have hy' : y' = sz := (kpair_injective M hNew').2
        rw [hy, hy']
  · intro k y hky
    rcases (hmem_g (kpair M k y)).mp hky with hOld | hNew
    · rcases hkeys k y hOld with hkm | hkm
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inl hkm))
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inr hkm))
    · exact Or.inr (kpair_injective M hNew).1
  · exact succRecGraphSucc_old M hbase
  · intro k hk
    rcases hk with hksm | hksm
    · rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
      · rcases htotal k (Or.inl hkm) with ⟨y, hy⟩
        exact ⟨y, succRecGraphSucc_old M hy⟩
      · rcases htotal k (Or.inr hkm) with ⟨y, hy⟩
        exact ⟨y, succRecGraphSucc_old M hy⟩
    · subst k
      exact ⟨sz, succRecGraphSucc_new M f m z⟩
  · intro k t y hksm hkt hsky
    rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
    · have hktOld : M.mem (kpair M k t) f :=
        pair_old_of_mem_key hkm hkt
      have hskyOld : M.mem (kpair M (M.adjoin k k) y) f := by
        rcases (hmem_g (kpair M (M.adjoin k k) y)).mp hsky with hOld | hNew
        · exact hOld
        · have hsk : M.adjoin k k = sm := (kpair_injective M hNew).1
          have hkOrd : OrdinalLike M.mem k := OrdinalLike.of_mem hm hkm
          have hkm_eq : k = m :=
            adjoin_self_injective_on_ordinalLike M hkOrd hm (by simpa [sm] using hsk)
          rw [hkm_eq] at hkm
          exact False.elim (mem_irrefl M m hkm)
      exact hstep k t y hkm hktOld hskyOld
    · subst k
      have hktOld : M.mem (kpair M m t) f := by
        rcases (hmem_g (kpair M m t)).mp hkt with hOld | hNew
        · exact hOld
        · have hm_eq_sm : m = sm := (kpair_injective M hNew).1
          exact False.elim (hsm_ne_m hm_eq_sm.symm)
      have ht : t = z := hfun m t z hktOld hz
      rcases (hmem_g (kpair M sm y)).mp hsky with hOld | hNew
      · exact False.elim (old_key_ne_succ hOld rfl)
      · have hy : y = sz := (kpair_injective M hNew).2
        rw [ht, hy]

/-- If successor-recursion is total through an ordinal-like key `m`, it is total
through its successor. -/
theorem succRecTotal_succ {α : Type u}
    (M : FirstOrderAdjunctionModel α) {s m : α}
    (hm : OrdinalLike M.mem m)
    (ht : SuccRecTotal M s m) :
    SuccRecTotal M s (M.adjoin m m) := by
  rcases ht with ⟨f, z, hf, hz⟩
  exact ⟨succRecGraphSucc M f m z, M.adjoin z z,
    succRecGraphSucc_succRecApprox M hm hf hz,
    succRecGraphSucc_new M f m z⟩

theorem HF_succRecApproxAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f s m : Nat) :
    Sat M.mem e (HF_succRecApproxAt f s m) ↔
      SuccRecApprox M (e s) (e f) (e m) := by
  change
    (Sat M.mem e (HF_pairFunctionalAt f) ∧
      (Sat M.mem e (HF_pairKeysBelowSuccAt f m) ∧
        (Sat M.mem e (HF_pairBaseAt f s) ∧
          (Sat M.mem e (HF_pairTotalBelowSuccAt f m) ∧
            Sat M.mem e (HF_pairSuccStepAt f m))))) ↔
      PairFunctional M (e f) ∧
        PairKeysBelowSucc M (e f) (e m) ∧
          M.mem (kpair M M.empty (e s)) (e f) ∧
            PairTotalBelowSucc M (e f) (e m) ∧
              PairSuccStep M (e f) (e m)
  rw [
    HF_pairFunctionalAt_spec M e f,
    HF_pairKeysBelowSuccAt_spec M e f m,
    HF_pairBaseAt_spec M e f s,
    HF_pairTotalBelowSuccAt_spec M e f m,
    HF_pairSuccStepAt_spec M e f m]

/-- Semantic reading of `HF_succRecTotalAt` in a chosen first-order adjunction
model. -/
theorem HF_succRecTotalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (s m : Nat) :
    Sat M.mem e (HF_succRecTotalAt s m) ↔
      SuccRecTotal M (e s) (e m) := by
  constructor
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    have hf' := (HF_succRecApproxAt_spec M (scons z (scons f e))
      1 (s+2) (m+2)).mp hf
    have hz' := (HF_pairMemAt_spec M (scons z (scons f e))
      (m+2) 0 1).mp hz
    change SuccRecApprox M (e s) f (e m) at hf'
    change M.mem (kpair M (e m) z) f at hz'
    exact ⟨f, z, hf', hz'⟩
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    refine ⟨f, z, ?_, ?_⟩
    · apply (HF_succRecApproxAt_spec M (scons z (scons f e))
        1 (s+2) (m+2)).mpr
      change SuccRecApprox M (e s) f (e m)
      exact hf
    · apply (HF_pairMemAt_spec M (scons z (scons f e))
        (m+2) 0 1).mpr
      change M.mem (kpair M (e m) z) f
      exact hz

/-- Semantic reading of the ordinal-relativized successor-recursion totality
formula. -/
theorem HF_succRecTotalOnOrdinalAt_spec {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α) (s m : Nat) :
    Sat M.mem e (HF_succRecTotalOnOrdinalAt s m) ↔
      (OrdinalLike M.mem (e m) → SuccRecTotal M (e s) (e m)) := by
  constructor
  · intro h hm
    exact (HF_succRecTotalAt_spec M e s m).mp
      (h ((HF_ordinalLikeAt_spec e m).mpr hm))
  · intro h hmSat
    exact (HF_succRecTotalAt_spec M e s m).mpr
      (h ((HF_ordinalLikeAt_spec e m).mp hmSat))

/-- If every ordinal-like object is either empty or a successor of one of its
members, first-order HF induction proves successor-recursion totality through
all ordinal-like keys. -/
theorem succRecTotal_of_ordinalLike_of_predecessor {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hPred : ∀ a, OrdinalLike M.mem a →
      a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p)
    (s m : α) (hm : OrdinalLike M.mem m) :
    SuccRecTotal M s m := by
  let phi : Form := HF_succRecTotalOnOrdinalAt 1 0
  let tail : Nat → α := fun _ => s
  have hind := M.induction_schema phi (scons s tail)
  have hall : ∀ a, Sat M.mem (scons a (scons s tail)) phi := by
    apply hind
    intro a ih
    apply (HF_succRecTotalOnOrdinalAt_spec M
      (scons a (scons s tail)) 1 0).mpr
    intro ha
    rcases hPred a ha with haEmpty | ⟨p, hpa, haSucc⟩
    · rw [haEmpty]
      exact succRecTotal_empty M s
    · have hpOrd : OrdinalLike M.mem p := OrdinalLike.of_mem ha hpa
      have hpSat : Sat M.mem (scons p (scons s tail)) phi :=
        (Sat_rename_rSkipParam phi (scons s tail) a p).mp (ih p hpa)
      have hpTotal : SuccRecTotal M s p := by
        simpa [phi, tail, scons] using
          ((HF_succRecTotalOnOrdinalAt_spec M
            (scons p (scons s tail)) 1 0).mp hpSat hpOrd)
      rw [haSucc]
      exact succRecTotal_succ M hpOrd hpTotal
  simpa [phi, tail, scons] using
    ((HF_succRecTotalOnOrdinalAt_spec M
      (scons m (scons s tail)) 1 0).mp (hall m) hm)

/-- A maximal-member principle for nonempty HF objects is enough to make
successor-recursion total on all ordinal-like keys. -/
theorem succRecTotal_of_ordinalLike_of_mem_max_exists {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hMax : ∀ a, (∃ x, M.mem x a) →
      ∃ p, M.mem p a ∧ ∀ q, M.mem q a → ¬ M.mem p q)
    (s m : α) (hm : OrdinalLike M.mem m) :
    SuccRecTotal M s m := by
  apply succRecTotal_of_ordinalLike_of_predecessor M
  · intro a ha
    exact ordinalLike_empty_or_succ_of_mem_max_exists M hMax ha
  · exact hm

end FirstOrderAdjunctionModel

def firstOrderHFModel_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    FirstOrderHFModel α where
  mem := mem
  extensional := semantic_extensionality_of_HFAx_s v hHF
  empty_exists := semantic_empty_of_HFAx_s v hHF
  adjoin_exists := semantic_adjoin_of_HFAx_s v hHF
  induction_schema := semantic_induction_schema_of_HFAx_s v hHF

/-- Select concrete empty and adjunction witnesses from any semantic model of
the sealed HF theory. -/
noncomputable def firstOrderAdjunctionModel_of_HFAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    FirstOrderAdjunctionModel α where
  mem := mem
  empty := Classical.choose (semantic_empty_of_HFAx_s v hHF)
  adjoin := fun a b => Classical.choose (semantic_adjoin_of_HFAx_s v hHF a b)
  extensional := semantic_extensionality_of_HFAx_s v hHF
  empty_spec := Classical.choose_spec (semantic_empty_of_HFAx_s v hHF)
  adjoin_spec := by
    intro x a b
    exact Classical.choose_spec (semantic_adjoin_of_HFAx_s v hHF a b) x
  induction_schema := semantic_induction_schema_of_HFAx_s v hHF

noncomputable def firstOrderFiniteAdjunctionModel_of_HFFinAx_s {α : Type u}
    {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    FirstOrderFiniteAdjunctionModel α where
  mem := mem
  empty := Classical.choose (semantic_empty_of_HFFinAx_s v hHF)
  adjoin := fun a b => Classical.choose (semantic_adjoin_of_HFFinAx_s v hHF a b)
  extensional := semantic_extensionality_of_HFFinAx_s v hHF
  empty_spec := Classical.choose_spec (semantic_empty_of_HFFinAx_s v hHF)
  adjoin_spec := by
    intro x a b
    exact Classical.choose_spec (semantic_adjoin_of_HFFinAx_s v hHF a b) x
  induction_schema := semantic_induction_schema_of_HFFinAx_s v hHF
  finite_induction_schema := semantic_finite_induction_schema_of_HFFinAx_s v hHF

namespace FirstOrderFiniteAdjunctionModel

theorem sepBy_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (psi : Form) (e : Nat → α) :
    ∀ a, ∃ s, ∀ x,
      M.mem x s ↔ M.mem x a ∧ Sat M.mem (scons x e) psi := by
  let theta : Form := rename rSepParam psi
  let phi : Form := HF_sepByAt theta 0
  have hind := M.finite_induction_schema phi e
  have hall : ∀ a, Sat M.mem (scons a e) phi := by
    apply (HF_finite_induction_form_spec phi e).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_sepByAt_spec theta (scons z e) 0).mpr
      refine ⟨M.empty, fun x => ?_⟩
      constructor
      · intro hx
        exact False.elim (M.empty_spec x hx)
      · intro hx
        exact False.elim (hzEmpty x hx.1)
    · intro a b c hc hOld
      rcases (HF_sepByAt_spec theta (scons a e) 0).mp hOld with ⟨s, hs⟩
      by_cases hb : Sat M.mem (scons b e) psi
      · apply (HF_sepByAt_spec theta (scons c e) 0).mpr
        refine ⟨M.adjoin s b, fun x => ?_⟩
        constructor
        · intro hx
          rcases (M.adjoin_spec x s b).mp hx with hxs | hxb
          · have hxOld := (hs x).mp hxs
            have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e a x).mp hxOld.2
            exact ⟨(hc x).mpr (Or.inl hxOld.1),
              (Sat_rename_rSepParam psi e c x).mpr hxPsi⟩
          · subst x
            exact ⟨(hc b).mpr (Or.inr rfl),
              (Sat_rename_rSepParam psi e c b).mpr hb⟩
        · intro hx
          rcases (hc x).mp hx.1 with hxa | hxb
          · apply (M.adjoin_spec x s b).mpr
            left
            have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e c x).mp hx.2
            exact (hs x).mpr
              ⟨hxa, (Sat_rename_rSepParam psi e a x).mpr hxPsi⟩
          · exact (M.adjoin_spec x s b).mpr (Or.inr hxb)
      · apply (HF_sepByAt_spec theta (scons c e) 0).mpr
        refine ⟨s, fun x => ?_⟩
        constructor
        · intro hxs
          have hxOld := (hs x).mp hxs
          have hxPsi : Sat M.mem (scons x e) psi :=
            (Sat_rename_rSepParam psi e a x).mp hxOld.2
          exact ⟨(hc x).mpr (Or.inl hxOld.1),
            (Sat_rename_rSepParam psi e c x).mpr hxPsi⟩
        · intro hx
          rcases (hc x).mp hx.1 with hxa | hxb
          · have hxPsi : Sat M.mem (scons x e) psi :=
              (Sat_rename_rSepParam psi e c x).mp hx.2
            exact (hs x).mpr
              ⟨hxa, (Sat_rename_rSepParam psi e a x).mpr hxPsi⟩
          · subst x
            have hb' : Sat M.mem (scons b e) psi :=
              (Sat_rename_rSepParam psi e c b).mp hx.2
            exact False.elim (hb hb')
  intro a
  rcases (HF_sepByAt_spec theta (scons a e) 0).mp (hall a) with ⟨s, hs⟩
  refine ⟨s, fun x => ?_⟩
  constructor
  · intro hxs
    have hx := (hs x).mp hxs
    have hxPsi : Sat M.mem (scons x e) psi :=
      (Sat_rename_rSepParam psi e a x).mp hx.2
    exact ⟨hx.1, hxPsi⟩
  · intro hx
    exact (hs x).mpr
      ⟨hx.1, (Sat_rename_rSepParam psi e a x).mpr hx.2⟩

theorem binUnion_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a b : α) :
    ∃ u, ∀ x, M.mem x u ↔ M.mem x a ∨ M.mem x b := by
  let phi : Form := HF_binUnionAt 1 0
  let tail : Nat → α := fun _ => a
  have hind := M.finite_induction_schema phi (scons a tail)
  have hall : ∀ b, Sat M.mem (scons b (scons a tail)) phi := by
    apply (HF_finite_induction_form_spec phi (scons a tail)).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_binUnionAt_spec (scons z (scons a tail)) 1 0).mpr
      refine ⟨a, fun x => ?_⟩
      constructor
      · intro hxa
        exact Or.inl hxa
      · intro hx
        rcases hx with hxa | hxz
        · exact hxa
        · exact False.elim (hzEmpty x hxz)
    · intro old y c hc hOld
      rcases (HF_binUnionAt_spec (scons old (scons a tail)) 1 0).mp hOld
        with ⟨u, hu⟩
      apply (HF_binUnionAt_spec (scons c (scons a tail)) 1 0).mpr
      refine ⟨M.adjoin u y, fun x => ?_⟩
      constructor
      · intro hx
        rcases (M.adjoin_spec x u y).mp hx with hxu | hxy
        · rcases (hu x).mp hxu with hxa | hxold
          · exact Or.inl hxa
          · exact Or.inr ((hc x).mpr (Or.inl hxold))
        · subst x
          exact Or.inr ((hc y).mpr (Or.inr rfl))
      · intro hx
        rcases hx with hxa | hxc
        · apply (M.adjoin_spec x u y).mpr
          exact Or.inl ((hu x).mpr (Or.inl hxa))
        · rcases (hc x).mp hxc with hxold | hxy
          · apply (M.adjoin_spec x u y).mpr
            exact Or.inl ((hu x).mpr (Or.inr hxold))
          · exact (M.adjoin_spec x u y).mpr (Or.inr hxy)
  simpa [phi, tail, scons] using
    (HF_binUnionAt_spec (scons b (scons a tail)) 1 0).mp (hall b)

theorem union_exists {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a : α) :
    ∃ u, ∀ x, M.mem x u ↔ ∃ v, M.mem v a ∧ M.mem x v := by
  let phi : Form := HF_unionAt 0
  let tail : Nat → α := fun _ => M.empty
  have hind := M.finite_induction_schema phi tail
  have hall : ∀ a, Sat M.mem (scons a tail) phi := by
    apply (HF_finite_induction_form_spec phi tail).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_unionAt_spec (scons z tail) 0).mpr
      refine ⟨M.empty, fun x => ?_⟩
      constructor
      · intro hx
        exact False.elim (M.empty_spec x hx)
      · intro hx
        rcases hx with ⟨v, hvz, _⟩
        exact False.elim (hzEmpty v hvz)
    · intro old y c hc hOld
      rcases (HF_unionAt_spec (scons old tail) 0).mp hOld with ⟨u, hu⟩
      rcases binUnion_exists M u y with ⟨w, hw⟩
      apply (HF_unionAt_spec (scons c tail) 0).mpr
      refine ⟨w, fun x => ?_⟩
      constructor
      · intro hxw
        rcases (hw x).mp hxw with hxu | hxy
        · rcases (hu x).mp hxu with ⟨v, hvold, hxv⟩
          exact ⟨v, (hc v).mpr (Or.inl hvold), hxv⟩
        · exact ⟨y, (hc y).mpr (Or.inr rfl), hxy⟩
      · intro hx
        rcases hx with ⟨v, hvc, hxv⟩
        rcases (hc v).mp hvc with hvold | hvy
        · apply (hw x).mpr
          exact Or.inl ((hu x).mpr ⟨v, hvold, hxv⟩)
        · subst v
          exact (hw x).mpr (Or.inr hxv)
  simpa [phi, tail, scons] using
    (HF_unionAt_spec (scons a tail) 0).mp (hall a)

theorem chainSubsetsMax_exists {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    ∀ a s, (∀ x, M.mem x s → M.mem x a) →
      ChainLike M.mem s →
        (∃ x, M.mem x s) →
          ∃ p, M.mem p s ∧ ∀ q, M.mem q s → ¬ M.mem p q := by
  let phi : Form := HF_chainSubsetsMaxAt 0
  let tail : Nat → α := fun _ => M.empty
  have hind := M.finite_induction_schema phi tail
  have hall : ∀ a, Sat M.mem (scons a tail) phi := by
    apply (HF_finite_induction_form_spec phi tail).mp hind
    constructor
    · intro z hzEmpty
      apply (HF_chainSubsetsMaxAt_spec (scons z tail) 0).mpr
      intro s hsSub _hsChain hsNonempty
      rcases hsNonempty with ⟨x, hxs⟩
      exact False.elim (hzEmpty x (hsSub x hxs))
    · intro old y c hc hOld
      have oldP :
          ∀ s, (∀ x, M.mem x s → M.mem x old) →
            ChainLike M.mem s →
              (∃ x, M.mem x s) →
                ∃ p, M.mem p s ∧ ∀ q, M.mem q s → ¬ M.mem p q :=
        (HF_chainSubsetsMaxAt_spec (scons old tail) 0).mp hOld
      apply (HF_chainSubsetsMaxAt_spec (scons c tail) 0).mpr
      intro s hsSub hsChain hsNonempty
      rcases sepBy_exists M (fMem 0 1) (scons s tail) old with ⟨t, ht⟩
      have htSubOld : ∀ x, M.mem x t → M.mem x old := by
        intro x hxt
        exact ((ht x).mp hxt).1
      have htSubS : ∀ x, M.mem x t → M.mem x s := by
        intro x hxt
        exact ((ht x).mp hxt).2
      have htChain : ChainLike M.mem t := by
        refine ⟨?trans, ?total⟩
        · intro x hxt
          exact hsChain.1 x (htSubS x hxt)
        · intro x hxt z hzt
          exact hsChain.2 x (htSubS x hxt) z (htSubS z hzt)
      by_cases htne : ∃ x, M.mem x t
      · rcases oldP t htSubOld htChain htne with ⟨p, hpt, hpMaxT⟩
        have hps : M.mem p s := htSubS p hpt
        by_cases hys : M.mem y s
        · rcases hsChain.2 p hps y hys with hpy | hpy | hyp
          · refine ⟨y, hys, ?_⟩
            intro q hqs hyq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              have htransq : TransitiveObj M.mem q := hsChain.1 q hqs
              have hpq : M.mem p q := htransq y hyq p hpy
              exact hpMaxT q hqt hpq
            · subst q
              exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hyq
          · subst p
            refine ⟨y, hys, ?_⟩
            intro q hqs hyq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              exact hpMaxT q hqt hyq
            · subst q
              exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hyq
          · refine ⟨p, hps, ?_⟩
            intro q hqs hpq
            rcases (hc q).mp (hsSub q hqs) with hqold | hqy
            · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
              exact hpMaxT q hqt hpq
            · subst q
              exact FirstOrderAdjunctionModel.mem_asymm
                M.toFirstOrderAdjunctionModel hyp hpq
        · refine ⟨p, hps, ?_⟩
          intro q hqs hpq
          rcases (hc q).mp (hsSub q hqs) with hqold | hqy
          · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
            exact hpMaxT q hqt hpq
          · subst q
            exact hys hqs
      · rcases hsNonempty with ⟨p, hps⟩
        have hp_eq_y : p = y := by
          rcases (hc p).mp (hsSub p hps) with hpold | hpy
          · have hpt : M.mem p t := (ht p).mpr ⟨hpold, hps⟩
            exact False.elim (htne ⟨p, hpt⟩)
          · exact hpy
        refine ⟨p, hps, ?_⟩
        intro q hqs hpq
        have hq_eq_y : q = y := by
          rcases (hc q).mp (hsSub q hqs) with hqold | hqy
          · have hqt : M.mem q t := (ht q).mpr ⟨hqold, hqs⟩
            exact False.elim (htne ⟨q, hqt⟩)
          · exact hqy
        subst p
        subst q
        exact FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel y hpq
  intro a s hsSub hsChain hsNonempty
  exact (HF_chainSubsetsMaxAt_spec (scons a tail) 0).mp (hall a)
    s hsSub hsChain hsNonempty

theorem ordinalLike_empty_or_succ {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    {a : α} (ha : OrdinalLike M.mem a) :
    a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p := by
  by_cases hne : ∃ x, M.mem x a
  · have hChain : ChainLike M.mem a := ⟨ha.2.1, ha.2.2⟩
    rcases chainSubsetsMax_exists M a a (fun _ hx => hx) hChain hne with
      ⟨p, hp, hmax⟩
    exact Or.inr ⟨p, hp,
      FirstOrderAdjunctionModel.ordinalLike_eq_succ_of_mem_max
        M.toFirstOrderAdjunctionModel ha hp hmax⟩
  · left
    apply M.extensional
    intro x
    constructor
    · intro hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro hx
      exact False.elim (M.empty_spec x hx)

theorem succRecTotal_of_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (s m : α) (hm : OrdinalLike M.mem m) :
    FirstOrderAdjunctionModel.SuccRecTotal M.toFirstOrderAdjunctionModel s m := by
  apply FirstOrderAdjunctionModel.succRecTotal_of_ordinalLike_of_predecessor
    M.toFirstOrderAdjunctionModel
  · intro a ha
    exact ordinalLike_empty_or_succ M ha
  · exact hm

/-- In finite HF, a successor-recursion trace starting from an ordinal-like
base assigns ordinal-like values to all keys covered by the trace.

The induction is over the key whose value is read from the trace, not over the
ambient endpoint of the trace.  This makes the successor case reusable: the
value at `p+1` is the successor of the value at `p`, and the induction
hypothesis applies to `p` inside the same ambient trace. -/
theorem succRecApprox_value_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {s f m z : α}
    (hs : OrdinalLike M.mem s) (hm : OrdinalLike M.mem m)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f) :
    OrdinalLike M.mem z := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fAll (fImp (HF_pairMemAt 2 0 4) (HF_ordinalLikeAt 0))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons s (scons f tail))
  have hall : ∀ k, Sat M.mem (scons k (scons s (scons f tail))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat z hpairSat
    let Em : Nat → α := scons m (scons k (scons s (scons f tail)))
    let Ez : Nat → α := scons z Em
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : FirstOrderAdjunctionModel.SuccRecApprox N s f m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hpair : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hpairSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases ordinalLike_empty_or_succ M hkOrd with hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hpairEmpty : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpair
      have hz_eq_s : z = s := hfun N.empty z s hpairEmpty hbase
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      simpa [Ez, Em, hz_eq_s, N, scons] using hs
    · rcases hfApprox with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotal p (Or.inl hpm) with ⟨t, hpt⟩
      have hpSat : Sat M.mem (scons p (scons s (scons f tail))) phi :=
        (Sat_rename_rSkipParam phi (scons s (scons f tail)) k p).mp (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons s (scons f tail)))
      let Etp : Nat → α := scons t Emp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (HF_succRecApproxAt 3 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have htDomain : Sat M.mem Etp (HF_ordinalLikeAt 0) :=
        hpSat m (Or.inl hpm) hmSatP hfSatP t hptSat
      have htOrd : OrdinalLike M.mem t :=
        (HF_ordinalLikeAt_spec Etp 0).mp htDomain
      have hpairSucc : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpair
      have hz_eq_succ : z = N.adjoin t t := hstep p t z hpm hpt hpairSucc
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      exact FirstOrderAdjunctionModel.ordinalLike_adjoin_self N htOrd hz_eq_succ
  let Em : Nat → α := scons m (scons m (scons s (scons f tail)))
  let Ez : Nat → α := scons z Em
  have hmain : Sat M.mem (scons m (scons s (scons f tail))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (HF_succRecApproxAt 3 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hzDomain : Sat M.mem Ez (HF_ordinalLikeAt 0) :=
    hmain m (Or.inr rfl) hmSat hfSat z hzSat
  exact (HF_ordinalLikeAt_spec Ez 0).mp hzDomain

/-- In finite HF, successor-recursion traces with the same base have a unique
value at every ordinal-like key covered by both traces. -/
theorem succRecApprox_value_unique {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {s f g m z w : α}
    (hm : OrdinalLike M.mem m)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel s g m)
    (hw : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m w) g) :
    z = w := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (HF_succRecApproxAt 3 2 0)
            (fImp (HF_succRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons s (scons f (scons g tail)))
  have hall : ∀ k, Sat M.mem (scons k (scons s (scons f (scons g tail)))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat hgSat z hzSat w hwSat
    let Em : Nat → α := scons m (scons k (scons s (scons f (scons g tail))))
    let Ez : Nat → α := scons z Em
    let Ewz : Nat → α := scons w Ez
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : FirstOrderAdjunctionModel.SuccRecApprox N s f m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hgApprox : FirstOrderAdjunctionModel.SuccRecApprox N s g m := by
      simpa [N, Em, tail, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 4 2 0).mp hgSat
    have hpairF : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hzSat
    have hpairG : N.mem (FirstOrderAdjunctionModel.kpair N k w) g := by
      simpa [N, Em, Ez, Ewz, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mp hwSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases ordinalLike_empty_or_succ M hkOrd with hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfunF, _hkeysF, hbaseF, _htotalF, _hstepF⟩
      rcases hgApprox with ⟨hfunG, _hkeysG, hbaseG, _htotalG, _hstepG⟩
      have hpairEmptyF : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpairF
      have hpairEmptyG : N.mem (FirstOrderAdjunctionModel.kpair N N.empty w) g := by
        simpa [N, hkEmpty] using hpairG
      have hz_eq_s : z = s := hfunF N.empty z s hpairEmptyF hbaseF
      have hw_eq_s : w = s := hfunG N.empty w s hpairEmptyG hbaseG
      exact hz_eq_s.trans hw_eq_s.symm
    · rcases hfApprox with ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      rcases hgApprox with ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotalF p (Or.inl hpm) with ⟨t, hpt⟩
      rcases htotalG p (Or.inl hpm) with ⟨u, hpu⟩
      have hpSat : Sat M.mem (scons p (scons s (scons f (scons g tail)))) phi :=
        (Sat_rename_rSkipParam phi (scons s (scons f (scons g tail))) k p).mp
          (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons s (scons f (scons g tail))))
      let Etp : Nat → α := scons t Emp
      let Eutp : Nat → α := scons u Etp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (HF_succRecApproxAt 3 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      have hgSatP : Sat M.mem Emp (HF_succRecApproxAt 4 2 0) := by
        apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Emp 4 2 0).mpr
        exact ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have hpuSat : Sat M.mem Eutp (HF_pairMemAt 3 0 6) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Eutp 3 0 6).mpr
        simpa [N, Emp, Etp, Eutp, tail, scons] using hpu
      have htu : t = u :=
        hpSat m (Or.inl hpm) hmSatP hfSatP hgSatP t hptSat u hpuSat
      have hpairSuccF : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpairF
      have hpairSuccG : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) w) g := by
        simpa [N, hkSucc] using hpairG
      have hz_eq_succ : z = N.adjoin t t :=
        hstepF p t z hpm hpt hpairSuccF
      have hw_eq_succ : w = N.adjoin u u :=
        hstepG p u w hpm hpu hpairSuccG
      rw [hz_eq_succ, hw_eq_succ, htu]
      rfl
  let Em : Nat → α := scons m (scons m (scons s (scons f (scons g tail))))
  let Ez : Nat → α := scons z Em
  let Ewz : Nat → α := scons w Ez
  have hmain : Sat M.mem (scons m (scons s (scons f (scons g tail)))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (HF_succRecApproxAt 3 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hgSat : Sat M.mem Em (HF_succRecApproxAt 4 2 0) := by
    apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N Em 4 2 0).mpr
    simpa [N, Em, tail, scons] using hg
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hwSat : Sat M.mem Ewz (HF_pairMemAt 3 0 6) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mpr
    simpa [N, Em, Ez, Ewz, tail, scons] using hw
  exact hmain m (Or.inr rfl) hmSat hfSat hgSat z hzSat w hwSat

end FirstOrderFiniteAdjunctionModel

/-! ## The finite von Neumann ordinals inside Ackermann HF -/

/-- Ackermann code of the finite von Neumann ordinal `n`.

This is deliberately just the recursive set-theoretic construction:
`0 = ∅` and `n+1 = n ∪ {n}`.  The fact that it is an embedding, and the
description of its members, are separate theorems below. -/
def ordinalCode : Nat → Nat
  | 0 => empty
  | n+1 => adjoin (ordinalCode n) (ordinalCode n)

theorem ordinalCode_zero : ordinalCode 0 = empty := rfl

theorem ordinalCode_succ (n : Nat) :
    ordinalCode (n+1) = adjoin (ordinalCode n) (ordinalCode n) := rfl

theorem mem_ordinalCode_succ (x n : Nat) :
    Mem x (ordinalCode (n+1)) ↔ Mem x (ordinalCode n) ∨ x = ordinalCode n := by
  rw [ordinalCode_succ, mem_adjoin]

theorem mem_ordinalCode_iff (x n : Nat) :
    Mem x (ordinalCode n) ↔ ∃ k, k < n ∧ x = ordinalCode k := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim (mem_empty x h)
      · intro h
        rcases h with ⟨k, hk, _⟩
        omega
  | succ n ih =>
      rw [mem_ordinalCode_succ]
      constructor
      · intro h
        rcases h with h | h
        · rcases ih.mp h with ⟨k, hk, hx⟩
          exact ⟨k, by omega, hx⟩
        · exact ⟨n, by omega, h⟩
      · intro h
        rcases h with ⟨k, hk, hx⟩
        have hle : k ≤ n := Nat.lt_succ_iff.mp hk
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl (ih.mpr ⟨k, hlt, hx⟩)
        · exact Or.inr (by subst heq; exact hx)

theorem ordinalCode_mem_of_lt {k n : Nat} (h : k < n) :
    Mem (ordinalCode k) (ordinalCode n) :=
  (mem_ordinalCode_iff (ordinalCode k) n).mpr ⟨k, h, rfl⟩

theorem ordinalCode_lt_of_lt {k n : Nat} (h : k < n) :
    ordinalCode k < ordinalCode n :=
  mem_lt (ordinalCode_mem_of_lt h)

theorem ordinalCode_transitive (n : Nat) : TransitiveObj Mem (ordinalCode n) := by
  intro y hy x hx
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨k, hk, rfl⟩
  rcases (mem_ordinalCode_iff x k).mp hx with ⟨j, hj, rfl⟩
  exact ordinalCode_mem_of_lt (Nat.lt_trans hj hk)

theorem ordinalCode_members_transitive (n : Nat) :
    ∀ y, Mem y (ordinalCode n) → TransitiveObj Mem y := by
  intro y hy
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨k, _hk, rfl⟩
  exact ordinalCode_transitive k

theorem ordinalCode_memTotalOn (n : Nat) : MemTotalOn Mem (ordinalCode n) := by
  intro y hy z hz
  rcases (mem_ordinalCode_iff y n).mp hy with ⟨j, _hj, rfl⟩
  rcases (mem_ordinalCode_iff z n).mp hz with ⟨k, _hk, rfl⟩
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (Or.inl (by rw [heq]))
  · exact Or.inr (Or.inr (ordinalCode_mem_of_lt hgt))

theorem ordinalCode_ordinalLike (n : Nat) : OrdinalLike Mem (ordinalCode n) :=
  ⟨ordinalCode_transitive n, ordinalCode_members_transitive n, ordinalCode_memTotalOn n⟩

theorem HF_ordinalLikeAt_of_ordinalCode (e : Nat → Nat) (i n : Nat)
    (h : e i = ordinalCode n) : Sat Mem e (HF_ordinalLikeAt i) :=
  (HF_ordinalLikeAt_spec e i).mpr (by rw [h]; exact ordinalCode_ordinalLike n)

def IsOrdinalCode (a : Nat) : Prop := ∃ n, ordinalCode n = a

theorem ordinalLike_is_ordinalCode (a : Nat)
    (ha : OrdinalLike Mem a) : IsOrdinalCode a := by
  exact Nat.strongRecOn a (fun a ih ha => by
    by_cases hzero : a = empty
    · exact ⟨0, by rw [ordinalCode_zero, ← hzero]⟩
    · obtain ⟨m, hm, hmax⟩ := exists_max_mem_of_ne_empty hzero
      rcases ih m (mem_lt hm) (OrdinalLike.of_mem ha hm) with ⟨k, hk⟩
      refine ⟨k+1, ?_⟩
      apply ext
      intro x
      constructor
      · intro hx
        rcases (mem_ordinalCode_succ x k).mp hx with hxk | hxk
        · have hxm : Mem x m := by
            rwa [hk] at hxk
          exact ha.1 m hm x hxm
        · rw [hxk, hk]
          exact hm
      · intro hx
        rcases ih x (mem_lt hx) (OrdinalLike.of_mem ha hx) with ⟨j, hj⟩
        have hjle : j ≤ k := by
          have hnot : ¬ k < j := by
            intro hkj
            have hlt : m < x := by
              have hlt0 := ordinalCode_lt_of_lt hkj
              rwa [hk, hj] at hlt0
            exact Nat.not_lt_of_ge (hmax x hx) hlt
          omega
        rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
        · apply (mem_ordinalCode_succ x k).mpr
          left
          rw [← hj]
          exact ordinalCode_mem_of_lt hjlt
        · apply (mem_ordinalCode_succ x k).mpr
          right
          rw [← hj, hjeq])
    ha

theorem HF_ordinalLikeAt_exact (e : Nat → Nat) (i : Nat) :
    Sat Mem e (HF_ordinalLikeAt i) ↔ IsOrdinalCode (e i) :=
  ⟨fun h => ordinalLike_is_ordinalCode (e i) ((HF_ordinalLikeAt_spec e i).mp h),
   fun h => by
    rcases h with ⟨n, hn⟩
    exact HF_ordinalLikeAt_of_ordinalCode e i n hn.symm⟩

theorem not_mem_self (a : Nat) : ¬ Mem a a := fun h =>
  Nat.lt_irrefl a (mem_lt h)

theorem ordinalCode_injective {m n : Nat}
    (h : ordinalCode m = ordinalCode n) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have hm : Mem (ordinalCode m) (ordinalCode n) := ordinalCode_mem_of_lt hlt
    rw [← h] at hm
    exact False.elim (not_mem_self (ordinalCode m) hm)
  · exact heq
  · have hn : Mem (ordinalCode n) (ordinalCode m) := ordinalCode_mem_of_lt hgt
    rw [h] at hn
    exact False.elim (not_mem_self (ordinalCode n) hn)

/-! ### Standard finite traces for successor recursion -/

/-- Iterate the HF successor operation `x ↦ x ∪ {x}` on an object. -/
def succIterObj (s : Nat) : Nat → Nat
  | 0 => s
  | n+1 => adjoin (succIterObj s n) (succIterObj s n)

theorem succIterObj_ordinalCode (m n : Nat) :
    succIterObj (ordinalCode m) n = ordinalCode (m + n) := by
  induction n with
  | zero =>
      simp [succIterObj]
  | succ n ih =>
      rw [succIterObj, ih, Nat.add_succ, ordinalCode_succ]

/-- The finite graph `{⟨0,s⟩, ⟨1,S s⟩, ..., ⟨n,S^n s⟩}` as an HF set. -/
def succRecTrace (s : Nat) : Nat → Nat
  | 0 => single standardModel (kpair standardModel empty s)
  | n+1 =>
      adjoin (succRecTrace s n)
        (kpair standardModel (ordinalCode (n+1)) (succIterObj s (n+1)))

theorem succRecTrace_mem_iff (s p n : Nat) :
    Mem p (succRecTrace s n) ↔
      ∃ k, k ≤ n ∧ p = kpair standardModel (ordinalCode k) (succIterObj s k) := by
  induction n with
  | zero =>
      constructor
      · intro hp
        have hp' := (single_spec standardModel (kpair standardModel empty s) p).mp hp
        exact ⟨0, by omega, by simpa [ordinalCode_zero, succIterObj] using hp'⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hk0 : k = 0 := by omega
        subst k
        apply (single_spec standardModel (kpair standardModel empty s) p).mpr
        simpa [ordinalCode_zero, succIterObj] using hp
  | succ n ih =>
      rw [succRecTrace, mem_adjoin, ih]
      constructor
      · intro hp
        rcases hp with hp | hp
        · rcases hp with ⟨k, hk, hp⟩
          exact ⟨k, by omega, hp⟩
        · exact ⟨n+1, by omega, hp⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hcases : k ≤ n ∨ k = n+1 := by omega
        rcases hcases with hle | heq
        · exact Or.inl ⟨k, hle, hp⟩
        · subst k
          exact Or.inr hp

theorem succRecTrace_pair_mem (s : Nat) {k n : Nat} (hk : k ≤ n) :
    Mem (kpair standardModel (ordinalCode k) (succIterObj s k)) (succRecTrace s n) :=
  (succRecTrace_mem_iff s _ n).mpr ⟨k, hk, rfl⟩

theorem succRecTrace_functional (s n : Nat) :
    PairFunctional standardModel (succRecTrace s n) := by
  intro k y y' hky hky'
  rcases (succRecTrace_mem_iff s _ n).mp hky with ⟨i, _hi, hpair_i⟩
  rcases (succRecTrace_mem_iff s _ n).mp hky' with ⟨j, _hj, hpair_j⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hcomp_i.1.symm.trans hcomp_j.1
  rw [hcomp_i.2, hcomp_j.2, hij]

theorem succRecTrace_keysBelowSucc (s n : Nat) :
    PairKeysBelowSucc standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k y hky
  rcases (succRecTrace_mem_iff s _ n).mp hky with ⟨i, hi, hpair_i⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  rw [hcomp_i.1]
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (by rw [heq])

theorem succRecTrace_totalBelowSucc (s n : Nat) :
    PairTotalBelowSucc standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k hk
  rcases hk with hmem | heq
  · rcases (mem_ordinalCode_iff k n).mp hmem with ⟨i, hi, rfl⟩
    exact ⟨succIterObj s i, succRecTrace_pair_mem s (Nat.le_of_lt hi)⟩
  · rw [heq]
    exact ⟨succIterObj s n, succRecTrace_pair_mem s (Nat.le_refl n)⟩

theorem succRecTrace_succStep (s n : Nat) :
    PairSuccStep standardModel (succRecTrace s n) (ordinalCode n) := by
  intro k t y hkm hkt hsy
  rcases (mem_ordinalCode_iff k n).mp hkm with ⟨i, _hi, hk⟩
  rcases (succRecTrace_mem_iff s _ n).mp hkt with ⟨j, _hj, hpair_j⟩
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hk.symm.trans hcomp_j.1
  have ht : t = succIterObj s i := by
    rw [hcomp_j.2, ← hij]
  have hsucck : adjoin k k = ordinalCode (i+1) := by
    rw [hk, ordinalCode_succ]
  rcases (succRecTrace_mem_iff s _ n).mp hsy with ⟨l, _hl, hpair_l⟩
  have hcomp_l := kpair_injective standardModel hpair_l
  have hil : i+1 = l := by
    apply ordinalCode_injective
    exact hsucck.symm.trans hcomp_l.1
  have hy : y = succIterObj s (i+1) := by
    rw [hcomp_l.2, ← hil]
  rw [hy, ht, succIterObj]
  rfl

theorem succRecTrace_succRecApprox (s n : Nat) :
    SuccRecApprox standardModel s (succRecTrace s n) (ordinalCode n) := by
  refine ⟨succRecTrace_functional s n,
    succRecTrace_keysBelowSucc s n,
    ?_,
    succRecTrace_totalBelowSucc s n,
    succRecTrace_succStep s n⟩
  change Mem (kpair standardModel empty s) (succRecTrace s n)
  simpa [ordinalCode_zero, succIterObj] using
    (succRecTrace_pair_mem s (k := 0) (n := n) (Nat.zero_le n))

theorem succRecApprox_value_of_le (s f : Nat) :
    ∀ n N y,
      SuccRecApprox standardModel s f (ordinalCode N) →
      n ≤ N →
      Mem (kpair standardModel (ordinalCode n) y) f →
      y = succIterObj s n := by
  intro n
  induction n with
  | zero =>
      intro N y hA _hn hy
      rcases hA with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hbase' : Mem (kpair standardModel (ordinalCode 0) s) f := by
        simpa [standardModel, ordinalCode_zero] using hbase
      have hy_eq := hfun (ordinalCode 0) y s hy hbase'
      simpa [succIterObj] using hy_eq
  | succ n ih =>
      intro N y hA hn hy
      have hA' := hA
      rcases hA with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hnlt : n < N := by omega
      rcases htotal (ordinalCode n) (Or.inl (ordinalCode_mem_of_lt hnlt)) with ⟨t, ht⟩
      have htval := ih N t hA' (Nat.le_of_lt hnlt) ht
      have hysucc :
          Mem (kpair standardModel (adjoin (ordinalCode n) (ordinalCode n)) y) f := by
        rw [← ordinalCode_succ]
        exact hy
      have hstepval := hstep (ordinalCode n) t y
        (ordinalCode_mem_of_lt hnlt) ht hysucc
      rw [hstepval, htval, succIterObj]
      rfl

/-! ### Standard finite traces for multiplication recursion -/

/-- The finite graph `{⟨0,0⟩, ⟨1,m⟩, ..., ⟨n,m*n⟩}` as an HF set. -/
def mulRecTrace (m : Nat) : Nat → Nat
  | 0 => single standardModel (kpair standardModel empty empty)
  | n+1 =>
      adjoin (mulRecTrace m n)
        (kpair standardModel (ordinalCode (n+1)) (ordinalCode (m * (n+1))))

theorem mulRecTrace_mem_iff (m p n : Nat) :
    Mem p (mulRecTrace m n) ↔
      ∃ k, k ≤ n ∧ p = kpair standardModel (ordinalCode k) (ordinalCode (m * k)) := by
  induction n with
  | zero =>
      constructor
      · intro hp
        have hp' := (single_spec standardModel (kpair standardModel empty empty) p).mp hp
        exact ⟨0, by omega, by simpa [ordinalCode_zero] using hp'⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hk0 : k = 0 := by omega
        subst k
        apply (single_spec standardModel (kpair standardModel empty empty) p).mpr
        simpa [ordinalCode_zero] using hp
  | succ n ih =>
      rw [mulRecTrace, mem_adjoin, ih]
      constructor
      · intro hp
        rcases hp with hp | hp
        · rcases hp with ⟨k, hk, hp⟩
          exact ⟨k, by omega, hp⟩
        · exact ⟨n+1, by omega, hp⟩
      · intro hp
        rcases hp with ⟨k, hk, hp⟩
        have hcases : k ≤ n ∨ k = n+1 := by omega
        rcases hcases with hle | heq
        · exact Or.inl ⟨k, hle, hp⟩
        · subst k
          exact Or.inr hp

theorem mulRecTrace_pair_mem (m : Nat) {k n : Nat} (hk : k ≤ n) :
    Mem (kpair standardModel (ordinalCode k) (ordinalCode (m * k))) (mulRecTrace m n) :=
  (mulRecTrace_mem_iff m _ n).mpr ⟨k, hk, rfl⟩

theorem mulRecTrace_functional (m n : Nat) :
    PairFunctional standardModel (mulRecTrace m n) := by
  intro k y y' hky hky'
  rcases (mulRecTrace_mem_iff m _ n).mp hky with ⟨i, _hi, hpair_i⟩
  rcases (mulRecTrace_mem_iff m _ n).mp hky' with ⟨j, _hj, hpair_j⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  have hcomp_j := kpair_injective standardModel hpair_j
  have hij : i = j := by
    apply ordinalCode_injective
    exact hcomp_i.1.symm.trans hcomp_j.1
  rw [hcomp_i.2, hcomp_j.2, hij]

theorem mulRecTrace_keysBelowSucc (m n : Nat) :
    PairKeysBelowSucc standardModel (mulRecTrace m n) (ordinalCode n) := by
  intro k y hky
  rcases (mulRecTrace_mem_iff m _ n).mp hky with ⟨i, hi, hpair_i⟩
  have hcomp_i := kpair_injective standardModel hpair_i
  rw [hcomp_i.1]
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact Or.inl (ordinalCode_mem_of_lt hlt)
  · exact Or.inr (by rw [heq])

theorem mulRecTrace_totalBelowSucc (m n : Nat) :
    PairTotalBelowSucc standardModel (mulRecTrace m n) (ordinalCode n) := by
  intro k hk
  rcases hk with hmem | heq
  · rcases (mem_ordinalCode_iff k n).mp hmem with ⟨i, hi, rfl⟩
    exact ⟨ordinalCode (m * i), mulRecTrace_pair_mem m (Nat.le_of_lt hi)⟩
  · rw [heq]
    exact ⟨ordinalCode (m * n), mulRecTrace_pair_mem m (Nat.le_refl n)⟩

/-! ### First PA-in-HF interpretation formulas already available -/

namespace PAInHF

/-- Domain formula for the PA interpretation in HF: finite ordinals. -/
def domainForm : Form := HF_ordinalLikeAt 0

/-- Graph formula for PA zero in HF.  Slot `0` is the candidate output. -/
def zeroGraph : Form := HF_emptyAt 0

/-- Graph formula for PA successor in HF.  Slot `0` is the output and slot `1`
is the input. -/
def succGraph : Form := HF_succAt 0 1

/-- Addition graph formula at arbitrary slots: `out = left + right`.  The
witness is a finite successor-recursion graph from `left` through `right`. -/
def addGraphAt (out left right : Nat) : Form :=
  fEx (fAnd (HF_succRecApproxAt 0 (left+1) (right+1))
    (HF_pairMemAt (right+1) (out+1) 0))

/-- Graph formula for PA addition in HF.  Slot `0` is the output, slot `1`
is the left input, and slot `2` is the right input. -/
def addGraph : Form := addGraphAt 0 1 2

/-- Step clause for multiplication recursion: if `f(k)=t` and `f(k+1)=y`,
then `y = t + a`, where `a` is the fixed left multiplicand. -/
def mulStepAt (f a m : Nat) : Form :=
  fAll (fAll (fAll
    (fImp
      (fMem 2 (m+3))
      (fImp
        (HF_pairMemAt 2 1 (f+3))
        (fAll
          (fImp
            (HF_succAt 0 3)
            (fImp
              (HF_pairMemAt 0 1 (f+4))
              (addGraphAt 1 2 (a+4)))))))))

/-- Formula macro for a finite multiplication-recursion trace.  Slot `f` is
the graph of `k ↦ a*k`, defined on keys up to slot `m`. -/
def mulRecApproxAt (f a m : Nat) : Form :=
  fAnd (HF_pairFunctionalAt f)
    (fAnd (HF_pairKeysBelowSuccAt f m)
      (fAnd (HF_pairZeroBaseAt f)
        (fAnd (HF_pairTotalBelowSuccAt f m)
          (mulStepAt f a m))))

/-- Multiplication graph formula at arbitrary slots: `out = left * right`. -/
def mulGraphAt (out left right : Nat) : Form :=
  fEx (fAnd (mulRecApproxAt 0 (left+1) (right+1))
    (HF_pairMemAt (right+1) (out+1) 0))

/-- Graph formula for PA multiplication in HF.  Slot `0` is the output, slot
`1` is the left input, and slot `2` is the right input. -/
def mulGraph : Form := mulGraphAt 0 1 2

/-- Totality formula for a multiplication-recursion trace.  Slot `a` is the
fixed left multiplicand and slot `m` is the right multiplicand/key. -/
def mulRecTotalAt (a m : Nat) : Form :=
  fEx (fEx (fAnd
    (mulRecApproxAt 1 (a+2) (m+2))
    (HF_pairMemAt (m+2) 0 1)))

/-- Multiplication-recursion totality, relativized to ordinal-like right
inputs.  The left multiplicand remains an explicit parameter. -/
def mulRecTotalOnOrdinalAt (a m : Nat) : Form :=
  fImp (HF_ordinalLikeAt m) (mulRecTotalAt a m)

/-- Semantic step clause for multiplication recursion in a chosen first-order
HF model: when `f(k)=t` and `f(k+1)=y`, the value `y` is obtained from an
addition trace for `t+a`. -/
def MulStep {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f a m : α) : Prop :=
  ∀ k t y,
    M.mem k m →
    M.mem (FirstOrderAdjunctionModel.kpair M k t) f →
    M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) y) f →
    ∃ g,
      FirstOrderAdjunctionModel.SuccRecApprox M t g a ∧
        M.mem (FirstOrderAdjunctionModel.kpair M a y) g

/-- Semantic package for a finite multiplication-recursion trace in a chosen
first-order HF model. -/
def MulRecApprox {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a f m : α) : Prop :=
  FirstOrderAdjunctionModel.PairFunctional M f ∧
  FirstOrderAdjunctionModel.PairKeysBelowSucc M f m ∧
  M.mem (FirstOrderAdjunctionModel.kpair M M.empty M.empty) f ∧
  FirstOrderAdjunctionModel.PairTotalBelowSucc M f m ∧
  MulStep M f a m

/-- Total multiplication-recursion data through a key `m`: a trace plus its
value at `m`. -/
def MulRecTotal {α : Type u} (M : FirstOrderAdjunctionModel α)
    (a m : α) : Prop :=
  ∃ f z, MulRecApprox M a f m ∧
    M.mem (FirstOrderAdjunctionModel.kpair M m z) f

theorem domainForm_free {i : Nat} (h : Free i domainForm) : i = 0 := by
  exact HF_ordinalLikeAt_free h

theorem zeroGraph_free {i : Nat} (h : Free i zeroGraph) : i = 0 := by
  exact HF_emptyAt_free h

theorem succGraph_free {i : Nat} (h : Free i succGraph) : i = 0 ∨ i = 1 := by
  exact HF_succAt_free h

theorem addGraphAt_free {i out left right : Nat}
    (h : Free i (addGraphAt out left right)) : i = out ∨ i = left ∨ i = right := by
  simp only [addGraphAt, Free] at h
  rcases h with h | h
  · have hs := HF_succRecApproxAt_free h
    omega
  · have hp := HF_pairMemAt_free h
    omega

theorem addGraph_free {i : Nat} (h : Free i addGraph) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact addGraphAt_free h

theorem mulStepAt_free {i f a m : Nat} (h : Free i (mulStepAt f a m)) :
    i = f ∨ i = a ∨ i = m := by
  simp only [mulStepAt, Free] at h
  rcases h with h | h
  · omega
  · rcases h with h | h
    · have hp := HF_pairMemAt_free h
      omega
    · rcases h with h | h
      · have hs := HF_succAt_free h
        omega
      · rcases h with h | h
        · have hp := HF_pairMemAt_free h
          omega
        · have ha := addGraphAt_free h
          omega

theorem mulRecApproxAt_free {i f a m : Nat} (h : Free i (mulRecApproxAt f a m)) :
    i = f ∨ i = a ∨ i = m := by
  simp only [mulRecApproxAt, Free] at h
  rcases h with h | h
  · have hf := HF_pairFunctionalAt_free h
    omega
  · rcases h with h | h
    · have hfm := HF_pairKeysBelowSuccAt_free h
      omega
    · rcases h with h | h
      · have hf := HF_pairZeroBaseAt_free h
        omega
      · rcases h with h | h
        · have hfm := HF_pairTotalBelowSuccAt_free h
          omega
        · have hstep := mulStepAt_free h
          omega

theorem mulGraphAt_free {i out left right : Nat}
    (h : Free i (mulGraphAt out left right)) : i = out ∨ i = left ∨ i = right := by
  simp only [mulGraphAt, Free] at h
  rcases h with h | h
  · have hm := mulRecApproxAt_free h
    omega
  · have hp := HF_pairMemAt_free h
    omega

theorem mulGraph_free {i : Nat} (h : Free i mulGraph) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact mulGraphAt_free h

theorem mulStepAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f a m : Nat) :
    Sat M.mem e (mulStepAt f a m) ↔ MulStep M (e f) (e a) (e m) := by
  constructor
  · intro h k t y hkm hkt hsky
    let sk := M.adjoin k k
    let Ekty := scons y (scons t (scons k e))
    let Eskty := scons sk Ekty
    have hktSat : Sat M.mem Ekty (HF_pairMemAt 2 1 (f+3)) := by
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M Ekty 2 1 (f+3)).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M k t) (e f)
      exact hkt
    have hskSat : Sat M.mem Eskty (HF_succAt 0 3) := by
      apply (FirstOrderAdjunctionModel.HF_succAt_spec M Eskty 0 3).mpr
      change sk = M.adjoin k k
      rfl
    have hskySat : Sat M.mem Eskty (HF_pairMemAt 0 1 (f+4)) := by
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M Eskty 0 1 (f+4)).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M sk y) (e f)
      exact hsky
    rcases h k t y hkm hktSat sk hskSat hskySat with ⟨g, hg, hy⟩
    have hg' := (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M
      (scons g Eskty) 0 3 (a+5)).mp hg
    have hy' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
      (scons g Eskty) (a+5) 2 0).mp hy
    refine ⟨g, ?_, ?_⟩
    · change FirstOrderAdjunctionModel.SuccRecApprox M t g (e a) at hg'
      exact hg'
    · change M.mem (FirstOrderAdjunctionModel.kpair M (e a) y) g at hy'
      exact hy'
  · intro h k t y hkm hkt sk hsk hsky
    have hsk' : sk = M.adjoin k k :=
      (FirstOrderAdjunctionModel.HF_succAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 3).mp hsk
    have hkt' : M.mem (FirstOrderAdjunctionModel.kpair M k t) (e f) := by
      exact (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons y (scons t (scons k e))) 2 1 (f+3)).mp hkt
    have hsky' : M.mem
        (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) y) (e f) := by
      have hp := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons sk (scons y (scons t (scons k e)))) 0 1 (f+4)).mp hsky
      rwa [hsk'] at hp
    rcases h k t y hkm hkt' hsky' with ⟨g, hg, hy⟩
    refine ⟨g, ?_, ?_⟩
    · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M
        (scons g (scons sk (scons y (scons t (scons k e))))) 0 3 (a+5)).mpr
      change FirstOrderAdjunctionModel.SuccRecApprox M t g (e a)
      exact hg
    · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons g (scons sk (scons y (scons t (scons k e))))) (a+5) 2 0).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M (e a) y) g
      exact hy

theorem mulRecApproxAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (f a m : Nat) :
    Sat M.mem e (mulRecApproxAt f a m) ↔
      MulRecApprox M (e a) (e f) (e m) := by
  change
    (Sat M.mem e (HF_pairFunctionalAt f) ∧
      (Sat M.mem e (HF_pairKeysBelowSuccAt f m) ∧
        (Sat M.mem e (HF_pairZeroBaseAt f) ∧
          (Sat M.mem e (HF_pairTotalBelowSuccAt f m) ∧
            Sat M.mem e (mulStepAt f a m))))) ↔
      FirstOrderAdjunctionModel.PairFunctional M (e f) ∧
        FirstOrderAdjunctionModel.PairKeysBelowSucc M (e f) (e m) ∧
          M.mem (FirstOrderAdjunctionModel.kpair M M.empty M.empty) (e f) ∧
            FirstOrderAdjunctionModel.PairTotalBelowSucc M (e f) (e m) ∧
              MulStep M (e f) (e a) (e m)
  rw [
    FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec M e f,
    FirstOrderAdjunctionModel.HF_pairKeysBelowSuccAt_spec M e f m,
    FirstOrderAdjunctionModel.HF_pairZeroBaseAt_spec M e f,
    FirstOrderAdjunctionModel.HF_pairTotalBelowSuccAt_spec M e f m,
    mulStepAt_spec M e f a m]

theorem mulRecTotalAt_spec {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (a m : Nat) :
    Sat M.mem e (mulRecTotalAt a m) ↔
      MulRecTotal M (e a) (e m) := by
  constructor
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    have hf' := (mulRecApproxAt_spec M (scons z (scons f e))
      1 (a+2) (m+2)).mp hf
    have hz' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
      (scons z (scons f e)) (m+2) 0 1).mp hz
    change MulRecApprox M (e a) f (e m) at hf'
    change M.mem (FirstOrderAdjunctionModel.kpair M (e m) z) f at hz'
    exact ⟨f, z, hf', hz'⟩
  · intro h
    rcases h with ⟨f, z, hf, hz⟩
    refine ⟨f, z, ?_, ?_⟩
    · apply (mulRecApproxAt_spec M (scons z (scons f e))
        1 (a+2) (m+2)).mpr
      change MulRecApprox M (e a) f (e m)
      exact hf
    · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons z (scons f e)) (m+2) 0 1).mpr
      change M.mem (FirstOrderAdjunctionModel.kpair M (e m) z) f
      exact hz

theorem mulRecTotalOnOrdinalAt_spec {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α) (a m : Nat) :
    Sat M.mem e (mulRecTotalOnOrdinalAt a m) ↔
      (OrdinalLike M.mem (e m) → MulRecTotal M (e a) (e m)) := by
  constructor
  · intro h hm
    exact (mulRecTotalAt_spec M e a m).mp
      (h ((HF_ordinalLikeAt_spec e m).mpr hm))
  · intro h hmSat
    exact (mulRecTotalAt_spec M e a m).mpr
      (h ((HF_ordinalLikeAt_spec e m).mp hmSat))

theorem zeroMulRecGraph_mulRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) (a : α) :
    MulRecApprox M a (FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty) M.empty := by
  have hf : FirstOrderAdjunctionModel.SuccRecApprox M M.empty
      (FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty) M.empty :=
    FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M M.empty
  rcases hf with ⟨hfun, hkeys, hbase, htotal, _hstep⟩
  refine ⟨hfun, hkeys, hbase, htotal, ?_⟩
  intro k _t _y hkm _ _
  exact False.elim (M.empty_spec k hkm)

theorem mulRecTotal_empty {α : Type u}
    (M : FirstOrderAdjunctionModel α) (a : α) :
    MulRecTotal M a M.empty := by
  exact ⟨FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty, M.empty,
    zeroMulRecGraph_mulRecApprox M a,
    FirstOrderAdjunctionModel.zeroSuccRecGraph_base M M.empty⟩

/-- Extend a multiplication-recursion graph by an arbitrary next value. -/
def mulRecGraphSucc {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m y : α) : α :=
  M.adjoin f (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)

theorem mulRecGraphSucc_old {α : Type u} (M : FirstOrderAdjunctionModel α)
    {f m y p : α} (hp : M.mem p f) :
    M.mem p (mulRecGraphSucc M f m y) :=
  (M.adjoin_spec p f
    (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)).mpr (Or.inl hp)

theorem mulRecGraphSucc_new {α : Type u} (M : FirstOrderAdjunctionModel α)
    (f m y : α) :
    M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)
      (mulRecGraphSucc M f m y) :=
  (M.adjoin_spec (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)
    f (FirstOrderAdjunctionModel.kpair M (M.adjoin m m) y)).mpr (Or.inr rfl)

theorem mulRecGraphSucc_mulRecApprox {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a f m z y : α}
    (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M m z) f)
    (hadd : ∃ g,
      FirstOrderAdjunctionModel.SuccRecApprox M z g a ∧
        M.mem (FirstOrderAdjunctionModel.kpair M a y) g) :
    MulRecApprox M a (mulRecGraphSucc M f m y) (M.adjoin m m) := by
  rcases hf with ⟨hfun, hkeys, hbase, htotal, hstep⟩
  let sm := M.adjoin m m
  let newPair := FirstOrderAdjunctionModel.kpair M sm y
  let g := mulRecGraphSucc M f m y
  have hsm_not_mem : ¬ M.mem sm m := by
    simpa [sm] using
      FirstOrderAdjunctionModel.adjoin_self_not_mem_of_ordinalLike M hm
  have hsm_ne_m : sm ≠ m := by
    simpa [sm] using FirstOrderAdjunctionModel.adjoin_self_ne_self M m
  have hmem_g : ∀ p, M.mem p g ↔ M.mem p f ∨ p = newPair := by
    intro p
    exact M.adjoin_spec p f newPair
  have old_key_ne_succ :
      ∀ {k y'}, M.mem (FirstOrderAdjunctionModel.kpair M k y') f → k ≠ sm := by
    intro k y' hOld hk
    have hkBound := hkeys k y' hOld
    rw [hk] at hkBound
    rcases hkBound with hmem | heq
    · exact hsm_not_mem hmem
    · exact hsm_ne_m heq
  have pair_old_of_mem_key :
      ∀ {k y'}, M.mem k m →
        M.mem (FirstOrderAdjunctionModel.kpair M k y') g →
          M.mem (FirstOrderAdjunctionModel.kpair M k y') f := by
    intro k y' hkm hkg
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k y')).mp hkg with
      hOld | hNew
    · exact hOld
    · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew).1
      rw [hk] at hkm
      exact False.elim (hsm_not_mem hkm)
  refine ⟨?functional, ?keys, ?base, ?total, ?step⟩
  · intro k u v hku hkv
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k u)).mp hku with
      hOld | hNew
    · rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k v)).mp hkv with
        hOld' | hNew'
      · exact hfun k u v hOld hOld'
      · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew').1
        exact False.elim (old_key_ne_succ hOld hk)
    · rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k v)).mp hkv with
        hOld' | hNew'
      · have hk : k = sm := (FirstOrderAdjunctionModel.kpair_injective M hNew).1
        exact False.elim (old_key_ne_succ hOld' hk)
      · have hu : u = y := (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        have hv : v = y := (FirstOrderAdjunctionModel.kpair_injective M hNew').2
        rw [hu, hv]
  · intro k u hku
    rcases (hmem_g (FirstOrderAdjunctionModel.kpair M k u)).mp hku with
      hOld | hNew
    · rcases hkeys k u hOld with hkm | hkm
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inl hkm))
      · exact Or.inl ((M.adjoin_spec k m m).mpr (Or.inr hkm))
    · exact Or.inr (FirstOrderAdjunctionModel.kpair_injective M hNew).1
  · exact mulRecGraphSucc_old M hbase
  · intro k hk
    rcases hk with hksm | hksm
    · rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
      · rcases htotal k (Or.inl hkm) with ⟨u, hu⟩
        exact ⟨u, mulRecGraphSucc_old M hu⟩
      · rcases htotal k (Or.inr hkm) with ⟨u, hu⟩
        exact ⟨u, mulRecGraphSucc_old M hu⟩
    · subst k
      exact ⟨y, mulRecGraphSucc_new M f m y⟩
  · intro k t out hksm hkt hsky
    rcases (M.adjoin_spec k m m).mp hksm with hkm | hkm
    · have hktOld : M.mem (FirstOrderAdjunctionModel.kpair M k t) f :=
        pair_old_of_mem_key hkm hkt
      have hskyOld :
          M.mem (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) out) f := by
        rcases (hmem_g
            (FirstOrderAdjunctionModel.kpair M (M.adjoin k k) out)).mp hsky with
          hOld | hNew
        · exact hOld
        · have hsk : M.adjoin k k = sm :=
            (FirstOrderAdjunctionModel.kpair_injective M hNew).1
          have hkOrd : OrdinalLike M.mem k := OrdinalLike.of_mem hm hkm
          have hkm_eq : k = m :=
            FirstOrderAdjunctionModel.adjoin_self_injective_on_ordinalLike
              M hkOrd hm (by simpa [sm] using hsk)
          rw [hkm_eq] at hkm
          exact False.elim (FirstOrderAdjunctionModel.mem_irrefl M m hkm)
      exact hstep k t out hkm hktOld hskyOld
    · subst k
      have hktOld :
          M.mem (FirstOrderAdjunctionModel.kpair M m t) f := by
        rcases (hmem_g (FirstOrderAdjunctionModel.kpair M m t)).mp hkt with
          hOld | hNew
        · exact hOld
        · have hm_eq_sm : m = sm :=
            (FirstOrderAdjunctionModel.kpair_injective M hNew).1
          exact False.elim (hsm_ne_m hm_eq_sm.symm)
      have ht : t = z := hfun m t z hktOld hz
      rcases (hmem_g (FirstOrderAdjunctionModel.kpair M sm out)).mp hsky with
        hOld | hNew
      · exact False.elim (old_key_ne_succ hOld rfl)
      · have hout : out = y :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        rw [ht, hout]
        exact hadd

theorem mulRecTotal_succ_of_addTotal {α : Type u}
    (M : FirstOrderAdjunctionModel α) {a m : α}
    (hm : OrdinalLike M.mem m)
    (hAddTotal : ∀ s, FirstOrderAdjunctionModel.SuccRecTotal M s a)
    (ht : MulRecTotal M a m) :
    MulRecTotal M a (M.adjoin m m) := by
  rcases ht with ⟨f, z, hf, hz⟩
  rcases hAddTotal z with ⟨g, y, hg, hy⟩
  exact ⟨mulRecGraphSucc M f m y, y,
    mulRecGraphSucc_mulRecApprox M hm hf hz ⟨g, hg, hy⟩,
    mulRecGraphSucc_new M f m y⟩

theorem mulRecTotal_of_ordinalLike_of_predecessor {α : Type u}
    (M : FirstOrderAdjunctionModel α)
    (hPred : ∀ a, OrdinalLike M.mem a →
      a = M.empty ∨ ∃ p, M.mem p a ∧ a = M.adjoin p p)
    (hAddTotal : ∀ s m, OrdinalLike M.mem m →
      FirstOrderAdjunctionModel.SuccRecTotal M s m)
    (a m : α) (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m) :
    MulRecTotal M a m := by
  let phi : Form := mulRecTotalOnOrdinalAt 1 0
  let tail : Nat → α := fun _ => a
  have hind := M.induction_schema phi (scons a tail)
  have hall : ∀ b, Sat M.mem (scons b (scons a tail)) phi := by
    apply hind
    intro b ih
    apply (mulRecTotalOnOrdinalAt_spec M
      (scons b (scons a tail)) 1 0).mpr
    intro hb
    rcases hPred b hb with hbEmpty | ⟨p, hpb, hbSucc⟩
    · rw [hbEmpty]
      exact mulRecTotal_empty M a
    · have hpOrd : OrdinalLike M.mem p := OrdinalLike.of_mem hb hpb
      have hpSat : Sat M.mem (scons p (scons a tail)) phi :=
        (Sat_rename_rSkipParam phi (scons a tail) b p).mp (ih p hpb)
      have hpTotal : MulRecTotal M a p := by
        simpa [phi, tail, scons] using
          ((mulRecTotalOnOrdinalAt_spec M
            (scons p (scons a tail)) 1 0).mp hpSat hpOrd)
      rw [hbSucc]
      exact mulRecTotal_succ_of_addTotal M hpOrd
        (fun s => hAddTotal s a ha) hpTotal
  simpa [phi, tail, scons] using
    ((mulRecTotalOnOrdinalAt_spec M
      (scons m (scons a tail)) 1 0).mp (hall m) hm)

theorem mulRecTotal_of_ordinalLike_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (a m : α) (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m) :
    MulRecTotal M.toFirstOrderAdjunctionModel a m := by
  apply mulRecTotal_of_ordinalLike_of_predecessor M.toFirstOrderAdjunctionModel
  · intro b hb
    exact FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hb
  · intro s r hr
    exact FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike M s r hr
  · exact ha
  · exact hm

/-- In finite HF, a multiplication-recursion trace with ordinal-like
multiplicand and endpoint assigns ordinal-like values to every covered key.

The multiplication step delegates to the successor-recursion closure theorem:
if the previous product `t` is ordinal-like, then the addition trace computing
`t + a` has an ordinal-like output. -/
theorem mulRecApprox_value_ordinalLike {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {a f m z : α}
    (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M.toFirstOrderAdjunctionModel a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f) :
    OrdinalLike M.mem z := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fAll (fImp (HF_pairMemAt 2 0 4) (HF_ordinalLikeAt 0))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons a (scons f tail))
  have hall : ∀ k, Sat M.mem (scons k (scons a (scons f tail))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat z hpairSat
    let Em : Nat → α := scons m (scons k (scons a (scons f tail)))
    let Ez : Nat → α := scons z Em
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : MulRecApprox N a f m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hpair : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hpairSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hkOrd with
      hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfun, _hkeys, hbase, _htotal, _hstep⟩
      have hpairEmpty : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpair
      have hz_eq_empty : z = N.empty := hfun N.empty z N.empty hpairEmpty hbase
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      simpa [Ez, Em, hz_eq_empty, N, scons] using
        FirstOrderAdjunctionModel.ordinalLike_empty N
    · rcases hfApprox with ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotal p (Or.inl hpm) with ⟨t, hpt⟩
      have hpSat : Sat M.mem (scons p (scons a (scons f tail))) phi :=
        (Sat_rename_rSkipParam phi (scons a (scons f tail)) k p).mp (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons a (scons f tail)))
      let Etp : Nat → α := scons t Emp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (mulRecApproxAt 3 2 0) := by
        apply (mulRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfun, _hkeys, _hbase, htotal, hstep⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have htDomain : Sat M.mem Etp (HF_ordinalLikeAt 0) :=
        hpSat m (Or.inl hpm) hmSatP hfSatP t hptSat
      have htOrd : OrdinalLike M.mem t :=
        (HF_ordinalLikeAt_spec Etp 0).mp htDomain
      have hpairSucc : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpair
      rcases hstep p t z hpm hpt hpairSucc with ⟨g, hgApprox, hgy⟩
      have hzOrd : OrdinalLike M.mem z :=
        FirstOrderFiniteAdjunctionModel.succRecApprox_value_ordinalLike
          M htOrd ha hgApprox hgy
      apply (HF_ordinalLikeAt_spec Ez 0).mpr
      exact hzOrd
  let Em : Nat → α := scons m (scons m (scons a (scons f tail)))
  let Ez : Nat → α := scons z Em
  have hmain : Sat M.mem (scons m (scons a (scons f tail))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (mulRecApproxAt 3 2 0) := by
    apply (mulRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hzDomain : Sat M.mem Ez (HF_ordinalLikeAt 0) :=
    hmain m (Or.inr rfl) hmSat hfSat z hzSat
  exact (HF_ordinalLikeAt_spec Ez 0).mp hzDomain

/-- In finite HF, multiplication-recursion traces with the same multiplicand
have a unique value at every ordinal-like key covered by both traces. -/
theorem mulRecApprox_value_unique {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) {a f g m z w : α}
    (ha : OrdinalLike M.mem a) (hm : OrdinalLike M.mem m)
    (hf : MulRecApprox M.toFirstOrderAdjunctionModel a f m)
    (hz : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m z) f)
    (hg : MulRecApprox M.toFirstOrderAdjunctionModel a g m)
    (hw : M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel m w) g) :
    z = w := by
  let N := M.toFirstOrderAdjunctionModel
  let phi : Form :=
    fAll
      (fImp (fOr (fMem 1 0) (fEq 1 0))
        (fImp (HF_ordinalLikeAt 0)
          (fImp (mulRecApproxAt 3 2 0)
            (fImp (mulRecApproxAt 4 2 0)
              (fAll
                (fImp (HF_pairMemAt 2 0 4)
                  (fAll (fImp (HF_pairMemAt 3 0 6) (fEq 1 0)))))))))
  let tail : Nat → α := fun _ => M.empty
  have hind := M.induction_schema phi (scons a (scons f (scons g tail)))
  have hall : ∀ k, Sat M.mem (scons k (scons a (scons f (scons g tail)))) phi := by
    apply hind
    intro k ih
    intro m hkey hmSat hfSat hgSat z hzSat w hwSat
    let Em : Nat → α := scons m (scons k (scons a (scons f (scons g tail))))
    let Ez : Nat → α := scons z Em
    let Ewz : Nat → α := scons w Ez
    have hmOrd : OrdinalLike M.mem m :=
      (HF_ordinalLikeAt_spec Em 0).mp hmSat
    have hfApprox : MulRecApprox N a f m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 3 2 0).mp hfSat
    have hgApprox : MulRecApprox N a g m := by
      simpa [N, Em, tail, scons] using
        (mulRecApproxAt_spec N Em 4 2 0).mp hgSat
    have hpairF : N.mem (FirstOrderAdjunctionModel.kpair N k z) f := by
      simpa [N, Em, Ez, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mp hzSat
    have hpairG : N.mem (FirstOrderAdjunctionModel.kpair N k w) g := by
      simpa [N, Em, Ez, Ewz, tail, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mp hwSat
    have hkOrd : OrdinalLike M.mem k := by
      rcases hkey with hkm | hkm
      · change M.mem k m at hkm
        exact OrdinalLike.of_mem hmOrd hkm
      · change k = m at hkm
        subst k
        exact hmOrd
    rcases FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ M hkOrd with
      hkEmpty | ⟨p, hpk, hkSucc⟩
    · rcases hfApprox with ⟨hfunF, _hkeysF, hbaseF, _htotalF, _hstepF⟩
      rcases hgApprox with ⟨hfunG, _hkeysG, hbaseG, _htotalG, _hstepG⟩
      have hpairEmptyF : N.mem (FirstOrderAdjunctionModel.kpair N N.empty z) f := by
        simpa [N, hkEmpty] using hpairF
      have hpairEmptyG : N.mem (FirstOrderAdjunctionModel.kpair N N.empty w) g := by
        simpa [N, hkEmpty] using hpairG
      have hz_eq_empty : z = N.empty := hfunF N.empty z N.empty hpairEmptyF hbaseF
      have hw_eq_empty : w = N.empty := hfunG N.empty w N.empty hpairEmptyG hbaseG
      exact hz_eq_empty.trans hw_eq_empty.symm
    · rcases hfApprox with ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      rcases hgApprox with ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hpm : M.mem p m := by
        rcases hkey with hkm | hkm
        · change M.mem k m at hkm
          exact hmOrd.1 k hkm p hpk
        · change k = m at hkm
          simpa [hkm] using hpk
      rcases htotalF p (Or.inl hpm) with ⟨t, hpt⟩
      rcases htotalG p (Or.inl hpm) with ⟨u, hpu⟩
      have hpSat : Sat M.mem (scons p (scons a (scons f (scons g tail)))) phi :=
        (Sat_rename_rSkipParam phi (scons a (scons f (scons g tail))) k p).mp
          (ih p hpk)
      let Emp : Nat → α := scons m (scons p (scons a (scons f (scons g tail))))
      let Etp : Nat → α := scons t Emp
      let Eutp : Nat → α := scons u Etp
      have hmSatP : Sat M.mem Emp (HF_ordinalLikeAt 0) :=
        (HF_ordinalLikeAt_spec Emp 0).mpr hmOrd
      have hfSatP : Sat M.mem Emp (mulRecApproxAt 3 2 0) := by
        apply (mulRecApproxAt_spec N Emp 3 2 0).mpr
        exact ⟨_hfunF, _hkeysF, _hbaseF, htotalF, hstepF⟩
      have hgSatP : Sat M.mem Emp (mulRecApproxAt 4 2 0) := by
        apply (mulRecApproxAt_spec N Emp 4 2 0).mpr
        exact ⟨_hfunG, _hkeysG, _hbaseG, htotalG, hstepG⟩
      have hptSat : Sat M.mem Etp (HF_pairMemAt 2 0 4) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Etp 2 0 4).mpr
        simpa [N, Emp, Etp, tail, scons] using hpt
      have hpuSat : Sat M.mem Eutp (HF_pairMemAt 3 0 6) := by
        apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Eutp 3 0 6).mpr
        simpa [N, Emp, Etp, Eutp, tail, scons] using hpu
      have htu : t = u :=
        hpSat m (Or.inl hpm) hmSatP hfSatP hgSatP t hptSat u hpuSat
      have hpairSuccF : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) z) f := by
        simpa [N, hkSucc] using hpairF
      have hpairSuccG : N.mem
          (FirstOrderAdjunctionModel.kpair N (N.adjoin p p) w) g := by
        simpa [N, hkSucc] using hpairG
      rcases hstepF p t z hpm hpt hpairSuccF with ⟨fAdd, hfAdd, hzAdd⟩
      rcases hstepG p u w hpm hpu hpairSuccG with ⟨gAdd, hgAdd, hwAdd⟩
      have hgAdd' : FirstOrderAdjunctionModel.SuccRecApprox N t gAdd a := by
        rwa [← htu] at hgAdd
      exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
        M ha hfAdd hzAdd hgAdd' hwAdd
  let Em : Nat → α := scons m (scons m (scons a (scons f (scons g tail))))
  let Ez : Nat → α := scons z Em
  let Ewz : Nat → α := scons w Ez
  have hmain : Sat M.mem (scons m (scons a (scons f (scons g tail)))) phi := hall m
  have hmSat : Sat M.mem Em (HF_ordinalLikeAt 0) :=
    (HF_ordinalLikeAt_spec Em 0).mpr hm
  have hfSat : Sat M.mem Em (mulRecApproxAt 3 2 0) := by
    apply (mulRecApproxAt_spec N Em 3 2 0).mpr
    simpa [N, Em, tail, scons] using hf
  have hgSat : Sat M.mem Em (mulRecApproxAt 4 2 0) := by
    apply (mulRecApproxAt_spec N Em 4 2 0).mpr
    simpa [N, Em, tail, scons] using hg
  have hzSat : Sat M.mem Ez (HF_pairMemAt 2 0 4) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ez 2 0 4).mpr
    simpa [N, Em, Ez, tail, scons] using hz
  have hwSat : Sat M.mem Ewz (HF_pairMemAt 3 0 6) := by
    apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec N Ewz 3 0 6).mpr
    simpa [N, Em, Ez, Ewz, tail, scons] using hw
  exact hmain m (Or.inr rfl) hmSat hfSat hgSat z hzSat w hwSat

theorem mulGraphAt_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) {f : α}
    (hf : MulRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f) :
    Sat M.mem e (mulGraphAt out left right) := by
  refine ⟨f, ?_, ?_⟩
  · apply (mulRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change MulRecApprox M (e left) f (e right)
    exact hf
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    exact hout

/-- In a finite first-order HF model, the multiplication graph is
single-valued on ordinal-like inputs. -/
theorem mulGraphAt_value_unique_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (e : Nat → α)
    (out₁ out₂ left right : Nat)
    (hleft : OrdinalLike M.mem (e left))
    (hright : OrdinalLike M.mem (e right))
    (h₁ : Sat M.mem e (mulGraphAt out₁ left right))
    (h₂ : Sat M.mem e (mulGraphAt out₂ left right)) :
    e out₁ = e out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : MulRecApprox N (e left) f (e right) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons f e)
        0 (left+1) (right+1)).mp hfSat
  have hpair₁ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e)
        (right+1) (out₁+1) 0).mp hout₁Sat
  have hg : MulRecApprox N (e left) g (e right) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons g e)
        0 (left+1) (right+1)).mp hgSat
  have hpair₂ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₂)) g := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e)
        (right+1) (out₂+1) 0).mp hout₂Sat
  exact mulRecApprox_value_unique M hleft hright hf hpair₁ hg hpair₂

/-- Cross-environment single-valuedness for multiplication graphs whose inputs
agree. -/
theorem mulGraphAt_outputs_eq_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e₁ e₂ : Nat → α)
    (out₁ out₂ left₁ left₂ right₁ right₂ : Nat)
    (hleft : e₁ left₁ = e₂ left₂)
    (hright : e₁ right₁ = e₂ right₂)
    (hleftOrd : OrdinalLike M.mem (e₁ left₁))
    (hrightOrd : OrdinalLike M.mem (e₁ right₁))
    (h₁ : Sat M.mem e₁ (mulGraphAt out₁ left₁ right₁))
    (h₂ : Sat M.mem e₂ (mulGraphAt out₂ left₂ right₂)) :
    e₁ out₁ = e₂ out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : MulRecApprox N (e₁ left₁) f (e₁ right₁) := by
    simpa [N, scons] using
      (mulRecApproxAt_spec N (scons f e₁)
        0 (left₁+1) (right₁+1)).mp hfSat
  have hpair₁ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₁ out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e₁)
        (right₁+1) (out₁+1) 0).mp hout₁Sat
  have hg : MulRecApprox N (e₁ left₁) g (e₁ right₁) := by
    have hgRaw : MulRecApprox N (e₂ left₂) g (e₂ right₂) := by
      simpa [N, scons] using
        (mulRecApproxAt_spec N (scons g e₂)
          0 (left₂+1) (right₂+1)).mp hgSat
    simpa [hleft, hright] using hgRaw
  have hpair₂ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₂ out₂)) g := by
    have hpairRaw : N.mem
        (FirstOrderAdjunctionModel.kpair N (e₂ right₂) (e₂ out₂)) g := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e₂)
          (right₂+1) (out₂+1) 0).mp hout₂Sat
    simpa [hright] using hpairRaw
  exact mulRecApprox_value_unique M hleftOrd hrightOrd hf hpair₁ hg hpair₂

theorem mulGraphAt_succ_right_of_mulRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left rightSucc right : Nat) {f z g y : α}
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (hout : e out = y)
    (hf : MulRecApprox M (e left) f (e right))
    (hz : M.mem (FirstOrderAdjunctionModel.kpair M (e right) z) f)
    (hg : FirstOrderAdjunctionModel.SuccRecApprox M z g (e left))
    (hy : M.mem (FirstOrderAdjunctionModel.kpair M (e left) y) g) :
    Sat M.mem e (mulGraphAt out left rightSucc) := by
  let h := mulRecGraphSucc M f (e right) y
  apply mulGraphAt_of_mulRecApprox_model M e out left rightSucc (f := h)
  · change MulRecApprox M (e left) h (e rightSucc)
    rw [hrightSucc]
    exact mulRecGraphSucc_mulRecApprox M hrightOrd hf hz ⟨g, hg, hy⟩
  · change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e out)) h
    rw [hrightSucc, hout]
    exact mulRecGraphSucc_new M f (e right) y

theorem addGraphAt_zero_right_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) (hout : e out = e left) (hright : e right = M.empty) :
    Sat M.mem e (addGraphAt out left right) := by
  let f := FirstOrderAdjunctionModel.zeroSuccRecGraph M (e left)
  refine ⟨f, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right)
    rw [hright]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M (e left)
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    rw [hright, hout]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_base M (e left)

/-- Build an addition graph from explicit successor-recursion trace data. -/
theorem addGraphAt_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) {f : α}
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f) :
    Sat M.mem e (addGraphAt out left right) := by
  refine ⟨f, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
      0 (left+1) (right+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right)
    exact hf
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    exact hout

/-- In a finite first-order HF model, the addition graph is single-valued on
ordinal-like right inputs. -/
theorem addGraphAt_value_unique_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (e : Nat → α)
    (out₁ out₂ left right : Nat)
    (hright : OrdinalLike M.mem (e right))
    (h₁ : Sat M.mem e (addGraphAt out₁ left right))
    (h₂ : Sat M.mem e (addGraphAt out₂ left right)) :
    e out₁ = e out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : FirstOrderAdjunctionModel.SuccRecApprox N (e left) f (e right) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons f e)
        0 (left+1) (right+1)).mp hfSat
  have hpair₁ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e)
        (right+1) (out₁+1) 0).mp hout₁Sat
  have hg : FirstOrderAdjunctionModel.SuccRecApprox N (e left) g (e right) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons g e)
        0 (left+1) (right+1)).mp hgSat
  have hpair₂ : N.mem (FirstOrderAdjunctionModel.kpair N (e right) (e out₂)) g := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e)
        (right+1) (out₂+1) 0).mp hout₂Sat
  exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
    M hright hf hpair₁ hg hpair₂

/-- Cross-environment single-valuedness for addition graphs whose inputs
agree. -/
theorem addGraphAt_outputs_eq_finite_model {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e₁ e₂ : Nat → α)
    (out₁ out₂ left₁ left₂ right₁ right₂ : Nat)
    (hleft : e₁ left₁ = e₂ left₂)
    (hright : e₁ right₁ = e₂ right₂)
    (hrightOrd : OrdinalLike M.mem (e₁ right₁))
    (h₁ : Sat M.mem e₁ (addGraphAt out₁ left₁ right₁))
    (h₂ : Sat M.mem e₂ (addGraphAt out₂ left₂ right₂)) :
    e₁ out₁ = e₂ out₂ := by
  let N := M.toFirstOrderAdjunctionModel
  rcases h₁ with ⟨f, hfSat, hout₁Sat⟩
  rcases h₂ with ⟨g, hgSat, hout₂Sat⟩
  have hf : FirstOrderAdjunctionModel.SuccRecApprox
      N (e₁ left₁) f (e₁ right₁) := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons f e₁)
        0 (left₁+1) (right₁+1)).mp hfSat
  have hpair₁ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₁ out₁)) f := by
    simpa [N, scons] using
      (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons f e₁)
        (right₁+1) (out₁+1) 0).mp hout₁Sat
  have hg : FirstOrderAdjunctionModel.SuccRecApprox
      N (e₁ left₁) g (e₁ right₁) := by
    have hgRaw : FirstOrderAdjunctionModel.SuccRecApprox
        N (e₂ left₂) g (e₂ right₂) := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N (scons g e₂)
          0 (left₂+1) (right₂+1)).mp hgSat
    simpa [hleft, hright] using hgRaw
  have hpair₂ : N.mem
      (FirstOrderAdjunctionModel.kpair N (e₁ right₁) (e₂ out₂)) g := by
    have hpairRaw : N.mem
        (FirstOrderAdjunctionModel.kpair N (e₂ right₂) (e₂ out₂)) g := by
      simpa [N, scons] using
        (FirstOrderAdjunctionModel.HF_pairMemAt_spec N (scons g e₂)
          (right₂+1) (out₂+1) 0).mp hout₂Sat
    simpa [hright] using hpairRaw
  exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_unique
    M hrightOrd hf hpair₁ hg hpair₂

theorem addGraphAt_succ_right_of_addGraphAt_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (outSucc out left rightSucc right : Nat)
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (houtSucc : e outSucc = M.adjoin (e out) (e out))
    (hadd : Sat M.mem e (addGraphAt out left right)) :
    Sat M.mem e (addGraphAt outSucc left rightSucc) := by
  rcases hadd with ⟨f, hf, hout⟩
  have hf' := (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons f e)
    0 (left+1) (right+1)).mp hf
  have hout' := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
    (right+1) (out+1) 0).mp hout
  change FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right) at hf'
  change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f at hout'
  let g := FirstOrderAdjunctionModel.succRecGraphSucc M f (e right) (e out)
  refine ⟨g, ?_, ?_⟩
  · apply (FirstOrderAdjunctionModel.HF_succRecApproxAt_spec M (scons g e)
      0 (left+1) (rightSucc+1)).mpr
    change FirstOrderAdjunctionModel.SuccRecApprox M (e left) g (e rightSucc)
    rw [hrightSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_succRecApprox M hrightOrd hf' hout'
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons g e)
      (rightSucc+1) (outSucc+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e outSucc)) g
    rw [hrightSucc, houtSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_new M f (e right) (e out)

/-- Extend an addition graph through the successor of the right input from
explicit predecessor trace data, without requiring the predecessor output to
occupy a slot in the current environment. -/
theorem addGraphAt_succ_right_of_succRecApprox_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (outSucc left rightSucc right : Nat) {f z : α}
    (hrightOrd : OrdinalLike M.mem (e right))
    (hrightSucc : e rightSucc = M.adjoin (e right) (e right))
    (houtSucc : e outSucc = M.adjoin z z)
    (hf : FirstOrderAdjunctionModel.SuccRecApprox M (e left) f (e right))
    (hout : M.mem (FirstOrderAdjunctionModel.kpair M (e right) z) f) :
    Sat M.mem e (addGraphAt outSucc left rightSucc) := by
  let g := FirstOrderAdjunctionModel.succRecGraphSucc M f (e right) z
  apply addGraphAt_of_succRecApprox_model M e outSucc left rightSucc
      (f := g)
  · change FirstOrderAdjunctionModel.SuccRecApprox M (e left) g (e rightSucc)
    rw [hrightSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_succRecApprox M hrightOrd hf hout
  · change M.mem (FirstOrderAdjunctionModel.kpair M (e rightSucc) (e outSucc)) g
    rw [hrightSucc, houtSucc]
    exact FirstOrderAdjunctionModel.succRecGraphSucc_new M f (e right) z

theorem mulStepAt_empty_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (f a m : Nat) (hm : e m = M.empty) :
    Sat M.mem e (mulStepAt f a m) := by
  intro k _t _y hkm
  change M.mem k (e m) at hkm
  rw [hm] at hkm
  exact False.elim (M.empty_spec k hkm)

theorem mulGraphAt_zero_right_model {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (out left right : Nat) (hout : e out = M.empty) (hright : e right = M.empty) :
    Sat M.mem e (mulGraphAt out left right) := by
  let f := FirstOrderAdjunctionModel.zeroSuccRecGraph M M.empty
  have hf : FirstOrderAdjunctionModel.SuccRecApprox M M.empty f M.empty :=
    FirstOrderAdjunctionModel.zeroSuccRecGraph_succRecApprox M M.empty
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfun, hkeys, hbase, htotal, _hstep⟩
    change
      Sat M.mem (scons f e) (HF_pairFunctionalAt 0) ∧
        (Sat M.mem (scons f e) (HF_pairKeysBelowSuccAt 0 (right+1)) ∧
          (Sat M.mem (scons f e) (HF_pairZeroBaseAt 0) ∧
            (Sat M.mem (scons f e) (HF_pairTotalBelowSuccAt 0 (right+1)) ∧
              Sat M.mem (scons f e) (mulStepAt 0 (left+1) (right+1)))))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec M (scons f e) 0).mpr hfun
    · apply (FirstOrderAdjunctionModel.HF_pairKeysBelowSuccAt_spec M
        (scons f e) 0 (right+1)).mpr
      simpa [scons, hright] using hkeys
    · exact (FirstOrderAdjunctionModel.HF_pairZeroBaseAt_spec M (scons f e) 0).mpr hbase
    · apply (FirstOrderAdjunctionModel.HF_pairTotalBelowSuccAt_spec M
        (scons f e) 0 (right+1)).mpr
      simpa [scons, hright] using htotal
    · apply mulStepAt_empty_model M (scons f e) 0 (left+1) (right+1)
      simpa [scons] using hright
  · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M (scons f e)
      (right+1) (out+1) 0).mpr
    change M.mem (FirstOrderAdjunctionModel.kpair M (e right) (e out)) f
    rw [hright, hout]
    exact FirstOrderAdjunctionModel.zeroSuccRecGraph_base M M.empty

theorem domain_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode n) e) domainForm :=
  HF_ordinalLikeAt_of_ordinalCode (scons (ordinalCode n) e) 0 n rfl

theorem domain_exact (e : Nat → Nat) :
    Sat Mem e domainForm ↔ IsOrdinalCode (e 0) :=
  HF_ordinalLikeAt_exact e 0

theorem zeroGraph_ordinalCode (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode 0) e) zeroGraph := by
  apply (HF_emptyAt_empty standardModel (scons (ordinalCode 0) e) 0).mpr
  rfl

theorem zeroGraph_exact_on_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode n) e) zeroGraph ↔ n = 0 := by
  constructor
  · intro h
    have hz := (HF_emptyAt_empty standardModel (scons (ordinalCode n) e) 0).mp h
    apply ordinalCode_injective
    rw [ordinalCode_zero]
    exact hz
  · intro h
    subst h
    exact zeroGraph_ordinalCode e

theorem succGraph_ordinalCode (n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode (n+1)) (scons (ordinalCode n) e)) succGraph := by
  apply (HF_succAt_spec standardModel
    (scons (ordinalCode (n+1)) (scons (ordinalCode n) e)) 0 1).mpr
  exact ordinalCode_succ n

theorem succGraph_exact_on_ordinalCodes (m n : Nat) (e : Nat → Nat) :
    Sat Mem (scons (ordinalCode m) (scons (ordinalCode n) e)) succGraph ↔
      m = n + 1 := by
  constructor
  · intro h
    have hs := (HF_succAt_spec standardModel
      (scons (ordinalCode m) (scons (ordinalCode n) e)) 0 1).mp h
    apply ordinalCode_injective
    rw [ordinalCode_succ]
    exact hs
  · intro h
    subst h
    exact succGraph_ordinalCode n e

theorem addGraph_ordinalCode (m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode (m+n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      addGraph := by
  let f := succRecTrace (ordinalCode m) n
  refine ⟨f, ?_, ?_⟩
  · exact (HF_succRecApproxAt_spec standardModel
      (scons f (scons (ordinalCode (m+n))
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 0 2 3).mpr
      (succRecTrace_succRecApprox (ordinalCode m) n)
  · apply (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode (m+n))
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 3 1 0).mpr
    have hp := succRecTrace_pair_mem (ordinalCode m) (k := n) (n := n) (Nat.le_refl n)
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode (m+n))) f
    simpa [f, succIterObj_ordinalCode] using hp

theorem addGraphAt_ordinalCode (out left right m n : Nat) (e : Nat → Nat)
    (hout : e out = ordinalCode (m+n))
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n) :
    Sat Mem e (addGraphAt out left right) := by
  let f := succRecTrace (ordinalCode m) n
  refine ⟨f, ?_, ?_⟩
  · apply (HF_succRecApproxAt_spec standardModel (scons f e)
      0 (left+1) (right+1)).mpr
    change SuccRecApprox standardModel (e left) f (e right)
    rw [hleft, hright]
    exact succRecTrace_succRecApprox (ordinalCode m) n
  · apply (HF_pairMemAt_spec standardModel (scons f e) (right+1) (out+1) 0).mpr
    change Mem (kpair standardModel (e right) (e out)) f
    rw [hout, hright]
    have hp := succRecTrace_pair_mem (ordinalCode m) (k := n) (n := n) (Nat.le_refl n)
    simpa [f, succIterObj_ordinalCode] using hp

theorem addGraphAt_value_of_ordinalInputs (out left right m n : Nat) (e : Nat → Nat)
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n)
    (h : Sat Mem e (addGraphAt out left right)) :
    e out = ordinalCode (m+n) := by
  rcases h with ⟨f, hf, hpair⟩
  have hf' := (HF_succRecApproxAt_spec standardModel (scons f e)
    0 (left+1) (right+1)).mp hf
  have hpair' := (HF_pairMemAt_spec standardModel (scons f e)
    (right+1) (out+1) 0).mp hpair
  change SuccRecApprox standardModel (e left) f (e right) at hf'
  change Mem (kpair standardModel (e right) (e out)) f at hpair'
  rw [hleft, hright] at hf'
  rw [hright] at hpair'
  have hval := succRecApprox_value_of_le (ordinalCode m) f n n (e out)
    hf' (Nat.le_refl n) hpair'
  rw [hval, succIterObj_ordinalCode]

theorem addGraphAt_exact_on_ordinalCodes (out left right r m n : Nat) (e : Nat → Nat)
    (hout : e out = ordinalCode r)
    (hleft : e left = ordinalCode m)
    (hright : e right = ordinalCode n) :
    Sat Mem e (addGraphAt out left right) ↔ r = m + n := by
  constructor
  · intro h
    have hval := addGraphAt_value_of_ordinalInputs out left right m n e hleft hright h
    apply ordinalCode_injective
    rw [← hout, hval]
  · intro h
    subst h
    exact addGraphAt_ordinalCode out left right m n e
      (by rw [hout]) hleft hright

theorem addGraph_exact_on_ordinalCodes (r m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      addGraph ↔ r = m + n := by
  constructor
  · intro h
    rcases h with ⟨f, hf, hout⟩
    have hf' := (HF_succRecApproxAt_spec standardModel
      (scons f (scons (ordinalCode r)
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 0 2 3).mp hf
    have hout' := (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode r)
        (scons (ordinalCode m) (scons (ordinalCode n) e)))) 3 1 0).mp hout
    have hval := succRecApprox_value_of_le (ordinalCode m) f n n (ordinalCode r)
      hf' (Nat.le_refl n) hout'
    apply ordinalCode_injective
    rw [hval, succIterObj_ordinalCode]
  · intro h
    subst h
    exact addGraph_ordinalCode m n e

theorem mulRecApproxAt_value_of_le (m N f outDummy : Nat) (e : Nat → Nat) :
    ∀ n y,
      Sat Mem
        (scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e))))
        (mulRecApproxAt 0 2 3) →
      n ≤ N →
      Mem (kpair standardModel (ordinalCode n) y) f →
      y = ordinalCode (m*n) := by
  intro n
  induction n with
  | zero =>
      intro y hA _hn hy
      let E := scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e)))
      change Sat Mem E (mulRecApproxAt 0 2 3) at hA
      rcases hA with ⟨hfunSat, _hkeysSat, hzeroSat, _htotalSat, _hstepSat⟩
      have hfun := (HF_pairFunctionalAt_spec standardModel E 0).mp hfunSat
      change PairFunctional standardModel f at hfun
      have hbase := (HF_pairZeroBaseAt_spec standardModel E 0).mp hzeroSat
      change Mem (kpair standardModel empty empty) f at hbase
      have hbase' : Mem (kpair standardModel (ordinalCode 0) (ordinalCode 0)) f := by
        simpa [ordinalCode_zero] using hbase
      have hy_eq := hfun (ordinalCode 0) y (ordinalCode 0) hy hbase'
      simpa [ordinalCode_zero] using hy_eq
  | succ n ih =>
      intro y hA hn hy
      let E := scons f (scons outDummy (scons (ordinalCode m) (scons (ordinalCode N) e)))
      change Sat Mem E (mulRecApproxAt 0 2 3) at hA
      have hA' := hA
      rcases hA with ⟨_hfunSat, _hkeysSat, _hzeroSat, htotalSat, hstepSat⟩
      have htotal := (HF_pairTotalBelowSuccAt_spec standardModel E 0 3).mp htotalSat
      change PairTotalBelowSucc standardModel f (ordinalCode N) at htotal
      have hnlt : n < N := by omega
      rcases htotal (ordinalCode n) (Or.inl (ordinalCode_mem_of_lt hnlt)) with ⟨t, ht⟩
      have htval := ih t hA' (Nat.le_of_lt hnlt) ht
      let Ekty := scons y (scons t (scons (ordinalCode n) E))
      let Eskty := scons (ordinalCode (n+1)) Ekty
      have hktSat : Sat Mem Ekty (HF_pairMemAt 2 1 3) := by
        apply (HF_pairMemAt_spec standardModel Ekty 2 1 3).mpr
        change Mem (kpair standardModel (ordinalCode n) t) f
        exact ht
      have hskSat : Sat Mem Eskty (HF_succAt 0 3) := by
        apply (HF_succAt_spec standardModel Eskty 0 3).mpr
        change ordinalCode (n+1) = adjoin (ordinalCode n) (ordinalCode n)
        exact ordinalCode_succ n
      have hskySat : Sat Mem Eskty (HF_pairMemAt 0 1 4) := by
        apply (HF_pairMemAt_spec standardModel Eskty 0 1 4).mpr
        change Mem (kpair standardModel (ordinalCode (n+1)) y) f
        exact hy
      have haddSat := hstepSat (ordinalCode n) t y
        (ordinalCode_mem_of_lt hnlt) hktSat (ordinalCode (n+1)) hskSat hskySat
      have hyval := addGraphAt_value_of_ordinalInputs 1 2 6 (m*n) m Eskty
        (by
          show t = ordinalCode (m*n)
          exact htval)
        (by rfl)
        haddSat
      change y = ordinalCode (m*n + m) at hyval
      rw [hyval, Nat.mul_succ]

theorem mulGraph_ordinalCode (m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode (m*n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      mulGraph := by
  let f := mulRecTrace m n
  let E := scons f
    (scons (ordinalCode (m*n)) (scons (ordinalCode m) (scons (ordinalCode n) e)))
  refine ⟨f, ?_, ?_⟩
  · change Sat Mem E (mulRecApproxAt 0 2 3)
    constructor
    · exact (HF_pairFunctionalAt_spec standardModel E 0).mpr (mulRecTrace_functional m n)
    · constructor
      · apply (HF_pairKeysBelowSuccAt_spec standardModel E 0 3).mpr
        change PairKeysBelowSucc standardModel f (ordinalCode n)
        exact mulRecTrace_keysBelowSucc m n
      · constructor
        · apply (HF_pairZeroBaseAt_spec standardModel E 0).mpr
          change Mem (kpair standardModel empty empty) f
          simpa [f, ordinalCode_zero] using
            (mulRecTrace_pair_mem m (k := 0) (n := n) (Nat.zero_le n))
        · constructor
          · apply (HF_pairTotalBelowSuccAt_spec standardModel E 0 3).mpr
            change PairTotalBelowSucc standardModel f (ordinalCode n)
            exact mulRecTrace_totalBelowSucc m n
          · intro k t y hkm hkt sk hsk hsky
            let Ekty := scons y (scons t (scons k E))
            let Eskty := scons sk Ekty
            have hkt' : Mem (kpair standardModel k t) f := by
              have h := (HF_pairMemAt_spec standardModel Ekty 2 1 3).mp hkt
              change Mem (kpair standardModel k t) f at h
              exact h
            have hsky' : Mem (kpair standardModel sk y) f := by
              have h := (HF_pairMemAt_spec standardModel Eskty 0 1 4).mp hsky
              change Mem (kpair standardModel sk y) f at h
              exact h
            have hsk' : sk = adjoin k k := by
              have h := (HF_succAt_spec standardModel Eskty 0 3).mp hsk
              change sk = adjoin k k at h
              exact h
            rcases (mem_ordinalCode_iff k n).mp hkm with ⟨i, hi, hk⟩
            rcases (mulRecTrace_mem_iff m _ n).mp hkt' with ⟨j, _hj, hpair_j⟩
            have hcomp_j := kpair_injective standardModel hpair_j
            have hij : i = j := by
              apply ordinalCode_injective
              exact hk.symm.trans hcomp_j.1
            have ht : t = ordinalCode (m * i) := by
              rw [hcomp_j.2, ← hij]
            have hskcode : sk = ordinalCode (i+1) := by
              rw [hsk', hk, ordinalCode_succ]
            rcases (mulRecTrace_mem_iff m _ n).mp hsky' with ⟨l, _hl, hpair_l⟩
            have hcomp_l := kpair_injective standardModel hpair_l
            have hil : i+1 = l := by
              apply ordinalCode_injective
              exact hskcode.symm.trans hcomp_l.1
            have hy : y = ordinalCode (m * (i+1)) := by
              rw [hcomp_l.2, ← hil]
            apply addGraphAt_ordinalCode 1 2 6 (m * i) m Eskty
            · show y = ordinalCode (m * i + m)
              rw [hy, Nat.mul_succ]
            · show t = ordinalCode (m * i)
              exact ht
            · rfl
  · apply (HF_pairMemAt_spec standardModel E 3 1 0).mpr
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode (m*n))) f
    exact mulRecTrace_pair_mem m (Nat.le_refl n)

theorem mulGraph_exact_on_ordinalCodes (r m n : Nat) (e : Nat → Nat) :
    Sat Mem
      (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e)))
      mulGraph ↔ r = m * n := by
  constructor
  · intro h
    rcases h with ⟨f, hf, hout⟩
    have hout' := (HF_pairMemAt_spec standardModel
      (scons f (scons (ordinalCode r) (scons (ordinalCode m) (scons (ordinalCode n) e))))
      3 1 0).mp hout
    change Mem (kpair standardModel (ordinalCode n) (ordinalCode r)) f at hout'
    have hval := mulRecApproxAt_value_of_le m n f (ordinalCode r) e n (ordinalCode r)
      hf (Nat.le_refl n) hout'
    exact ordinalCode_injective hval
  · intro h
    subst h
    exact mulGraph_ordinalCode m n e

theorem mulGraph_value_of_ordinalInputs (m n : Nat) (e : Nat → Nat)
    (hleft : e 1 = ordinalCode m)
    (hright : e 2 = ordinalCode n)
    (h : Sat Mem e mulGraph) :
    e 0 = ordinalCode (m*n) := by
  rcases h with ⟨f, hf, hout⟩
  let tail : Nat → Nat := fun k => e (k+3)
  let eCanon : Nat → Nat :=
    scons f (scons (e 0) (scons (ordinalCode m) (scons (ordinalCode n) tail)))
  have heq : ∀ k, eCanon k = scons f e k := by
    intro k
    rcases k with _ | k
    · rfl
    rcases k with _ | k
    · rfl
    rcases k with _ | k
    · exact hleft.symm
    rcases k with _ | k
    · exact hright.symm
    · simp [eCanon, tail, scons]
  have hfCanon : Sat Mem eCanon (mulRecApproxAt 0 2 3) :=
    (Sat_ext (mulRecApproxAt 0 2 3) eCanon (scons f e) heq).mpr hf
  have hout' := (HF_pairMemAt_spec standardModel (scons f e) 3 1 0).mp hout
  change Mem (kpair standardModel (e 2) (e 0)) f at hout'
  rw [hright] at hout'
  exact mulRecApproxAt_value_of_le m n f (e 0) tail n (e 0)
    hfCanon (Nat.le_refl n) hout'

/-- In any adjunction model, the HF empty set is in the interpreted PA
domain. -/
theorem domain_empty_model {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem (scons M.empty e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons M.empty e) 0).mpr
  exact OrdinalLike.empty M

/-- In any adjunction model, the HF empty set realizes the PA-in-HF zero
graph. -/
theorem zeroGraph_empty_model {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem (scons M.empty e) zeroGraph := by
  apply (HF_emptyAt_empty M (scons M.empty e) 0).mpr
  rfl

/-- In any adjunction model, self-adjunction realizes the PA-in-HF successor
graph. -/
theorem succGraph_adjoin_self_model {α : Type} (M : AdjunctionModel α)
    (a : α) (e : Nat → α) :
    Sat M.mem (scons (M.adjoin a a) (scons a e)) succGraph := by
  apply (HF_succAt_spec M (scons (M.adjoin a a) (scons a e)) 0 1).mpr
  rfl

/-- In any adjunction model, self-adjunction preserves the interpreted PA
domain. -/
theorem domain_adjoin_self_model {α : Type} (M : AdjunctionModel α)
    (a : α) (e : Nat → α)
    (ha : Sat M.mem (scons a e) domainForm) :
    Sat M.mem (scons (M.adjoin a a) e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons (M.adjoin a a) e) 0).mpr
  have ha' := (HF_ordinalLikeAt_spec (scons a e) 0).mp ha
  exact OrdinalLike.adjoin_self M ha' rfl

/-- The carrier of the PA interpretation inside an adjunction model. -/
def Domain {α : Type} (M : AdjunctionModel α) : Type :=
  {a : α // OrdinalLike M.mem a}

/-- Zero of the interpreted PA domain. -/
def domainZero {α : Type} (M : AdjunctionModel α) : Domain M :=
  ⟨M.empty, OrdinalLike.empty M⟩

/-- Successor of the interpreted PA domain. -/
def domainSucc {α : Type} (M : AdjunctionModel α) (a : Domain M) : Domain M :=
  ⟨M.adjoin a.val a.val, OrdinalLike.adjoin_self M a.property rfl⟩

theorem domainZero_val {α : Type} (M : AdjunctionModel α) :
    (domainZero M).val = M.empty :=
  rfl

theorem domainSucc_val {α : Type} (M : AdjunctionModel α) (a : Domain M) :
    (domainSucc M a).val = M.adjoin a.val a.val :=
  rfl

/-- Self-adjunction is never empty. -/
theorem adjoin_self_ne_empty_model {α : Type} (M : AdjunctionModel α) (a : α) :
    M.adjoin a a ≠ M.empty := by
  intro h
  have ha : M.mem a (M.adjoin a a) := (M.adjoin_spec a a a).mpr (Or.inr rfl)
  rw [h] at ha
  exact M.empty_spec a ha

/-- Self-adjunction is injective on ordinal-like objects. -/
theorem adjoin_self_injective_on_ordinalLike_model {α : Type}
    (M : AdjunctionModel α) {a b : α}
    (_ha : OrdinalLike M.mem a) (hb : OrdinalLike M.mem b)
    (h : M.adjoin a a = M.adjoin b b) : a = b := by
  have hasucc : M.mem a (M.adjoin b b) := by
    have : M.mem a (M.adjoin a a) := (M.adjoin_spec a a a).mpr (Or.inr rfl)
    simpa [h] using this
  rcases (M.adjoin_spec a b b).mp hasucc with hab | hab
  · have hbsucc : M.mem b (M.adjoin a a) := by
      have : M.mem b (M.adjoin b b) := (M.adjoin_spec b b b).mpr (Or.inr rfl)
      simpa [← h] using this
    rcases (M.adjoin_spec b a a).mp hbsucc with hba | hba
    · have hbb : M.mem b b := hb.1 a hab b hba
      exact False.elim (M.mem_irrefl b hbb)
    · exact hba.symm
  · exact hab

/-- Successor is injective on the interpreted PA domain. -/
theorem domainSucc_injective_model {α : Type} (M : AdjunctionModel α)
    {a b : Domain M} (h : domainSucc M a = domainSucc M b) : a = b := by
  apply Subtype.ext
  apply adjoin_self_injective_on_ordinalLike_model M a.property b.property
  exact congrArg Subtype.val h

/-- No successor in the interpreted PA domain is zero. -/
theorem domainSucc_ne_zero_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) : domainSucc M a ≠ domainZero M := by
  intro h
  exact adjoin_self_ne_empty_model M a.val (congrArg Subtype.val h)

/-- Every element of the interpreted PA carrier satisfies the domain formula. -/
theorem domainElement_domainForm_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons a.val e) domainForm := by
  apply (HF_ordinalLikeAt_spec (scons a.val e) 0).mpr
  exact a.property

/-- The interpreted zero satisfies the PA-in-HF domain formula. -/
theorem domainZero_domainForm_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem (scons (domainZero M).val e) domainForm :=
  domainElement_domainForm_model M (domainZero M) e

/-- The interpreted zero realizes the PA-in-HF zero graph. -/
theorem domainZero_zeroGraph_model {α : Type} (M : AdjunctionModel α)
    (e : Nat → α) :
    Sat M.mem (scons (domainZero M).val e) zeroGraph := by
  simpa [domainZero_val] using zeroGraph_empty_model M e

/-- The interpreted successor satisfies the PA-in-HF domain formula. -/
theorem domainSucc_domainForm_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons (domainSucc M a).val e) domainForm :=
  domainElement_domainForm_model M (domainSucc M a) e

/-- The interpreted successor realizes the PA-in-HF successor graph. -/
theorem domainSucc_succGraph_model {α : Type} (M : AdjunctionModel α)
    (a : Domain M) (e : Nat → α) :
    Sat M.mem (scons (domainSucc M a).val (scons a.val e)) succGraph := by
  simpa [domainSucc_val] using succGraph_adjoin_self_model M a.val e

/-- In any adjunction model, the PA-in-HF zero graph lands in the interpreted
PA domain. -/
theorem zeroGraph_domain_model {α : Type} (M : AdjunctionModel α) (e : Nat → α)
    (hz : Sat M.mem e zeroGraph) : Sat M.mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hz' := (HF_emptyAt_empty M e 0).mp hz
  rw [hz']
  exact OrdinalLike.empty M

/-- Standard Ackermann-HF specialization of `zeroGraph_domain_model`. -/
theorem zeroGraph_domain (e : Nat → Nat)
    (hz : Sat Mem e zeroGraph) : Sat Mem e domainForm :=
  zeroGraph_domain_model standardModel e hz

/-- In any adjunction model, the PA-in-HF successor graph preserves the
interpreted PA domain. -/
theorem succGraph_preserves_domain_model {α : Type} (M : AdjunctionModel α) (e : Nat → α)
    (hin : Sat M.mem e (HF_ordinalLikeAt 1))
    (hs : Sat M.mem e succGraph) :
    Sat M.mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hin' := (HF_ordinalLikeAt_spec e 1).mp hin
  have hs' := (HF_succAt_spec M e 0 1).mp hs
  exact OrdinalLike.adjoin_self M hin' hs'

/-- Standard Ackermann-HF specialization of
`succGraph_preserves_domain_model`. -/
theorem succGraph_preserves_domain (e : Nat → Nat)
    (hin : Sat Mem e (HF_ordinalLikeAt 1))
    (hs : Sat Mem e succGraph) :
    Sat Mem e domainForm :=
  succGraph_preserves_domain_model standardModel e hin hs

end PAInHF

/-- The interpreted PA domain inside Ackermann HF: the finite von Neumann
ordinals, represented by their Ackermann codes. -/
def OrdinalHF : Type := {a : Nat // IsOrdinalCode a}

def ordinalOfNat (n : Nat) : OrdinalHF := ⟨ordinalCode n, ⟨n, rfl⟩⟩

noncomputable def natOfOrdinal (a : OrdinalHF) : Nat := a.property.choose

theorem ordinalOfNat_val (n : Nat) :
    (ordinalOfNat n).val = ordinalCode n := rfl

theorem natOfOrdinal_spec (a : OrdinalHF) :
    ordinalCode (natOfOrdinal a) = a.val :=
  a.property.choose_spec

theorem natOfOrdinal_ordinalOfNat (n : Nat) :
    natOfOrdinal (ordinalOfNat n) = n :=
  ordinalCode_injective (natOfOrdinal_spec (ordinalOfNat n))

theorem ordinalOfNat_natOfOrdinal (a : OrdinalHF) :
    ordinalOfNat (natOfOrdinal a) = a := by
  apply Subtype.ext
  exact natOfOrdinal_spec a

end AckermannHF

/-! ## Shallow PA models and the PA-in-HF round trip -/

namespace PA

universe u v

/-- A shallow model of first-order Peano arithmetic in the language
`0, S, +, *`, with induction represented as a schema over Lean predicates. -/
structure Model (α : Type u) where
  zero : α
  succ : α → α
  add : α → α → α
  mul : α → α → α
  succ_injective : ∀ {a b}, succ a = succ b → a = b
  zero_not_succ : ∀ a, succ a ≠ zero
  induction :
    ∀ P : α → Prop, P zero → (∀ a, P a → P (succ a)) → ∀ a, P a
  add_zero : ∀ a, add a zero = a
  add_succ : ∀ a b, add a (succ b) = succ (add a b)
  mul_zero : ∀ a, mul a zero = zero
  mul_succ : ∀ a b, mul a (succ b) = add (mul a b) a

/-- Isomorphism of shallow PA models, preserving the arithmetic operations. -/
structure Iso {α : Type u} {β : Type v} (M : Model α) (N : Model β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_zero : toFun M.zero = N.zero
  map_succ : ∀ a, toFun (M.succ a) = N.succ (toFun a)
  map_add : ∀ a b, toFun (M.add a b) = N.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (M.mul a b) = N.mul (toFun a) (toFun b)

/-- The standard model of PA on Lean's natural numbers. -/
def natModel : Model Nat where
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul
  succ_injective := by
    intro a b h
    exact Nat.succ.inj h
  zero_not_succ := by
    intro a h
    exact Nat.succ_ne_zero a h
  induction := by
    intro P h0 hs a
    induction a with
    | zero => exact h0
    | succ n ih => exact hs n ih
  add_zero := Nat.add_zero
  add_succ := Nat.add_succ
  mul_zero := Nat.mul_zero
  mul_succ := Nat.mul_succ

/-! ### First-order PA syntax and semantics -/

inductive Term : Type
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving Repr, DecidableEq

inductive Formula : Type
  | eq : Term → Term → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula
  deriving Repr, DecidableEq

namespace Term

def rename (r : Nat → Nat) : Term → Term
  | var n => var (r n)
  | zero => zero
  | succ t => succ (rename r t)
  | add a b => add (rename r a) (rename r b)
  | mul a b => mul (rename r a) (rename r b)

def upSubst (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n+1 => rename Nat.succ (σ n)

def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | zero => zero
  | succ t => succ (subst σ t)
  | add a b => add (subst σ a) (subst σ b)
  | mul a b => mul (subst σ a) (subst σ b)

def eval {α : Type u} (M : Model α) (e : Nat → α) : Term → α
  | var n => e n
  | zero => M.zero
  | succ t => M.succ (eval M e t)
  | add a b => M.add (eval M e a) (eval M e b)
  | mul a b => M.mul (eval M e a) (eval M e b)

def numeral : Nat → Term
  | 0 => zero
  | n+1 => succ (numeral n)

/-- The PA term obtained by adding a fixed left term to a standard numeral on
the right, unfolded using the PA recursion equation for addition. -/
def addRightNumeral (t : Term) : Nat → Term
  | 0 => t
  | n+1 => succ (addRightNumeral t n)

/-- The PA term obtained by multiplying a fixed left term by a standard numeral
on the right, unfolded using the PA recursion equation for multiplication. -/
def mulRightNumeral (t : Term) : Nat → Term
  | 0 => zero
  | n+1 => add (mulRightNumeral t n) t

def numeralValue {α : Type u} (M : Model α) : Nat → α
  | 0 => M.zero
  | n+1 => M.succ (numeralValue M n)

@[simp] theorem rename_numeral (r : Nat → Nat) :
    ∀ n, rename r (numeral n) = numeral n
  | 0 => rfl
  | n+1 => by simp [numeral, rename, rename_numeral r n]

@[simp] theorem subst_numeral (σ : Nat → Term) :
    ∀ n, subst σ (numeral n) = numeral n
  | 0 => rfl
  | n+1 => by simp [numeral, subst, subst_numeral σ n]

@[simp] theorem numeral_succ (n : Nat) :
    numeral (n + 1) = succ (numeral n) := by
  rfl

theorem addRightNumeral_numeral (m n : Nat) :
    addRightNumeral (numeral m) n = numeral (m + n) := by
  induction n with
  | zero =>
      simp [addRightNumeral]
  | succ n ih =>
      rw [Nat.add_succ]
      simp [addRightNumeral, numeral, ih]

theorem eval_numeral {α : Type u} (M : Model α) (e : Nat → α) :
    ∀ n, eval M e (numeral n) = numeralValue M n
  | 0 => rfl
  | n+1 => by
      simp only [numeral, numeralValue, eval, eval_numeral M e n]

theorem numeralValue_natModel : ∀ n, numeralValue natModel n = n
  | 0 => rfl
  | n+1 => by
      change Nat.succ (numeralValue natModel n) = n + 1
      rw [numeralValue_natModel n]

theorem eval_numeral_natModel (e : Nat → Nat) (n : Nat) :
    eval natModel e (numeral n) = n := by
  rw [eval_numeral, numeralValue_natModel]

def bound : Term → Nat
  | var n => n + 1
  | zero => 0
  | succ t => bound t
  | add a b => bound a + bound b
  | mul a b => bound a + bound b

def Free : Nat → Term → Prop
  | n, var k => n = k
  | _, zero => False
  | n, succ t => Free n t
  | n, add a b => Free n a ∨ Free n b
  | n, mul a b => Free n a ∨ Free n b

theorem free_lt_bound (t : Term) : ∀ n, Free n t → n < bound t := by
  induction t with
  | var k =>
      intro n hn
      simp only [Free] at hn
      subst hn
      simp [bound]
  | zero =>
      intro n hn
      cases hn
  | succ t ih =>
      intro n hn
      exact ih n hn
  | add a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | mul a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega

theorem eval_ext {α : Type u} (M : Model α) (t : Term)
    {e e' : Nat → α} (h : ∀ n, e n = e' n) :
    eval M e t = eval M e' t := by
  induction t with
  | var n => exact h n
  | zero => rfl
  | succ t ih => simp only [eval, ih]
  | add a b iha ihb => simp only [eval, iha, ihb]
  | mul a b iha ihb => simp only [eval, iha, ihb]

theorem eval_rename {α : Type u} (M : Model α) (t : Term)
    (r : Nat → Nat) (e : Nat → α) :
    eval M e (rename r t) = eval M (fun n => e (r n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp only [rename, eval, ih]
  | add a b iha ihb => simp only [rename, eval, iha, ihb]
  | mul a b iha ihb => simp only [rename, eval, iha, ihb]

theorem rename_ext (t : Term) (r r' : Nat → Nat) (h : ∀ n, r n = r' n) :
    rename r t = rename r' t := by
  induction t with
  | var n => simp [rename, h n]
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem rename_ext_free (t : Term) :
    ∀ r r', (∀ n, Free n t → r n = r' n) → rename r t = rename r' t := by
  induction t with
  | var n =>
      intro r r' h
      simp [rename, h n rfl]
  | zero =>
      intro r r' h
      rfl
  | succ t ih =>
      intro r r' h
      simp [rename, ih r r' h]
  | add a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | mul a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]

theorem rename_id (t : Term) : rename (fun n : Nat => n) t = t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem rename_comp (t : Term) (r r' : Nat → Nat) :
    rename r (rename r' t) = rename (fun n => r (r' n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem eval_upSubst {α : Type u} (M : Model α) (σ : Nat → Term)
    (e : Nat → α) (d : α) (n : Nat) :
    eval M (SetTheory.scons d e) (upSubst σ n) =
      SetTheory.scons d (fun k => eval M e (σ k)) n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [upSubst, SetTheory.scons]
      rw [eval_rename]
      rfl

theorem eval_subst {α : Type u} (M : Model α) (t : Term)
    (σ : Nat → Term) (e : Nat → α) :
    eval M e (subst σ t) = eval M (fun n => eval M e (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp only [subst, eval, ih]
  | add a b iha ihb => simp only [subst, eval, iha, ihb]
  | mul a b iha ihb => simp only [subst, eval, iha, ihb]

theorem subst_ext (t : Term) (σ τ : Nat → Term) (h : ∀ n, σ n = τ n) :
    subst σ t = subst τ t := by
  induction t with
  | var n => exact h n
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

theorem subst_rename (t : Term) (σ : Nat → Term) (r : Nat → Nat) :
    subst σ (rename r t) = subst (fun n => σ (r n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, subst, ih]
  | add a b iha ihb => simp [rename, subst, iha, ihb]
  | mul a b iha ihb => simp [rename, subst, iha, ihb]

theorem rename_subst (t : Term) (r : Nat → Nat) (σ : Nat → Term) :
    rename r (subst σ t) =
      subst (fun n => rename r (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, subst, ih]
  | add a b iha ihb => simp [rename, subst, iha, ihb]
  | mul a b iha ihb => simp [rename, subst, iha, ihb]

theorem subst_comp (t : Term) (σ τ : Nat → Term) :
    subst τ (subst σ t) =
      subst (fun n => subst τ (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

theorem subst_rename_succ_up (t : Term) (σ : Nat → Term) :
    subst (upSubst σ) (rename Nat.succ t) =
      rename Nat.succ (subst σ t) := by
  rw [subst_rename, rename_subst]
  exact subst_ext t _ _ (fun n => by rfl)

theorem subst_ext_free (t : Term) :
    ∀ σ τ, (∀ n, Free n t → σ n = τ n) → subst σ t = subst τ t := by
  induction t with
  | var n =>
      intro σ τ h
      exact h n rfl
  | zero =>
      intro σ τ h
      rfl
  | succ t ih =>
      intro σ τ h
      simp [subst, ih σ τ h]
  | add a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | mul a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]

theorem subst_id (t : Term) :
    subst (fun n => var n) t = t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

end Term

namespace Formula

def iffForm (a b : Formula) : Formula := and (imp a b) (imp b a)

def rename (r : Nat → Nat) : Formula → Formula
  | eq a b => eq (Term.rename r a) (Term.rename r b)
  | bot => bot
  | imp a b => imp (rename r a) (rename r b)
  | and a b => and (rename r a) (rename r b)
  | or a b => or (rename r a) (rename r b)
  | all a => all (rename (SetTheory.up r) a)
  | ex a => ex (rename (SetTheory.up r) a)

def subst (σ : Nat → Term) : Formula → Formula
  | eq a b => eq (Term.subst σ a) (Term.subst σ b)
  | bot => bot
  | imp a b => imp (subst σ a) (subst σ b)
  | and a b => and (subst σ a) (subst σ b)
  | or a b => or (subst σ a) (subst σ b)
  | all a => all (subst (Term.upSubst σ) a)
  | ex a => ex (subst (Term.upSubst σ) a)

def Sat {α : Type u} (M : Model α) : (Nat → α) → Formula → Prop
  | e, eq a b => Term.eval M e a = Term.eval M e b
  | _, bot => False
  | e, imp a b => Sat M e a → Sat M e b
  | e, and a b => Sat M e a ∧ Sat M e b
  | e, or a b => Sat M e a ∨ Sat M e b
  | e, all a => ∀ d, Sat M (SetTheory.scons d e) a
  | e, ex a => ∃ d, Sat M (SetTheory.scons d e) a

theorem Sat_iffForm {α : Type u} (M : Model α) (e : Nat → α) (a b : Formula) :
    Sat M e (iffForm a b) ↔ (Sat M e a ↔ Sat M e b) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · intro h
    exact ⟨h.1, h.2⟩

def bound : Formula → Nat
  | eq a b => Term.bound a + Term.bound b
  | bot => 0
  | imp a b => bound a + bound b
  | and a b => bound a + bound b
  | or a b => bound a + bound b
  | all a => bound a
  | ex a => bound a

def Free : Nat → Formula → Prop
  | n, eq a b => Term.Free n a ∨ Term.Free n b
  | _, bot => False
  | n, imp a b => Free n a ∨ Free n b
  | n, and a b => Free n a ∨ Free n b
  | n, or a b => Free n a ∨ Free n b
  | n, all a => Free (n+1) a
  | n, ex a => Free (n+1) a

def Sentence (phi : Formula) : Prop := ∀ n, ¬ Free n phi

def Sentences (B : Formula → Prop) : Prop := ∀ phi, B phi → Sentence phi

theorem free_lt_bound (phi : Formula) : ∀ n, Free n phi → n < bound phi := by
  induction phi with
  | eq a b =>
      intro n hn
      rcases hn with hn | hn
      · have := Term.free_lt_bound a n hn
        simp [bound]
        omega
      · have := Term.free_lt_bound b n hn
        simp [bound]
        omega
  | bot =>
      intro n hn
      cases hn
  | imp a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | and a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | or a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | all a ih =>
      intro n hn
      have := ih (n+1) hn
      simp [bound]
      omega
  | ex a ih =>
      intro n hn
      have := ih (n+1) hn
      simp [bound]
      omega

def closeN : Nat → Formula → Formula
  | 0, phi => phi
  | n+1, phi => closeN n (all phi)

def sealPA (phi : Formula) : Formula := closeN (bound phi) phi

theorem Free_closeN : ∀ (k : Nat) (phi : Formula) (n : Nat),
    Free n (closeN k phi) → Free (k + n) phi := by
  intro k
  induction k with
  | zero =>
      intro phi n h
      rw [Nat.zero_add]
      exact h
  | succ k ih =>
      intro phi n h
      have h1 : Free (k + n) (all phi) := ih (all phi) n h
      have h2 : Free (k + n + 1) phi := h1
      have harg : k + 1 + n = k + n + 1 := by omega
      rw [harg]
      exact h2

theorem sealPA_sentence (phi : Formula) : Sentence (sealPA phi) := by
  intro n h
  have h1 := Free_closeN (bound phi) phi n h
  have h2 := free_lt_bound phi _ h1
  omega

theorem Sat_ext {α : Type u} (M : Model α) (phi : Formula)
    {e e' : Nat → α} (h : ∀ n, e n = e' n) :
    Sat M e phi ↔ Sat M e' phi := by
  induction phi generalizing e e' with
  | eq a b =>
      simp only [Sat]
      rw [Term.eval_ext M a h, Term.eval_ext M b h]
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
      simp only [Sat]
      exact ⟨fun hab ha => (ihb h).mp (hab ((iha h).mpr ha)),
             fun hab ha => (ihb h).mpr (hab ((iha h).mp ha))⟩
  | and a b iha ihb =>
      simp only [Sat]
      exact and_congr (iha h) (ihb h)
  | or a b iha ihb =>
      simp only [Sat]
      exact or_congr (iha h) (ihb h)
  | all a ih =>
      simp only [Sat]
      constructor
      · intro hall d
        exact (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mp (hall d)
      · intro hall d
        exact (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mpr (hall d)
  | ex a ih =>
      simp only [Sat]
      constructor
      · intro ⟨d, hd⟩
        exact ⟨d, (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mp hd⟩
      · intro ⟨d, hd⟩
        exact ⟨d, (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mpr hd⟩

theorem Sat_subst {α : Type u} (M : Model α) (phi : Formula)
    (σ : Nat → Term) (e : Nat → α) :
    Sat M e (subst σ phi) ↔
      Sat M (fun n => Term.eval M e (σ n)) phi := by
  induction phi generalizing e σ with
  | eq a b =>
      simp only [subst, Sat, Term.eval_subst]
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
      simp only [subst, Sat]
      exact ⟨fun hab ha => (ihb σ e).mp (hab ((iha σ e).mpr ha)),
             fun hab ha => (ihb σ e).mpr (hab ((iha σ e).mp ha))⟩
  | and a b iha ihb =>
      simp only [subst, Sat]
      exact and_congr (iha σ e) (ihb σ e)
  | or a b iha ihb =>
      simp only [subst, Sat]
      exact or_congr (iha σ e) (ihb σ e)
  | all a ih =>
      simp only [subst, Sat]
      constructor
      · intro hall d
        have h1 := (ih (Term.upSubst σ) (SetTheory.scons d e)).mp (hall d)
        exact (Sat_ext M a (Term.eval_upSubst M σ e d)).mp h1
      · intro hall d
        have h1 : Sat M (fun n => Term.eval M (SetTheory.scons d e) (Term.upSubst σ n)) a :=
          (Sat_ext M a (Term.eval_upSubst M σ e d)).mpr (hall d)
        exact (ih (Term.upSubst σ) (SetTheory.scons d e)).mpr h1
  | ex a ih =>
      simp only [subst, Sat]
      constructor
      · intro ⟨d, hd⟩
        have h1 := (ih (Term.upSubst σ) (SetTheory.scons d e)).mp hd
        exact ⟨d, (Sat_ext M a (Term.eval_upSubst M σ e d)).mp h1⟩
      · intro ⟨d, hd⟩
        have h1 : Sat M (fun n => Term.eval M (SetTheory.scons d e) (Term.upSubst σ n)) a :=
          (Sat_ext M a (Term.eval_upSubst M σ e d)).mpr hd
        exact ⟨d, (ih (Term.upSubst σ) (SetTheory.scons d e)).mpr h1⟩

theorem closeN_valid {α : Type u} (M : Model α) (k : Nat) :
    ∀ phi : Formula, (∀ e : Nat → α, Sat M e (closeN k phi)) ↔
      (∀ e, Sat M e phi) := by
  induction k with
  | zero =>
      intro phi
      exact Iff.rfl
  | succ k ih =>
      intro phi
      show (∀ e, Sat M e (closeN k (all phi))) ↔ _
      rw [ih (all phi)]
      constructor
      · intro h e'
        have pf : ∀ n, SetTheory.scons (e' 0) (fun n => e' (n+1)) n = e' n := by
          intro n
          cases n <;> rfl
        exact (Sat_ext M phi pf).mp (h (fun n => e' (n+1)) (e' 0))
      · intro h e d
        exact h _

theorem seal_valid {α : Type u} (M : Model α) (phi : Formula) :
    (∀ e : Nat → α, Sat M e (sealPA phi)) ↔ (∀ e, Sat M e phi) :=
  closeN_valid M (bound phi) phi

/-! ### PA proof calculus -/

def instTerm (t : Term) : Nat → Term
  | 0 => t
  | n+1 => Term.var n

/-- PA-term substitution by variables is just PA-term renaming. -/
theorem term_subst_var_rename (t : Term) (r : Nat → Nat) :
    Term.subst (fun n => Term.var (r n)) t = Term.rename r t := by
  induction t with
  | var n =>
      rfl
  | zero =>
      rfl
  | succ t ih =>
      simp [Term.subst, Term.rename, ih]
  | add a b iha ihb =>
      simp [Term.subst, Term.rename, iha, ihb]
  | mul a b iha ihb =>
      simp [Term.subst, Term.rename, iha, ihb]

/-- Substituting PA de Bruijn 0 by a variable is just PA-term renaming by the
corresponding variable-instantiation map. -/
theorem term_subst_instTerm_var (t : Term) (k : Nat) :
    Term.subst (instTerm (Term.var k)) t = Term.rename (SetTheory.inst k) t := by
  rw [← term_subst_var_rename t (SetTheory.inst k)]
  exact Term.subst_ext t _ _ (fun n => by cases n <;> rfl)

theorem Sat_rename {α : Type u} (M : Model α) (phi : Formula)
    (r : Nat → Nat) (e : Nat → α) :
    Sat M e (rename r phi) ↔ Sat M (fun n => e (r n)) phi := by
  induction phi generalizing r e with
  | eq a b =>
      simp only [rename, Sat, Term.eval_rename]
  | bot =>
      exact Iff.rfl
  | imp a b iha ihb =>
      simp only [rename, Sat]
      exact ⟨fun hab ha => (ihb r e).mp (hab ((iha r e).mpr ha)),
        fun hab ha => (ihb r e).mpr (hab ((iha r e).mp ha))⟩
  | and a b iha ihb =>
      simp only [rename, Sat]
      exact and_congr (iha r e) (ihb r e)
  | or a b iha ihb =>
      simp only [rename, Sat]
      exact or_congr (iha r e) (ihb r e)
  | all a ih =>
      simp only [rename, Sat]
      constructor
      · intro h d
        have hbody := (ih (SetTheory.up r) (SetTheory.scons d e)).mp (h d)
        exact (Sat_ext M a (fun n => by cases n <;> rfl)).mp hbody
      · intro h d
        have hbody : Sat M (fun n => SetTheory.scons d e (SetTheory.up r n)) a :=
          (Sat_ext M a (fun n => by cases n <;> rfl)).mpr (h d)
        exact (ih (SetTheory.up r) (SetTheory.scons d e)).mpr hbody
  | ex a ih =>
      simp only [rename, Sat]
      constructor
      · intro ⟨d, hd⟩
        have hbody := (ih (SetTheory.up r) (SetTheory.scons d e)).mp hd
        exact ⟨d, (Sat_ext M a (fun n => by cases n <;> rfl)).mp hbody⟩
      · intro ⟨d, hd⟩
        have hbody : Sat M (fun n => SetTheory.scons d e (SetTheory.up r n)) a :=
          (Sat_ext M a (fun n => by cases n <;> rfl)).mpr hd
        exact ⟨d, (ih (SetTheory.up r) (SetTheory.scons d e)).mpr hbody⟩

theorem Sat_rename_succ {α : Type u} (M : Model α) (phi : Formula)
    (e : Nat → α) (d : α) :
    Sat M (SetTheory.scons d e) (rename Nat.succ phi) ↔ Sat M e phi := by
  rw [Sat_rename]
  exact Sat_ext M phi (fun n => rfl)

theorem rename_ext (phi : Formula) (r r' : Nat → Nat) (h : ∀ n, r n = r' n) :
    rename r phi = rename r' phi := by
  induction phi generalizing r r' with
  | eq a b =>
      simp [rename, Term.rename_ext a r r' h, Term.rename_ext b r r' h]
  | bot => rfl
  | imp a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | and a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | or a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | all a ih =>
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n])]
  | ex a ih =>
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n])]

theorem rename_ext_free (phi : Formula) :
    ∀ r r', (∀ n, Free n phi → r n = r' n) →
      rename r phi = rename r' phi := by
  induction phi with
  | eq a b =>
      intro r r' h
      simp [rename,
        Term.rename_ext_free a r r' (fun n hn => h n (Or.inl hn)),
        Term.rename_ext_free b r r' (fun n hn => h n (Or.inr hn))]
  | bot =>
      intro r r' h
      rfl
  | imp a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | and a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | or a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | all a ih =>
      intro r r' h
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n hn])]
  | ex a ih =>
      intro r r' h
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n hn])]

theorem rename_id (phi : Formula) : rename (fun n : Nat => n) phi = phi := by
  induction phi with
  | eq a b =>
      simp [rename, Term.rename_id]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [rename, iha, ihb]
  | and a b iha ihb =>
      simp [rename, iha, ihb]
  | or a b iha ihb =>
      simp [rename, iha, ihb]
  | all a ih =>
      simp only [rename]
      apply congrArg all
      calc
        rename (SetTheory.up (fun n : Nat => n)) a =
            rename (fun n : Nat => n) a := by
          apply rename_ext
          intro n
          cases n <;> rfl
        _ = a := ih
  | ex a ih =>
      simp only [rename]
      apply congrArg ex
      calc
        rename (SetTheory.up (fun n : Nat => n)) a =
            rename (fun n : Nat => n) a := by
          apply rename_ext
          intro n
          cases n <;> rfl
        _ = a := ih

theorem rename_eq_of_sentence {phi : Formula} (hphi : Sentence phi)
    (r : Nat → Nat) : rename r phi = phi := by
  calc
    rename r phi = rename (fun n : Nat => n) phi := by
      apply rename_ext_free
      intro n hn
      exact False.elim (hphi n hn)
    _ = phi := rename_id phi

theorem rename_comp (phi : Formula) (r r' : Nat → Nat) :
    rename r (rename r' phi) = rename (fun n => r (r' n)) phi := by
  induction phi generalizing r r' with
  | eq a b =>
      simp [rename, Term.rename_comp]
  | bot => rfl
  | imp a b iha ihb => simp [rename, iha, ihb]
  | and a b iha ihb => simp [rename, iha, ihb]
  | or a b iha ihb => simp [rename, iha, ihb]
  | all a ih =>
      simp only [rename]
      rw [ih]
      exact congrArg all (rename_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))
  | ex a ih =>
      simp only [rename]
      rw [ih]
      exact congrArg ex (rename_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))

theorem rename_up_succ (phi : Formula) (r : Nat → Nat) :
    rename (SetTheory.up r) (rename Nat.succ phi) =
      rename Nat.succ (rename r phi) := by
  rw [rename_comp, rename_comp]
  exact rename_ext phi _ _ (fun n => by rfl)

theorem subst_ext (phi : Formula) (σ τ : Nat → Term) (h : ∀ n, σ n = τ n) :
    subst σ phi = subst τ phi := by
  induction phi generalizing σ τ with
  | eq a b =>
      simp [subst, Term.subst_ext a σ τ h, Term.subst_ext b σ τ h]
  | bot => rfl
  | imp a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | and a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | or a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | all a ih =>
      simp [subst, ih (Term.upSubst σ) (Term.upSubst τ) (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [Term.upSubst, h n])]
  | ex a ih =>
      simp [subst, ih (Term.upSubst σ) (Term.upSubst τ) (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [Term.upSubst, h n])]

theorem subst_rename (phi : Formula) (σ : Nat → Term) (r : Nat → Nat) :
    subst σ (rename r phi) = subst (fun n => σ (r n)) phi := by
  induction phi generalizing σ r with
  | eq a b =>
      simp [rename, subst, Term.subst_rename]
  | bot => rfl
  | imp a b iha ihb => simp [rename, subst, iha, ihb]
  | and a b iha ihb => simp [rename, subst, iha, ihb]
  | or a b iha ihb => simp [rename, subst, iha, ihb]
  | all a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))
  | ex a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))

theorem rename_subst (phi : Formula) (r : Nat → Nat) (σ : Nat → Term) :
    rename r (subst σ phi) =
      subst (fun n => Term.rename r (σ n)) phi := by
  induction phi generalizing r σ with
  | eq a b =>
      simp [rename, subst, Term.rename_subst]
  | bot => rfl
  | imp a b iha ihb => simp [rename, subst, iha, ihb]
  | and a b iha ihb => simp [rename, subst, iha, ihb]
  | or a b iha ihb => simp [rename, subst, iha, ihb]
  | all a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst]
            rw [Term.rename_comp, Term.rename_comp]
            exact Term.rename_ext (σ n) _ _ (fun k => rfl)))
  | ex a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst]
            rw [Term.rename_comp, Term.rename_comp]
            exact Term.rename_ext (σ n) _ _ (fun k => rfl)))

theorem subst_comp (phi : Formula) (σ τ : Nat → Term) :
    subst τ (subst σ phi) =
      subst (fun n => Term.subst τ (σ n)) phi := by
  induction phi generalizing σ τ with
  | eq a b =>
      simp [subst, Term.subst_comp]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [subst, iha, ihb]
  | and a b iha ihb =>
      simp [subst, iha, ihb]
  | or a b iha ihb =>
      simp [subst, iha, ihb]
  | all a ih =>
      simp only [subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, Term.subst_rename_succ_up]))
  | ex a ih =>
      simp only [subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, Term.subst_rename_succ_up]))

theorem subst_rename_succ_up (phi : Formula) (σ : Nat → Term) :
    subst (Term.upSubst σ) (rename Nat.succ phi) =
      rename Nat.succ (subst σ phi) := by
  rw [subst_rename, rename_subst]
  exact subst_ext phi _ _ (fun n => by rfl)

theorem subst_ext_free (phi : Formula) :
    ∀ σ τ, (∀ n, Free n phi → σ n = τ n) → subst σ phi = subst τ phi := by
  induction phi with
  | eq a b =>
      intro σ τ h
      simp [subst,
        Term.subst_ext_free a σ τ (fun n hn => h n (Or.inl hn)),
        Term.subst_ext_free b σ τ (fun n hn => h n (Or.inr hn))]
  | bot =>
      intro σ τ h
      rfl
  | imp a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | and a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | or a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | all a ih =>
      intro σ τ h
      simp only [subst]
      apply congrArg all
      exact ih (Term.upSubst σ) (Term.upSubst τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, h n hn])
  | ex a ih =>
      intro σ τ h
      simp only [subst]
      apply congrArg ex
      exact ih (Term.upSubst σ) (Term.upSubst τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, h n hn])

/-- PA-formula substitution by variables is just PA-formula renaming. -/
theorem subst_var_rename (phi : Formula) (r : Nat → Nat) :
    subst (fun n => Term.var (r n)) phi = rename r phi := by
  induction phi generalizing r with
  | eq a b =>
      simp [subst, rename, term_subst_var_rename]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | and a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | or a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | all a ih =>
      simp only [subst, rename]
      apply congrArg all
      have hsubst :
          subst (Term.upSubst (fun n => Term.var (r n))) a =
            subst (fun n => Term.var (SetTheory.up r n)) a := by
        exact subst_ext a _ _ (fun n => by cases n <;> rfl)
      rw [hsubst]
      exact ih (SetTheory.up r)
  | ex a ih =>
      simp only [subst, rename]
      apply congrArg ex
      have hsubst :
          subst (Term.upSubst (fun n => Term.var (r n))) a =
            subst (fun n => Term.var (SetTheory.up r n)) a := by
        exact subst_ext a _ _ (fun n => by cases n <;> rfl)
      rw [hsubst]
      exact ih (SetTheory.up r)

/-- Substituting PA de Bruijn 0 by a variable is just PA-formula renaming by the
corresponding variable-instantiation map. -/
theorem subst_instTerm_var (phi : Formula) (k : Nat) :
    subst (instTerm (Term.var k)) phi =
      rename (SetTheory.inst k) phi := by
  rw [← subst_var_rename phi (SetTheory.inst k)]
  exact subst_ext phi _ _ (fun n => by cases n <;> rfl)

theorem subst_id (phi : Formula) :
    subst (fun n => Term.var n) phi = phi := by
  rw [subst_var_rename, rename_id]

theorem subst_eq_of_sentence {phi : Formula} (hphi : Sentence phi)
    (σ : Nat → Term) : subst σ phi = phi := by
  calc
    subst σ phi = subst (fun n => Term.var n) phi := by
      apply subst_ext_free
      intro n hn
      exact False.elim (hphi n hn)
    _ = phi := subst_id phi

theorem subst_instTerm_rename_up (phi : Formula) (r : Nat → Nat) (t : Term) :
    subst (instTerm (Term.rename r t)) (rename (SetTheory.up r) phi) =
      rename r (subst (instTerm t) phi) := by
  rw [subst_rename, rename_subst]
  exact subst_ext phi _ _ (fun n => by
    cases n with
    | zero => rfl
    | succ n => rfl)

/-- Instantiating the newest variable after shifting a term through one binder
leaves that term unchanged. -/
theorem term_subst_instTerm_rename_succ (t u : Term) :
    Term.subst (instTerm u) (Term.rename Nat.succ t) = t := by
  rw [Term.subst_rename]
  simpa [instTerm, Term.rename_id] using
    (term_subst_var_rename t (fun n : Nat => n))

/-- Instantiating the newest variable after shifting a formula through one
binder leaves that formula unchanged. -/
theorem subst_instTerm_rename_succ (phi : Formula) (t : Term) :
    subst (instTerm t) (rename Nat.succ phi) = phi := by
  rw [subst_rename]
  simpa [instTerm, rename_id] using
    (subst_var_rename phi (fun n : Nat => n))

theorem subst_instTerm_subst_up (phi : Formula) (σ : Nat → Term) (t : Term) :
    subst (instTerm (Term.subst σ t)) (subst (Term.upSubst σ) phi) =
      subst σ (subst (instTerm t) phi) := by
  rw [subst_comp, subst_comp]
  exact subst_ext phi _ _ (fun n => by
    cases n with
    | zero => rfl
    | succ n =>
        simp [instTerm, Term.subst, Term.upSubst,
          term_subst_instTerm_rename_succ])

theorem Sat_instTerm {α : Type u} (M : Model α) (phi : Formula)
    (t : Term) (e : Nat → α) :
    Sat M e (subst (instTerm t) phi) ↔
      Sat M (SetTheory.scons (Term.eval M e t) e) phi := by
  rw [Sat_subst]
  exact Sat_ext M phi (fun n => by cases n <;> rfl)

/-- Natural deduction for PA formulas.  This is deliberately proof-theoretic:
terms are genuine PA terms, quantifier rules use de Bruijn substitution, and
equality elimination is the Leibniz rule for a one-variable formula context. -/
inductive Prov : List Formula → Formula → Prop
  | P_ass    : ∀ G a, a ∈ G → Prov G a
  | P_impI   : ∀ G a b, Prov (a :: G) b → Prov G (imp a b)
  | P_impE   : ∀ G a b, Prov G (imp a b) → Prov G a → Prov G b
  | P_botE   : ∀ G a, Prov G bot → Prov G a
  | P_lem    : ∀ G a, Prov G (or a (imp a bot))
  | P_andI   : ∀ G a b, Prov G a → Prov G b → Prov G (and a b)
  | P_andE1  : ∀ G a b, Prov G (and a b) → Prov G a
  | P_andE2  : ∀ G a b, Prov G (and a b) → Prov G b
  | P_orI1   : ∀ G a b, Prov G a → Prov G (or a b)
  | P_orI2   : ∀ G a b, Prov G b → Prov G (or a b)
  | P_orE    : ∀ G a b c, Prov G (or a b) → Prov (a :: G) c →
               Prov (b :: G) c → Prov G c
  | P_allI   : ∀ G a, Prov (G.map (rename Nat.succ)) a → Prov G (all a)
  | P_allE   : ∀ G a t, Prov G (all a) → Prov G (subst (instTerm t) a)
  | P_exI    : ∀ G a t, Prov G (subst (instTerm t) a) → Prov G (ex a)
  | P_exE    : ∀ G a c, Prov G (ex a) →
               Prov (a :: G.map (rename Nat.succ)) (rename Nat.succ c) →
               Prov G c
  | P_eqRefl : ∀ G t, Prov G (eq t t)
  | P_eqElim : ∀ G s t a,
      Prov G (eq s t) → Prov G (subst (instTerm s) a) →
      Prov G (subst (instTerm t) a)

/-- Context inclusion is preserved by consing the same PA formula. -/
theorem cons_sub {a : Formula} {G G' : List Formula}
    (hsub : ∀ x, x ∈ G → x ∈ G') :
    ∀ x, x ∈ a :: G → x ∈ a :: G' := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons.mpr (Or.inl rfl)
  · exact List.mem_cons.mpr (Or.inr (hsub x hx))

/-- Context inclusion is preserved by mapping a PA formula transformer. -/
theorem mem_map_sub {f : Formula → Formula} {G G' : List Formula}
    (hsub : ∀ x, x ∈ G → x ∈ G') :
    ∀ x, x ∈ G.map f → x ∈ G'.map f := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hsub y hy, rfl⟩

/-- Weakening for the PA calculus: enlarging the context preserves proofs. -/
theorem Prov_weaken {G : List Formula} {a : Formula} (h : Prov G a) :
    ∀ G', (∀ x, x ∈ G → x ∈ G') → Prov G' a := by
  induction h with
  | P_ass G a hin =>
      intro G' hsub
      exact .P_ass _ _ (hsub a hin)
  | P_impI G a b _ ih =>
      intro G' hsub
      exact .P_impI _ _ _ (ih _ (cons_sub hsub))
  | P_impE G a b _ _ ihab iha =>
      intro G' hsub
      exact .P_impE _ a b (ihab _ hsub) (iha _ hsub)
  | P_botE G a _ ih =>
      intro G' hsub
      exact .P_botE _ a (ih _ hsub)
  | P_lem G a =>
      intro G' hsub
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro G' hsub
      exact .P_andI _ _ _ (iha _ hsub) (ihb _ hsub)
  | P_andE1 G a b _ ih =>
      intro G' hsub
      exact .P_andE1 _ a b (ih _ hsub)
  | P_andE2 G a b _ ih =>
      intro G' hsub
      exact .P_andE2 _ a b (ih _ hsub)
  | P_orI1 G a b _ ih =>
      intro G' hsub
      exact .P_orI1 _ _ _ (ih _ hsub)
  | P_orI2 G a b _ ih =>
      intro G' hsub
      exact .P_orI2 _ _ _ (ih _ hsub)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro G' hsub
      exact .P_orE _ a b c (ihor _ hsub)
        (iha _ (cons_sub hsub)) (ihb _ (cons_sub hsub))
  | P_allI G a _ ih =>
      intro G' hsub
      exact .P_allI _ _ (ih _ (mem_map_sub hsub))
  | P_allE G a t _ ih =>
      intro G' hsub
      exact .P_allE _ a t (ih _ hsub)
  | P_exI G a t _ ih =>
      intro G' hsub
      exact .P_exI _ a t (ih _ hsub)
  | P_exE G a c _ _ ihex ihbody =>
      intro G' hsub
      exact .P_exE _ a c (ihex _ hsub)
        (ihbody _ (cons_sub (mem_map_sub hsub)))
  | P_eqRefl G t =>
      intro G' hsub
      exact .P_eqRefl _ t
  | P_eqElim G s t a _ _ iheq iha =>
      intro G' hsub
      exact .P_eqElim _ s t a (iheq _ hsub) (iha _ hsub)

/-- A handy corollary: prepend an additional PA hypothesis. -/
theorem Prov_cons {G : List Formula} {a b : Formula} (h : Prov G b) :
    Prov (a :: G) b :=
  Prov_weaken h _ (fun _ hx => List.mem_cons.mpr (Or.inr hx))

theorem map_rename_up_succ (r : Nat → Nat) (G : List Formula) :
    (G.map (rename Nat.succ)).map (rename (SetTheory.up r)) =
      (G.map (rename r)).map (rename Nat.succ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro phi _
  exact rename_up_succ phi r

theorem map_subst_rename_succ_up (σ : Nat → Term) (G : List Formula) :
    (G.map (rename Nat.succ)).map (subst (Term.upSubst σ)) =
      (G.map (subst σ)).map (rename Nat.succ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro phi _
  exact subst_rename_succ_up phi σ

theorem Prov_rename {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ r, Prov (G.map (rename r)) (rename r phi) := by
  induction h with
  | P_ass G a hin =>
      intro r
      exact .P_ass _ _ (List.mem_map_of_mem (f := rename r) hin)
  | P_impI G a b _ ih =>
      intro r
      exact .P_impI _ _ _ (ih r)
  | P_impE G a b _ _ ihab iha =>
      intro r
      exact .P_impE _ (rename r a) (rename r b) (ihab r) (iha r)
  | P_botE G a _ ih =>
      intro r
      exact .P_botE _ (rename r a) (ih r)
  | P_lem G a =>
      intro r
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro r
      exact .P_andI _ _ _ (iha r) (ihb r)
  | P_andE1 G a b _ ih =>
      intro r
      exact .P_andE1 _ (rename r a) (rename r b) (ih r)
  | P_andE2 G a b _ ih =>
      intro r
      exact .P_andE2 _ (rename r a) (rename r b) (ih r)
  | P_orI1 G a b _ ih =>
      intro r
      exact .P_orI1 _ _ _ (ih r)
  | P_orI2 G a b _ ih =>
      intro r
      exact .P_orI2 _ _ _ (ih r)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro r
      exact .P_orE _ (rename r a) (rename r b) (rename r c)
        (ihor r) (iha r) (ihb r)
  | P_allI G a _ ih =>
      intro r
      apply Prov.P_allI
      rw [← map_rename_up_succ r G]
      exact ih (SetTheory.up r)
  | P_allE G a t _ ih =>
      intro r
      have hAll : Prov (G.map (rename r)) (all (rename (SetTheory.up r) a)) := by
        simpa [rename] using ih r
      have hInst := Prov.P_allE _ (rename (SetTheory.up r) a) (Term.rename r t) hAll
      simpa [subst_instTerm_rename_up] using hInst
  | P_exI G a t _ ih =>
      intro r
      apply Prov.P_exI _ (rename (SetTheory.up r) a) (Term.rename r t)
      simpa [subst_instTerm_rename_up] using ih r
  | P_exE G a c _ _ ihex ihbody =>
      intro r
      have hEx : Prov (G.map (rename r)) (ex (rename (SetTheory.up r) a)) := by
        simpa [rename] using ihex r
      have hctx :
          (a :: G.map (rename Nat.succ)).map (rename (SetTheory.up r)) =
            rename (SetTheory.up r) a :: (G.map (rename r)).map (rename Nat.succ) := by
        simp only [List.map_cons]
        rw [map_rename_up_succ r G]
      have hbody' :
          Prov (rename (SetTheory.up r) a :: (G.map (rename r)).map (rename Nat.succ))
            (rename Nat.succ (rename r c)) := by
        rw [← hctx, ← rename_up_succ c r]
        exact ihbody (SetTheory.up r)
      exact .P_exE _ (rename (SetTheory.up r) a) (rename r c) hEx hbody'
  | P_eqRefl G t =>
      intro r
      exact .P_eqRefl _ (Term.rename r t)
  | P_eqElim G s t a _ _ iheq iha =>
      intro r
      have hEq : Prov (G.map (rename r)) (eq (Term.rename r s) (Term.rename r t)) := by
        simpa [rename] using iheq r
      have hA :
          Prov (G.map (rename r))
            (subst (instTerm (Term.rename r s)) (rename (SetTheory.up r) a)) := by
        simpa [subst_instTerm_rename_up] using iha r
      have hElim := Prov.P_eqElim _ (Term.rename r s) (Term.rename r t)
        (rename (SetTheory.up r) a) hEq hA
      simpa [subst_instTerm_rename_up] using hElim

/-- Simultaneous substitution of PA terms through a derivation. -/
theorem Prov_subst {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ σ, Prov (G.map (subst σ)) (subst σ phi) := by
  induction h with
  | P_ass G a hin =>
      intro σ
      exact .P_ass _ _ (List.mem_map_of_mem (f := subst σ) hin)
  | P_impI G a b _ ih =>
      intro σ
      exact .P_impI _ _ _ (ih σ)
  | P_impE G a b _ _ ihab iha =>
      intro σ
      exact .P_impE _ (subst σ a) (subst σ b) (ihab σ) (iha σ)
  | P_botE G a _ ih =>
      intro σ
      exact .P_botE _ (subst σ a) (ih σ)
  | P_lem G a =>
      intro σ
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro σ
      exact .P_andI _ _ _ (iha σ) (ihb σ)
  | P_andE1 G a b _ ih =>
      intro σ
      exact .P_andE1 _ (subst σ a) (subst σ b) (ih σ)
  | P_andE2 G a b _ ih =>
      intro σ
      exact .P_andE2 _ (subst σ a) (subst σ b) (ih σ)
  | P_orI1 G a b _ ih =>
      intro σ
      exact .P_orI1 _ _ _ (ih σ)
  | P_orI2 G a b _ ih =>
      intro σ
      exact .P_orI2 _ _ _ (ih σ)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro σ
      exact .P_orE _ (subst σ a) (subst σ b) (subst σ c)
        (ihor σ) (iha σ) (ihb σ)
  | P_allI G a _ ih =>
      intro σ
      apply Prov.P_allI
      rw [← map_subst_rename_succ_up σ G]
      exact ih (Term.upSubst σ)
  | P_allE G a t _ ih =>
      intro σ
      have hAll : Prov (G.map (subst σ)) (all (subst (Term.upSubst σ) a)) := by
        simpa [subst] using ih σ
      have hInst := Prov.P_allE _ (subst (Term.upSubst σ) a)
        (Term.subst σ t) hAll
      simpa [subst, subst_instTerm_subst_up] using hInst
  | P_exI G a t _ ih =>
      intro σ
      apply Prov.P_exI _ (subst (Term.upSubst σ) a) (Term.subst σ t)
      simpa [subst_instTerm_subst_up] using ih σ
  | P_exE G a c _ _ ihex ihbody =>
      intro σ
      have hEx : Prov (G.map (subst σ)) (ex (subst (Term.upSubst σ) a)) := by
        simpa [subst] using ihex σ
      have hctx :
          (a :: G.map (rename Nat.succ)).map (subst (Term.upSubst σ)) =
            subst (Term.upSubst σ) a :: (G.map (subst σ)).map (rename Nat.succ) := by
        simp only [List.map_cons]
        rw [map_subst_rename_succ_up σ G]
      have hbody' :
          Prov (subst (Term.upSubst σ) a ::
              (G.map (subst σ)).map (rename Nat.succ))
            (rename Nat.succ (subst σ c)) := by
        rw [← hctx, ← subst_rename_succ_up c σ]
        exact ihbody (Term.upSubst σ)
      exact .P_exE _ (subst (Term.upSubst σ) a) (subst σ c) hEx hbody'
  | P_eqRefl G t =>
      intro σ
      exact .P_eqRefl _ (Term.subst σ t)
  | P_eqElim G s t a _ _ iheq iha =>
      intro σ
      have hEq : Prov (G.map (subst σ))
          (eq (Term.subst σ s) (Term.subst σ t)) := by
        simpa [subst] using iheq σ
      have hA :
          Prov (G.map (subst σ))
            (subst (instTerm (Term.subst σ s))
              (subst (Term.upSubst σ) a)) := by
        simpa [subst_instTerm_subst_up] using iha σ
      have hElim := Prov.P_eqElim _ (Term.subst σ s) (Term.subst σ t)
        (subst (Term.upSubst σ) a) hEq hA
      simpa [subst_instTerm_subst_up] using hElim

theorem Prov_cut {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ De, (∀ x, x ∈ G → Prov De x) → Prov De phi := by
  induction h with
  | P_ass G a hin =>
      intro De hD
      exact hD a hin
  | P_impI G a b _ ih =>
      intro De hD
      apply Prov.P_impI
      apply ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
      · exact Prov_cons (hD x hx)
  | P_impE G a b _ _ ihab iha =>
      intro De hD
      exact .P_impE _ a b (ihab De hD) (iha De hD)
  | P_botE G a _ ih =>
      intro De hD
      exact .P_botE _ a (ih De hD)
  | P_lem G a =>
      intro De hD
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro De hD
      exact .P_andI _ _ _ (iha De hD) (ihb De hD)
  | P_andE1 G a b _ ih =>
      intro De hD
      exact .P_andE1 _ a b (ih De hD)
  | P_andE2 G a b _ ih =>
      intro De hD
      exact .P_andE2 _ a b (ih De hD)
  | P_orI1 G a b _ ih =>
      intro De hD
      exact .P_orI1 _ _ _ (ih De hD)
  | P_orI2 G a b _ ih =>
      intro De hD
      exact .P_orI2 _ _ _ (ih De hD)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro De hD
      apply Prov.P_orE _ a b c (ihor De hD)
      · apply iha
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
        · exact Prov_cons (hD x hx)
      · apply ihb
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
        · exact Prov_cons (hD x hx)
  | P_allI G a _ ih =>
      intro De hD
      apply Prov.P_allI
      apply ih
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨x0, hx0, rfl⟩
      exact Prov_rename (hD x0 hx0) Nat.succ
  | P_allE G a t _ ih =>
      intro De hD
      exact .P_allE _ a t (ih De hD)
  | P_exI G a t _ ih =>
      intro De hD
      exact .P_exI _ a t (ih De hD)
  | P_exE G a c _ _ ihex ihbody =>
      intro De hD
      apply Prov.P_exE _ a c (ihex De hD)
      apply ihbody
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
      · rw [List.mem_map] at hx
        rcases hx with ⟨x0, hx0, rfl⟩
        exact Prov_cons (Prov_rename (hD x0 hx0) Nat.succ)
  | P_eqRefl G t =>
      intro De hD
      exact .P_eqRefl _ t
  | P_eqElim G s t a _ _ iheq iha =>
      intro De hD
      exact .P_eqElim _ s t a (iheq De hD) (iha De hD)

theorem soundness {α : Type u} (M : Model α) {G : List Formula} {a : Formula}
    (h : Prov G a) :
    ∀ e : Nat → α, (∀ x, x ∈ G → Sat M e x) → Sat M e a := by
  induction h with
  | P_ass G a hin =>
      intro e hG
      exact hG a hin
  | P_impI G a b _ ih =>
      intro e hG ha
      exact ih e (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hG x hx)
  | P_impE G a b _ _ ihab iha =>
      intro e hG
      exact ihab e hG (iha e hG)
  | P_botE G a _ ih =>
      intro e hG
      exact False.elim (ih e hG)
  | P_lem G a =>
      intro e hG
      exact Classical.em (Sat M e a)
  | P_andI G a b _ _ iha ihb =>
      intro e hG
      exact ⟨iha e hG, ihb e hG⟩
  | P_andE1 G a b _ ih =>
      intro e hG
      exact (ih e hG).1
  | P_andE2 G a b _ ih =>
      intro e hG
      exact (ih e hG).2
  | P_orI1 G a b _ ih =>
      intro e hG
      exact Or.inl (ih e hG)
  | P_orI2 G a b _ ih =>
      intro e hG
      exact Or.inr (ih e hG)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro e hG
      rcases ihor e hG with ha | hb
      · exact iha e (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hG x hx)
      · exact ihb e (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hG x hx)
  | P_allI G a _ ih =>
      intro e hG d
      exact ih (SetTheory.scons d e) (fun x hx => by
        rw [List.mem_map] at hx
        rcases hx with ⟨g, hg, rfl⟩
        exact (Sat_rename_succ M g e d).mpr (hG g hg))
  | P_allE G a t _ ih =>
      intro e hG
      exact (Sat_instTerm M a t e).mpr (ih e hG (Term.eval M e t))
  | P_exI G a t _ ih =>
      intro e hG
      exact ⟨Term.eval M e t, (Sat_instTerm M a t e).mp (ih e hG)⟩
  | P_exE G a c _ _ ihex ihbody =>
      intro e hG
      rcases ihex e hG with ⟨d, hd⟩
      have hc_shift : Sat M (SetTheory.scons d e) (rename Nat.succ c) :=
        ihbody (SetTheory.scons d e) (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hd
          · rw [List.mem_map] at hx
            rcases hx with ⟨g, hg, rfl⟩
            exact (Sat_rename_succ M g e d).mpr (hG g hg))
      exact (Sat_rename_succ M c e d).mp hc_shift
  | P_eqRefl G t =>
      intro e hG
      rfl
  | P_eqElim G s t a _ _ iheq iha =>
      intro e hG
      have heq : Term.eval M e s = Term.eval M e t := iheq e hG
      have ha : Sat M (SetTheory.scons (Term.eval M e s) e) a :=
        (Sat_instTerm M a s e).mp (iha e hG)
      have henv :
          ∀ n, SetTheory.scons (Term.eval M e s) e n =
            SetTheory.scons (Term.eval M e t) e n := by
        intro n
        cases n with
        | zero => exact heq
        | succ n => rfl
      exact (Sat_instTerm M a t e).mpr ((Sat_ext M a henv).mp ha)

def BProv (B : Formula → Prop) (G : List Formula) (phi : Formula) : Prop :=
  ∃ L, (∀ x ∈ L, B x) ∧ Prov (L ++ G) phi

/-- Enlarging the finite PA context preserves relative provability. -/
theorem BProv_mono (B : Formula → Prop) (G G' : List Formula) (phi : Formula)
    (hsub : ∀ x, x ∈ G → x ∈ G') (h : BProv B G phi) :
    BProv B G' phi := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  exact Prov_weaken hp _ (fun x hx => by
    rw [List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hsub x hx))

/-- A closed relative PA proof may be used under any finite PA context. -/
theorem BProv_weaken_nil {B : Formula → Prop} {G : List Formula}
    {phi : Formula} (h : BProv B [] phi) :
    BProv B G phi :=
  BProv_mono B [] G phi (fun _ hx => by cases hx) h

/-- A PA theory axiom is relatively provable from that theory. -/
theorem BProv_ax {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (hphi : B phi) : BProv B G phi := by
  refine ⟨[phi], ?_, ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact hphi
  · exact Prov.P_ass _ _ (by simp)

/-- A bare PA proof is also a proof relative to any PA theory. -/
theorem BProv_of_Prov {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (h : Prov G phi) : BProv B G phi := by
  refine ⟨[], ?_, ?_⟩
  · intro x hx
    cases hx
  · simpa using h

/-- A finite-context assumption is relatively provable. -/
theorem BProv_ass {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (hphi : phi ∈ G) : BProv B G phi :=
  BProv_of_Prov (Prov.P_ass G phi hphi)

/-- Rename every finite-context assumption in a relative PA proof.  The
background theory is preserved when its axioms are sentences, since renaming a
sentence is syntactically equal to itself. -/
theorem BProv_rename_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {phi : Formula}
    (h : BProv B G phi) (r : Nat → Nat) :
    BProv B (G.map (rename r)) (rename r phi) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename r) = L := by
    calc
      L.map (rename r) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hL x hx)) r
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  have hpRen : Prov ((L ++ G).map (rename r)) (rename r phi) :=
    Prov_rename hp r
  apply Prov_weaken hpRen
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Substitute PA terms through every finite-context assumption of a relative
PA proof.  Sentence axioms of the background theory are unchanged by the
substitution. -/
theorem BProv_subst_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {phi : Formula}
    (h : BProv B G phi) (σ : Nat → Term) :
    BProv B (G.map (subst σ)) (subst σ phi) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (subst σ) = L := by
    calc
      L.map (subst σ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact subst_eq_of_sentence (hB x (hL x hx)) σ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  have hpSub : Prov ((L ++ G).map (subst σ)) (subst σ phi) :=
    Prov_subst hp σ
  apply Prov_weaken hpSub
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Relative PA provability is closed under modus ponens. -/
theorem BProv_mp (B : Formula → Prop) (G : List Formula) (a b : Formula)
    (himp : BProv B G (imp a b)) (ha : BProv B G a) : BProv B G b := by
  rcases himp with ⟨L₁, hL₁, hpimp⟩
  rcases ha with ⟨L₂, hL₂, hpa⟩
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hL₁ x hx
    · exact hL₂ x hx
  · apply Prov.P_impE _ a b
    · exact Prov_weaken hpimp _ (fun x hx => by
        rw [List.mem_append] at hx ⊢
        grind)
    · exact Prov_weaken hpa _ (fun x hx => by
        rw [List.mem_append] at hx ⊢
        grind)

/-- A finite list of PA relative proofs can be put over one shared finite list
of theory axioms. -/
theorem BProv_bound_list (B : Formula → Prop) (D : List Formula) :
    ∀ L : List Formula, (∀ x, x ∈ L → BProv B D x) →
      ∃ Lb, (∀ x, x ∈ Lb → B x) ∧
        ∀ x, x ∈ L → Prov (Lb ++ D) x := by
  intro L
  induction L with
  | nil =>
      intro _hL
      refine ⟨[], ?_, ?_⟩
      · intro x hx
        cases hx
      · intro x hx
        cases hx
  | cons a L ih =>
      intro hL
      rcases hL a (by simp) with ⟨La, hLa, hpa⟩
      rcases ih (fun x hx => hL x (by simp [hx])) with ⟨Lb, hLb, hpL⟩
      refine ⟨La ++ Lb, ?_, ?_⟩
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hLa x hx
        · exact hLb x hx
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · apply Prov_weaken hpa
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inl hy))
          · exact Or.inr hy
        · apply Prov_weaken (hpL x hx)
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inr hy))
          · exact Or.inr hy

/-- Transport a PA relative proof to another PA theory/context once every used
source axiom and every finite-context assumption has been proved in the target. -/
theorem BProv_lift {B C : Formula → Prop} {G D : List Formula} {phi : Formula}
    (h : BProv B G phi)
    (hB : ∀ b, B b → BProv C D b)
    (hG : ∀ g, g ∈ G → BProv C D g) : BProv C D phi := by
  rcases h with ⟨Lb, hLb, hp⟩
  have hctx : ∀ x, x ∈ Lb ++ G → BProv C D x := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hB x (hLb x hx)
    · exact hG x hx
  rcases BProv_bound_list C D (Lb ++ G) hctx with ⟨Lc, hLc, hpctx⟩
  refine ⟨Lc, hLc, ?_⟩
  exact Prov_cut hp (Lc ++ D) hpctx

/-- PA relative provability is closed under cutting in proofs of the finite
context. -/
theorem BProv_cut {B : Formula → Prop} {G D : List Formula} {phi : Formula}
    (h : BProv B G phi)
    (hG : ∀ g, g ∈ G → BProv B D g) : BProv B D phi :=
  BProv_lift h (fun _ hb => BProv_ax (G := D) hb) hG

/-- Enlarging the PA background theory preserves relative provability. -/
theorem BProv_theory_mono {B C : Formula → Prop} {G : List Formula} {phi : Formula}
    (hBC : ∀ b, B b → C b) (h : BProv B G phi) : BProv C G phi :=
  BProv_lift h
    (fun b hb => BProv_ax (G := G) (hBC b hb))
    (fun g hg => BProv_of_Prov (B := C) (Prov.P_ass G g hg))

/-- PA relative provability is closed under PA equality elimination.  The
formula `a` is the one-variable PA context, instantiated first by term `s` and
then by term `t`. -/
theorem BProv_eqElim {B : Formula → Prop} {G : List Formula} {s t : Term}
    {a : Formula}
    (heq : BProv B G (eq s t))
    (ha : BProv B G (subst (instTerm s) a)) :
    BProv B G (subst (instTerm t) a) := by
  have hbare : BProv B [eq s t, subst (instTerm s) a]
      (subst (instTerm t) a) := by
    apply BProv_of_Prov
    apply Prov.P_eqElim [eq s t, subst (instTerm s) a] s t a
    · exact Prov.P_ass _ _ (by simp)
    · exact Prov.P_ass _ _ (by simp)
  exact BProv_lift hbare
    (fun _ hb => BProv_ax (G := G) hb)
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil] at hg
      rcases hg with rfl | hg
      · exact heq
      · rcases hg with rfl | hnil
        · exact ha
        · cases hnil)

/-- PA relative provability proves reflexivity of equality for every term. -/
theorem BProv_eqRefl {B : Formula → Prop} {G : List Formula} (t : Term) :
    BProv B G (eq t t) :=
  BProv_of_Prov (Prov.P_eqRefl G t)

/-- PA relative provability is closed under symmetry of term equality. -/
theorem BProv_eqSym {B : Formula → Prop} {G : List Formula} {s t : Term}
    (heq : BProv B G (eq s t)) :
    BProv B G (eq t s) := by
  have hrefl : BProv B G (eq s s) := BProv_eqRefl s
  have ha : BProv B G
      (subst (instTerm s) (eq (Term.var 0) (Term.rename Nat.succ s))) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hrefl
  have h := BProv_eqElim (B := B) (G := G) (s := s) (t := t)
    (a := eq (Term.var 0) (Term.rename Nat.succ s)) heq ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA relative provability is closed under transitivity of term equality. -/
theorem BProv_eqTrans {B : Formula → Prop} {G : List Formula}
    {s t u : Term}
    (hst : BProv B G (eq s t)) (htu : BProv B G (eq t u)) :
    BProv B G (eq s u) := by
  have ha : BProv B G
      (subst (instTerm t) (eq (Term.rename Nat.succ s) (Term.var 0))) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hst
  have h := BProv_eqElim (B := B) (G := G) (s := t) (t := u)
    (a := eq (Term.rename Nat.succ s) (Term.var 0)) htu ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA equality is congruent through an arbitrary one-hole term context.  The
hole is de Bruijn variable `0`; other ambient variables are represented by the
usual shifted indices of the context term. -/
theorem BProv_eq_congr_term {B : Formula → Prop} {G : List Formula}
    {s t : Term} (c : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq
      (Term.subst (instTerm s) c)
      (Term.subst (instTerm t) c)) := by
  have hrefl : BProv B G
      (eq (Term.subst (instTerm s) c)
        (Term.subst (instTerm s) c)) :=
    BProv_eqRefl (Term.subst (instTerm s) c)
  have ha : BProv B G
      (subst (instTerm s)
        (eq (Term.rename Nat.succ (Term.subst (instTerm s) c)) c)) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hrefl
  have h := BProv_eqElim (B := B) (G := G) (s := s) (t := t)
    (a := eq
      (Term.rename Nat.succ (Term.subst (instTerm s) c)) c)
    heq ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA equality is congruent under successor. -/
theorem BProv_eq_congr_succ {B : Formula → Prop} {G : List Formula}
    {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.succ s) (Term.succ t)) := by
  simpa [Term.subst, instTerm] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t) (Term.succ (Term.var 0)) heq

/-- PA equality is congruent in the left argument of addition. -/
theorem BProv_eq_congr_add_left {B : Formula → Prop} {G : List Formula}
    {s t : Term} (u : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.add s u) (Term.add t u)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.add (Term.var 0) (Term.rename Nat.succ u)) heq

/-- PA equality is congruent in the right argument of addition. -/
theorem BProv_eq_congr_add_right {B : Formula → Prop} {G : List Formula}
    (u : Term) {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.add u s) (Term.add u t)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.add (Term.rename Nat.succ u) (Term.var 0)) heq

/-- PA equality is congruent in both arguments of addition. -/
theorem BProv_eq_congr_add {B : Formula → Prop} {G : List Formula}
    {s t u v : Term}
    (hst : BProv B G (eq s t)) (huv : BProv B G (eq u v)) :
    BProv B G (eq (Term.add s u) (Term.add t v)) :=
  BProv_eqTrans (BProv_eq_congr_add_left u hst)
    (BProv_eq_congr_add_right t huv)

/-- PA equality is congruent in the left argument of multiplication. -/
theorem BProv_eq_congr_mul_left {B : Formula → Prop} {G : List Formula}
    {s t : Term} (u : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.mul s u) (Term.mul t u)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.mul (Term.var 0) (Term.rename Nat.succ u)) heq

/-- PA equality is congruent in the right argument of multiplication. -/
theorem BProv_eq_congr_mul_right {B : Formula → Prop} {G : List Formula}
    (u : Term) {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.mul u s) (Term.mul u t)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.mul (Term.rename Nat.succ u) (Term.var 0)) heq

/-- PA equality is congruent in both arguments of multiplication. -/
theorem BProv_eq_congr_mul {B : Formula → Prop} {G : List Formula}
    {s t u v : Term}
    (hst : BProv B G (eq s t)) (huv : BProv B G (eq u v)) :
    BProv B G (eq (Term.mul s u) (Term.mul t v)) :=
  BProv_eqTrans (BProv_eq_congr_mul_left u hst)
    (BProv_eq_congr_mul_right t huv)

/-- A relative PA proof may ignore one extra finite-context assumption. -/
theorem BProv_context_cons {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G b) : BProv B (a :: G) b :=
  BProv_mono B G (a :: G) b
    (fun _ hx => List.mem_cons.mpr (Or.inr hx)) h

/-- Relative PA provability is closed under implication introduction. -/
theorem BProv_impI {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B (a :: G) b) :
    BProv B G (imp a b) := by
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

/-- Implication introduction with a fixed prefix of PA assumptions. -/
theorem BProv_impI_after_prefix {B : Formula → Prop}
    {Γ Δ : List Formula} {a b : Formula}
    (h : BProv B (Γ ++ a :: Δ) b) :
    BProv B (Γ ++ Δ) (imp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  grind

/-- Relative PA provability is closed under conjunction introduction. -/
theorem BProv_andI {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (ha : BProv B G a) (hb : BProv B G b) :
    BProv B G (and a b) := by
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

/-- Relative PA provability is closed under bottom elimination. -/
theorem BProv_botE {B : Formula → Prop} {G : List Formula} {a : Formula}
    (hbot : BProv B G bot) : BProv B G a := by
  rcases hbot with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_botE _ a hp⟩

/-- Relative PA provability is closed under the first conjunction projection. -/
theorem BProv_andE1 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G (and a b)) : BProv B G a := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE1 _ a b hp⟩

/-- Relative PA provability is closed under the second conjunction projection. -/
theorem BProv_andE2 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G (and a b)) : BProv B G b := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE2 _ a b hp⟩

/-- Relative PA provability is closed under left disjunction introduction. -/
theorem BProv_orI1 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (ha : BProv B G a) : BProv B G (or a b) := by
  rcases ha with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI1 _ a b hp⟩

/-- Relative PA provability is closed under right disjunction introduction. -/
theorem BProv_orI2 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (hb : BProv B G b) : BProv B G (or a b) := by
  rcases hb with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI2 _ a b hp⟩

/-- Relative PA provability is closed under disjunction elimination. -/
theorem BProv_orE {B : Formula → Prop} {G : List Formula}
    {a b c : Formula}
    (hor : BProv B G (or a b))
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

/-- Relative PA provability is closed under universal elimination. -/
theorem BProv_allE {B : Formula → Prop} {G : List Formula}
    {a : Formula} {t : Term} (h : BProv B G (all a)) :
    BProv B G (subst (instTerm t) a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_allE _ _ t hp⟩

/-- Relative PA provability is closed under existential introduction. -/
theorem BProv_exI {B : Formula → Prop} {G : List Formula}
    {a : Formula} {t : Term}
    (h : BProv B G (subst (instTerm t) a)) :
    BProv B G (ex a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_exI _ _ t hp⟩

/-- Universal introduction for relative PA proofs whose theory axioms are
sentences. -/
theorem BProv_allI_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a : Formula}
    (h : BProv B (G.map (rename Nat.succ)) a) :
    BProv B G (all a) := by
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

/-- Existential elimination for relative PA proofs whose theory axioms are
sentences. -/
theorem BProv_exE_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a c : Formula}
    (hex : BProv B G (ex a))
    (hbody : BProv B (a :: G.map (rename Nat.succ)) (rename Nat.succ c)) :
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

/-- Instantiate every quantifier in a finite universal closure by a PA-variable
renaming.

The side condition says that `k` really closes all free variables of `phi`.
This is the syntactic counterpart of the semantic `seal_valid` lemma and is
the workhorse for using sealed PA axiom-schema instances without hiding the
de Bruijn bookkeeping. -/
theorem BProv_closeN_allE_rename {B : Formula → Prop} {G : List Formula} :
    ∀ (k : Nat) (phi : Formula) (r : Nat → Nat),
      (∀ n, Free n phi → n < k) →
      BProv B G (closeN k phi) →
      BProv B G (rename r phi) := by
  intro k
  induction k with
  | zero =>
      intro phi r hfree h
      have hsent : Sentence phi := by
        intro n hn
        have hlt := hfree n hn
        omega
      simpa [closeN, rename_eq_of_sentence hsent r] using h
  | succ k ih =>
      intro phi r hfree h
      let tail : Nat → Nat := fun n => r (n+1)
      have hclosed : BProv B G (rename tail (all phi)) := by
        apply ih (all phi) tail
        · intro n hn
          have hlt := hfree (n+1) hn
          omega
        · simpa [closeN] using h
      have hAll : BProv B G (all (rename (SetTheory.up tail) phi)) := by
        simpa [rename, tail] using hclosed
      have hInst : BProv B G
          (subst (instTerm (Term.var (r 0)))
            (rename (SetTheory.up tail) phi)) :=
        BProv_allE (B := B) (G := G)
          (a := rename (SetTheory.up tail) phi)
          (t := Term.var (r 0)) hAll
      have htarget :
          subst (instTerm (Term.var (r 0)))
              (rename (SetTheory.up tail) phi) =
            rename r phi := by
        calc
          subst (instTerm (Term.var (r 0)))
              (rename (SetTheory.up tail) phi) =
              rename (SetTheory.inst (r 0))
                (rename (SetTheory.up tail) phi) := by
                exact subst_instTerm_var
                  (rename (SetTheory.up tail) phi) (r 0)
          _ = rename
              (fun n => SetTheory.inst (r 0) (SetTheory.up tail n)) phi := by
                exact rename_comp phi (SetTheory.inst (r 0))
                  (SetTheory.up tail)
          _ = rename r phi := by
                apply rename_ext
                intro n
                cases n with
                | zero => rfl
                | succ n => rfl
      simpa [htarget] using hInst

/-- Use a sealed PA formula at any variable-renamed instance of its body. -/
theorem BProv_sealPA_allE_rename {B : Formula → Prop} {G : List Formula}
    (phi : Formula) (r : Nat → Nat)
    (h : BProv B G (sealPA phi)) :
    BProv B G (rename r phi) :=
  BProv_closeN_allE_rename (bound phi) phi r
    (fun n hn => free_lt_bound phi n hn) h

theorem soundness_BProv {α : Type u} (M : Model α) {B : Formula → Prop}
    {G : List Formula} {phi : Formula} (h : BProv B G phi) :
    ∀ e : Nat → α, (∀ b, B b → Sat M e b) →
      (∀ g, g ∈ G → Sat M e g) → Sat M e phi := by
  intro e hB hG
  rcases h with ⟨L, hL, hprov⟩
  exact soundness M hprov e (fun x hx => by
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hB x (hL x hx)
    · exact hG x hx)

/-! ### Arithmetic relation macros for the reverse interpretation -/

def leAt (a b : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1)))

/-- Bounded order against a closed standard numeral.  This is intentionally only
the formula macro; PA proofs that relate it to `leAt` are kept as separate
lemmas. -/
def leConstAt (a n : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.numeral n))

def ltAt (a b : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0))) (Term.var (b+1)))

def dvdAt (a b : Nat) : Formula :=
  ex (eq (Term.mul (Term.var (a+1)) (Term.var 0)) (Term.var (b+1)))

def eqConstAt (a n : Nat) : Formula :=
  eq (Term.var a) (Term.numeral n)

def zeroAt (a : Nat) : Formula := eqConstAt a 0

def oneAt (a : Nat) : Formula := eqConstAt a 1

def twoAt (a : Nat) : Formula := eqConstAt a 2

def nonzeroAt (a : Nat) : Formula :=
  ex (eq (Term.succ (Term.var 0)) (Term.var (a+1)))

/-- Slot `a` is the successor of some predecessor. -/
def succPredAt (a : Nat) : Formula :=
  ex (eq (Term.var (a+1)) (Term.succ (Term.var 0)))

/-- The elementary PA case split for a number: zero or a successor. -/
def zeroOrSuccPredAt (a : Nat) : Formula :=
  or (zeroAt a) (succPredAt a)

def boolAt (a : Nat) : Formula :=
  or (zeroAt a) (oneAt a)

def doubleEqAt (value half : Nat) : Formula :=
  eq (Term.var value) (Term.add (Term.var half) (Term.var half))

def oddDoubleEqAt (value half : Nat) : Formula :=
  eq (Term.var value) (Term.succ (Term.add (Term.var half) (Term.var half)))

def div2StepAt (value half bit : Nat) : Formula :=
  and (boolAt bit)
    (eq (Term.var value)
      (Term.add (Term.add (Term.var half) (Term.var half)) (Term.var bit)))

def remAt (rem value modulus : Nat) : Formula :=
  ex (and
    (ltAt (rem+1) (modulus+1))
    (eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.var (rem+1)))))

def betaModTerm (step idx : Nat) : Term :=
  Term.succ (Term.mul (Term.succ (Term.var idx)) (Term.var step))

def betaAt (out code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
    (remAt (out+1) (code+1) 0))

def betaAtConstIdx (out code step idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0))

def betaAtSuccIdx (out code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
    (betaAt (out+1) (code+1) (step+1) 0))

/-- The modulus used by Gödel's beta function at sequence index `idx`. -/
def BetaModulus (step idx : Nat) : Nat :=
  1 + (idx + 1) * step

/-- The semantic relation expressed by `betaAt`: `value` is the `idx`-th
entry of a beta-coded sequence with ambient parameters `code` and `step`. -/
def BetaEntry (code step idx value : Nat) : Prop :=
  ∃ q, code = q * BetaModulus step idx + value ∧
    value < BetaModulus step idx

/-- A tiny local factorial, kept here to avoid adding a dependency just for
the Gödel beta coding lemma. -/
def betaFact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * betaFact n

/-- Product of the first `n` Gödel-beta moduli for a fixed step. -/
def BetaModuliProduct (step : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => BetaModuliProduct step n * BetaModulus step n

/-- Semantic mirror of a beta-coded binary-halving step. -/
def BetaDiv2Step (code step idx cur next bit : Nat) : Prop :=
  BetaEntry code step idx cur ∧
    BetaEntry code step (idx + 1) next ∧
      (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit

/-- Semantic mirror of a beta-coded halving trace through `last`. -/
def BetaDiv2StepsThrough (code step last : Nat) : Prop :=
  ∀ k, k ≤ last → ∃ cur next bit, BetaDiv2Step code step k cur next bit

/-- Semantic mirror of the bit read from a beta-coded halving trace. -/
def BetaDiv2Bit (code step idx bit : Nat) : Prop :=
  ∃ cur next, BetaDiv2Step code step idx cur next bit

/-- Semantic trace predicate used by the PA interpretation of HF membership. -/
def HFMemTrace (elem set code step : Nat) : Prop :=
  BetaEntry code step 0 set ∧
    BetaDiv2StepsThrough code step elem ∧
      BetaDiv2Bit code step elem 1

/-- A single adjacent beta-coded sequence step is a binary-halving step:
the current value is `2 * next + bit`, with `bit ∈ {0,1}`. -/
def betaDiv2StepWitnessAt (code step idx : Nat) : Formula :=
    (ex (ex (ex
      (and
        (betaAt 2 (code+3) (step+3) (idx+3))
        (and
          (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
          (div2StepAt 2 1 0))))))

/-- Every adjacent pair below `limit` in a beta-coded sequence is one
binary-halving step. -/
def betaDiv2StepAt (code step limit : Nat) : Formula :=
  all (imp (ltAt 0 (limit+1))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Every adjacent pair through `last` in a beta-coded sequence is one
binary-halving step. -/
def betaDiv2StepsThroughAt (code step last : Nat) : Formula :=
  all (imp (leAt 0 (last+1))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Closed-bound variant of `betaDiv2StepsThroughAt`: every adjacent pair up to
the standard numeral `last` in a beta-coded sequence is one binary-halving step.
This is only a formula macro; the PA constructors connecting it to the variable
bound form are separate lemmas. -/
def betaDiv2StepsThroughConstAt (code step last : Nat) : Formula :=
  all (imp (leConstAt 0 last)
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Read a specified bit from a beta-coded halving trace at `idx`. -/
def betaDiv2BitAt (bit code step idx : Nat) : Formula :=
  ex (ex
    (and
      (betaAt 1 (code+2) (step+2) (idx+2))
      (and
        (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
        (div2StepAt 1 0 (bit+2)))))

/-- PA formula for Ackermann-coded HF membership, mediated by a beta-coded
binary-halving trace. -/
def hfMemAt (elem set : Nat) : Formula :=
  ex (ex
    (and
      (betaAtConstIdx (set+2) 1 0 0)
      (and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex
          (and
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem+3)))))))

theorem rename_hfMemAt (r : Nat → Nat) (elem set : Nat) :
    rename r (hfMemAt elem set) = hfMemAt (r elem) (r set) := by
  simp [hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAtConstIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt,
    eqConstAt, betaModTerm, rename, Term.rename, SetTheory.up]

theorem leAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (leAt a b) ↔ e a ≤ e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    change e a + d = e b at hd
    omega
  · intro h
    refine ⟨e b - e a, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a + (e b - e a) = e b
    omega

theorem leConstAt_nat (e : Nat → Nat) (a n : Nat) :
    Sat natModel e (leConstAt a n) ↔ e a ≤ n := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat] at hd
    rw [Term.eval_numeral_natModel] at hd
    simp only [Term.eval, natModel, scons] at hd
    change e a + d = n at hd
    omega
  · intro h
    refine ⟨n - e a, ?_⟩
    simp only [Sat]
    rw [Term.eval_numeral_natModel]
    simp only [Term.eval, natModel, scons]
    change e a + (n - e a) = n
    omega

theorem ltAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (ltAt a b) ↔ e a < e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    change e a + (d + 1) = e b at hd
    omega
  · intro h
    refine ⟨e b - e a - 1, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a + ((e b - e a - 1) + 1) = e b
    omega

theorem dvdAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (dvdAt a b) ↔ e a ∣ e b := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    simp only [Sat, Term.eval, natModel, scons] at hq
    change e a * q = e b at hq
    exact ⟨q, hq.symm⟩
  · intro h
    rcases h with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a * q = e b
    exact hq.symm

theorem eqConstAt_nat (e : Nat → Nat) (a n : Nat) :
    Sat natModel e (eqConstAt a n) ↔ e a = n := by
  simp only [eqConstAt, Sat, Term.eval, Term.eval_numeral_natModel]

theorem zeroAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (zeroAt a) ↔ e a = 0 :=
  eqConstAt_nat e a 0

theorem oneAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (oneAt a) ↔ e a = 1 :=
  eqConstAt_nat e a 1

theorem twoAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (twoAt a) ↔ e a = 2 :=
  eqConstAt_nat e a 2

theorem nonzeroAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (nonzeroAt a) ↔ e a ≠ 0 := by
  constructor
  · intro h hzero
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    omega
  · intro h
    refine ⟨e a - 1, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    omega

theorem succPredAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (succPredAt a) ↔ ∃ p, e a = p + 1 := by
  constructor
  · intro h
    rcases h with ⟨p, hp⟩
    simp only [Sat, Term.eval, natModel, scons] at hp
    exact ⟨p, by omega⟩
  · intro h
    rcases h with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    omega

theorem zeroOrSuccPredAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (zeroOrSuccPredAt a) ↔
      e a = 0 ∨ ∃ p, e a = p + 1 := by
  simp only [zeroOrSuccPredAt, Sat]
  exact or_congr (zeroAt_nat e a) (succPredAt_nat e a)

theorem boolAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (boolAt a) ↔ e a = 0 ∨ e a = 1 := by
  simp only [boolAt, Sat]
  exact or_congr (zeroAt_nat e a) (oneAt_nat e a)

theorem doubleEqAt_nat (e : Nat → Nat) (value half : Nat) :
    Sat natModel e (doubleEqAt value half) ↔ e value = e half + e half := by
  simp only [doubleEqAt, Sat, Term.eval, natModel]
  rfl

theorem oddDoubleEqAt_nat (e : Nat → Nat) (value half : Nat) :
    Sat natModel e (oddDoubleEqAt value half) ↔ e value = e half + e half + 1 := by
  simp only [oddDoubleEqAt, Sat, Term.eval, natModel]
  change e value = Nat.succ (e half + e half) ↔ e value = e half + e half + 1
  omega

theorem div2StepAt_nat (e : Nat → Nat) (value half bit : Nat) :
    Sat natModel e (div2StepAt value half bit) ↔
      (e bit = 0 ∨ e bit = 1) ∧ e value = e half + e half + e bit := by
  simp only [div2StepAt, Sat]
  constructor
  · intro h
    have hval : e value = e half + e half + e bit := by
      have hraw := h.2
      simp only [Term.eval, natModel] at hraw
      change e value = e half + e half + e bit at hraw
      exact hraw
    exact ⟨(boolAt_nat e bit).mp h.1, hval⟩
  · intro h
    exact ⟨(boolAt_nat e bit).mpr h.1, by
      simp only [Term.eval, natModel]
      change e value = e half + e half + e bit
      omega⟩

theorem betaModTerm_nat (e : Nat → Nat) (step idx : Nat) :
    Term.eval natModel e (betaModTerm step idx) = 1 + (e idx + 1) * e step := by
  simp only [betaModTerm, Term.eval, natModel]
  change Nat.succ ((e idx + 1) * e step) = 1 + (e idx + 1) * e step
  omega

theorem remAt_nat (e : Nat → Nat) (rem value modulus : Nat) :
    Sat natModel e (remAt rem value modulus) ↔
      ∃ q, e value = q * e modulus + e rem ∧ e rem < e modulus := by
  constructor
  · intro h
    rcases h with ⟨q, hlt, hval⟩
    refine ⟨q, ?_, ?_⟩
    · simp only [Sat, Term.eval, natModel, scons] at hval
      change e value = q * e modulus + e rem at hval
      exact hval
    · exact (ltAt_nat (scons q e) (rem+1) (modulus+1)).mp hlt
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · exact (ltAt_nat (scons q e) (rem+1) (modulus+1)).mpr hlt
    · simp only [Sat, Term.eval, natModel, scons]
      change e value = q * e modulus + e rem
      exact hval

theorem betaAt_nat (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAt out code step idx) ↔
      ∃ q,
        e code = q * (1 + (e idx + 1) * e step) + e out ∧
          e out < 1 + (e idx + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨m, hmod, hrem⟩
    have hm : m = 1 + (e idx + 1) * e step := by
      simp only [Sat, Term.eval_rename, betaModTerm_nat, scons] at hmod
      exact hmod
    rcases (remAt_nat (scons m e) (out+1) (code+1) 0).mp hrem with
      ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [scons, hm] using hval
    · simpa [scons, hm] using hlt
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    let m := 1 + (e idx + 1) * e step
    refine ⟨m, ?_, ?_⟩
    · simp only [Sat, Term.eval_rename, betaModTerm_nat, scons]
      rfl
    · apply (remAt_nat (scons m e) (out+1) (code+1) 0).mpr
      refine ⟨q, ?_, ?_⟩
      · simpa [scons, m] using hval
      · simpa [scons, m] using hlt

theorem betaAtConstIdx_nat (e : Nat → Nat) (out code step idxValue : Nat) :
    Sat natModel e (betaAtConstIdx out code step idxValue) ↔
      ∃ q,
        e code = q * (1 + (idxValue + 1) * e step) + e out ∧
          e out < 1 + (idxValue + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨i, hi, hbeta⟩
    have hi' : i = idxValue := (eqConstAt_nat (scons i e) 0 idxValue).mp hi
    rcases (betaAt_nat (scons i e) (out+1) (code+1) (step+1) 0).mp hbeta with
      ⟨q, hval, hlt⟩
    subst hi'
    exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨idxValue, ?_, ?_⟩
    · exact (eqConstAt_nat (scons idxValue e) 0 idxValue).mpr rfl
    · apply (betaAt_nat (scons idxValue e) (out+1) (code+1) (step+1) 0).mpr
      exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩

theorem betaAtSuccIdx_nat (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAtSuccIdx out code step idx) ↔
      ∃ q,
        e code = q * (1 + (e idx + 1 + 1) * e step) + e out ∧
          e out < 1 + (e idx + 1 + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨i, hi, hbeta⟩
    have hi' : i = e idx + 1 := by
      simp only [Sat, Term.eval, natModel, scons] at hi
      exact hi
    rcases (betaAt_nat (scons i e) (out+1) (code+1) (step+1) 0).mp hbeta with
      ⟨q, hval, hlt⟩
    subst hi'
    exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨e idx + 1, ?_, ?_⟩
    · simp only [Sat, Term.eval, natModel, scons]
    · apply (betaAt_nat (scons (e idx + 1) e) (out+1) (code+1) (step+1) 0).mpr
      exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩

theorem betaAt_nat_entry (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAt out code step idx) ↔
      BetaEntry (e code) (e step) (e idx) (e out) := by
  exact betaAt_nat e out code step idx

theorem betaAtConstIdx_nat_entry
    (e : Nat → Nat) (out code step idxValue : Nat) :
    Sat natModel e (betaAtConstIdx out code step idxValue) ↔
      BetaEntry (e code) (e step) idxValue (e out) := by
  exact betaAtConstIdx_nat e out code step idxValue

theorem betaAtSuccIdx_nat_entry
    (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAtSuccIdx out code step idx) ↔
      BetaEntry (e code) (e step) (e idx + 1) (e out) := by
  exact betaAtSuccIdx_nat e out code step idx

theorem betaDiv2StepWitnessAt_nat (e : Nat → Nat) (code step idx : Nat) :
    Sat natModel e (betaDiv2StepWitnessAt code step idx) ↔
      ∃ cur next bit,
        BetaEntry (e code) (e step) (e idx) cur ∧
        BetaEntry (e code) (e step) (e idx + 1) next ∧
        (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hstep⟩
    let E := scons bit (scons next (scons cur e))
    have hcur' :
        BetaEntry (e code) (e step) (e idx) cur := by
      have hc := (betaAt_nat_entry E 2 (code+3) (step+3) (idx+3)).mp hcur
      simpa [E, scons] using hc
    have hnext' :
        BetaEntry (e code) (e step) (e idx + 1) next := by
      have hn := (betaAtSuccIdx_nat_entry E 1 (code+3) (step+3) (idx+3)).mp hnext
      simpa [E, scons, Nat.add_assoc] using hn
    have hstep' :
        (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
      have hs := (div2StepAt_nat E 2 1 0).mp hstep
      simpa [E, scons] using hs
    exact ⟨cur, next, bit, hcur', hnext', hstep'⟩
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hstep⟩
    refine ⟨cur, next, bit, ?_, ?_, ?_⟩
    · let E := scons bit (scons next (scons cur e))
      apply (betaAt_nat_entry E 2 (code+3) (step+3) (idx+3)).mpr
      simpa [E, scons] using hcur
    · let E := scons bit (scons next (scons cur e))
      apply (betaAtSuccIdx_nat_entry E 1 (code+3) (step+3) (idx+3)).mpr
      simpa [E, scons, Nat.add_assoc] using hnext
    · let E := scons bit (scons next (scons cur e))
      apply (div2StepAt_nat E 2 1 0).mpr
      simpa [E, scons] using hstep

theorem betaDiv2StepAt_nat (e : Nat → Nat) (code step limit : Nat) :
    Sat natModel e (betaDiv2StepAt code step limit) ↔
      ∀ k, k < e limit →
        ∃ cur next bit,
          BetaEntry (e code) (e step) k cur ∧
          BetaEntry (e code) (e step) (k+1) next ∧
          (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (ltAt 0 (limit+1)) := by
      exact (ltAt_nat (scons k e) 0 (limit+1)).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    simpa [scons] using hw
  · intro h k hkSat
    have hk : k < e limit := by
      have hlt := (ltAt_nat (scons k e) 0 (limit+1)).mp hkSat
      simpa [scons] using hlt
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    simpa [scons] using h k hk

theorem betaDiv2StepsThroughAt_nat (e : Nat → Nat) (code step last : Nat) :
    Sat natModel e (betaDiv2StepsThroughAt code step last) ↔
      ∀ k, k ≤ e last →
        ∃ cur next bit,
          BetaEntry (e code) (e step) k cur ∧
          BetaEntry (e code) (e step) (k+1) next ∧
          (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (leAt 0 (last+1)) := by
      exact (leAt_nat (scons k e) 0 (last+1)).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    simpa [scons] using hw
  · intro h k hkSat
    have hk : k ≤ e last := by
      have hle := (leAt_nat (scons k e) 0 (last+1)).mp hkSat
      simpa [scons] using hle
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    simpa [scons] using h k hk

theorem betaDiv2StepsThroughConstAt_nat
    (e : Nat → Nat) (code step last : Nat) :
    Sat natModel e (betaDiv2StepsThroughConstAt code step last) ↔
      BetaDiv2StepsThrough (e code) (e step) last := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (leConstAt 0 last) := by
      exact (leConstAt_nat (scons k e) 0 last).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    rcases hw with ⟨cur, next, bit, hcur, hnext, hbit, hvalue⟩
    exact ⟨cur, next, bit, by
      simpa [BetaDiv2Step, scons] using
        And.intro hcur (And.intro hnext (And.intro hbit hvalue))⟩
  · intro h k hkSat
    have hk : k ≤ last := by
      have hle := (leConstAt_nat (scons k e) 0 last).mp hkSat
      simpa [scons] using hle
    rcases h k hk with ⟨cur, next, bit, hdiv⟩
    rcases hdiv with ⟨hcur, hnext, hbit, hvalue⟩
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    exact ⟨cur, next, bit, by simpa [scons] using hcur,
      by simpa [scons] using hnext, by
        simpa using And.intro hbit hvalue⟩

theorem betaDiv2BitAt_nat (e : Nat → Nat) (bit code step idx : Nat) :
    Sat natModel e (betaDiv2BitAt bit code step idx) ↔
      BetaDiv2Bit (e code) (e step) (e idx) (e bit) := by
  constructor
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hstep⟩
    let E := scons next (scons cur e)
    have hcur' :
        BetaEntry (e code) (e step) (e idx) cur := by
      have hc := (betaAt_nat_entry E 1 (code+2) (step+2) (idx+2)).mp hcur
      simpa [E, scons] using hc
    have hnext' :
        BetaEntry (e code) (e step) (e idx + 1) next := by
      have hn := (betaAtSuccIdx_nat_entry E 0 (code+2) (step+2) (idx+2)).mp hnext
      simpa [E, scons, Nat.add_assoc] using hn
    have hstep' :
        (e bit = 0 ∨ e bit = 1) ∧ cur = next + next + e bit := by
      have hs := (div2StepAt_nat E 1 0 (bit+2)).mp hstep
      simpa [E, scons] using hs
    exact ⟨cur, next, hcur', hnext', hstep'⟩
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hstep⟩
    refine ⟨cur, next, ?_, ?_, ?_⟩
    · let E := scons next (scons cur e)
      apply (betaAt_nat_entry E 1 (code+2) (step+2) (idx+2)).mpr
      simpa [E, scons] using hcur
    · let E := scons next (scons cur e)
      apply (betaAtSuccIdx_nat_entry E 0 (code+2) (step+2) (idx+2)).mpr
      simpa [E, scons, Nat.add_assoc] using hnext
    · let E := scons next (scons cur e)
      apply (div2StepAt_nat E 1 0 (bit+2)).mpr
      simpa [E, scons] using hstep

theorem hfMemAt_nat_trace (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) ↔
      ∃ code step, HFMemTrace (e elem) (e set) code step := by
  constructor
  · intro h
    rcases h with ⟨code, step, hstart, hsteps, hbitOne⟩
    let E := scons step (scons code e)
    have hstart' :
        BetaEntry code step 0 (e set) := by
      have hs := (betaAtConstIdx_nat_entry E (set+2) 1 0 0).mp hstart
      simpa [E, scons] using hs
    have hsteps' :
        BetaDiv2StepsThrough code step (e elem) := by
      have hs := (betaDiv2StepsThroughAt_nat E 1 0 (elem+2)).mp hsteps
      intro k hk
      have hkE : k ≤ E (elem+2) := by
        simpa [E, scons] using hk
      have hraw := hs k hkE
      simpa [BetaDiv2Step, E, scons] using hraw
    have hbit' :
        BetaDiv2Bit code step (e elem) 1 := by
      rcases hbitOne with ⟨bit, hone, hbit⟩
      have hone' : bit = 1 := (oneAt_nat (scons bit E) 0).mp hone
      have hb := (betaDiv2BitAt_nat (scons bit E) 0 2 1 (elem+3)).mp hbit
      subst bit
      simpa [E, scons] using hb
    exact ⟨code, step, hstart', hsteps', hbit'⟩
  · intro h
    rcases h with ⟨code, step, hstart, hsteps, hbit⟩
    let E := scons step (scons code e)
    refine ⟨code, step, ?_, ?_, ?_⟩
    · apply (betaAtConstIdx_nat_entry E (set+2) 1 0 0).mpr
      simpa [E, scons] using hstart
    · apply (betaDiv2StepsThroughAt_nat E 1 0 (elem+2)).mpr
      intro k hk
      have hk' : k ≤ e elem := by
        simpa [E, scons] using hk
      have hraw := hsteps k hk'
      simpa [BetaDiv2Step, E, scons] using hraw
    · refine ⟨1, ?_, ?_⟩
      · exact (oneAt_nat (scons 1 E) 0).mpr rfl
      · apply (betaDiv2BitAt_nat (scons 1 E) 0 2 1 (elem+3)).mpr
        simpa [E, scons] using hbit

theorem betaFact_pos : ∀ n, 0 < betaFact n
  | 0 => by simp [betaFact]
  | n+1 => by
      simp [betaFact, betaFact_pos n]

theorem dvd_betaFact_of_pos_le {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ betaFact n := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      omega
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hkn with hlt | heq
      · have hle : k ≤ n := Nat.lt_succ_iff.mp hlt
        exact Nat.dvd_trans (ih hle) (by
          change betaFact n ∣ (n+1) * betaFact n
          exact Nat.dvd_mul_left (betaFact n) (n+1))
      · subst k
        change n+1 ∣ (n+1) * betaFact n
        exact Nat.dvd_mul_right (n+1) (betaFact n)

theorem BetaModulus_pos (step idx : Nat) : 0 < BetaModulus step idx := by
  simp [BetaModulus]
  omega

theorem BetaModuliProduct_pos (step : Nat) :
    ∀ n, 0 < BetaModuliProduct step n
  | 0 => by simp [BetaModuliProduct]
  | n+1 => by
      have hp := BetaModuliProduct_pos step n
      have hm := BetaModulus_pos step n
      simp [BetaModuliProduct]
      exact Nat.mul_pos hp hm

theorem BetaModulus_coprime_step (step idx : Nat) :
    (BetaModulus step idx).Coprime step := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step idx) step
  have hdm : d ∣ BetaModulus step idx := Nat.gcd_dvd_left _ _
  have hdstep : d ∣ step := Nat.gcd_dvd_right _ _
  have hdprod : d ∣ (idx + 1) * step :=
    Nat.dvd_trans hdstep (Nat.dvd_mul_left step (idx+1))
  have hdone : d ∣ 1 := by
    have hsub := Nat.dvd_sub hdm hdprod
    have hdiff : BetaModulus step idx - (idx + 1) * step = 1 := by
      simp [BetaModulus]
    rw [hdiff] at hsub
    exact hsub
  exact Nat.dvd_one.mp hdone

theorem BetaModulus_sub {step i j : Nat} (hij : i ≤ j) :
    BetaModulus step j - BetaModulus step i = (j - i) * step := by
  have hj : j + 1 = (j - i) + (i + 1) := by omega
  simp [BetaModulus, hj, Nat.add_mul]
  omega

theorem BetaModulus_pair_coprime_of_dvd_step {step i j : Nat}
    (hij : i < j) (hdiff : j - i ∣ step) :
    (BetaModulus step i).Coprime (BetaModulus step j) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step i) (BetaModulus step j)
  have hdi : d ∣ BetaModulus step i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ BetaModulus step j := Nat.gcd_dvd_right _ _
  have hcopStep : d.Coprime step :=
    Nat.Coprime.coprime_dvd_left hdi (BetaModulus_coprime_step step i)
  have hddiffstep : d ∣ (j - i) * step := by
    have hsub := Nat.dvd_sub hdj hdi
    simpa [d, BetaModulus_sub (Nat.le_of_lt hij)] using hsub
  have hddiff : d ∣ j - i := by
    apply hcopStep.dvd_of_dvd_mul_left
    simpa [Nat.mul_comm] using hddiffstep
  have hdstep' : d ∣ step := Nat.dvd_trans hddiff hdiff
  exact hcopStep.eq_one_of_dvd hdstep'

theorem BetaModulus_pair_coprime_of_lt_le {i j N : Nat}
    (hij : i < j) (hj : j ≤ N) :
    (BetaModulus (betaFact N) i).Coprime (BetaModulus (betaFact N) j) := by
  apply BetaModulus_pair_coprime_of_dvd_step hij
  apply dvd_betaFact_of_pos_le
  · omega
  · omega

theorem BetaModuliProduct_coprime_modulus_of_le {n j N : Nat}
    (hnj : n ≤ j) (hjN : j ≤ N) :
    (BetaModuliProduct (betaFact N) n).Coprime
      (BetaModulus (betaFact N) j) := by
  induction n with
  | zero =>
      simp [BetaModuliProduct]
  | succ n ih =>
      simp [BetaModuliProduct]
      apply Nat.Coprime.mul_left
      · exact ih (by omega)
      · exact BetaModulus_pair_coprime_of_lt_le (by omega) hjN

theorem BetaModuliProduct_coprime_next_of_le {n N : Nat} (hn : n ≤ N) :
    (BetaModuliProduct (betaFact N) n).Coprime
      (BetaModulus (betaFact N) n) :=
  BetaModuliProduct_coprime_modulus_of_le (Nat.le_refl n) hn

theorem int_bezout_gcd (m n : Nat) :
    ∃ s t : Int, s * (m : Int) + t * (n : Int) = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n =>
      refine ⟨0, 1, ?_⟩
      simp
  | H1 m n hm ih =>
      rcases ih with ⟨s, t, hst⟩
      refine ⟨t - s * ((n / m : Nat) : Int), s, ?_⟩
      rw [Nat.gcd_rec]
      rw [← hst]
      let M : Int := (m : Int)
      let q : Int := ((n / m : Nat) : Int)
      let r : Int := ((n % m : Nat) : Int)
      have hdiv : M * q + r = (n : Int) := by
        have h : ((m * (n / m) + n % m : Nat) : Int) = (n : Int) := by
          have h0 := Nat.div_add_mod n m
          rw [h0]
        simpa [M, q, r, Int.natCast_add, Int.natCast_mul] using h
      change (t - s * q) * M + s * (n : Int) = s * r + t * M
      rw [← hdiv]
      simp [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm, Int.add_comm]
      omega

theorem coprime_int_bezout {m n : Nat} (h : m.Coprime n) :
    ∃ s t : Int, s * (m : Int) + t * (n : Int) = 1 := by
  rcases int_bezout_gcd m n with ⟨s, t, hst⟩
  refine ⟨s, t, ?_⟩
  have hg : Nat.gcd m n = 1 := h.gcd_eq_one
  simpa [hg] using hst

theorem int_nonneg_shift (z : Int) {M : Nat} (hM : 0 < M) :
    0 ≤ z + ((M : Nat) : Int) * (((z.natAbs + 1 : Nat) : Int)) := by
  have hzlow : -((z.natAbs : Nat) : Int) ≤ z := by
    rcases Int.natAbs_eq z with hz | hz <;> omega
  have hprodNat : z.natAbs ≤ M * (z.natAbs + 1) := by
    have h1 : z.natAbs ≤ z.natAbs + 1 := by omega
    have h2 : z.natAbs + 1 ≤ M * (z.natAbs + 1) := by
      have hm1 : 1 ≤ M := by omega
      have hm := Nat.mul_le_mul_right (z.natAbs + 1) hm1
      simpa [Nat.one_mul] using hm
    exact Nat.le_trans h1 h2
  have hprod :
      ((z.natAbs : Nat) : Int) ≤
        (M : Int) * (((z.natAbs + 1 : Nat) : Int)) := by
    exact Int.ofNat_le.mpr hprodNat
  omega

theorem int_crt_shape_left {s t m n a b : Int}
    (hbez : s * m + t * n = 1) :
    a * (t * n) + b * (s * m) = a + m * (b * s - a * s) := by
  have htn : t * n = 1 - s * m := by omega
  rw [htn]
  simp [Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

theorem int_crt_shape_right {s t m n a b : Int}
    (hbez : s * m + t * n = 1) :
    a * (t * n) + b * (s * m) = b + n * (a * t - b * t) := by
  have hsm : s * m = 1 - t * n := by omega
  rw [hsm]
  simp [Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

theorem crt_two_mod {m n a b : Nat} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (ha : a < m) (hb : b < n) :
    ∃ c, c % m = a ∧ c % n = b := by
  rcases coprime_int_bezout hcop with ⟨s, t, hbez⟩
  let z : Int := (a : Int) * (t * (n : Int)) + (b : Int) * (s * (m : Int))
  let K : Int := (((z.natAbs + 1 : Nat) : Int))
  let big : Nat := m * n
  let cInt : Int := z + (big : Int) * K
  let c : Nat := cInt.toNat
  have hbig : 0 < big := Nat.mul_pos hm hn
  have hcNonneg : 0 ≤ cInt := by
    simpa [cInt, K, big] using int_nonneg_shift z hbig
  have hcCast : (c : Int) = cInt := by
    exact Int.toNat_of_nonneg hcNonneg
  refine ⟨c, ?_, ?_⟩
  · have hzmod : z % (m : Int) = (a : Int) := by
      have hshape :
          z = (a : Int) + (m : Int) * ((b : Int) * s - (a : Int) * s) := by
        exact int_crt_shape_left hbez
      rw [hshape]
      rw [Int.add_mul_emod_self_left]
      apply Int.emod_eq_of_lt <;> omega
    have hcmodInt : (c : Int) % (m : Int) = (a : Int) := by
      rw [hcCast]
      have hbigshape : (big : Int) * K = (m : Int) * ((n : Int) * K) := by
        simp [big, Int.natCast_mul, Int.mul_assoc]
      simp only [cInt]
      rw [hbigshape]
      rw [Int.add_mul_emod_self_left]
      exact hzmod
    have hcastmod : ((c % m : Nat) : Int) = (a : Int) := by
      rw [Int.natCast_emod]
      exact hcmodInt
    omega
  · have hzmod : z % (n : Int) = (b : Int) := by
      have hshape :
          z = (b : Int) + (n : Int) * ((a : Int) * t - (b : Int) * t) := by
        exact int_crt_shape_right hbez
      rw [hshape]
      rw [Int.add_mul_emod_self_left]
      apply Int.emod_eq_of_lt <;> omega
    have hcmodInt : (c : Int) % (n : Int) = (b : Int) := by
      rw [hcCast]
      have hbigshape : (big : Int) * K = (n : Int) * ((m : Int) * K) := by
        simp [big, Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm]
      simp only [cInt]
      rw [hbigshape]
      rw [Int.add_mul_emod_self_left]
      exact hzmod
    have hcastmod : ((c % n : Nat) : Int) = (b : Int) := by
      rw [Int.natCast_emod]
      exact hcmodInt
    omega

theorem BetaEntry_value_lt {code step idx value : Nat}
    (h : BetaEntry code step idx value) :
    value < BetaModulus step idx := by
  rcases h with ⟨_, _, hlt⟩
  exact hlt

theorem BetaEntry_mod_eq {code step idx value : Nat}
    (h : BetaEntry code step idx value) :
    code % BetaModulus step idx = value := by
  rcases h with ⟨q, hcode, hlt⟩
  rw [hcode]
  rw [Nat.mul_comm q (BetaModulus step idx)]
  rw [Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

theorem BetaEntry_of_mod_eq {code step idx value : Nat}
    (hlt : value < BetaModulus step idx)
    (hmod : code % BetaModulus step idx = value) :
    BetaEntry code step idx value := by
  refine ⟨code / BetaModulus step idx, ?_, hlt⟩
  have hdiv : code = (code / BetaModulus step idx) * BetaModulus step idx +
      code % BetaModulus step idx := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod code (BetaModulus step idx)).symm
  simpa [hmod] using hdiv

theorem BetaModuliProduct_dvd_of_lt {step i n : Nat} (hi : i < n) :
    BetaModulus step i ∣ BetaModuliProduct step n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · have hd : BetaModulus step i ∣ BetaModuliProduct step n := ih hlt
        rcases hd with ⟨q, hq⟩
        refine ⟨q * BetaModulus step n, ?_⟩
        simp [BetaModuliProduct, hq, Nat.mul_assoc]
      · subst i
        change BetaModulus step n ∣ BetaModuliProduct step n * BetaModulus step n
        exact Nat.dvd_mul_left (BetaModulus step n) (BetaModuliProduct step n)

theorem mod_eq_of_mod_BetaModuliProduct_eq {code old step idx n : Nat}
    (hi : idx < n)
    (hmod : code % BetaModuliProduct step n = old % BetaModuliProduct step n) :
    code % BetaModulus step idx = old % BetaModulus step idx := by
  have hd : BetaModulus step idx ∣ BetaModuliProduct step n :=
    BetaModuliProduct_dvd_of_lt hi
  calc
    code % BetaModulus step idx = code % BetaModuliProduct step n % BetaModulus step idx := by
      exact (Nat.mod_mod_of_dvd code hd).symm
    _ = old % BetaModuliProduct step n % BetaModulus step idx := by rw [hmod]
    _ = old % BetaModulus step idx := Nat.mod_mod_of_dvd old hd

theorem BetaEntry_of_mod_BetaModuliProduct_eq {code old step idx n value : Nat}
    (hi : idx < n)
    (hmod : code % BetaModuliProduct step n = old % BetaModuliProduct step n)
    (hold : BetaEntry old step idx value) :
    BetaEntry code step idx value := by
  apply BetaEntry_of_mod_eq (BetaEntry_value_lt hold)
  calc
    code % BetaModulus step idx = old % BetaModulus step idx :=
      mod_eq_of_mod_BetaModuliProduct_eq hi hmod
    _ = value := BetaEntry_mod_eq hold

theorem BetaModulus_pair_coprime_of_lt_le_mul_betaFact {i j N scale : Nat}
    (hij : i < j) (hj : j ≤ N) :
    (BetaModulus (betaFact N * scale) i).Coprime
      (BetaModulus (betaFact N * scale) j) := by
  apply BetaModulus_pair_coprime_of_dvd_step hij
  have hd : j - i ∣ betaFact N := by
    apply dvd_betaFact_of_pos_le
    · omega
    · omega
  exact Nat.dvd_trans hd (Nat.dvd_mul_right (betaFact N) scale)

theorem BetaModuliProduct_coprime_modulus_of_le_mul_betaFact {n j N scale : Nat}
    (hnj : n ≤ j) (hjN : j ≤ N) :
    (BetaModuliProduct (betaFact N * scale) n).Coprime
      (BetaModulus (betaFact N * scale) j) := by
  induction n with
  | zero =>
      simp [BetaModuliProduct]
  | succ n ih =>
      simp [BetaModuliProduct]
      apply Nat.Coprime.mul_left
      · exact ih (by omega)
      · exact BetaModulus_pair_coprime_of_lt_le_mul_betaFact (by omega) hjN

theorem BetaModuliProduct_coprime_next_of_le_mul_betaFact {n N scale : Nat}
    (hn : n ≤ N) :
    (BetaModuliProduct (betaFact N * scale) n).Coprime
      (BetaModulus (betaFact N * scale) n) :=
  BetaModuliProduct_coprime_modulus_of_le_mul_betaFact (Nat.le_refl n) hn

theorem beta_entries_exist_lt_mul_betaFact {N n scale : Nat} (hn : n ≤ N + 1)
    (value : Nat → Nat)
    (hsmall : ∀ i, i < n → value i < BetaModulus (betaFact N * scale) i) :
    ∃ code, ∀ i, i < n → BetaEntry code (betaFact N * scale) i (value i) := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro i hi
      omega
  | succ n ih =>
      have hnOld : n ≤ N + 1 := by omega
      rcases ih hnOld (by
        intro i hi
        exact hsmall i (by omega)) with ⟨old, hold⟩
      let step := betaFact N * scale
      let prod := BetaModuliProduct step n
      let modn := BetaModulus step n
      have hprodPos : 0 < prod := by
        simpa [prod, step] using BetaModuliProduct_pos step n
      have hmodnPos : 0 < modn := by
        simpa [modn, step] using BetaModulus_pos step n
      have hnN : n ≤ N := by omega
      have hcop : prod.Coprime modn := by
        simpa [prod, modn, step] using
          BetaModuliProduct_coprime_next_of_le_mul_betaFact
            (n := n) (N := N) (scale := scale) hnN
      have ha : old % prod < prod := Nat.mod_lt old hprodPos
      have hb : value n < modn := by
        simpa [modn, step] using hsmall n (Nat.lt_succ_self n)
      rcases crt_two_mod hprodPos hmodnPos hcop ha hb with ⟨code, hprod, hnew⟩
      refine ⟨code, ?_⟩
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · apply BetaEntry_of_mod_BetaModuliProduct_eq hlt
        · simpa [prod, step] using hprod
        · exact hold i hlt
      · subst i
        apply BetaEntry_of_mod_eq
        · exact hsmall n (Nat.lt_succ_self n)
        · simpa [modn, step] using hnew

theorem beta_entries_exist_through_mul_betaFact {N scale : Nat} (value : Nat → Nat)
    (hsmall : ∀ i, i ≤ N → value i < BetaModulus (betaFact N * scale) i) :
    ∃ code, ∀ i, i ≤ N → BetaEntry code (betaFact N * scale) i (value i) := by
  rcases beta_entries_exist_lt_mul_betaFact (N := N) (n := N + 1) (scale := scale)
      (Nat.le_refl (N + 1)) value (by
    intro i hi
    exact hsmall i (by omega)) with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  intro i hi
  exact hcode i (by omega)

theorem shiftRight_lt_trace_modulus (elem set i : Nat) :
    set >>> i < BetaModulus (betaFact (elem + 1) * (set + 1)) i := by
  let step := betaFact (elem + 1) * (set + 1)
  have hshift : set >>> i ≤ set := Nat.shiftRight_le set i
  have hbf1 : 1 ≤ betaFact (elem + 1) := Nat.succ_le_of_lt (betaFact_pos (elem + 1))
  have hstep_ge : set + 1 ≤ step := by
    have hm := Nat.mul_le_mul_right (set + 1) hbf1
    simpa [step, Nat.mul_comm, Nat.mul_assoc] using hm
  have hset_lt_step : set < step := by omega
  have hstep_le_mul : step ≤ (i + 1) * step := by
    have hi1 : 1 ≤ i + 1 := by omega
    have hm := Nat.mul_le_mul_right step hi1
    simpa [Nat.one_mul, Nat.mul_comm] using hm
  change set >>> i < 1 + (i + 1) * step
  omega

theorem div2_step_shiftRight (set k : Nat) :
    let cur := set >>> k
    let next := set >>> (k + 1)
    let bit := cur % 2
    (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  intro cur next bit
  have hbit : bit = 0 ∨ bit = 1 := by
    simpa [bit] using Nat.mod_two_eq_zero_or_one cur
  have hnext : next = cur / 2 := by
    simpa [cur, next] using Nat.shiftRight_succ set k
  have hdiv := Nat.div_add_mod cur 2
  constructor
  · exact hbit
  · omega

theorem div2_step_shiftRight_one {set elem : Nat}
    (hmem : AckermannHF.Mem elem set) :
    let cur := set >>> elem
    let next := set >>> (elem + 1)
    cur = next + next + 1 := by
  intro cur next
  have hbitTrue : cur.testBit 0 = true := by
    have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
    simpa [AckermannHF.Mem, cur, Nat.add_comm] using hmem.symm.trans hshift.symm
  have hmod : cur % 2 = 1 := by
    rw [Nat.testBit_zero] at hbitTrue
    exact of_decide_eq_true hbitTrue
  have hnext : next = cur / 2 := by
    simpa [cur, next] using Nat.shiftRight_succ set elem
  have hdiv := Nat.div_add_mod cur 2
  omega

theorem HFMemTrace_exists_of_mem {elem set : Nat}
    (hmem : AckermannHF.Mem elem set) :
    ∃ code step, HFMemTrace elem set code step := by
  let N := elem + 1
  let scale := set + 1
  let step := betaFact N * scale
  let value : Nat → Nat := fun k => set >>> k
  have hsmall : ∀ i, i ≤ N → value i < BetaModulus step i := by
    intro i _hi
    simpa [value, step, N, scale] using shiftRight_lt_trace_modulus elem set i
  rcases beta_entries_exist_through_mul_betaFact (N := N) (scale := scale) value hsmall with
    ⟨code, hcode⟩
  refine ⟨code, step, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · have h0 := hcode 0 (by omega)
    simpa [value, step, Nat.shiftRight_zero] using h0
  · intro k hk
    let cur := set >>> k
    let next := set >>> (k + 1)
    let bit := cur % 2
    have hcur : BetaEntry code step k cur := by
      have h := hcode k (by omega)
      simpa [value, cur] using h
    have hnext : BetaEntry code step (k + 1) next := by
      have h := hcode (k + 1) (by omega)
      simpa [value, next] using h
    have hstep := div2_step_shiftRight set k
    refine ⟨cur, next, bit, ?_, ?_, ?_, ?_⟩
    · exact hcur
    · exact hnext
    · simpa [cur, bit] using hstep.1
    · simpa [cur, next, bit] using hstep.2
  · let cur := set >>> elem
    let next := set >>> (elem + 1)
    have hcur : BetaEntry code step elem cur := by
      have h := hcode elem (by omega)
      simpa [value, cur] using h
    have hnext : BetaEntry code step (elem + 1) next := by
      have h := hcode (elem + 1) (by omega)
      simpa [value, next] using h
    have hcurEq : cur = next + next + 1 := by
      simpa [cur, next] using div2_step_shiftRight_one hmem
    refine ⟨cur, next, ?_, ?_, ?_, ?_⟩
    · exact hcur
    · exact hnext
    · exact Or.inr rfl
    · exact hcurEq

theorem BetaEntry_functional {code step idx a b : Nat}
    (ha : BetaEntry code step idx a) (hb : BetaEntry code step idx b) : a = b := by
  rcases ha with ⟨qa, hca, hla⟩
  rcases hb with ⟨qb, hcb, hlb⟩
  let m := BetaModulus step idx
  have hmoda : code % m = a := by
    rw [hca]
    have htmp : (qa * m + a) % m = a := by
      rw [Nat.mul_comm qa m]
      rw [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [m] using hla)
    simpa [m] using htmp
  have hmodb : code % m = b := by
    rw [hcb]
    have htmp : (qb * m + b) % m = b := by
      rw [Nat.mul_comm qb m]
      rw [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [m] using hlb)
    simpa [m] using htmp
  exact hmoda.symm.trans hmodb

theorem BetaDiv2Step_div_two {code step idx cur next bit : Nat}
    (h : BetaDiv2Step code step idx cur next bit) : cur / 2 = next := by
  rcases h with ⟨_, _, hbit, hcur⟩
  rcases hbit with rfl | rfl
  · rw [hcur, ← Nat.two_mul next]
    rw [Nat.mul_add_div]
    · simp
    · decide
  · rw [hcur, ← Nat.two_mul next]
    rw [Nat.mul_add_div]
    · simp
    · decide

theorem BetaDiv2Step_bit_one_testBit_zero {code step idx cur next : Nat}
    (h : BetaDiv2Step code step idx cur next 1) : cur.testBit 0 = true := by
  rcases h with ⟨_, _, _, hcur⟩
  rw [hcur, Nat.testBit_zero]
  have hshape : next + next + 1 = 1 + 2 * next := by omega
  rw [hshape]
  rw [Nat.add_mul_mod_self_left]
  simp

theorem HFMemTrace_entry_shiftRight {elem set code step : Nat}
    (h : HFMemTrace elem set code step) :
    ∀ k value, k ≤ elem + 1 →
      BetaEntry code step k value → value = set >>> k := by
  intro k
  induction k with
  | zero =>
      intro value _ hvalue
      have hstart : BetaEntry code step 0 set := h.1
      have hv : value = set := BetaEntry_functional hvalue hstart
      simpa [Nat.shiftRight_zero] using hv
  | succ k ih =>
      intro value hle hvalue
      have hk : k ≤ elem := by omega
      rcases h.2.1 k hk with ⟨cur, next, bit, hstep⟩
      have hcur : cur = set >>> k := ih cur (by omega) hstep.1
      have hvalue_next : value = next :=
        BetaEntry_functional hvalue hstep.2.1
      have hnext : next = cur / 2 :=
        (BetaDiv2Step_div_two hstep).symm
      calc
        value = next := hvalue_next
        _ = cur / 2 := hnext
        _ = (set >>> k) / 2 := by rw [hcur]
        _ = set >>> (k+1) := (Nat.shiftRight_succ set k).symm

theorem HFMemTrace_mem {elem set code step : Nat}
    (h : HFMemTrace elem set code step) : AckermannHF.Mem elem set := by
  rcases h.2.2 with ⟨cur, next, hstep⟩
  have hcur : cur = set >>> elem :=
    HFMemTrace_entry_shiftRight h elem cur (by omega) hstep.1
  have hlow : (set >>> elem).testBit 0 = true := by
    have hbit := BetaDiv2Step_bit_one_testBit_zero hstep
    simpa [hcur] using hbit
  have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
  rw [hshift] at hlow
  simpa [AckermannHF.Mem] using hlow

theorem hfMemAt_sound (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) → AckermannHF.Mem (e elem) (e set) := by
  intro h
  rcases (hfMemAt_nat_trace e elem set).mp h with ⟨code, step, htrace⟩
  exact HFMemTrace_mem htrace

theorem hfMemAt_complete (e : Nat → Nat) (elem set : Nat) :
    AckermannHF.Mem (e elem) (e set) → Sat natModel e (hfMemAt elem set) := by
  intro hmem
  rcases HFMemTrace_exists_of_mem hmem with ⟨code, step, htrace⟩
  exact (hfMemAt_nat_trace e elem set).mpr ⟨code, step, htrace⟩

theorem hfMemAt_exact (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) ↔ AckermannHF.Mem (e elem) (e set) := by
  constructor
  · exact hfMemAt_sound e elem set
  · exact hfMemAt_complete e elem set

theorem hfMemAt_free {i elem set : Nat} (h : Free i (hfMemAt elem set)) :
    i = elem ∨ i = set := by
  simp [hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtConstIdx, betaAtSuccIdx, betaAt, remAt, ltAt, leAt, div2StepAt,
    boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, Free, Term.Free,
    Term.rename, Term.numeral] at h
  omega

/-- Slot-map extension across a translated HF quantifier.  The newly bound HF
variable is represented by the newly bound PA variable `0`; older HF variables
are shifted past it. -/
def hfUpVarMap (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

/-- Translate set-theory formulas to PA formulas using Ackermann membership.
The HF domain is all natural numbers, so quantifiers are not relativized. -/
def hfFormulaAt (ρ : Nat → Nat) : Form → Formula
  | Form.fMem i j => hfMemAt (ρ i) (ρ j)
  | Form.fEq i j => eq (Term.var (ρ i)) (Term.var (ρ j))
  | Form.fBot => bot
  | Form.fImp a b => imp (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fAnd a b => and (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fOr a b => or (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fAll a => all (hfFormulaAt (hfUpVarMap ρ) a)
  | Form.fEx a => ex (hfFormulaAt (hfUpVarMap ρ) a)

theorem hfFormulaAt_free (phi : Form) :
    ∀ {ρ : Nat → Nat} {i : Nat}, Free i (hfFormulaAt ρ phi) →
      ∃ n, SetTheory.Free n phi ∧ i = ρ n := by
  induction phi with
  | fMem a b =>
      intro ρ i h
      rcases hfMemAt_free h with hi | hi
      · exact ⟨a, Or.inl rfl, hi⟩
      · exact ⟨b, Or.inr rfl, hi⟩
  | fEq a b =>
      intro ρ i h
      simp only [hfFormulaAt, Free, Term.Free] at h
      rcases h with hi | hi
      · exact ⟨a, Or.inl rfl, hi⟩
      · exact ⟨b, Or.inr rfl, hi⟩
  | fBot =>
      intro ρ i h
      cases h
  | fImp a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fAnd a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fOr a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fAll a ih =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases ih h with ⟨n, hn, hi⟩
      cases n with
      | zero =>
          simp [hfUpVarMap] at hi
      | succ n =>
          exists n
          constructor
          · exact hn
          · simp [hfUpVarMap] at hi
            omega
  | fEx a ih =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases ih h with ⟨n, hn, hi⟩
      cases n with
      | zero =>
          simp [hfUpVarMap] at hi
      | succ n =>
          exists n
          constructor
          · exact hn
          · simp [hfUpVarMap] at hi
            omega

/-- The default HF-in-PA translation reads HF variable `n` from PA slot `n`. -/
def translateHFFormula (phi : Form) : Formula :=
  hfFormulaAt (fun n : Nat => n) phi

/-- Context-level counterpart of `hfFormulaAt`. -/
def hfContextAt (ρ : Nat → Nat) (G : List Form) : List Formula :=
  G.map (hfFormulaAt ρ)

/-- Default context translation for the HF-in-PA interpretation. -/
def translateHFContext (G : List Form) : List Formula :=
  G.map translateHFFormula

theorem translateHFContext_eq_hfContextAt_id (G : List Form) :
    translateHFContext G = hfContextAt (fun n : Nat => n) G := by
  simp [translateHFContext, hfContextAt, translateHFFormula]

theorem hfFormulaAt_ext (phi : Form) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, ρ n = σ n) → hfFormulaAt ρ phi = hfFormulaAt σ phi := by
  induction phi with
  | fMem i j =>
      intro ρ σ h
      simp [hfFormulaAt, h]
  | fEq i j =>
      intro ρ σ h
      simp [hfFormulaAt, h]
  | fBot =>
      intro ρ σ h
      rfl
  | fImp a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fAnd a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fOr a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fAll a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg all
      exact ih (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n])
  | fEx a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg ex
      exact ih (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n])

/-- HF-in-PA translation only depends on the slot map at variables free in the
source HF formula. -/
theorem hfFormulaAt_ext_free (phi : Form) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, SetTheory.Free n phi → ρ n = σ n) →
        hfFormulaAt ρ phi = hfFormulaAt σ phi := by
  induction phi with
  | fMem i j =>
      intro ρ σ h
      simp [hfFormulaAt, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fEq i j =>
      intro ρ σ h
      simp [hfFormulaAt, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fBot =>
      intro ρ σ h
      rfl
  | fImp a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fAnd a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fOr a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fAll a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg all
      exact ih (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n hn])
  | fEx a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg ex
      exact ih (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n hn])

theorem hfFormulaAt_source_rename (phi : Form) (ρ r : Nat → Nat) :
    hfFormulaAt ρ (SetTheory.rename r phi) =
      hfFormulaAt (fun n => ρ (r n)) phi := by
  induction phi generalizing ρ r with
  | fMem i j =>
      rfl
  | fEq i j =>
      rfl
  | fBot =>
      rfl
  | fImp a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fAnd a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fOr a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fAll a ih =>
      simp only [SetTheory.rename, hfFormulaAt]
      apply congrArg all
      calc
        hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename (SetTheory.up r) a)
            = hfFormulaAt (fun n => hfUpVarMap ρ (SetTheory.up r n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => ρ (r n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)
  | fEx a ih =>
      simp only [SetTheory.rename, hfFormulaAt]
      apply congrArg ex
      calc
        hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename (SetTheory.up r) a)
            = hfFormulaAt (fun n => hfUpVarMap ρ (SetTheory.up r n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => ρ (r n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)

theorem rename_hfFormulaAt (phi : Form) (ρ r : Nat → Nat) :
    rename r (hfFormulaAt ρ phi) =
      hfFormulaAt (fun n => r (ρ n)) phi := by
  induction phi generalizing ρ r with
  | fMem i j =>
      simp [hfFormulaAt, rename_hfMemAt]
  | fEq i j =>
      rfl
  | fBot =>
      rfl
  | fImp a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fAnd a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fOr a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fAll a ih =>
      simp only [hfFormulaAt, rename]
      apply congrArg all
      calc
        rename (SetTheory.up r) (hfFormulaAt (hfUpVarMap ρ) a)
            = hfFormulaAt (fun n => SetTheory.up r (hfUpVarMap ρ n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => r (ρ n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)
  | fEx a ih =>
      simp only [hfFormulaAt, rename]
      apply congrArg ex
      calc
        rename (SetTheory.up r) (hfFormulaAt (hfUpVarMap ρ) a)
            = hfFormulaAt (fun n => SetTheory.up r (hfUpVarMap ρ n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => r (ρ n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)

theorem hfFormulaAt_rename_succ (phi : Form) (ρ : Nat → Nat) :
    hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename Nat.succ phi) =
      rename Nat.succ (hfFormulaAt ρ phi) := by
  calc
    hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename Nat.succ phi)
        = hfFormulaAt (fun n => hfUpVarMap ρ (Nat.succ n)) phi := by
            exact hfFormulaAt_source_rename phi (hfUpVarMap ρ) Nat.succ
    _ = hfFormulaAt (fun n => Nat.succ (ρ n)) phi := by
            exact hfFormulaAt_ext phi (fun n => by rfl)
    _ = rename Nat.succ (hfFormulaAt ρ phi) := by
            exact (rename_hfFormulaAt phi ρ Nat.succ).symm

theorem hfContextAt_rename_succ (ρ : Nat → Nat) (G : List Form) :
    hfContextAt (hfUpVarMap ρ) (G.map (SetTheory.rename Nat.succ)) =
      (hfContextAt ρ G).map (rename Nat.succ) := by
  simp only [hfContextAt, List.map_map]
  apply List.map_congr_left
  intro phi _hphi
  exact hfFormulaAt_rename_succ phi ρ

theorem hfContextAt_cons_rename_succ (ρ : Nat → Nat) (a : Form)
    (G : List Form) :
    hfContextAt (hfUpVarMap ρ)
        (a :: G.map (SetTheory.rename Nat.succ)) =
      hfFormulaAt (hfUpVarMap ρ) a ::
        (hfContextAt ρ G).map (rename Nat.succ) := by
  simp only [hfContextAt, List.map_cons]
  exact congrArg (fun tail => hfFormulaAt (hfUpVarMap ρ) a :: tail)
    (hfContextAt_rename_succ ρ G)

theorem subst_instTerm_var_hfFormulaAt (phi : Form) (ρ : Nat → Nat)
    (k : Nat) :
    subst (instTerm (Term.var (ρ k))) (hfFormulaAt (hfUpVarMap ρ) phi) =
      hfFormulaAt ρ (SetTheory.rename (SetTheory.inst k) phi) := by
  calc
    subst (instTerm (Term.var (ρ k))) (hfFormulaAt (hfUpVarMap ρ) phi)
        = rename (SetTheory.inst (ρ k)) (hfFormulaAt (hfUpVarMap ρ) phi) := by
            exact subst_instTerm_var (hfFormulaAt (hfUpVarMap ρ) phi) (ρ k)
    _ = hfFormulaAt
          (fun n => SetTheory.inst (ρ k) (hfUpVarMap ρ n)) phi := by
            exact rename_hfFormulaAt phi (hfUpVarMap ρ) (SetTheory.inst (ρ k))
    _ = hfFormulaAt (fun n => ρ (SetTheory.inst k n)) phi := by
            exact hfFormulaAt_ext phi (fun n => by
              cases n with
              | zero => rfl
              | succ n => rfl)
    _ = hfFormulaAt ρ (SetTheory.rename (SetTheory.inst k) phi) := by
            exact (hfFormulaAt_source_rename phi ρ (SetTheory.inst k)).symm

theorem hfFormulaAt_eq_translateHFFormula_of_HF_sentence (phi : Form)
    (ρ : Nat → Nat) (hphi : SetTheory.Sentence phi) :
    hfFormulaAt ρ phi = translateHFFormula phi := by
  unfold translateHFFormula
  exact hfFormulaAt_ext_free phi
    (fun n hn => False.elim (hphi n hn))

theorem hfFormulaAt_exact (phi : Form) :
    ∀ (ρ : Nat → Nat) (v e : Nat → Nat),
      (∀ n, e (ρ n) = v n) →
        (Sat natModel e (hfFormulaAt ρ phi) ↔ SetTheory.Sat AckermannHF.Mem v phi) := by
  induction phi with
  | fMem i j =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat]
      rw [hfMemAt_exact]
      rw [hρ i, hρ j]
  | fEq i j =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat, Term.eval]
      constructor
      · intro h
        rw [← hρ i, ← hρ j]
        exact h
      · intro h
        rw [hρ i, hρ j]
        exact h
  | fBot =>
      intro ρ v e _hρ
      simp [hfFormulaAt, SetTheory.Sat, Sat]
  | fImp a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fAnd a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fOr a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fAll a ih =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      constructor
      · intro h d
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mp (h d)
      · intro h d
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mpr (h d)
  | fEx a ih =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      constructor
      · intro h
        rcases h with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mp hd
      · intro h
        rcases h with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mpr hd

theorem translateHFFormula_exact (phi : Form) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) ↔ SetTheory.Sat AckermannHF.Mem v phi :=
  hfFormulaAt_exact phi (fun n : Nat => n) v v (fun _ => rfl)

theorem translated_HF_axiom_sat_nat (phi : Form)
    (hphi : AckermannHF.HFAx_s phi) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) :=
  (translateHFFormula_exact phi v).mpr (AckermannHF.standard_sat_HF v phi hphi)

theorem translated_HFFin_axiom_sat_nat (phi : Form)
    (hphi : AckermannHF.HFFinAx_s phi) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) :=
  (translateHFFormula_exact phi v).mpr (AckermannHF.standard_sat_HFFin v phi hphi)

theorem hfFormulaAt_sentence_of_HF_sentence (phi : Form) (ρ : Nat → Nat)
    (hphi : SetTheory.Sentence phi) : Sentence (hfFormulaAt ρ phi) := by
  intro i hi
  rcases hfFormulaAt_free phi hi with ⟨n, hn, _⟩
  exact hphi n hn

theorem translateHFFormula_sentence_of_HF_sentence (phi : Form)
    (hphi : SetTheory.Sentence phi) : Sentence (translateHFFormula phi) :=
  hfFormulaAt_sentence_of_HF_sentence phi (fun n : Nat => n) hphi

theorem translated_HF_axiom_sentence (g : Form)
    (hg : AckermannHF.HFAx_s g) : Sentence (translateHFFormula g) :=
  translateHFFormula_sentence_of_HF_sentence g (AckermannHF.Sentences_HF g hg)

theorem translated_HFFin_axiom_sentence (g : Form)
    (hg : AckermannHF.HFFinAx_s g) : Sentence (translateHFFormula g) :=
  translateHFFormula_sentence_of_HF_sentence g (AckermannHF.Sentences_HFFin g hg)

/-- The PA-side theory consisting of syntactic translations of the sealed HF
axiom-scheme instances. -/
def translatedHFAx (phi : Formula) : Prop :=
  ∃ g, AckermannHF.HFAx_s g ∧ phi = translateHFFormula g

/-- The PA-side theory consisting of syntactic translations of the strengthened
hereditary-finite axiom-scheme instances.  This is the PA-side target for the
HF-in-PA half of the PA/HFFin deductive bi-interpretability theorem. -/
def translatedHFFinAx (phi : Formula) : Prop :=
  ∃ g, AckermannHF.HFFinAx_s g ∧ phi = translateHFFormula g

theorem translatedHFAx_intro {g : Form} (hg : AckermannHF.HFAx_s g) :
    translatedHFAx (translateHFFormula g) :=
  ⟨g, hg, rfl⟩

theorem translatedHFFinAx_intro {g : Form} (hg : AckermannHF.HFFinAx_s g) :
    translatedHFFinAx (translateHFFormula g) :=
  ⟨g, hg, rfl⟩

theorem translatedHFFinAx_of_translatedHFAx {phi : Formula}
    (hphi : translatedHFAx phi) : translatedHFFinAx phi := by
  rcases hphi with ⟨g, hg, rfl⟩
  exact translatedHFFinAx_intro (AckermannHF.HFFinAx_s_of_HFAx_s hg)

theorem Sentences_translatedHFAx : ∀ phi, translatedHFAx phi → Sentence phi := by
  intro phi hphi
  rcases hphi with ⟨g, hg, rfl⟩
  exact translated_HF_axiom_sentence g hg

theorem Sentences_translatedHFFinAx :
    ∀ phi, translatedHFFinAx phi → Sentence phi := by
  intro phi hphi
  rcases hphi with ⟨g, hg, rfl⟩
  exact translated_HFFin_axiom_sentence g hg

theorem BProv_translatedHFAx_of_HFAx {g : Form} (hg : AckermannHF.HFAx_s g) :
    BProv translatedHFAx [] (translateHFFormula g) :=
  BProv_ax (translatedHFAx_intro hg)

theorem BProv_translatedHFFinAx_of_HFFinAx {g : Form}
    (hg : AckermannHF.HFFinAx_s g) :
    BProv translatedHFFinAx [] (translateHFFormula g) :=
  BProv_ax (translatedHFFinAx_intro hg)

theorem BProv_lift_translatedHFAx_to_PA
    (hAx : ∀ f, translatedHFAx f → BProv Ax_s [] f)
    {f : Formula} (h : BProv translatedHFAx [] f) : BProv Ax_s [] f :=
  BProv_lift h hAx (fun _ hg => nomatch hg)

theorem BProv_lift_translatedHFFinAx_to_PA
    (hAx : ∀ f, translatedHFFinAx f → BProv Ax_s [] f)
    {f : Formula} (h : BProv translatedHFFinAx [] f) : BProv Ax_s [] f :=
  BProv_lift h hAx (fun _ hg => nomatch hg)

theorem standard_sat_translatedHFAx (e : Nat → Nat) :
    ∀ g, translatedHFAx g → Sat natModel e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_HF_axiom_sat_nat phi hphi e

theorem standard_sat_translatedHFFinAx (e : Nat → Nat) :
    ∀ g, translatedHFFinAx g → Sat natModel e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_HFFin_axiom_sat_nat phi hphi e

/-- Pure first-order HF derivations translate structurally to PA derivations
under the Ackermann membership translation.

This theorem is intentionally only a proof-calculus translation: source axioms
are not discharged here.  The finite axiom list introduced by `BProv` is
handled separately by `BProv_hfFormulaAt_of_BProv_HFFin`. -/
theorem Prov_hfFormulaAt_of_Prov {G : List Form} {phi : Form}
    (h : SetTheory.Prov G phi) :
    ∀ ρ : Nat → Nat, Prov (hfContextAt ρ G) (hfFormulaAt ρ phi) := by
  induction h with
  | P_ass G a hin =>
      intro ρ
      exact Prov.P_ass _ _ (List.mem_map_of_mem (f := hfFormulaAt ρ) hin)
  | P_impI G a b _ ih =>
      intro ρ
      exact Prov.P_impI _ _ _ (ih ρ)
  | P_impE G a b _ _ ihab iha =>
      intro ρ
      exact Prov.P_impE _ (hfFormulaAt ρ a) (hfFormulaAt ρ b)
        (ihab ρ) (iha ρ)
  | P_botE G a _ ih =>
      intro ρ
      exact Prov.P_botE _ (hfFormulaAt ρ a) (ih ρ)
  | P_lem G a =>
      intro ρ
      exact Prov.P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro ρ
      exact Prov.P_andI _ _ _ (iha ρ) (ihb ρ)
  | P_andE1 G a b _ ih =>
      intro ρ
      exact Prov.P_andE1 _ (hfFormulaAt ρ a) (hfFormulaAt ρ b) (ih ρ)
  | P_andE2 G a b _ ih =>
      intro ρ
      exact Prov.P_andE2 _ (hfFormulaAt ρ a) (hfFormulaAt ρ b) (ih ρ)
  | P_orI1 G a b _ ih =>
      intro ρ
      exact Prov.P_orI1 _ _ _ (ih ρ)
  | P_orI2 G a b _ ih =>
      intro ρ
      exact Prov.P_orI2 _ _ _ (ih ρ)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro ρ
      exact Prov.P_orE _ (hfFormulaAt ρ a) (hfFormulaAt ρ b)
        (hfFormulaAt ρ c) (ihor ρ) (iha ρ) (ihb ρ)
  | P_allI G a _ ih =>
      intro ρ
      apply Prov.P_allI
      have hbody := ih (hfUpVarMap ρ)
      rwa [hfContextAt_rename_succ ρ G] at hbody
  | P_allE G a k _ ih =>
      intro ρ
      have hinst := Prov.P_allE _ (hfFormulaAt (hfUpVarMap ρ) a)
        (Term.var (ρ k)) (ih ρ)
      simpa [hfFormulaAt, subst_instTerm_var_hfFormulaAt] using hinst
  | P_exI G a k _ ih =>
      intro ρ
      apply Prov.P_exI _ (hfFormulaAt (hfUpVarMap ρ) a)
        (Term.var (ρ k))
      simpa [hfFormulaAt, subst_instTerm_var_hfFormulaAt] using ih ρ
  | P_exE G a c _ _ ihex ihbody =>
      intro ρ
      apply Prov.P_exE _ (hfFormulaAt (hfUpVarMap ρ) a) (hfFormulaAt ρ c)
      · exact ihex ρ
      · have hbody := ihbody (hfUpVarMap ρ)
        rw [hfContextAt_cons_rename_succ ρ a G,
          hfFormulaAt_rename_succ c ρ] at hbody
        exact hbody
  | P_eqRefl G k =>
      intro ρ
      exact Prov.P_eqRefl _ (Term.var (ρ k))
  | P_eqElim G i j a _ _ iheq iha =>
      intro ρ
      have hbody :
          Prov (hfContextAt ρ G)
            (subst (instTerm (Term.var (ρ i)))
              (hfFormulaAt (hfUpVarMap ρ) a)) := by
        simpa [subst_instTerm_var_hfFormulaAt] using iha ρ
      have hmain := Prov.P_eqElim _ (Term.var (ρ i)) (Term.var (ρ j))
        (hfFormulaAt (hfUpVarMap ρ) a) (iheq ρ) hbody
      simpa [subst_instTerm_var_hfFormulaAt] using hmain

theorem BProv_hfFormulaAt_of_BProv_HFFin {G : List Form} {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFFinAx_s G phi) :
    ∀ ρ : Nat → Nat,
      BProv translatedHFFinAx (hfContextAt ρ G) (hfFormulaAt ρ phi) := by
  rcases h with ⟨L, hL, hprov⟩
  intro ρ
  refine ⟨hfContextAt ρ L, ?_, ?_⟩
  · intro f hf
    simp only [hfContextAt, List.mem_map] at hf
    rcases hf with ⟨g, hg, rfl⟩
    have hgAx : AckermannHF.HFFinAx_s g := hL g hg
    rw [hfFormulaAt_eq_translateHFFormula_of_HF_sentence g ρ
      (AckermannHF.Sentences_HFFin g hgAx)]
    exact translatedHFFinAx_intro hgAx
  · have hp := Prov_hfFormulaAt_of_Prov hprov ρ
    simpa [hfContextAt, List.map_append] using hp

theorem BProv_translateHFFormula_of_BProv_HFFin {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFFinAx_s [] phi) :
    BProv translatedHFFinAx [] (translateHFFormula phi) := by
  have htranslated :=
    BProv_hfFormulaAt_of_BProv_HFFin h (fun n : Nat => n)
  simpa [hfContextAt, translateHFFormula] using htranslated

end Formula

namespace Formula

def substZero : Nat → Term
  | 0 => Term.zero
  | n+1 => Term.var n

def substZeroAt (p : Nat) : Nat → Term :=
  fun n => if n < p then Term.var n else if n = p then Term.zero else Term.var (n - 1)

@[simp] theorem substZeroAt_lt {p n : Nat} (h : n < p) :
    substZeroAt p n = Term.var n := by
  simp [substZeroAt, h]

@[simp] theorem substZeroAt_eq {p : Nat} :
    substZeroAt p p = Term.zero := by
  simp [substZeroAt]

theorem substZeroAt_gt {p n : Nat} (h : p < n) :
    substZeroAt p n = Term.var (n - 1) := by
  have hnlt : ¬ n < p := by omega
  have hne : n ≠ p := by omega
  simp [substZeroAt, hnlt, hne]

@[simp] theorem substZeroAt_zero :
    substZeroAt 0 = substZero := by
  funext n
  cases n <;> simp [substZeroAt, substZero]

theorem upSubst_substZeroAt (p : Nat) :
    Term.upSubst (substZeroAt p) = substZeroAt (p+1) := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substZeroAt]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        rw [Term.upSubst, substZeroAt_lt hlt, substZeroAt_lt hslt]
        rfl
      · by_cases heq : n = p
        · subst n
          rw [Term.upSubst, substZeroAt_eq, substZeroAt_eq]
          rfl
        · have hgt : p < n := by omega
          have hsgt : p + 1 < n + 1 := by omega
          rw [Term.upSubst, substZeroAt_gt hgt, substZeroAt_gt hsgt]
          simp [Term.rename]
          omega

/-- Substitute PA variable `p` by the term `t`, shifting the free variables of
`t` through the `p` surrounding binders and closing the de Bruijn gap above
`p`.  The case `p = 0` is ordinary `instTerm t`. -/
def substTermAt (p : Nat) (t : Term) : Nat → Term :=
  fun n =>
    if n < p then Term.var n
    else if n = p then Term.rename (fun m => m + p) t
    else Term.var (n - 1)

@[simp] theorem substTermAt_lt {p n : Nat} {t : Term} (h : n < p) :
    substTermAt p t n = Term.var n := by
  simp [substTermAt, h]

@[simp] theorem substTermAt_eq {p : Nat} {t : Term} :
    substTermAt p t p = Term.rename (fun m => m + p) t := by
  simp [substTermAt]

theorem substTermAt_gt {p n : Nat} {t : Term} (h : p < n) :
    substTermAt p t n = Term.var (n - 1) := by
  have hnlt : ¬ n < p := by omega
  have hne : n ≠ p := by omega
  simp [substTermAt, hnlt, hne]

@[simp] theorem substTermAt_zero (t : Term) :
    substTermAt 0 t = instTerm t := by
  have hrename : Term.rename (fun m => m) t = t := by
    induction t with
    | var n => rfl
    | zero => rfl
    | succ t ih => simp [Term.rename, ih]
    | add a b iha ihb => simp [Term.rename, iha, ihb]
    | mul a b iha ihb => simp [Term.rename, iha, ihb]
  funext n
  cases n with
  | zero =>
      simp [substTermAt, instTerm, hrename]
  | succ n =>
      simp [substTermAt, instTerm]

theorem upSubst_substTermAt (p : Nat) (t : Term) :
    Term.upSubst (substTermAt p t) = substTermAt (p+1) t := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substTermAt]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        rw [Term.upSubst, substTermAt_lt hlt, substTermAt_lt hslt]
        rfl
      · by_cases heq : n = p
        · subst n
          rw [Term.upSubst, substTermAt_eq, substTermAt_eq]
          rw [Term.rename_comp]
          exact Term.rename_ext t _ _ (fun m => by omega)
        · have hgt : p < n := by omega
          have hsgt : p + 1 < n + 1 := by omega
          rw [Term.upSubst, substTermAt_gt hgt, substTermAt_gt hsgt]
          simp [Term.rename]
          omega

def substSuccVar : Nat → Term
  | 0 => Term.succ (Term.var 0)
  | n+1 => Term.var (n+1)

def substSuccAt (p : Nat) : Nat → Term :=
  fun n => if n = p then Term.succ (Term.var p) else Term.var n

@[simp] theorem substSuccAt_eq {p : Nat} :
    substSuccAt p p = Term.succ (Term.var p) := by
  simp [substSuccAt]

theorem substSuccAt_ne {p n : Nat} (h : n ≠ p) :
    substSuccAt p n = Term.var n := by
  simp [substSuccAt, h]

@[simp] theorem substSuccAt_zero :
    substSuccAt 0 = substSuccVar := by
  funext n
  cases n <;> simp [substSuccAt, substSuccVar]

theorem upSubst_substSuccAt (p : Nat) :
    Term.upSubst (substSuccAt p) = substSuccAt (p+1) := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substSuccAt]
  | succ n =>
      by_cases heq : n = p
      · subst n
        rw [Term.upSubst, substSuccAt_eq, substSuccAt_eq]
        rfl
      · have hsne : n + 1 ≠ p + 1 := by omega
        rw [Term.upSubst, substSuccAt_ne heq, substSuccAt_ne hsne]
        rfl

def succInj : Formula :=
  all (all (imp
    (eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))
    (eq (Term.var 1) (Term.var 0))))

def zeroNotSucc : Formula :=
  all (imp (eq (Term.succ (Term.var 0)) Term.zero) bot)

def addZero : Formula :=
  all (eq (Term.add (Term.var 0) Term.zero) (Term.var 0))

def addSucc : Formula :=
  all (all (eq
    (Term.add (Term.var 1) (Term.succ (Term.var 0)))
    (Term.succ (Term.add (Term.var 1) (Term.var 0)))))

def mulZero : Formula :=
  all (eq (Term.mul (Term.var 0) Term.zero) Term.zero)

def mulSucc : Formula :=
  all (all (eq
    (Term.mul (Term.var 1) (Term.succ (Term.var 0)))
    (Term.add (Term.mul (Term.var 1) (Term.var 0)) (Term.var 1))))

def inductionForm (phi : Formula) : Formula :=
  imp
    (and (subst substZero phi)
         (all (imp phi (subst substSuccVar phi))))
    (all phi)

/-- Modus ponens form of the PA induction body.

This is not the PA induction axiom itself: callers still have to supply a
proof of `inductionForm phi`, typically by instantiating the sealed PA axiom
schema. -/
theorem BProv_inductionForm_mp {B : Formula → Prop} {G : List Formula}
    {phi : Formula}
    (hind : BProv B G (inductionForm phi))
    (hzero : BProv B G (subst substZero phi))
    (hsucc : BProv B G (all (imp phi (subst substSuccVar phi)))) :
    BProv B G (all phi) := by
  exact BProv_mp B G
    (and (subst substZero phi)
      (all (imp phi (subst substSuccVar phi))))
    (all phi) hind (BProv_andI hzero hsucc)

def Ax (f : Formula) : Prop :=
  f = succInj ∨ f = zeroNotSucc ∨
  f = addZero ∨ f = addSucc ∨
  f = mulZero ∨ f = mulSucc ∨
  ∃ phi, f = inductionForm phi

def Ax_s (f : Formula) : Prop :=
  f = sealPA succInj ∨ f = sealPA zeroNotSucc ∨
  f = sealPA addZero ∨ f = sealPA addSucc ∨
  f = sealPA mulZero ∨ f = sealPA mulSucc ∨
  ∃ phi, f = sealPA (inductionForm phi)

theorem sentence_ax_s {f : Formula} (hf : Ax_s f) : Sentence f := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ <;>
    exact sealPA_sentence _

/-- Named membership of the sealed successor-injectivity axiom in PA. -/
theorem Ax_s_succInj : Ax_s (sealPA succInj) :=
  Or.inl rfl

/-- Named membership of the sealed zero-is-not-successor axiom in PA. -/
theorem Ax_s_zeroNotSucc : Ax_s (sealPA zeroNotSucc) :=
  Or.inr (Or.inl rfl)

/-- Named membership of the sealed addition-by-zero axiom in PA. -/
theorem Ax_s_addZero : Ax_s (sealPA addZero) :=
  Or.inr (Or.inr (Or.inl rfl))

/-- Named membership of the sealed addition-successor axiom in PA. -/
theorem Ax_s_addSucc : Ax_s (sealPA addSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- Named membership of the sealed multiplication-by-zero axiom in PA. -/
theorem Ax_s_mulZero : Ax_s (sealPA mulZero) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- Named membership of the sealed multiplication-successor axiom in PA. -/
theorem Ax_s_mulSucc : Ax_s (sealPA mulSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- Named membership of a sealed induction instance in PA. -/
theorem Ax_s_induction (phi : Formula) : Ax_s (sealPA (inductionForm phi)) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨phi, rfl⟩)))))

/-- PA proves every variable-renamed body whose sealed form is one of its
axioms. -/
theorem BProv_Ax_s_of_sealPA_rename {phi : Formula}
    (hphi : Ax_s (sealPA phi)) (r : Nat → Nat) :
    BProv Ax_s [] (rename r phi) :=
  BProv_sealPA_allE_rename phi r (BProv_ax hphi)

/-- PA proves every variable-renamed body of successor injectivity. -/
theorem BProv_Ax_s_succInj_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r succInj) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_succInj r

/-- PA proves successor injectivity. -/
theorem BProv_Ax_s_succInj :
    BProv Ax_s [] succInj := by
  simpa [rename_id] using
    BProv_Ax_s_succInj_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA successor injectivity. -/
theorem BProv_Ax_s_succInj_terms (s t : Term) :
    BProv Ax_s [] (imp
      (eq (Term.succ s) (Term.succ t))
      (eq s t)) := by
  have h1 := BProv_allE (B := Ax_s) (G := []) (t := s)
    BProv_Ax_s_succInj
  have h2 := BProv_allE (B := Ax_s) (G := []) (t := t) h1
  simpa [succInj, subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using h2

/-- PA proves every variable-renamed body of zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r zeroNotSucc) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_zeroNotSucc r

/-- PA proves zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc :
    BProv Ax_s [] zeroNotSucc := by
  simpa [rename_id] using
    BProv_Ax_s_zeroNotSucc_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc_term (t : Term) :
    BProv Ax_s [] (imp (eq (Term.succ t) Term.zero) bot) := by
  have h := BProv_allE (B := Ax_s) (G := []) (t := t)
    BProv_Ax_s_zeroNotSucc
  simpa [zeroNotSucc, subst, instTerm, Term.subst] using h

/-- PA proves every variable-renamed body of addition by zero. -/
theorem BProv_Ax_s_addZero_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r addZero) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_addZero r

/-- PA proves addition by zero. -/
theorem BProv_Ax_s_addZero :
    BProv Ax_s [] addZero := by
  simpa [rename_id] using
    BProv_Ax_s_addZero_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA addition by zero. -/
theorem BProv_Ax_s_addZero_term (t : Term) :
    BProv Ax_s [] (eq (Term.add t Term.zero) t) := by
  have h := BProv_allE (B := Ax_s) (G := []) (t := t)
    BProv_Ax_s_addZero
  simpa [addZero, subst, instTerm, Term.subst] using h

/-- PA proves every variable-renamed body of the addition-successor axiom. -/
theorem BProv_Ax_s_addSucc_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r addSucc) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_addSucc r

/-- PA proves the addition-successor axiom. -/
theorem BProv_Ax_s_addSucc :
    BProv Ax_s [] addSucc := by
  simpa [rename_id] using
    BProv_Ax_s_addSucc_rename (fun n : Nat => n)

/-- Arbitrary-term instance of the PA addition-successor axiom. -/
theorem BProv_Ax_s_addSucc_terms (s t : Term) :
    BProv Ax_s [] (eq
      (Term.add s (Term.succ t))
      (Term.succ (Term.add s t))) := by
  have h1 := BProv_allE (B := Ax_s) (G := []) (t := s)
    BProv_Ax_s_addSucc
  have h2 := BProv_allE (B := Ax_s) (G := []) (t := t) h1
  simpa [addSucc, subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using h2

/-- PA proves that every number is either zero or the successor of a
predecessor. -/
theorem BProv_Ax_s_zeroOrSuccPredAt_all :
    BProv Ax_s [] (all (zeroOrSuccPredAt 0)) := by
  let phi : Formula := zeroOrSuccPredAt 0
  have hzeroLeft : BProv Ax_s [] (subst substZero (zeroAt 0)) := by
    simpa [zeroAt, eqConstAt, substZero, subst, instTerm, Term.subst,
      Term.upSubst, Term.numeral] using
      (BProv_eqRefl (B := Ax_s) (G := []) Term.zero)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, zeroOrSuccPredAt, subst] using
      (BProv_orI1 (B := Ax_s) (G := [])
        (b := subst substZero (succPredAt 0)) hzeroLeft)
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    have hrefl : BProv Ax_s [phi]
        (eq (Term.succ (Term.var 0)) (Term.succ (Term.var 0))) :=
      BProv_eqRefl (B := Ax_s) (G := [phi])
        (Term.succ (Term.var 0))
    have hinst : BProv Ax_s [phi]
        (subst (instTerm (Term.var 0))
          (eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))) := by
      simpa [subst, instTerm, Term.subst] using hrefl
    have hright : BProv Ax_s [phi] (subst substSuccVar (succPredAt 0)) := by
      simpa [succPredAt, subst, substSuccVar, Term.subst, Term.upSubst,
        Term.rename]
        using
          (BProv_exI (B := Ax_s) (G := [phi])
            (a := eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))
            (t := Term.var 0) hinst)
    simpa [phi, zeroOrSuccPredAt, subst] using
      (BProv_orI2 (B := Ax_s) (G := [phi])
        (a := subst substSuccVar (zeroAt 0)) hright)
  have hsuccImp : BProv Ax_s [] (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccBody
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsuccImp
  have hind : BProv Ax_s [] (inductionForm phi) := by
    simpa [rename_id] using
      BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) (fun n : Nat => n)
  simpa [phi] using BProv_inductionForm_mp hind hzero hsucc

/-- Arbitrary-term instance of the PA zero-or-successor predecessor split. -/
theorem BProv_Ax_s_zeroOrSuccPred_term {G : List Formula} (t : Term) :
    BProv Ax_s G
      (or (eq t Term.zero)
        (ex (eq (Term.rename Nat.succ t) (Term.succ (Term.var 0))))) := by
  have hall : BProv Ax_s G (all (zeroOrSuccPredAt 0)) :=
    BProv_weaken_nil BProv_Ax_s_zeroOrSuccPredAt_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := t) hall
  simpa [zeroOrSuccPredAt, zeroAt, succPredAt, eqConstAt, subst,
    instTerm, Term.subst, Term.upSubst, Term.numeral,
    term_subst_instTerm_rename_succ]
    using hinst

/-- Slot-level zero-or-successor predecessor split. -/
theorem BProv_Ax_s_zeroOrSuccPredAt {G : List Formula} (a : Nat) :
    BProv Ax_s G (zeroOrSuccPredAt a) := by
  simpa [zeroOrSuccPredAt, zeroAt, succPredAt, eqConstAt, Term.rename,
    Term.numeral]
    using (BProv_Ax_s_zeroOrSuccPred_term (G := G) (Term.var a))

/-- Zero-substitution removes one surrounding binder from a shifted term. -/
theorem term_substZero_rename_succ (t : Term) :
    Term.subst substZero (Term.rename Nat.succ t) = t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [Term.rename, Term.subst, ih]
  | add a b iha ihb => simp [Term.rename, Term.subst, iha, ihb]
  | mul a b iha ihb => simp [Term.rename, Term.subst, iha, ihb]

/-- Successor-substitution leaves a term shifted through the induction binder. -/
theorem term_substSuccVar_rename_succ (t : Term) :
    Term.subst substSuccVar (Term.rename Nat.succ t) =
      Term.rename Nat.succ t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [Term.rename, Term.subst, ih]
  | add a b iha ihb => simp [Term.rename, Term.subst, iha, ihb]
  | mul a b iha ihb => simp [Term.rename, Term.subst, iha, ihb]

/-- PA proves uniformly in the right summand that if `x + y = 0`, then
`x = 0`.  The free term `x` is shifted under the displayed universal binder. -/
theorem BProv_Ax_s_add_eq_zero_left_all (x : Term) :
    BProv Ax_s []
      (all
        (imp
          (eq (Term.add (Term.rename Nat.succ x) (Term.var 0)) Term.zero)
          (eq (Term.rename Nat.succ x) Term.zero))) := by
  let phi : Formula :=
    imp
      (eq (Term.add (Term.rename Nat.succ x) (Term.var 0)) Term.zero)
      (eq (Term.rename Nat.succ x) Term.zero)
  have hzeroBody : BProv Ax_s
      [eq (Term.add x Term.zero) Term.zero]
      (eq x Term.zero) := by
    have hzeroAss : BProv Ax_s [eq (Term.add x Term.zero) Term.zero]
        (eq (Term.add x Term.zero) Term.zero) :=
      BProv_ass (B := Ax_s) (G := [eq (Term.add x Term.zero) Term.zero])
        (by simp)
    have haddZero : BProv Ax_s [eq (Term.add x Term.zero) Term.zero]
        (eq (Term.add x Term.zero) x) :=
      BProv_weaken_nil (BProv_Ax_s_addZero_term x)
    exact BProv_eqTrans (BProv_eqSym haddZero) hzeroAss
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using BProv_impI hzeroBody
  have hsuccBody : BProv Ax_s
      [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
          Term.zero,
        phi]
      (eq (Term.rename Nat.succ x) Term.zero) := by
    have hbad : BProv Ax_s
        [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi]
        (eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
          Term.zero) :=
      BProv_ass (B := Ax_s)
        (G := [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi])
        (by simp)
    have haddSucc : BProv Ax_s
        [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi]
        (eq
          (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
          (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0)))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addSucc_terms (Term.rename Nat.succ x) (Term.var 0))
    have hsuccZero : BProv Ax_s
        [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi]
        (eq (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0)))
          Term.zero) :=
      BProv_eqTrans (BProv_eqSym haddSucc) hbad
    have hnot : BProv Ax_s
        [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi]
        (imp
          (eq (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0)))
            Term.zero)
          bot) :=
      BProv_weaken_nil
        (BProv_Ax_s_zeroNotSucc_term
          (Term.add (Term.rename Nat.succ x) (Term.var 0)))
    have hbot : BProv Ax_s
        [eq (Term.add (Term.rename Nat.succ x) (Term.succ (Term.var 0)))
            Term.zero,
          phi]
        bot :=
      BProv_mp Ax_s _ _ _ hnot hsuccZero
    exact BProv_botE hbot
  have hsuccInner : BProv Ax_s [phi]
      (subst substSuccVar phi) := by
    simpa [phi, substSuccVar, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substSuccVar_rename_succ] using BProv_impI hsuccBody
  have hsuccImp : BProv Ax_s []
      (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccInner
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) := by
    exact BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsuccImp
  have hind : BProv Ax_s [] (inductionForm phi) := by
    simpa [rename_id] using
      BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) (fun n : Nat => n)
  simpa [phi] using BProv_inductionForm_mp hind hzero hsucc

/-- Modus-ponens form of `BProv_Ax_s_add_eq_zero_left_all`. -/
theorem BProv_Ax_s_add_eq_zero_left_terms {G : List Formula}
    {x y : Term}
    (h : BProv Ax_s G (eq (Term.add x y) Term.zero)) :
    BProv Ax_s G (eq x Term.zero) := by
  have hall : BProv Ax_s G
      (all
        (imp
          (eq (Term.add (Term.rename Nat.succ x) (Term.var 0)) Term.zero)
          (eq (Term.rename Nat.succ x) Term.zero))) :=
    BProv_weaken_nil (BProv_Ax_s_add_eq_zero_left_all x)
  have himp : BProv Ax_s G
      (imp (eq (Term.add x y) Term.zero) (eq x Term.zero)) := by
    have hinst := BProv_allE (B := Ax_s) (G := G) (t := y) hall
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hinst
  exact BProv_mp Ax_s G _ _ himp h

/-- PA turns a variable-bounded order proof into a closed-numeral bounded order
proof once the bound variable is known to contain that numeral. -/
theorem BProv_Ax_s_leConstAt_of_leAt_eqConst {G : List Formula}
    {a b n : Nat}
    (hle : BProv Ax_s G (leAt a b))
    (hb : BProv Ax_s G (eqConstAt b n)) :
    BProv Ax_s G (leConstAt a n) := by
  let leBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1))
  have hbody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
      (rename Nat.succ (leConstAt a n)) := by
    have hleBody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        leBody :=
      BProv_ass (B := Ax_s) (G := leBody :: G.map (rename Nat.succ))
        (by simp)
    have hbRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (eqConstAt b n)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hb Nat.succ
    have hbBody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        (eq (Term.var (b+1)) (Term.numeral n)) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_context_cons hbRen
    have htarget : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        (eq (Term.add (Term.var (a+1)) (Term.var 0))
          (Term.numeral n)) :=
      BProv_eqTrans hleBody hbBody
    have hinst : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        (subst (instTerm (Term.var 0))
          (eq (Term.add (Term.var (a+2)) (Term.var 0))
            (Term.numeral n))) := by
      simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
    have hex : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        (ex
          (eq (Term.add (Term.var (a+2)) (Term.var 0))
            (Term.numeral n))) :=
      BProv_exI (B := Ax_s) (G := leBody :: G.map (rename Nat.succ))
        (a := eq (Term.add (Term.var (a+2)) (Term.var 0))
          (Term.numeral n))
        (t := Term.var 0) hinst
    simpa [leConstAt, rename, Term.rename, SetTheory.up] using hex
  simpa [leAt, leBody] using
    (BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hle hbody)

/-- PA proves the closed zero bound case: from `x ≤ 0`, derive `x = 0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero {G : List Formula}
    {a : Nat}
    (hle : BProv Ax_s G (leConstAt a 0)) :
    BProv Ax_s G (eqConstAt a 0) := by
  let leBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) Term.zero
  have hbody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt a 0)) := by
    have hleBody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        leBody :=
      BProv_ass (B := Ax_s) (G := leBody :: G.map (rename Nat.succ))
        (by simp)
    have haZero : BProv Ax_s (leBody :: G.map (rename Nat.succ))
        (eq (Term.var (a+1)) Term.zero) :=
      BProv_Ax_s_add_eq_zero_left_terms hleBody
    simpa [eqConstAt, rename, Term.rename, Term.numeral] using haZero
  simpa [leConstAt, leBody, Term.numeral] using
    (BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hle hbody)

/-- PA proves the base bounded-order case: from `x ≤ y` and `y = 0`, derive
`x = 0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_leAt_eqConst_zero {G : List Formula}
    {a b : Nat}
    (hle : BProv Ax_s G (leAt a b))
    (hb : BProv Ax_s G (eqConstAt b 0)) :
    BProv Ax_s G (eqConstAt a 0) :=
  BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero
    (BProv_Ax_s_leConstAt_of_leAt_eqConst hle hb)

/-- Closed-bound successor decomposition for PA order: from `x ≤ n+1`, PA
derives either `x ≤ n` or `x = n+1`.  The proof explicitly case-splits on the
existential difference witness for the order relation. -/
theorem BProv_Ax_s_leConstAt_succ_cases {G : List Formula}
    {a n : Nat}
    (hle : BProv Ax_s G (leConstAt a (n+1))) :
    BProv Ax_s G (or (leConstAt a n) (eqConstAt a (n+1))) := by
  let target : Formula := or (leConstAt a n) (eqConstAt a (n+1))
  let leBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.numeral (n+1))
  have hbody : BProv Ax_s (leBody :: G.map (rename Nat.succ))
      (rename Nat.succ target) := by
    let C : List Formula := leBody :: G.map (rename Nat.succ)
    have hcases : BProv Ax_s C (zeroOrSuccPredAt 0) :=
      BProv_Ax_s_zeroOrSuccPredAt (G := C) 0
    have hzeroBranch : BProv Ax_s (zeroAt 0 :: C)
        (rename Nat.succ target) := by
      have hzero : BProv Ax_s (zeroAt 0 :: C)
          (eq (Term.var 0) Term.zero) := by
        have hraw : BProv Ax_s (zeroAt 0 :: C) (zeroAt 0) :=
          BProv_ass (B := Ax_s) (G := zeroAt 0 :: C) (by simp)
        simpa [zeroAt, eqConstAt, Term.numeral] using hraw
      have hleBody : BProv Ax_s (zeroAt 0 :: C) leBody :=
        BProv_ass (B := Ax_s) (G := zeroAt 0 :: C) (by simp [C])
      have hzeroAdd : BProv Ax_s (zeroAt 0 :: C)
          (eq (Term.add (Term.var (a+1)) (Term.var 0))
            (Term.add (Term.var (a+1)) Term.zero)) :=
        BProv_eq_congr_add_right (Term.var (a+1)) hzero
      have haddZero : BProv Ax_s (zeroAt 0 :: C)
          (eq (Term.add (Term.var (a+1)) Term.zero)
            (Term.var (a+1))) :=
        BProv_weaken_nil (BProv_Ax_s_addZero_term (Term.var (a+1)))
      have hleft : BProv Ax_s (zeroAt 0 :: C)
          (eq (Term.add (Term.var (a+1)) (Term.var 0))
            (Term.var (a+1))) :=
        BProv_eqTrans hzeroAdd haddZero
      have heq : BProv Ax_s (zeroAt 0 :: C)
          (eq (Term.var (a+1)) (Term.numeral (n+1))) :=
        BProv_eqTrans (BProv_eqSym hleft) hleBody
      simpa [target, eqConstAt, rename, leConstAt, Term.rename,
        SetTheory.up] using
        (BProv_orI2 (B := Ax_s) (G := zeroAt 0 :: C)
          (a := rename Nat.succ (leConstAt a n)) heq)
    have hsuccBranch : BProv Ax_s (succPredAt 0 :: C)
        (rename Nat.succ target) := by
      let succBody : Formula :=
        eq (Term.var 1) (Term.succ (Term.var 0))
      have hsuccAss : BProv Ax_s (succPredAt 0 :: C) (succPredAt 0) :=
        BProv_ass (B := Ax_s) (G := succPredAt 0 :: C) (by simp)
      have hsuccBody : BProv Ax_s
          (succBody :: (succPredAt 0 :: C).map (rename Nat.succ))
          (rename Nat.succ (rename Nat.succ target)) := by
        let D : List Formula :=
          succBody :: (succPredAt 0 :: C).map (rename Nat.succ)
        have hpred : BProv Ax_s D succBody :=
          BProv_ass (B := Ax_s) (G := D) (by simp [D])
        have hleShiftRaw : BProv Ax_s D (rename Nat.succ leBody) :=
          BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
        have hleShift : BProv Ax_s D
            (eq
              (Term.add (Term.var (a+2)) (Term.var 1))
              (Term.numeral (n+1))) := by
          simpa [leBody, rename, Term.rename] using hleShiftRaw
        have haddPred : BProv Ax_s D
            (eq
              (Term.add (Term.var (a+2)) (Term.var 1))
              (Term.add (Term.var (a+2)) (Term.succ (Term.var 0)))) := by
          simpa [succBody] using
            (BProv_eq_congr_add_right (Term.var (a+2)) hpred)
        have haddSucc : BProv Ax_s D
            (eq
              (Term.add (Term.var (a+2)) (Term.succ (Term.var 0)))
              (Term.succ (Term.add (Term.var (a+2)) (Term.var 0)))) :=
          BProv_weaken_nil
            (BProv_Ax_s_addSucc_terms (Term.var (a+2)) (Term.var 0))
        have hleft : BProv Ax_s D
            (eq
              (Term.add (Term.var (a+2)) (Term.var 1))
              (Term.succ (Term.add (Term.var (a+2)) (Term.var 0)))) :=
          BProv_eqTrans haddPred haddSucc
        have hsuccEqRaw : BProv Ax_s D
            (eq
              (Term.succ (Term.add (Term.var (a+2)) (Term.var 0)))
              (Term.numeral (n+1))) :=
          BProv_eqTrans (BProv_eqSym hleft) hleShift
        have hsuccEq : BProv Ax_s D
            (eq
              (Term.succ (Term.add (Term.var (a+2)) (Term.var 0)))
              (Term.succ (Term.numeral n))) := by
          simpa [Term.numeral_succ] using hsuccEqRaw
        have hinj : BProv Ax_s D
            (imp
              (eq
                (Term.succ (Term.add (Term.var (a+2)) (Term.var 0)))
                (Term.succ (Term.numeral n)))
              (eq (Term.add (Term.var (a+2)) (Term.var 0))
                (Term.numeral n))) :=
          BProv_weaken_nil
            (BProv_Ax_s_succInj_terms
              (Term.add (Term.var (a+2)) (Term.var 0))
              (Term.numeral n))
        have hsum : BProv Ax_s D
            (eq (Term.add (Term.var (a+2)) (Term.var 0))
              (Term.numeral n)) :=
          BProv_mp Ax_s D _ _ hinj hsuccEq
        have hleInst : BProv Ax_s D
            (subst (instTerm (Term.var 0))
              (eq (Term.add (Term.var (a+3)) (Term.var 0))
                (Term.numeral n))) := by
          simpa [subst, instTerm, Term.subst, Term.upSubst] using hsum
        have hleClosed : BProv Ax_s D (rename Nat.succ (rename Nat.succ
            (leConstAt a n))) := by
          have hex : BProv Ax_s D
              (ex (eq (Term.add (Term.var (a+3)) (Term.var 0))
                (Term.numeral n))) :=
            BProv_exI (B := Ax_s) (G := D)
              (a := eq (Term.add (Term.var (a+3)) (Term.var 0))
                (Term.numeral n))
              (t := Term.var 0) hleInst
          simpa [leConstAt, rename, Term.rename, SetTheory.up] using hex
        simpa [D, target, rename] using
          (BProv_orI1 (B := Ax_s) (G := D)
            (b := rename Nat.succ (rename Nat.succ (eqConstAt a (n+1))))
            hleClosed)
      simpa [succPredAt, succBody] using
        (BProv_exE_of_sentences (B := Ax_s)
          (fun f hf => sentence_ax_s (f := f) hf)
          hsuccAss hsuccBody)
    exact BProv_orE hcases hzeroBranch hsuccBranch
  simpa [leConstAt, leBody, target] using
    (BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hle hbody)

/-- PA proves every variable-renamed body of multiplication by zero. -/
theorem BProv_Ax_s_mulZero_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r mulZero) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_mulZero r

/-- PA proves multiplication by zero. -/
theorem BProv_Ax_s_mulZero :
    BProv Ax_s [] mulZero := by
  simpa [rename_id] using
    BProv_Ax_s_mulZero_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA multiplication by zero. -/
theorem BProv_Ax_s_mulZero_term (t : Term) :
    BProv Ax_s [] (eq (Term.mul t Term.zero) Term.zero) := by
  have h := BProv_allE (B := Ax_s) (G := []) (t := t)
    BProv_Ax_s_mulZero
  simpa [mulZero, subst, instTerm, Term.subst] using h

/-- PA proves every variable-renamed body of the multiplication-successor
axiom. -/
theorem BProv_Ax_s_mulSucc_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r mulSucc) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_mulSucc r

/-- PA proves the multiplication-successor axiom. -/
theorem BProv_Ax_s_mulSucc :
    BProv Ax_s [] mulSucc := by
  simpa [rename_id] using
    BProv_Ax_s_mulSucc_rename (fun n : Nat => n)

/-- Arbitrary-term instance of the PA multiplication-successor axiom. -/
theorem BProv_Ax_s_mulSucc_terms (s t : Term) :
    BProv Ax_s [] (eq
      (Term.mul s (Term.succ t))
      (Term.add (Term.mul s t) s)) := by
  have h1 := BProv_allE (B := Ax_s) (G := []) (t := s)
    BProv_Ax_s_mulSucc
  have h2 := BProv_allE (B := Ax_s) (G := []) (t := t) h1
  simpa [mulSucc, subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using h2

/-- PA proves the recursive normal form of right addition by a standard
numeral. -/
theorem BProv_Ax_s_addRightNumeral (t : Term) :
    ∀ n : Nat,
      BProv Ax_s [] (eq
        (Term.add t (Term.numeral n))
        (Term.addRightNumeral t n)) := by
  intro n
  induction n with
  | zero =>
      simpa [Term.numeral, Term.addRightNumeral] using
        BProv_Ax_s_addZero_term t
  | succ n ih =>
      have hstep : BProv Ax_s [] (eq
          (Term.add t (Term.succ (Term.numeral n)))
          (Term.succ (Term.add t (Term.numeral n)))) :=
        BProv_Ax_s_addSucc_terms t (Term.numeral n)
      have hsucc : BProv Ax_s [] (eq
          (Term.succ (Term.add t (Term.numeral n)))
          (Term.succ (Term.addRightNumeral t n))) :=
        BProv_eq_congr_succ ih
      have h := BProv_eqTrans hstep hsucc
      simpa [Term.numeral, Term.addRightNumeral] using h

/-- PA proves the recursive normal form of right multiplication by a standard
numeral. -/
theorem BProv_Ax_s_mulRightNumeral (t : Term) :
    ∀ n : Nat,
      BProv Ax_s [] (eq
        (Term.mul t (Term.numeral n))
        (Term.mulRightNumeral t n)) := by
  intro n
  induction n with
  | zero =>
      simpa [Term.numeral, Term.mulRightNumeral] using
        BProv_Ax_s_mulZero_term t
  | succ n ih =>
      have hstep : BProv Ax_s [] (eq
          (Term.mul t (Term.succ (Term.numeral n)))
          (Term.add (Term.mul t (Term.numeral n)) t)) :=
        BProv_Ax_s_mulSucc_terms t (Term.numeral n)
      have hadd : BProv Ax_s [] (eq
          (Term.add (Term.mul t (Term.numeral n)) t)
          (Term.add (Term.mulRightNumeral t n) t)) :=
        BProv_eq_congr_add_left t ih
      have h := BProv_eqTrans hstep hadd
      simpa [Term.numeral, Term.mulRightNumeral] using h

/-- PA proves closed addition of standard numerals. -/
theorem BProv_Ax_s_addNumerals (m n : Nat) :
    BProv Ax_s [] (eq
      (Term.add (Term.numeral m) (Term.numeral n))
      (Term.numeral (m + n))) := by
  simpa [Term.addRightNumeral_numeral] using
    BProv_Ax_s_addRightNumeral (Term.numeral m) n

/-- The recursive right-numeral multiplication normal form for standard
numerals is PA-provably equal to the corresponding standard numeral. -/
theorem BProv_Ax_s_mulRightNumeral_numeral (m n : Nat) :
    BProv Ax_s [] (eq
      (Term.mulRightNumeral (Term.numeral m) n)
      (Term.numeral (m * n))) := by
  induction n with
  | zero =>
      simpa [Term.mulRightNumeral, Term.numeral] using
        (BProv_eqRefl (B := Ax_s) (G := []) Term.zero)
  | succ n ih =>
      have hcongr : BProv Ax_s [] (eq
          (Term.add (Term.mulRightNumeral (Term.numeral m) n)
            (Term.numeral m))
          (Term.add (Term.numeral (m * n)) (Term.numeral m))) :=
        BProv_eq_congr_add ih
          (BProv_eqRefl (B := Ax_s) (G := []) (Term.numeral m))
      have hadd : BProv Ax_s [] (eq
          (Term.add (Term.numeral (m * n)) (Term.numeral m))
          (Term.numeral (m * n + m))) :=
        BProv_Ax_s_addNumerals (m * n) m
      have h := BProv_eqTrans hcongr hadd
      simpa [Term.mulRightNumeral, Nat.mul_succ] using h

/-- PA proves closed multiplication of standard numerals. -/
theorem BProv_Ax_s_mulNumerals (m n : Nat) :
    BProv Ax_s [] (eq
      (Term.mul (Term.numeral m) (Term.numeral n))
      (Term.numeral (m * n))) :=
  BProv_eqTrans (BProv_Ax_s_mulRightNumeral (Term.numeral m) n)
    (BProv_Ax_s_mulRightNumeral_numeral m n)

/-- From PA proofs that two slots contain fixed numerals, derive the corresponding
`leAt` relation by exhibiting the difference as witness. -/
theorem BProv_Ax_s_leAt_of_eqConst {G : List Formula}
    {a b m n : Nat}
    (ha : BProv Ax_s G (eqConstAt a m))
    (hb : BProv Ax_s G (eqConstAt b n))
    (hmn : m ≤ n) :
    BProv Ax_s G (leAt a b) := by
  let w := n - m
  have hleft : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.numeral w))
        (Term.add (Term.numeral m) (Term.numeral w))) :=
    BProv_eq_congr_add_left (Term.numeral w) ha
  have haddRaw : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.numeral w))
        (Term.numeral (m + w))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals m w)
  have hmw : m + w = n := by
    simp [w]
    omega
  have hadd : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.numeral w))
        (Term.numeral n)) := by
    simpa [hmw] using haddRaw
  have htarget : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.numeral w)) (Term.var b)) :=
    BProv_eqTrans (BProv_eqTrans hleft hadd) (BProv_eqSym hb)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral w))
        (eq (Term.add (Term.var (a+1)) (Term.var 0))
          (Term.var (b+1)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  simpa [leAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.add (Term.var (a+1)) (Term.var 0))
        (Term.var (b+1)))
      (t := Term.numeral w) hbody)

/-- From PA proofs that two slots contain fixed numerals, derive the corresponding
`ltAt` relation by exhibiting the positive difference predecessor. -/
theorem BProv_Ax_s_ltAt_of_eqConst {G : List Formula}
    {a b m n : Nat}
    (ha : BProv Ax_s G (eqConstAt a m))
    (hb : BProv Ax_s G (eqConstAt b n))
    (hmn : m < n) :
    BProv Ax_s G (ltAt a b) := by
  let w := n - m - 1
  have hleft : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.succ (Term.numeral w)))
        (Term.add (Term.numeral m) (Term.succ (Term.numeral w)))) :=
    BProv_eq_congr_add_left (Term.succ (Term.numeral w)) ha
  have haddRaw : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.numeral (w + 1)))
        (Term.numeral (m + (w + 1)))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals m (w + 1))
  have hmw : m + (w + 1) = n := by
    simp [w]
    omega
  have hadd : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.succ (Term.numeral w)))
        (Term.numeral n)) := by
    simpa [hmw] using haddRaw
  have htarget : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.succ (Term.numeral w)))
        (Term.var b)) :=
    BProv_eqTrans (BProv_eqTrans hleft hadd) (BProv_eqSym hb)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral w))
        (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.var (b+1)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  simpa [ltAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
        (Term.var (b+1)))
      (t := Term.numeral w) hbody)

/-- From a PA proof that a slot contains a fixed numeral, derive the
less-than-a-closed-numeral relation by exhibiting the positive difference
predecessor. -/
theorem BProv_Ax_s_ltConst_of_eqConst {G : List Formula}
    {a m n : Nat}
    (ha : BProv Ax_s G (eqConstAt a m))
    (hmn : m < n) :
    BProv Ax_s G
      (ex (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
        (Term.numeral n))) := by
  let w := n - m - 1
  have hleft : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.succ (Term.numeral w)))
        (Term.add (Term.numeral m) (Term.succ (Term.numeral w)))) :=
    BProv_eq_congr_add_left (Term.succ (Term.numeral w)) ha
  have haddRaw : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.numeral (w + 1)))
        (Term.numeral (m + (w + 1)))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals m (w + 1))
  have hmw : m + (w + 1) = n := by
    simp [w]
    omega
  have hadd : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.succ (Term.numeral w)))
        (Term.numeral n)) := by
    simpa [hmw] using haddRaw
  have htarget : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.succ (Term.numeral w)))
        (Term.numeral n)) :=
    BProv_eqTrans hleft hadd
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral w))
        (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.numeral n))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  exact BProv_exI (B := Ax_s) (G := G)
    (a := eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.numeral n))
    (t := Term.numeral w) hbody

/-- Closed-numeral version of `BProv_Ax_s_ltConst_of_eqConst`. -/
theorem BProv_Ax_s_ltConst_closed {G : List Formula}
    {m n : Nat} (hmn : m < n) :
    BProv Ax_s G
      (ex (eq (Term.add (Term.numeral m) (Term.succ (Term.var 0)))
        (Term.numeral n))) := by
  let w := n - m - 1
  have haddRaw : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.numeral (w + 1)))
        (Term.numeral (m + (w + 1)))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals m (w + 1))
  have hmw : m + (w + 1) = n := by
    simp [w]
    omega
  have hadd : BProv Ax_s G
      (eq (Term.add (Term.numeral m) (Term.succ (Term.numeral w)))
        (Term.numeral n)) := by
    simpa [hmw] using haddRaw
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral w))
        (eq (Term.add (Term.numeral m) (Term.succ (Term.var 0)))
          (Term.numeral n))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using hadd
  exact BProv_exI (B := Ax_s) (G := G)
    (a := eq (Term.add (Term.numeral m) (Term.succ (Term.var 0)))
      (Term.numeral n))
    (t := Term.numeral w) hbody

/-- From PA proofs that two slots contain fixed numerals and a divisibility
witness, derive the corresponding `dvdAt` relation. -/
theorem BProv_Ax_s_dvdAt_of_eqConst_mul {G : List Formula}
    {a b m n q : Nat}
    (ha : BProv Ax_s G (eqConstAt a m))
    (hb : BProv Ax_s G (eqConstAt b n))
    (hmul : m * q = n) :
    BProv Ax_s G (dvdAt a b) := by
  have hleft : BProv Ax_s G
      (eq (Term.mul (Term.var a) (Term.numeral q))
        (Term.mul (Term.numeral m) (Term.numeral q))) :=
    BProv_eq_congr_mul_left (Term.numeral q) ha
  have hmulRaw : BProv Ax_s G
      (eq (Term.mul (Term.numeral m) (Term.numeral q))
        (Term.numeral (m * q))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals m q)
  have hmul' : BProv Ax_s G
      (eq (Term.mul (Term.numeral m) (Term.numeral q))
        (Term.numeral n)) := by
    simpa [hmul] using hmulRaw
  have htarget : BProv Ax_s G
      (eq (Term.mul (Term.var a) (Term.numeral q)) (Term.var b)) :=
    BProv_eqTrans (BProv_eqTrans hleft hmul') (BProv_eqSym hb)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (eq (Term.mul (Term.var (a+1)) (Term.var 0))
          (Term.var (b+1)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  simpa [dvdAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.mul (Term.var (a+1)) (Term.var 0))
        (Term.var (b+1)))
      (t := Term.numeral q) hbody)

/-- Divisibility version of `BProv_Ax_s_dvdAt_of_eqConst_mul`, with the
quotient extracted from the divisibility proof. -/
theorem BProv_Ax_s_dvdAt_of_eqConst {G : List Formula}
    {a b m n : Nat}
    (ha : BProv Ax_s G (eqConstAt a m))
    (hb : BProv Ax_s G (eqConstAt b n))
    (hmn : m ∣ n) :
    BProv Ax_s G (dvdAt a b) := by
  rcases hmn with ⟨q, hq⟩
  exact BProv_Ax_s_dvdAt_of_eqConst_mul
    (a := a) (b := b) (m := m) (n := n) (q := q) ha hb hq.symm

/-- A fixed `0` or `1` numeral proof yields the corresponding boolean-slot
predicate. -/
theorem BProv_Ax_s_boolAt_of_eqConst {G : List Formula}
    {a b : Nat}
    (ha : BProv Ax_s G (eqConstAt a b))
    (hb : b = 0 ∨ b = 1) :
    BProv Ax_s G (boolAt a) := by
  rcases hb with rfl | rfl
  · exact BProv_orI1 (B := Ax_s) (G := G) (b := oneAt a)
      (by simpa [zeroAt] using ha)
  · exact BProv_orI2 (B := Ax_s) (G := G) (a := zeroAt a)
      (by simpa [oneAt] using ha)

/-- From fixed numeral proofs of the value, half, and bit slots, derive the
`div2StepAt` relation with the arithmetic equation left explicit. -/
theorem BProv_Ax_s_div2StepAt_of_eqConst {G : List Formula}
    {value half bit v h b : Nat}
    (hvalue : BProv Ax_s G (eqConstAt value v))
    (hhalf : BProv Ax_s G (eqConstAt half h))
    (hbit : BProv Ax_s G (eqConstAt bit b))
    (hb : b = 0 ∨ b = 1)
    (hval : h + h + b = v) :
    BProv Ax_s G (div2StepAt value half bit) := by
  have hbool : BProv Ax_s G (boolAt bit) :=
    BProv_Ax_s_boolAt_of_eqConst hbit hb
  have hdoubleLeft : BProv Ax_s G
      (eq
        (Term.add (Term.var half) (Term.var half))
        (Term.add (Term.numeral h) (Term.numeral h))) :=
    BProv_eq_congr_add hhalf hhalf
  have hdoubleRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral h) (Term.numeral h))
        (Term.numeral (h + h))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals h h)
  have hdouble : BProv Ax_s G
      (eq
        (Term.add (Term.var half) (Term.var half))
        (Term.numeral (h + h))) :=
    BProv_eqTrans hdoubleLeft hdoubleRaw
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add (Term.add (Term.var half) (Term.var half))
          (Term.var bit))
        (Term.add (Term.numeral (h + h)) (Term.var bit))) :=
    BProv_eq_congr_add_left (Term.var bit) hdouble
  have haddRight : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.var bit))
        (Term.add (Term.numeral (h + h)) (Term.numeral b))) :=
    BProv_eq_congr_add_right (Term.numeral (h + h)) hbit
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.numeral b))
        (Term.numeral (h + h + b))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (h + h) b)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.numeral b))
        (Term.numeral v)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add (Term.add (Term.var half) (Term.var half))
          (Term.var bit))
        (Term.numeral v)) :=
    BProv_eqTrans (BProv_eqTrans haddLeft haddRight) hadd
  have htarget : BProv Ax_s G
      (eq (Term.var value)
        (Term.add (Term.add (Term.var half) (Term.var half))
          (Term.var bit))) :=
    BProv_eqTrans hvalue (BProv_eqSym hcomputed)
  simpa [div2StepAt] using BProv_andI hbool htarget

/-- A binary-halving step cannot have current value `0` and output bit `1`.
This is the local contradiction kernel needed for refuting membership in the
Ackermann-coded empty set. -/
theorem BProv_Ax_s_div2StepAt_zero_one_bot {G : List Formula}
    {value half bit : Nat}
    (hvalue : BProv Ax_s G (eqConstAt value 0))
    (hbit : BProv Ax_s G (eqConstAt bit 1))
    (hstep : BProv Ax_s G (div2StepAt value half bit)) :
    BProv Ax_s G bot := by
  let t : Term := Term.add (Term.var half) (Term.var half)
  have hstepEq : BProv Ax_s G
      (eq (Term.var value) (Term.add t (Term.var bit))) := by
    simpa [div2StepAt, t] using
      (BProv_andE2 (a := boolAt bit)
        (b := eq (Term.var value)
          (Term.add (Term.add (Term.var half) (Term.var half))
            (Term.var bit))) hstep)
  have hrightZero : BProv Ax_s G
      (eq (Term.add t (Term.var bit)) Term.zero) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eqTrans (BProv_eqSym hstepEq) hvalue
  have hbitRight : BProv Ax_s G
      (eq (Term.add t (Term.var bit)) (Term.add t (Term.succ Term.zero))) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eq_congr_add_right t hbit
  have haddSucc : BProv Ax_s G
      (eq (Term.add t (Term.succ Term.zero))
        (Term.succ (Term.add t Term.zero))) :=
    BProv_weaken_nil (BProv_Ax_s_addSucc_terms t Term.zero)
  have hrightSucc : BProv Ax_s G
      (eq (Term.add t (Term.var bit))
        (Term.succ (Term.add t Term.zero))) :=
    BProv_eqTrans hbitRight haddSucc
  have hsuccZero : BProv Ax_s G
      (eq (Term.succ (Term.add t Term.zero)) Term.zero) :=
    BProv_eqTrans (BProv_eqSym hrightSucc) hrightZero
  have hnot : BProv Ax_s G
      (imp (eq (Term.succ (Term.add t Term.zero)) Term.zero) bot) :=
    BProv_weaken_nil (BProv_Ax_s_zeroNotSucc_term (Term.add t Term.zero))
  exact BProv_mp Ax_s G _ _ hnot hsuccZero

/-- Constructor for the formula obtained after all three variables of
`div2StepAt` have been instantiated by closed numerals. -/
theorem BProv_Ax_s_div2StepAt_closedSubst {G : List Formula}
    {value half bit : Nat}
    (hbit : bit = 0 ∨ bit = 1)
    (hval : half + half + bit = value) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral half)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral value))))
            (div2StepAt 2 1 0)))) := by
  have hbool : BProv Ax_s G (subst (instTerm (Term.numeral bit)) (boolAt 0)) := by
    rcases hbit with rfl | rfl
    · exact BProv_orI1 (B := Ax_s) (G := G)
        (b := subst (instTerm (Term.numeral 0)) (oneAt 0))
        (by
          simpa [zeroAt, eqConstAt, subst, instTerm, Term.subst] using
            (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral 0)))
    · exact BProv_orI2 (B := Ax_s) (G := G)
        (a := subst (instTerm (Term.numeral 1)) (zeroAt 0))
        (by
          simpa [oneAt, eqConstAt, subst, instTerm, Term.subst, Term.numeral] using
            (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral 1)))
  have hboolBody : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral half)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral value))))
            (boolAt 0)))) := by
    simpa [boolAt, zeroAt, oneAt, eqConstAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename] using hbool
  have hdoubleRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral half) (Term.numeral half))
        (Term.numeral (half + half))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals half half)
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add
          (Term.add (Term.numeral half) (Term.numeral half))
          (Term.numeral bit))
        (Term.add (Term.numeral (half + half)) (Term.numeral bit))) :=
    BProv_eq_congr_add_left (Term.numeral bit) hdoubleRaw
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (half + half)) (Term.numeral bit))
        (Term.numeral (half + half + bit))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (half + half) bit)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (half + half)) (Term.numeral bit))
        (Term.numeral value)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add
          (Term.add (Term.numeral half) (Term.numeral half))
          (Term.numeral bit))
        (Term.numeral value)) :=
    BProv_eqTrans haddLeft hadd
  have heqBody : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral half)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral value))))
            (eq (Term.var 2)
              (Term.add (Term.add (Term.var 1) (Term.var 1))
                (Term.var 0)))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename] using
      BProv_eqSym hcomputed
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral half)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral value))))
            (and (boolAt 0)
              (eq (Term.var 2)
                (Term.add (Term.add (Term.var 1) (Term.var 1))
                  (Term.var 0))))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hboolBody heqBody)
  simpa [div2StepAt] using hbody

/-- Constructor for the formula obtained after the value and half variables of
`div2StepAt` have been instantiated, while the bit slot is a free variable
with an explicit closed-numeral proof. -/
theorem BProv_Ax_s_div2StepAt_constValueHalfSubst_of_eqConst
    {G : List Formula}
    {bit b v h : Nat}
    (hbit : BProv Ax_s G (eqConstAt bit b))
    (hb : b = 0 ∨ b = 1)
    (hval : h + h + b = v) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral h))
        (subst (Term.upSubst (instTerm (Term.numeral v)))
          (div2StepAt 1 0 (bit+2)))) := by
  have hbool : BProv Ax_s G (boolAt bit) :=
    BProv_Ax_s_boolAt_of_eqConst hbit hb
  have hboolBody : BProv Ax_s G
      (subst (instTerm (Term.numeral h))
        (subst (Term.upSubst (instTerm (Term.numeral v)))
          (boolAt (bit+2)))) := by
    simpa [boolAt, zeroAt, oneAt, eqConstAt, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename] using hbool
  have hdoubleRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral h) (Term.numeral h))
        (Term.numeral (h + h))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals h h)
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add
          (Term.add (Term.numeral h) (Term.numeral h))
          (Term.var bit))
        (Term.add (Term.numeral (h + h)) (Term.var bit))) :=
    BProv_eq_congr_add_left (Term.var bit) hdoubleRaw
  have haddRight : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.var bit))
        (Term.add (Term.numeral (h + h)) (Term.numeral b))) :=
    BProv_eq_congr_add_right (Term.numeral (h + h)) hbit
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.numeral b))
        (Term.numeral (h + h + b))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (h + h) b)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (h + h)) (Term.numeral b))
        (Term.numeral v)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add
          (Term.add (Term.numeral h) (Term.numeral h))
          (Term.var bit))
        (Term.numeral v)) :=
    BProv_eqTrans (BProv_eqTrans haddLeft haddRight) hadd
  have heqBody : BProv Ax_s G
      (subst (instTerm (Term.numeral h))
        (subst (Term.upSubst (instTerm (Term.numeral v)))
          (eq (Term.var 1)
            (Term.add (Term.add (Term.var 0) (Term.var 0))
              (Term.var (bit+2)))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename] using
      BProv_eqSym hcomputed
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral h))
        (subst (Term.upSubst (instTerm (Term.numeral v)))
          (and (boolAt (bit+2))
            (eq (Term.var 1)
              (Term.add (Term.add (Term.var 0) (Term.var 0))
                (Term.var (bit+2))))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hboolBody heqBody)
  simpa [div2StepAt] using hbody

/-- From PA proofs that the three slots contain fixed numerals, and from an
explicit Euclidean-division witness in the metatheory, derive the corresponding
`remAt` relation. -/
theorem BProv_Ax_s_remAt_of_eqConst {G : List Formula}
    {rem value modulus r v m q : Nat}
    (hrem : BProv Ax_s G (eqConstAt rem r))
    (hvalue : BProv Ax_s G (eqConstAt value v))
    (hmod : BProv Ax_s G (eqConstAt modulus m))
    (hlt : r < m)
    (hval : q * m + r = v) :
    BProv Ax_s G (remAt rem value modulus) := by
  have hltAt : BProv Ax_s G (ltAt rem modulus) :=
    BProv_Ax_s_ltAt_of_eqConst hrem hmod hlt
  have hltBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q)) (ltAt (rem+1) (modulus+1))) := by
    simpa [ltAt, subst, instTerm, Term.subst, Term.upSubst, Term.rename]
      using hltAt
  have hmulLeft : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) (Term.var modulus))
        (Term.mul (Term.numeral q) (Term.numeral m))) :=
    BProv_eq_congr_mul_right (Term.numeral q) hmod
  have hmulRaw : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) (Term.numeral m))
        (Term.numeral (q * m))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals q m)
  have hmul : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) (Term.var modulus))
        (Term.numeral (q * m))) :=
    BProv_eqTrans hmulLeft hmulRaw
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.var modulus))
          (Term.var rem))
        (Term.add (Term.numeral (q * m)) (Term.var rem))) :=
    BProv_eq_congr_add_left (Term.var rem) hmul
  have haddRight : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.var rem))
        (Term.add (Term.numeral (q * m)) (Term.numeral r))) :=
    BProv_eq_congr_add_right (Term.numeral (q * m)) hrem
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral (q * m + r))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (q * m) r)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral v)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.var modulus))
          (Term.var rem))
        (Term.numeral v)) :=
    BProv_eqTrans (BProv_eqTrans haddLeft haddRight) hadd
  have htarget : BProv Ax_s G
      (eq (Term.var value)
        (Term.add (Term.mul (Term.numeral q) (Term.var modulus))
          (Term.var rem))) :=
    BProv_eqTrans hvalue (BProv_eqSym hcomputed)
  have hvalueBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (eq (Term.var (value+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.var (rem+1))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename]
      using htarget
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (and (ltAt (rem+1) (modulus+1))
          (eq (Term.var (value+1))
            (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
              (Term.var (rem+1)))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hltBody hvalueBody)
  simpa [remAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := and (ltAt (rem+1) (modulus+1))
        (eq (Term.var (value+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.var (rem+1)))))
      (t := Term.numeral q) hbody)

/-- Remainder constructor for the common nested-existential shape where the
modulus slot of `remAt` has just been instantiated by a closed numeral. -/
theorem BProv_Ax_s_remAt_constMod_of_eqConst {G : List Formula}
    {rem value r v m q : Nat}
    (hrem : BProv Ax_s G (eqConstAt rem r))
    (hvalue : BProv Ax_s G (eqConstAt value v))
    (hlt : r < m)
    (hval : q * m + r = v) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral m)) (remAt (rem+1) (value+1) 0)) := by
  have hltConst : BProv Ax_s G
      (ex (eq (Term.add (Term.var (rem+1)) (Term.succ (Term.var 0)))
        (Term.numeral m))) :=
    BProv_Ax_s_ltConst_of_eqConst hrem hlt
  have hltBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (ltAt ((rem+1)+1) (0+1)))) := by
    simpa [ltAt, subst, instTerm, Term.subst, Term.upSubst, Term.rename]
      using hltConst
  have hmulRaw : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) (Term.numeral m))
        (Term.numeral (q * m))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals q m)
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.var rem))
        (Term.add (Term.numeral (q * m)) (Term.var rem))) :=
    BProv_eq_congr_add_left (Term.var rem) hmulRaw
  have haddRight : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.var rem))
        (Term.add (Term.numeral (q * m)) (Term.numeral r))) :=
    BProv_eq_congr_add_right (Term.numeral (q * m)) hrem
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral (q * m + r))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (q * m) r)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral v)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.var rem))
        (Term.numeral v)) :=
    BProv_eqTrans (BProv_eqTrans haddLeft haddRight) hadd
  have htarget : BProv Ax_s G
      (eq (Term.var value)
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.var rem))) :=
    BProv_eqTrans hvalue (BProv_eqSym hcomputed)
  have hvalueBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (eq (Term.var ((value+1)+1))
            (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
              (Term.var ((rem+1)+1)))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename]
      using htarget
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (and (ltAt ((rem+1)+1) (0+1))
            (eq (Term.var ((value+1)+1))
              (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
                (Term.var ((rem+1)+1))))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hltBody hvalueBody)
  simpa [remAt, subst, instTerm, Term.subst, Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral m)))
        (and (ltAt ((rem+1)+1) (0+1))
          (eq (Term.var ((value+1)+1))
            (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
              (Term.var ((rem+1)+1))))))
      (t := Term.numeral q) hbody)

/-- Remainder constructor for the shape where both the remainder and modulus
slots have just been instantiated by closed numerals. -/
theorem BProv_Ax_s_remAt_constRemMod_of_eqConst {G : List Formula}
    {value r v m q : Nat}
    (hvalue : BProv Ax_s G (eqConstAt value v))
    (hlt : r < m)
    (hval : q * m + r = v) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral r)))
          (remAt 1 (value+2) 0))) := by
  have hltClosed : BProv Ax_s G
      (ex (eq (Term.add (Term.numeral r) (Term.succ (Term.var 0)))
        (Term.numeral m))) :=
    BProv_Ax_s_ltConst_closed hlt
  have hltBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral r))))
            (ltAt (1+1) (0+1))))) := by
    simpa [ltAt, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename] using hltClosed
  have hmulRaw : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) (Term.numeral m))
        (Term.numeral (q * m))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals q m)
  have haddLeft : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.numeral r))
        (Term.add (Term.numeral (q * m)) (Term.numeral r))) :=
    BProv_eq_congr_add_left (Term.numeral r) hmulRaw
  have haddRaw : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral (q * m + r))) :=
    BProv_weaken_nil (BProv_Ax_s_addNumerals (q * m) r)
  have hadd : BProv Ax_s G
      (eq
        (Term.add (Term.numeral (q * m)) (Term.numeral r))
        (Term.numeral v)) := by
    simpa [hval] using haddRaw
  have hcomputed : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.numeral r))
        (Term.numeral v)) :=
    BProv_eqTrans haddLeft hadd
  have htarget : BProv Ax_s G
      (eq (Term.var value)
        (Term.add (Term.mul (Term.numeral q) (Term.numeral m))
          (Term.numeral r))) :=
    BProv_eqTrans hvalue (BProv_eqSym hcomputed)
  have hvalueBody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral r))))
            (eq (Term.var ((value+2)+1))
              (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
                (Term.var ((1)+1))))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename]
      using htarget
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral m)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral r))))
            (and (ltAt (1+1) (0+1))
              (eq (Term.var ((value+2)+1))
                (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
                  (Term.var ((1)+1)))))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hltBody hvalueBody)
  simpa [remAt, subst, instTerm, Term.subst, Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral m)))
        (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral r))))
          (and (ltAt (1+1) (0+1))
            (eq (Term.var ((value+2)+1))
              (Term.add (Term.mul (Term.var 0) (Term.var (0+1)))
                (Term.var ((1)+1)))))))
      (t := Term.numeral q) hbody)

/-- If the `step` and `idx` slots are fixed numerals, PA proves that the
Gödel-beta modulus term computes the corresponding closed numeral. -/
theorem BProv_Ax_s_betaModTerm_of_eqConst {G : List Formula}
    {step idx s i : Nat}
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i)) :
    BProv Ax_s G
      (eq (betaModTerm step idx) (Term.numeral (BetaModulus s i))) := by
  have hidxSucc : BProv Ax_s G
      (eq (Term.succ (Term.var idx)) (Term.numeral (i + 1))) := by
    simpa [Term.numeral_succ] using BProv_eq_congr_succ hidx
  have hmul : BProv Ax_s G
      (eq
        (Term.mul (Term.succ (Term.var idx)) (Term.var step))
        (Term.mul (Term.numeral (i + 1)) (Term.numeral s))) :=
    BProv_eq_congr_mul hidxSucc hstep
  have hmulRaw : BProv Ax_s G
      (eq
        (Term.mul (Term.numeral (i + 1)) (Term.numeral s))
        (Term.numeral ((i + 1) * s))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals (i + 1) s)
  have hsucc : BProv Ax_s G
      (eq
        (Term.succ
          (Term.mul (Term.succ (Term.var idx)) (Term.var step)))
        (Term.succ (Term.numeral ((i + 1) * s)))) :=
    BProv_eq_congr_succ (BProv_eqTrans hmul hmulRaw)
  have hbeta : BetaModulus s i = (i + 1) * s + 1 := by
    unfold BetaModulus
    omega
  simpa [betaModTerm, hbeta, Term.numeral_succ] using hsucc

/-- From fixed numeral proofs for the output, code, step, and index slots, and
an explicit beta-entry quotient in the metatheory, derive the corresponding
`betaAt` relation. -/
theorem BProv_Ax_s_betaAt_of_eqConst {G : List Formula}
    {out code step idx o c s i q : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hlt : o < BetaModulus s i)
    (hval : q * BetaModulus s i + o = c) :
    BProv Ax_s G (betaAt out code step idx) := by
  let m := BetaModulus s i
  have hmodTerm : BProv Ax_s G
      (eq (betaModTerm step idx) (Term.numeral m)) := by
    simpa [m] using BProv_Ax_s_betaModTerm_of_eqConst hstep hidx
  have hmodBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_subst_instTerm_rename_succ] using
      BProv_eqSym hmodTerm
  have hremBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m)) (remAt (out+1) (code+1) 0)) := by
    exact BProv_Ax_s_remAt_constMod_of_eqConst
      (rem := out) (value := code) (r := o) (v := c) (m := m) (q := q)
      hout hcode (by simpa [m] using hlt) (by simpa [m] using hval)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hmodBody hremBody)
  simpa [betaAt, m] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := and
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
        (remAt (out+1) (code+1) 0))
      (t := Term.numeral m) hbody)

/-- Constructor for the formula obtained by instantiating the output variable
of `betaAt` with a closed numeral. -/
theorem BProv_Ax_s_betaAt_constOutSubst_of_eqConst {G : List Formula}
    {code step idx o c s i q : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hlt : o < BetaModulus s i)
    (hval : q * BetaModulus s i + o = c) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral o))
        (betaAt 0 (code+1) (step+1) (idx+1))) := by
  let m := BetaModulus s i
  have hmodTerm : BProv Ax_s G
      (eq (betaModTerm step idx) (Term.numeral m)) := by
    simpa [m] using BProv_Ax_s_betaModTerm_of_eqConst hstep hidx
  have hmodBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (eq (Term.var 0)
            (Term.rename Nat.succ (betaModTerm (step+1) (idx+1)))))) := by
    simpa [betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_subst_instTerm_rename_succ] using
      BProv_eqSym hmodTerm
  have hremBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (remAt (0+1) ((code+1)+1) 0))) := by
    exact BProv_Ax_s_remAt_constRemMod_of_eqConst
      (value := code) (r := o) (v := c) (m := m) (q := q)
      hcode (by simpa [m] using hlt) (by simpa [m] using hval)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (and
            (eq (Term.var 0)
              (Term.rename Nat.succ (betaModTerm (step+1) (idx+1))))
            (remAt (0+1) ((code+1)+1) 0)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hmodBody hremBody)
  simpa [betaAt, subst, instTerm, Term.subst, Term.upSubst, m] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral o)))
        (and
          (eq (Term.var 0)
            (Term.rename Nat.succ (betaModTerm (step+1) (idx+1))))
          (remAt (0+1) ((code+1)+1) 0)))
      (t := Term.numeral m) hbody)

/-- Constant-index variant of `BProv_Ax_s_betaModTerm_of_eqConst`, used after
the index variable in `betaAtConstIdx` or `betaAtSuccIdx` has been instantiated
by a closed numeral. -/
theorem BProv_Ax_s_betaModTerm_constIdx_of_eqConst {G : List Formula}
    {step s i : Nat}
    (hstep : BProv Ax_s G (eqConstAt step s)) :
    BProv Ax_s G
      (eq
        (Term.succ (Term.mul (Term.succ (Term.numeral i)) (Term.var step)))
        (Term.numeral (BetaModulus s i))) := by
  have hmulLeft : BProv Ax_s G
      (eq
        (Term.mul (Term.succ (Term.numeral i)) (Term.var step))
        (Term.mul (Term.numeral (i + 1)) (Term.numeral s))) := by
    simpa [Term.numeral_succ] using
      (BProv_eq_congr_mul_right (Term.succ (Term.numeral i)) hstep)
  have hmulRaw : BProv Ax_s G
      (eq
        (Term.mul (Term.numeral (i + 1)) (Term.numeral s))
        (Term.numeral ((i + 1) * s))) :=
    BProv_weaken_nil (BProv_Ax_s_mulNumerals (i + 1) s)
  have hsucc : BProv Ax_s G
      (eq
        (Term.succ
          (Term.mul (Term.succ (Term.numeral i)) (Term.var step)))
        (Term.succ (Term.numeral ((i + 1) * s)))) :=
    BProv_eq_congr_succ (BProv_eqTrans hmulLeft hmulRaw)
  have hbeta : BetaModulus s i = (i + 1) * s + 1 := by
    unfold BetaModulus
    omega
  simpa [hbeta, Term.numeral_succ] using hsucc

/-- Constructor for the formula obtained by instantiating both the output and
index variables around a `betaAt` occurrence. -/
theorem BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst {G : List Formula}
    {code step o c s i q : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hlt : o < BetaModulus s i)
    (hval : q * BetaModulus s i + o = c) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral i))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (betaAt (0+1) ((code+1)+1) ((step+1)+1) 0))) := by
  let m := BetaModulus s i
  have hmodTerm : BProv Ax_s G
      (eq
        (Term.succ (Term.mul (Term.succ (Term.numeral i)) (Term.var step)))
        (Term.numeral m)) := by
    simpa [m] using BProv_Ax_s_betaModTerm_constIdx_of_eqConst
      (step := step) (s := s) (i := i) hstep
  have hmodBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral o))))
            (eq (Term.var 0)
              (Term.rename Nat.succ
                (betaModTerm ((step+1)+1) 0)))))) := by
    simpa [betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_subst_instTerm_rename_succ] using
      BProv_eqSym hmodTerm
  have hremRaw : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (remAt (0+1) (code+2) 0))) := by
    exact BProv_Ax_s_remAt_constRemMod_of_eqConst
      (value := code) (r := o) (v := c) (m := m) (q := q)
      hcode (by simpa [m] using hlt) (by simpa [m] using hval)
  have hremBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral o))))
            (remAt ((0+1)+1) (((code+1)+1)+1) 0)))) := by
    simpa [remAt, ltAt, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename]
      using hremRaw
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral o))))
            (and
              (eq (Term.var 0)
                (Term.rename Nat.succ
                  (betaModTerm ((step+1)+1) 0)))
              (remAt ((0+1)+1) (((code+1)+1)+1) 0))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hmodBody hremBody)
  simpa [betaAt, subst, instTerm, Term.subst, Term.upSubst, m] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral i)))
        (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral o))))
          (and
            (eq (Term.var 0)
              (Term.rename Nat.succ
                (betaModTerm ((step+1)+1) 0)))
            (remAt ((0+1)+1) (((code+1)+1)+1) 0))))
      (t := Term.numeral m) hbody)

/-- Constructor for the formula obtained by instantiating the index variable of
`betaAt` with a closed numeral. -/
theorem BProv_Ax_s_betaAt_constIdxSubst_of_eqConst {G : List Formula}
    {out code step o c s i q : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hlt : o < BetaModulus s i)
    (hval : q * BetaModulus s i + o = c) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral i)) (betaAt (out+1) (code+1) (step+1) 0)) := by
  let m := BetaModulus s i
  have hmodTerm : BProv Ax_s G
      (eq
        (Term.succ (Term.mul (Term.succ (Term.numeral i)) (Term.var step)))
        (Term.numeral m)) := by
    simpa [m] using BProv_Ax_s_betaModTerm_constIdx_of_eqConst
      (step := step) (s := s) (i := i) hstep
  have hmodBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (eq (Term.var 0)
            (Term.rename Nat.succ (betaModTerm (step+1) 0))))) := by
    simpa [betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_subst_instTerm_rename_succ] using
      BProv_eqSym hmodTerm
  have hremRaw : BProv Ax_s G
      (subst (instTerm (Term.numeral m)) (remAt (out+1) (code+1) 0)) := by
    exact BProv_Ax_s_remAt_constMod_of_eqConst
      (rem := out) (value := code) (r := o) (v := c) (m := m) (q := q)
      hout hcode (by simpa [m] using hlt) (by simpa [m] using hval)
  have hremBody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (remAt ((out+1)+1) ((code+1)+1) 0))) := by
    simpa [remAt, ltAt, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename]
      using hremRaw
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral m))
        (subst (Term.upSubst (instTerm (Term.numeral i)))
          (and
            (eq (Term.var 0)
              (Term.rename Nat.succ (betaModTerm (step+1) 0)))
            (remAt ((out+1)+1) ((code+1)+1) 0)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hmodBody hremBody)
  simpa [betaAt, subst, instTerm, Term.subst, Term.upSubst, m] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral i)))
        (and
          (eq (Term.var 0)
            (Term.rename Nat.succ (betaModTerm (step+1) 0)))
          (remAt ((out+1)+1) ((code+1)+1) 0)))
      (t := Term.numeral m) hbody)

/-- Constructor for `betaAtConstIdx` from fixed numeral proofs and an explicit
beta-entry quotient. -/
theorem BProv_Ax_s_betaAtConstIdx_of_eqConst {G : List Formula}
    {out code step o c s idxValue q : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hlt : o < BetaModulus s idxValue)
    (hval : q * BetaModulus s idxValue + o = c) :
    BProv Ax_s G (betaAtConstIdx out code step idxValue) := by
  have hidxBody : BProv Ax_s G
      (subst (instTerm (Term.numeral idxValue)) (eqConstAt 0 idxValue)) := by
    simpa [eqConstAt, subst, instTerm, Term.subst] using
      (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral idxValue))
  have hbetaBody : BProv Ax_s G
      (subst (instTerm (Term.numeral idxValue))
        (betaAt (out+1) (code+1) (step+1) 0)) :=
    BProv_Ax_s_betaAt_constIdxSubst_of_eqConst
      (out := out) (code := code) (step := step)
      (o := o) (c := c) (s := s) (i := idxValue) (q := q)
      hout hcode hstep hlt hval
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral idxValue))
        (and (eqConstAt 0 idxValue)
          (betaAt (out+1) (code+1) (step+1) 0))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hidxBody hbetaBody)
  simpa [betaAtConstIdx] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := and (eqConstAt 0 idxValue)
        (betaAt (out+1) (code+1) (step+1) 0))
      (t := Term.numeral idxValue) hbody)

/-- Constructor for `betaAtSuccIdx` from fixed numeral proofs and an explicit
beta-entry quotient at the successor index. -/
theorem BProv_Ax_s_betaAtSuccIdx_of_eqConst {G : List Formula}
    {out code step idx o c s i q : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hlt : o < BetaModulus s (i + 1))
    (hval : q * BetaModulus s (i + 1) + o = c) :
    BProv Ax_s G (betaAtSuccIdx out code step idx) := by
  have hidxSucc : BProv Ax_s G
      (eq (Term.numeral (i + 1)) (Term.succ (Term.var idx))) := by
    have hs : BProv Ax_s G
        (eq (Term.succ (Term.var idx)) (Term.numeral (i + 1))) := by
      simpa [Term.numeral_succ] using BProv_eq_congr_succ hidx
    exact BProv_eqSym hs
  have hidxBody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (eq (Term.var 0) (Term.succ (Term.var (idx+1))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename] using
      hidxSucc
  have hbetaBody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (betaAt (out+1) (code+1) (step+1) 0)) :=
    BProv_Ax_s_betaAt_constIdxSubst_of_eqConst
      (out := out) (code := code) (step := step)
      (o := o) (c := c) (s := s) (i := i + 1) (q := q)
      hout hcode hstep hlt hval
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (and
          (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
          (betaAt (out+1) (code+1) (step+1) 0))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hidxBody hbetaBody)
  simpa [betaAtSuccIdx] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := and
        (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
        (betaAt (out+1) (code+1) (step+1) 0))
      (t := Term.numeral (i + 1)) hbody)

/-- Constructor for the formula obtained by instantiating the output variable
of `betaAtSuccIdx` with a closed numeral. -/
theorem BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst
    {G : List Formula}
    {code step idx o c s i q : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hlt : o < BetaModulus s (i + 1))
    (hval : q * BetaModulus s (i + 1) + o = c) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral o))
        (betaAtSuccIdx 0 (code+1) (step+1) (idx+1))) := by
  have hidxSucc : BProv Ax_s G
      (eq (Term.numeral (i + 1)) (Term.succ (Term.var idx))) := by
    have hs : BProv Ax_s G
        (eq (Term.succ (Term.var idx)) (Term.numeral (i + 1))) := by
      simpa [Term.numeral_succ] using BProv_eq_congr_succ hidx
    exact BProv_eqSym hs
  have hidxBody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (eq (Term.var 0) (Term.succ (Term.var ((idx+1)+1)))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst, Term.rename] using
      hidxSucc
  have hbetaBody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (betaAt (0+1) ((code+1)+1) ((step+1)+1) 0))) :=
    BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst
      (code := code) (step := step)
      (o := o) (c := c) (s := s) (i := i + 1) (q := q)
      hcode hstep hlt hval
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral (i + 1)))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (and
            (eq (Term.var 0) (Term.succ (Term.var ((idx+1)+1))))
            (betaAt (0+1) ((code+1)+1) ((step+1)+1) 0)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hidxBody hbetaBody)
  simpa [betaAtSuccIdx, subst, instTerm, Term.subst, Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral o)))
        (and
          (eq (Term.var 0) (Term.succ (Term.var ((idx+1)+1))))
          (betaAt (0+1) ((code+1)+1) ((step+1)+1) 0)))
      (t := Term.numeral (i + 1)) hbody)

/-- Constructor for a beta-coded binary-halving witness from explicit beta
entry quotients and the closed binary-halving equation. -/
theorem BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst {G : List Formula}
    {code step idx c s i cur next bit qcur qnext : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hcurLt : cur < BetaModulus s i)
    (hcurVal : qcur * BetaModulus s i + cur = c)
    (hnextLt : next < BetaModulus s (i + 1))
    (hnextVal : qnext * BetaModulus s (i + 1) + next = c)
    (hbit : bit = 0 ∨ bit = 1)
    (hdiv : next + next + bit = cur) :
    BProv Ax_s G (betaDiv2StepWitnessAt code step idx) := by
  let body : Formula :=
    and
      (betaAt 2 (code+3) (step+3) (idx+3))
      (and
        (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
        (div2StepAt 2 1 0))
  have hcurBeta : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            (betaAt 2 (code+3) (step+3) (idx+3))))) := by
    simpa [betaAt, remAt, betaModTerm, ltAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_subst_instTerm_rename_succ] using
      (BProv_Ax_s_betaAt_constOutSubst_of_eqConst
        (code := code) (step := step) (idx := idx)
        (o := cur) (c := c) (s := s) (i := i) (q := qcur)
        hcode hstep hidx hcurLt hcurVal)
  have hnextBeta : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))))) := by
    simpa [betaAtSuccIdx, betaAt, remAt, betaModTerm, ltAt, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      term_subst_instTerm_rename_succ] using
      (BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst
        (code := code) (step := step) (idx := idx)
        (o := next) (c := c) (s := s) (i := i) (q := qnext)
        hcode hstep hidx hnextLt hnextVal)
  have hdivBody : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            (div2StepAt 2 1 0)))) :=
    BProv_Ax_s_div2StepAt_closedSubst hbit hdiv
  have htail : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            (and
              (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
              (div2StepAt 2 1 0))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hnextBeta hdivBody)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral bit))
        (subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            body))) := by
    simpa [body, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hcurBeta htail)
  have hbitEx : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          (ex body))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_exI (B := Ax_s) (G := G)
        (a := subst (Term.upSubst (instTerm (Term.numeral next)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral cur))))
            body))
        (t := Term.numeral bit) hbody)
  have hnextEx : BProv Ax_s G
      (subst (instTerm (Term.numeral cur))
        (ex (ex body))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_exI (B := Ax_s) (G := G)
        (a := subst (Term.upSubst (instTerm (Term.numeral cur)))
          (ex body))
        (t := Term.numeral next) hbitEx)
  simpa [betaDiv2StepWitnessAt, body, subst, instTerm, Term.subst,
    Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := ex (ex body))
      (t := Term.numeral cur) hnextEx)

/-- Constructor for `betaDiv2BitAt` from explicit beta-entry quotients and a
closed proof of the bit slot. -/
theorem BProv_Ax_s_betaDiv2BitAt_of_eqConst {G : List Formula}
    {bit code step idx b c s i cur next qcur qnext : Nat}
    (hbit : BProv Ax_s G (eqConstAt bit b))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hcurLt : cur < BetaModulus s i)
    (hcurVal : qcur * BetaModulus s i + cur = c)
    (hnextLt : next < BetaModulus s (i + 1))
    (hnextVal : qnext * BetaModulus s (i + 1) + next = c)
    (hb : b = 0 ∨ b = 1)
    (hdiv : next + next + b = cur) :
    BProv Ax_s G (betaDiv2BitAt bit code step idx) := by
  let body : Formula :=
    and
      (betaAt 1 (code+2) (step+2) (idx+2))
      (and
        (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
        (div2StepAt 1 0 (bit+2)))
  have hcurBeta : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          (betaAt 1 (code+2) (step+2) (idx+2)))) := by
    simpa [betaAt, remAt, betaModTerm, ltAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_subst_instTerm_rename_succ] using
      (BProv_Ax_s_betaAt_constOutSubst_of_eqConst
        (code := code) (step := step) (idx := idx)
        (o := cur) (c := c) (s := s) (i := i) (q := qcur)
        hcode hstep hidx hcurLt hcurVal)
  have hnextBeta : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          (betaAtSuccIdx 0 (code+2) (step+2) (idx+2)))) := by
    simpa [betaAtSuccIdx, betaAt, remAt, betaModTerm, ltAt, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      term_subst_instTerm_rename_succ] using
      (BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst
        (code := code) (step := step) (idx := idx)
        (o := next) (c := c) (s := s) (i := i) (q := qnext)
        hcode hstep hidx hnextLt hnextVal)
  have hdivBody : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          (div2StepAt 1 0 (bit+2)))) :=
    BProv_Ax_s_div2StepAt_constValueHalfSubst_of_eqConst
      (bit := bit) (b := b) (v := cur) (h := next)
      hbit hb hdiv
  have htail : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          (and
            (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
            (div2StepAt 1 0 (bit+2))))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hnextBeta hdivBody)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral next))
        (subst (Term.upSubst (instTerm (Term.numeral cur)))
          body)) := by
    simpa [body, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hcurBeta htail)
  have hnextEx : BProv Ax_s G
      (subst (instTerm (Term.numeral cur)) (ex body)) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_exI (B := Ax_s) (G := G)
        (a := subst (Term.upSubst (instTerm (Term.numeral cur))) body)
        (t := Term.numeral next) hbody)
  simpa [betaDiv2BitAt, body, subst, instTerm, Term.subst, Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := ex body)
      (t := Term.numeral cur) hnextEx)

/-- `BetaEntry`-packaged version of `BProv_Ax_s_betaAt_of_eqConst`. -/
theorem BProv_Ax_s_betaAt_of_eqConst_entry {G : List Formula}
    {out code step idx o c s i : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hentry : BetaEntry c s i o) :
    BProv Ax_s G (betaAt out code step idx) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAt_of_eqConst
    (out := out) (code := code) (step := step) (idx := idx)
    (o := o) (c := c) (s := s) (i := i) (q := q)
    hout hcode hstep hidx hlt hval.symm

/-- `BetaEntry`-packaged version of
`BProv_Ax_s_betaAt_constOutSubst_of_eqConst`. -/
theorem BProv_Ax_s_betaAt_constOutSubst_of_eqConst_entry
    {G : List Formula}
    {code step idx o c s i : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hentry : BetaEntry c s i o) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral o))
        (betaAt 0 (code+1) (step+1) (idx+1))) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAt_constOutSubst_of_eqConst
    (code := code) (step := step) (idx := idx)
    (o := o) (c := c) (s := s) (i := i) (q := q)
    hcode hstep hidx hlt hval.symm

/-- `BetaEntry`-packaged version of
`BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst`. -/
theorem BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst_entry
    {G : List Formula}
    {code step o c s i : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hentry : BetaEntry c s i o) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral i))
        (subst (Term.upSubst (instTerm (Term.numeral o)))
          (betaAt (0+1) ((code+1)+1) ((step+1)+1) 0))) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAt_constOutIdxSubst_of_eqConst
    (code := code) (step := step)
    (o := o) (c := c) (s := s) (i := i) (q := q)
    hcode hstep hlt hval.symm

/-- `BetaEntry`-packaged version of
`BProv_Ax_s_betaAtConstIdx_of_eqConst`. -/
theorem BProv_Ax_s_betaAtConstIdx_of_eqConst_entry {G : List Formula}
    {out code step o c s idxValue : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hentry : BetaEntry c s idxValue o) :
    BProv Ax_s G (betaAtConstIdx out code step idxValue) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAtConstIdx_of_eqConst
    (out := out) (code := code) (step := step)
    (o := o) (c := c) (s := s) (idxValue := idxValue) (q := q)
    hout hcode hstep hlt hval.symm

/-- `BetaEntry`-packaged version of
`BProv_Ax_s_betaAtSuccIdx_of_eqConst`. -/
theorem BProv_Ax_s_betaAtSuccIdx_of_eqConst_entry {G : List Formula}
    {out code step idx o c s i : Nat}
    (hout : BProv Ax_s G (eqConstAt out o))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hentry : BetaEntry c s (i + 1) o) :
    BProv Ax_s G (betaAtSuccIdx out code step idx) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAtSuccIdx_of_eqConst
    (out := out) (code := code) (step := step) (idx := idx)
    (o := o) (c := c) (s := s) (i := i) (q := q)
    hout hcode hstep hidx hlt hval.symm

/-- `BetaEntry`-packaged version of
`BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst`. -/
theorem BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst_entry
    {G : List Formula}
    {code step idx o c s i : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hentry : BetaEntry c s (i + 1) o) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral o))
        (betaAtSuccIdx 0 (code+1) (step+1) (idx+1))) := by
  rcases hentry with ⟨q, hval, hlt⟩
  exact BProv_Ax_s_betaAtSuccIdx_constOutSubst_of_eqConst
    (code := code) (step := step) (idx := idx)
    (o := o) (c := c) (s := s) (i := i) (q := q)
    hcode hstep hidx hlt hval.symm

/-- `BetaDiv2Step`-packaged version of
`BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst`. -/
theorem BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst_step
    {G : List Formula}
    {code step idx c s i cur next bit : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hdivStep : BetaDiv2Step c s i cur next bit) :
    BProv Ax_s G (betaDiv2StepWitnessAt code step idx) := by
  rcases hdivStep with ⟨hcur, hnext, hbit, hdiv⟩
  rcases hcur with ⟨qcur, hcurVal, hcurLt⟩
  rcases hnext with ⟨qnext, hnextVal, hnextLt⟩
  exact BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst
    (code := code) (step := step) (idx := idx)
    (c := c) (s := s) (i := i) (cur := cur) (next := next)
    (bit := bit) (qcur := qcur) (qnext := qnext)
    hcode hstep hidx hcurLt hcurVal.symm hnextLt hnextVal.symm
    hbit hdiv.symm

/-- `BetaDiv2Step`-packaged version of
`BProv_Ax_s_betaDiv2BitAt_of_eqConst`. -/
theorem BProv_Ax_s_betaDiv2BitAt_of_eqConst_step {G : List Formula}
    {bit code step idx b c s i cur next : Nat}
    (hbit : BProv Ax_s G (eqConstAt bit b))
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hidx : BProv Ax_s G (eqConstAt idx i))
    (hdivStep : BetaDiv2Step c s i cur next b) :
    BProv Ax_s G (betaDiv2BitAt bit code step idx) := by
  rcases hdivStep with ⟨hcur, hnext, hb, hdiv⟩
  rcases hcur with ⟨qcur, hcurVal, hcurLt⟩
  rcases hnext with ⟨qnext, hnextVal, hnextLt⟩
  exact BProv_Ax_s_betaDiv2BitAt_of_eqConst
    (bit := bit) (code := code) (step := step) (idx := idx)
    (b := b) (c := c) (s := s) (i := i) (cur := cur) (next := next)
    (qcur := qcur) (qnext := qnext)
    hbit hcode hstep hidx hcurLt hcurVal.symm hnextLt hnextVal.symm
    hb hdiv.symm

/-- Once a `betaDiv2BitAt` body has been opened, a zero current value and a
one output bit contradict the embedded binary-halving step. -/
theorem BProv_Ax_s_betaDiv2BitAt_body_zero_one_bot {G : List Formula}
    {bit code step idx : Nat}
    (hcurZero : BProv Ax_s G (eqConstAt 1 0))
    (hbitOne : BProv Ax_s G (eqConstAt (bit+2) 1))
    (hbody : BProv Ax_s G
      (and
        (betaAt 1 (code+2) (step+2) (idx+2))
        (and
          (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
          (div2StepAt 1 0 (bit+2))))) :
    BProv Ax_s G bot := by
  have htail : BProv Ax_s G
      (and
        (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
        (div2StepAt 1 0 (bit+2))) :=
    BProv_andE2 hbody
  have hstep : BProv Ax_s G (div2StepAt 1 0 (bit+2)) :=
    BProv_andE2 htail
  exact BProv_Ax_s_div2StepAt_zero_one_bot
    (value := 1) (half := 0) (bit := bit+2)
    hcurZero hbitOne hstep

/-- Eliminate a final-bit formula to contradiction once the opened current
witness can be proved to be zero.  The `hcurZero` premise is deliberately a
proof obligation over the opened existential context: later trace-invariant
lemmas can provide it without changing the membership definition. -/
theorem BProv_Ax_s_betaDiv2BitAt_current_zero_bot {G : List Formula}
    {bit code step idx : Nat}
    (hbitOne : BProv Ax_s G (eqConstAt bit 1))
    (hcurZero :
      let body : Formula :=
        and
          (betaAt 1 (code+2) (step+2) (idx+2))
          (and
            (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
            (div2StepAt 1 0 (bit+2)))
      BProv Ax_s
        (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
        (eqConstAt 1 0))
    (hbitAt : BProv Ax_s G (betaDiv2BitAt bit code step idx)) :
    BProv Ax_s G bot := by
  let body : Formula :=
    and
      (betaAt 1 (code+2) (step+2) (idx+2))
      (and
        (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
        (div2StepAt 1 0 (bit+2)))
  have hbitRen1 : BProv Ax_s (G.map (rename Nat.succ))
      (eqConstAt (bit+1) 1) := by
    simpa [eqConstAt, rename, Term.rename] using
      (BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbitOne Nat.succ)
  have hbitRen2 : BProv Ax_s ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (eqConstAt (bit+2) 1) := by
    simpa [eqConstAt, rename, Term.rename] using
      (BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbitRen1 Nat.succ)
  have houter : BProv Ax_s (ex body :: G.map (rename Nat.succ)) bot := by
    have hex : BProv Ax_s (ex body :: G.map (rename Nat.succ)) (ex body) :=
      BProv_ass (B := Ax_s)
        (G := ex body :: G.map (rename Nat.succ)) (by simp)
    have hinner : BProv Ax_s
        (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
        bot := by
      have hbody : BProv Ax_s
          (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
          body :=
        BProv_ass (B := Ax_s)
          (G := body ::
            (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
          (by simp)
      have hbitCtx : BProv Ax_s
          (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
          (eqConstAt (bit+2) 1) := by
        simpa using BProv_context_cons
          (BProv_context_cons (B := Ax_s) hbitRen2)
      exact BProv_Ax_s_betaDiv2BitAt_body_zero_one_bot
        (bit := bit) (code := code) (step := step) (idx := idx)
        (by simpa [body] using hcurZero) hbitCtx (by simpa [body] using hbody)
    exact BProv_exE_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hex (by simpa [rename] using hinner)
  have hbitAt' : BProv Ax_s G (ex (ex body)) := by
    simpa [betaDiv2BitAt, body] using hbitAt
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hbitAt' (by simpa [rename] using houter)

/-- Base bounded-trace constructor: if the trace bound is `0`, the quantified
index in `betaDiv2StepsThroughAt` is forced to be `0`, so one pointwise
`BetaDiv2Step` supplies the whole bounded trace. -/
theorem BProv_Ax_s_betaDiv2StepsThroughAt_zero_of_eqConst_step
    {G : List Formula}
    {code step last c s cur next bit : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hlast : BProv Ax_s G (eqConstAt last 0))
    (hdivStep : BetaDiv2Step c s 0 cur next bit) :
    BProv Ax_s G (betaDiv2StepsThroughAt code step last) := by
  let leHyp : Formula := leAt 0 (last+1)
  have hle : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) leHyp :=
    BProv_ass (B := Ax_s) (G := leHyp :: G.map (rename Nat.succ))
      (by simp)
  have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt code c)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hcode Nat.succ
  have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt step s)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstep Nat.succ
  have hlastRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt last 0)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hlast Nat.succ
  have hcodeBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (code+1) c) := by
    simpa [eqConstAt, rename, Term.rename] using BProv_context_cons hcodeRen
  have hstepBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (step+1) s) := by
    simpa [eqConstAt, rename, Term.rename] using BProv_context_cons hstepRen
  have hlastBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (last+1) 0) := by
    simpa [eqConstAt, rename, Term.rename] using BProv_context_cons hlastRen
  have hidxZero : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt 0 0) :=
    BProv_Ax_s_eqConstAt_zero_of_leAt_eqConst_zero hle hlastBody
  have hwitness : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (betaDiv2StepWitnessAt (code+1) (step+1) 0) :=
    BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst_step
      (code := code+1) (step := step+1) (idx := 0)
      (c := c) (s := s) (i := 0)
      (cur := cur) (next := next) (bit := bit)
      hcodeBody hstepBody hidxZero hdivStep
  have himp : BProv Ax_s (G.map (rename Nat.succ))
      (imp leHyp (betaDiv2StepWitnessAt (code+1) (step+1) 0)) :=
    BProv_impI hwitness
  simpa [betaDiv2StepsThroughAt, leHyp] using
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp

/-- Closed-bound base trace constructor.  With standard bound `0`, the
quantified index is forced to be `0`, so one pointwise `BetaDiv2Step` supplies
the whole closed bounded trace. -/
theorem BProv_Ax_s_betaDiv2StepsThroughConstAt_zero_of_eqConst_step
    {G : List Formula}
    {code step c s cur next bit : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hdivStep : BetaDiv2Step c s 0 cur next bit) :
    BProv Ax_s G (betaDiv2StepsThroughConstAt code step 0) := by
  let leHyp : Formula := leConstAt 0 0
  have hle : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) leHyp :=
    BProv_ass (B := Ax_s) (G := leHyp :: G.map (rename Nat.succ))
      (by simp)
  have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt code c)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hcode Nat.succ
  have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt step s)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstep Nat.succ
  have hcodeBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (code+1) c) := by
    simpa [eqConstAt, rename, Term.rename] using BProv_context_cons hcodeRen
  have hstepBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (step+1) s) := by
    simpa [eqConstAt, rename, Term.rename] using BProv_context_cons hstepRen
  have hidxZero : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt 0 0) :=
    BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero hle
  have hwitness : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (betaDiv2StepWitnessAt (code+1) (step+1) 0) :=
    BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst_step
      (code := code+1) (step := step+1) (idx := 0)
      (c := c) (s := s) (i := 0)
      (cur := cur) (next := next) (bit := bit)
      hcodeBody hstepBody hidxZero hdivStep
  have himp : BProv Ax_s (G.map (rename Nat.succ))
      (imp leHyp (betaDiv2StepWitnessAt (code+1) (step+1) 0)) :=
    BProv_impI hwitness
  simpa [betaDiv2StepsThroughConstAt, leHyp] using
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp

/-- Closed-bound successor trace constructor.  The proof splits a closed
standard bound `i ≤ n+1` into `i ≤ n` or `i = n+1`; the first branch reuses the
previous closed trace, and the second branch uses the supplied pointwise
halving step at the new endpoint. -/
theorem BProv_Ax_s_betaDiv2StepsThroughConstAt_succ_of_eqConst_step
    {G : List Formula}
    {code step c s n cur next bit : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hprev : BProv Ax_s G (betaDiv2StepsThroughConstAt code step n))
    (hdivStep : BetaDiv2Step c s (n+1) cur next bit) :
    BProv Ax_s G (betaDiv2StepsThroughConstAt code step (n+1)) := by
  let leHyp : Formula := leConstAt 0 (n+1)
  let witness : Formula := betaDiv2StepWitnessAt (code+1) (step+1) 0
  have hle : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) leHyp :=
    BProv_ass (B := Ax_s) (G := leHyp :: G.map (rename Nat.succ))
      (by simp)
  have hcases : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (or (leConstAt 0 n) (eqConstAt 0 (n+1))) :=
    BProv_Ax_s_leConstAt_succ_cases hle
  have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt code c)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hcode Nat.succ
  have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt step s)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstep Nat.succ
  have hprevRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughConstAt code step n)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hprev Nat.succ
  have hleft : BProv Ax_s
      (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ)) witness := by
    have hprevAll : BProv Ax_s
        (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
        (betaDiv2StepsThroughConstAt (code+1) (step+1) n) := by
      have hprevCtx : BProv Ax_s
          (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
          (rename Nat.succ (betaDiv2StepsThroughConstAt code step n)) :=
        BProv_context_cons (BProv_context_cons hprevRen)
      simpa [betaDiv2StepsThroughConstAt, betaDiv2StepWitnessAt,
        betaAtSuccIdx, betaAt, remAt, ltAt, div2StepAt, boolAt,
        zeroAt, oneAt, eqConstAt, leConstAt, betaModTerm,
        rename, Term.rename, SetTheory.up] using
        hprevCtx
    have himpRaw := BProv_allE (B := Ax_s)
      (G := leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
      (t := Term.var 0) hprevAll
    have himp : BProv Ax_s
        (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
        (imp (leConstAt 0 n) witness) := by
      simpa [witness, betaDiv2StepsThroughConstAt, leConstAt,
        betaDiv2StepWitnessAt, betaAtSuccIdx, betaAt, remAt, ltAt,
        div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm,
        subst, instTerm, Term.subst, Term.upSubst, Term.rename,
        term_subst_instTerm_rename_succ] using himpRaw
    have hleN : BProv Ax_s
        (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
        (leConstAt 0 n) :=
      BProv_ass (B := Ax_s)
        (G := leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
        (by simp)
    exact BProv_mp Ax_s
      (leConstAt 0 n :: leHyp :: G.map (rename Nat.succ))
      (leConstAt 0 n) witness himp hleN
  have hright : BProv Ax_s
      (eqConstAt 0 (n+1) :: leHyp :: G.map (rename Nat.succ)) witness := by
    have hidx : BProv Ax_s
        (eqConstAt 0 (n+1) :: leHyp :: G.map (rename Nat.succ))
        (eqConstAt 0 (n+1)) :=
      BProv_ass (B := Ax_s)
        (G := eqConstAt 0 (n+1) :: leHyp :: G.map (rename Nat.succ))
        (by simp)
    have hcodeBody : BProv Ax_s
        (eqConstAt 0 (n+1) :: leHyp :: G.map (rename Nat.succ))
        (eqConstAt (code+1) c) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_context_cons (BProv_context_cons hcodeRen)
    have hstepBody : BProv Ax_s
        (eqConstAt 0 (n+1) :: leHyp :: G.map (rename Nat.succ))
        (eqConstAt (step+1) s) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_context_cons (BProv_context_cons hstepRen)
    simpa [witness] using
      BProv_Ax_s_betaDiv2StepWitnessAt_of_eqConst_step
        (code := code+1) (step := step+1) (idx := 0)
        (c := c) (s := s) (i := n+1)
        (cur := cur) (next := next) (bit := bit)
        hcodeBody hstepBody hidx hdivStep
  have hbody : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) witness :=
    BProv_orE (B := Ax_s) (G := leHyp :: G.map (rename Nat.succ))
      (a := leConstAt 0 n) (b := eqConstAt 0 (n+1))
      (c := witness) hcases hleft hright
  have himp : BProv Ax_s (G.map (rename Nat.succ))
      (imp leHyp witness) :=
    BProv_impI hbody
  simpa [betaDiv2StepsThroughConstAt, leHyp, witness] using
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp

/-- Convert a closed-standard bounded trace into the ordinary variable-bound
trace once the variable bound is proved to contain that standard numeral. -/
theorem BProv_Ax_s_betaDiv2StepsThroughAt_of_const_eqConst
    {G : List Formula}
    {code step last n : Nat}
    (hconst : BProv Ax_s G (betaDiv2StepsThroughConstAt code step n))
    (hlast : BProv Ax_s G (eqConstAt last n)) :
    BProv Ax_s G (betaDiv2StepsThroughAt code step last) := by
  let leHyp : Formula := leAt 0 (last+1)
  let witness : Formula := betaDiv2StepWitnessAt (code+1) (step+1) 0
  have hle : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) leHyp :=
    BProv_ass (B := Ax_s) (G := leHyp :: G.map (rename Nat.succ))
      (by simp)
  have hlastRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt last n)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hlast Nat.succ
  have hconstRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughConstAt code step n)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hconst Nat.succ
  have hlastBody : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (eqConstAt (last+1) n) := by
    simpa [eqConstAt, rename, Term.rename] using
      BProv_context_cons hlastRen
  have hleConst : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (leConstAt 0 n) :=
    BProv_Ax_s_leConstAt_of_leAt_eqConst hle hlastBody
  have hconstAll : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (betaDiv2StepsThroughConstAt (code+1) (step+1) n) := by
    have hctx : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
        (rename Nat.succ (betaDiv2StepsThroughConstAt code step n)) :=
      BProv_context_cons hconstRen
    simpa [betaDiv2StepsThroughConstAt, betaDiv2StepWitnessAt,
      betaAtSuccIdx, betaAt, remAt, ltAt, div2StepAt, boolAt,
      zeroAt, oneAt, eqConstAt, leConstAt, betaModTerm,
      rename, Term.rename, SetTheory.up] using hctx
  have himpRaw := BProv_allE (B := Ax_s)
    (G := leHyp :: G.map (rename Nat.succ))
    (t := Term.var 0) hconstAll
  have himp : BProv Ax_s (leHyp :: G.map (rename Nat.succ))
      (imp (leConstAt 0 n) witness) := by
    simpa [witness, betaDiv2StepsThroughConstAt, leConstAt,
      betaDiv2StepWitnessAt, betaAtSuccIdx, betaAt, remAt, ltAt,
      div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm,
      subst, instTerm, Term.subst, Term.upSubst, Term.rename,
      term_subst_instTerm_rename_succ] using himpRaw
  have hwitness : BProv Ax_s (leHyp :: G.map (rename Nat.succ)) witness :=
    BProv_mp Ax_s (leHyp :: G.map (rename Nat.succ))
      (leConstAt 0 n) witness himp hleConst
  have hfinal : BProv Ax_s (G.map (rename Nat.succ))
      (imp leHyp witness) :=
    BProv_impI hwitness
  simpa [betaDiv2StepsThroughAt, leHyp, witness] using
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hfinal

/-- Build a closed-standard bounded beta-halving trace from a semantic finite
trace, by induction on the standard bound. -/
theorem BProv_Ax_s_betaDiv2StepsThroughConstAt_of_eqConst_trace
    {G : List Formula}
    {code step c s n : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s)) :
    BetaDiv2StepsThrough c s n →
      BProv Ax_s G (betaDiv2StepsThroughConstAt code step n) := by
  induction n with
  | zero =>
      intro htrace
      rcases htrace 0 (by omega) with ⟨cur, next, bit, hdivStep⟩
      exact BProv_Ax_s_betaDiv2StepsThroughConstAt_zero_of_eqConst_step
        (code := code) (step := step) (c := c) (s := s)
        (cur := cur) (next := next) (bit := bit)
        hcode hstep hdivStep
  | succ n ih =>
      intro htrace
      have hprevTrace : BetaDiv2StepsThrough c s n := by
        intro k hk
        exact htrace k (by omega)
      have hprev : BProv Ax_s G
          (betaDiv2StepsThroughConstAt code step n) :=
        ih hprevTrace
      rcases htrace (n+1) (by omega) with ⟨cur, next, bit, hdivStep⟩
      exact BProv_Ax_s_betaDiv2StepsThroughConstAt_succ_of_eqConst_step
        (code := code) (step := step) (c := c) (s := s)
        (n := n) (cur := cur) (next := next) (bit := bit)
        hcode hstep hprev hdivStep

/-- Build the ordinary variable-bound beta-halving trace from a semantic trace
and a proof that the variable bound contains the corresponding numeral. -/
theorem BProv_Ax_s_betaDiv2StepsThroughAt_of_eqConst_trace
    {G : List Formula}
    {code step last c s n : Nat}
    (hcode : BProv Ax_s G (eqConstAt code c))
    (hstep : BProv Ax_s G (eqConstAt step s))
    (hlast : BProv Ax_s G (eqConstAt last n))
    (htrace : BetaDiv2StepsThrough c s n) :
    BProv Ax_s G (betaDiv2StepsThroughAt code step last) :=
  BProv_Ax_s_betaDiv2StepsThroughAt_of_const_eqConst
    (BProv_Ax_s_betaDiv2StepsThroughConstAt_of_eqConst_trace
      (code := code) (step := step) (c := c) (s := s) (n := n)
      hcode hstep htrace)
    hlast

/-- Package the innermost membership bit witness.  The premise is only the
closed, code/step-instantiated `betaDiv2BitAt` component; the constructor adds
the explicit proof that the witness bit is the numeral `1`. -/
theorem BProv_Ax_s_hfMemAt_bitOneEx_of_bit {G : List Formula}
    {elem code step : Nat}
    (hbit : BProv Ax_s G
      (subst (instTerm (Term.numeral 1))
        (subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            (betaDiv2BitAt 0 2 1 (elem+3)))))) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (ex
            (and
              (oneAt 0)
              (betaDiv2BitAt 0 2 1 (elem+3)))))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  have hone : BProv Ax_s G
      (subst (instTerm (Term.numeral 1))
        (subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            (oneAt 0)))) := by
    simpa [oneAt, eqConstAt, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename] using
      (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral 1))
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral 1))
        (subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            bitBody))) := by
    simpa [bitBody, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hone hbit)
  simpa [bitBody, subst, instTerm, Term.subst, Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a :=
        subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            bitBody))
      (t := Term.numeral 1) hbody)

/-- Introduce the PA formula for HF membership from its three closed trace
components: the zero-index beta entry for the set code, the still-explicit
bounded halving trace, and the final bit witness existential. -/
theorem BProv_Ax_s_hfMemAt_of_closed_components {G : List Formula}
    {elem set code step : Nat}
    (hentry : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaAtConstIdx (set+2) 1 0 0))))
    (hsteps : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaDiv2StepsThroughAt 1 0 (elem+2)))))
    (hbitEx : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (ex
            (and
              (oneAt 0)
              (betaDiv2BitAt 0 2 1 (elem+3))))))) :
    BProv Ax_s G (hfMemAt elem set) := by
  let bitEx : Formula :=
    ex
      (and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3)))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      bitEx
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  have htail : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          tail)) := by
    simpa [tail, bitEx, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hsteps hbitEx)
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          body)) := by
    simpa [body, tail, bitEx, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_andI hentry htail)
  have hstepEx : BProv Ax_s G
      (subst (instTerm (Term.numeral code)) (ex body)) := by
    simpa [body, subst, instTerm, Term.subst, Term.upSubst] using
      (BProv_exI (B := Ax_s) (G := G)
        (a := subst (Term.upSubst (instTerm (Term.numeral code))) body)
        (t := Term.numeral step) hbody)
  simpa [hfMemAt, body, tail, bitEx, subst, instTerm, Term.subst,
    Term.upSubst] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := ex body)
      (t := Term.numeral code) hstepEx)

/-- Membership-introduction variant that takes the final bit component before
the inner witness bit has been existentially packaged. -/
theorem BProv_Ax_s_hfMemAt_of_closed_bit_components {G : List Formula}
    {elem set code step : Nat}
    (hentry : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaAtConstIdx (set+2) 1 0 0))))
    (hsteps : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaDiv2StepsThroughAt 1 0 (elem+2)))))
    (hbit : BProv Ax_s G
      (subst (instTerm (Term.numeral 1))
        (subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            (betaDiv2BitAt 0 2 1 (elem+3)))))) :
    BProv Ax_s G (hfMemAt elem set) := by
  exact BProv_Ax_s_hfMemAt_of_closed_components
    (elem := elem) (set := set) (code := code) (step := step)
    hentry hsteps
    (BProv_Ax_s_hfMemAt_bitOneEx_of_bit
      (elem := elem) (code := code) (step := step) hbit)

/-- Produce the closed zero-index beta-entry component of `hfMemAt` from an
ordinary proof that the set slot contains the intended numeral and the semantic
`BetaEntry` record for index `0`. -/
theorem BProv_Ax_s_hfMemAt_entryComponent_of_eqConst_entry
    {G : List Formula}
    {set setValue code step : Nat}
    (hset : BProv Ax_s G (eqConstAt set setValue))
    (hentry : BetaEntry code step 0 setValue) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaAtConstIdx (set+2) 1 0 0))) := by
  let H : List Formula :=
    [eqConstAt (set+2) setValue, eqConstAt 1 code, eqConstAt 0 step]
  let σcode : Nat → Term := Term.upSubst (instTerm (Term.numeral code))
  let σstep : Nat → Term := instTerm (Term.numeral step)
  have hsetH : BProv Ax_s H (eqConstAt (set+2) setValue) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hcodeH : BProv Ax_s H (eqConstAt 1 code) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hstepH : BProv Ax_s H (eqConstAt 0 step) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hopen : BProv Ax_s H (betaAtConstIdx (set+2) 1 0 0) :=
    BProv_Ax_s_betaAtConstIdx_of_eqConst_entry
      (out := set+2) (code := 1) (step := 0)
      (o := setValue) (c := code) (s := step) (idxValue := 0)
      hsetH hcodeH hstepH hentry
  have hsubstCode : BProv Ax_s (H.map (subst σcode))
      (subst σcode (betaAtConstIdx (set+2) 1 0 0)) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hopen σcode
  have hsubst : BProv Ax_s ((H.map (subst σcode)).map (subst σstep))
      (subst σstep
        (subst σcode (betaAtConstIdx (set+2) 1 0 0))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsubstCode σstep
  have hclosed := BProv_cut hsubst (D := G) (fun g hg => by
    simp [H, σcode, σstep, eqConstAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename] at hg
    rcases hg with rfl | rfl | rfl
    · simpa [eqConstAt] using hset
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral code))
    · simpa [eqConstAt] using
      (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral step)))
  simpa [σcode, σstep] using hclosed

/-- Produce the closed final-bit beta component of `hfMemAt` from an ordinary
proof that the element slot contains the intended numeral and the semantic
halving-step record whose bit is `1`. -/
theorem BProv_Ax_s_hfMemAt_bitComponent_of_eqConst_bit
    {G : List Formula}
    {elem elemValue code step : Nat}
    (helem : BProv Ax_s G (eqConstAt elem elemValue))
    (hbit : BetaDiv2Bit code step elemValue 1) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral 1))
        (subst (Term.upSubst (instTerm (Term.numeral step)))
          (subst (Term.upSubst (Term.upSubst (instTerm (Term.numeral code))))
            (betaDiv2BitAt 0 2 1 (elem+3))))) := by
  rcases hbit with ⟨cur, next, hstepBit⟩
  let H : List Formula :=
    [eqConstAt (elem+3) elemValue, eqConstAt 2 code,
      eqConstAt 1 step, eqConstAt 0 1]
  let σcode : Nat → Term :=
    Term.upSubst (Term.upSubst (instTerm (Term.numeral code)))
  let σstep : Nat → Term := Term.upSubst (instTerm (Term.numeral step))
  let σbit : Nat → Term := instTerm (Term.numeral 1)
  have helemH : BProv Ax_s H (eqConstAt (elem+3) elemValue) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hcodeH : BProv Ax_s H (eqConstAt 2 code) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hstepH : BProv Ax_s H (eqConstAt 1 step) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hbitH : BProv Ax_s H (eqConstAt 0 1) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hopen : BProv Ax_s H (betaDiv2BitAt 0 2 1 (elem+3)) :=
    BProv_Ax_s_betaDiv2BitAt_of_eqConst_step
      (bit := 0) (code := 2) (step := 1) (idx := elem+3)
      (b := 1) (c := code) (s := step) (i := elemValue)
      (cur := cur) (next := next)
      hbitH hcodeH hstepH helemH hstepBit
  have hsubstCode : BProv Ax_s (H.map (subst σcode))
      (subst σcode (betaDiv2BitAt 0 2 1 (elem+3))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hopen σcode
  have hsubstStep : BProv Ax_s ((H.map (subst σcode)).map (subst σstep))
      (subst σstep
        (subst σcode (betaDiv2BitAt 0 2 1 (elem+3)))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsubstCode σstep
  have hsubst : BProv Ax_s
      (((H.map (subst σcode)).map (subst σstep)).map (subst σbit))
      (subst σbit
        (subst σstep
          (subst σcode (betaDiv2BitAt 0 2 1 (elem+3))))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsubstStep σbit
  have hclosed := BProv_cut hsubst (D := G) (fun g hg => by
    simp [H, σcode, σstep, σbit, eqConstAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simpa [eqConstAt] using helem
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral code))
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral step))
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral 1)))
  simpa [σcode, σstep, σbit] using hclosed

/-- Produce the closed bounded-trace component of `hfMemAt` from an ordinary
proof that the element slot contains the intended numeral and a semantic
halving trace through that element. -/
theorem BProv_Ax_s_hfMemAt_stepsComponent_of_eqConst_trace
    {G : List Formula}
    {elem elemValue code step : Nat}
    (helem : BProv Ax_s G (eqConstAt elem elemValue))
    (hthrough : BetaDiv2StepsThrough code step elemValue) :
    BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaDiv2StepsThroughAt 1 0 (elem+2)))) := by
  let H : List Formula :=
    [eqConstAt (elem+2) elemValue, eqConstAt 1 code,
      eqConstAt 0 step]
  let σcode : Nat → Term := Term.upSubst (instTerm (Term.numeral code))
  let σstep : Nat → Term := instTerm (Term.numeral step)
  have helemH : BProv Ax_s H (eqConstAt (elem+2) elemValue) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hcodeH : BProv Ax_s H (eqConstAt 1 code) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hstepH : BProv Ax_s H (eqConstAt 0 step) :=
    BProv_ass (B := Ax_s) (G := H) (by simp [H])
  have hopen : BProv Ax_s H (betaDiv2StepsThroughAt 1 0 (elem+2)) :=
    BProv_Ax_s_betaDiv2StepsThroughAt_of_eqConst_trace
      (code := 1) (step := 0) (last := elem+2)
      (c := code) (s := step) (n := elemValue)
      hcodeH hstepH helemH hthrough
  have hsubstCode : BProv Ax_s (H.map (subst σcode))
      (subst σcode (betaDiv2StepsThroughAt 1 0 (elem+2))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hopen σcode
  have hsubst : BProv Ax_s ((H.map (subst σcode)).map (subst σstep))
      (subst σstep
        (subst σcode (betaDiv2StepsThroughAt 1 0 (elem+2)))) :=
    BProv_subst_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsubstCode σstep
  have hclosed := BProv_cut hsubst (D := G) (fun g hg => by
    simp [H, σcode, σstep, eqConstAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename] at hg
    rcases hg with rfl | rfl | rfl
    · simpa [eqConstAt] using helem
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral code))
    · simpa [eqConstAt] using
        (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral step)))
  simpa [σcode, σstep] using hclosed

/-- HF-membership introduction from a semantic trace, with the bounded trace
component still supplied as an explicit PA proof obligation. -/
theorem BProv_Ax_s_hfMemAt_of_eqConst_trace_with_steps
    {G : List Formula}
    {elem set elemValue setValue code step : Nat}
    (helem : BProv Ax_s G (eqConstAt elem elemValue))
    (hset : BProv Ax_s G (eqConstAt set setValue))
    (hsteps : BProv Ax_s G
      (subst (instTerm (Term.numeral step))
        (subst (Term.upSubst (instTerm (Term.numeral code)))
          (betaDiv2StepsThroughAt 1 0 (elem+2)))))
    (htrace : HFMemTrace elemValue setValue code step) :
    BProv Ax_s G (hfMemAt elem set) := by
  rcases htrace with ⟨hentry, _hthrough, hbit⟩
  exact BProv_Ax_s_hfMemAt_of_closed_bit_components
    (elem := elem) (set := set) (code := code) (step := step)
    (BProv_Ax_s_hfMemAt_entryComponent_of_eqConst_entry
      (set := set) (setValue := setValue) (code := code) (step := step)
      hset hentry)
    hsteps
    (BProv_Ax_s_hfMemAt_bitComponent_of_eqConst_bit
      (elem := elem) (elemValue := elemValue) (code := code) (step := step)
      helem hbit)

/-- HF-membership introduction from a semantic trace.  The beta-coded bounded
trace component is built internally by the closed-bound trace constructors. -/
theorem BProv_Ax_s_hfMemAt_of_eqConst_trace
    {G : List Formula}
    {elem set elemValue setValue code step : Nat}
    (helem : BProv Ax_s G (eqConstAt elem elemValue))
    (hset : BProv Ax_s G (eqConstAt set setValue))
    (htrace : HFMemTrace elemValue setValue code step) :
    BProv Ax_s G (hfMemAt elem set) := by
  exact BProv_Ax_s_hfMemAt_of_eqConst_trace_with_steps
    (elem := elem) (set := set) (elemValue := elemValue)
    (setValue := setValue) (code := code) (step := step)
    helem hset
    (BProv_Ax_s_hfMemAt_stepsComponent_of_eqConst_trace
      (elem := elem) (elemValue := elemValue)
      (code := code) (step := step) helem htrace.2.1)
    htrace

/-- HF-membership introduction from the Ackermann membership relation on the
proved numerals. -/
theorem BProv_Ax_s_hfMemAt_of_eqConst_mem
    {G : List Formula}
    {elem set elemValue setValue : Nat}
    (helem : BProv Ax_s G (eqConstAt elem elemValue))
    (hset : BProv Ax_s G (eqConstAt set setValue))
    (hmem : AckermannHF.Mem elemValue setValue) :
    BProv Ax_s G (hfMemAt elem set) := by
  rcases HFMemTrace_exists_of_mem hmem with ⟨code, step, htrace⟩
  exact BProv_Ax_s_hfMemAt_of_eqConst_trace
    (elem := elem) (set := set) (elemValue := elemValue)
    (setValue := setValue) (code := code) (step := step)
    helem hset htrace

/-- PA proves every variable-renamed body of one of its sealed induction
schema instances. -/
theorem BProv_Ax_s_inductionForm_rename (phi : Formula) (r : Nat → Nat) :
    BProv Ax_s [] (rename r (inductionForm phi)) :=
  BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) r

/-- PA proves the unrenamed body of every induction schema instance. -/
theorem BProv_Ax_s_inductionForm (phi : Formula) :
    BProv Ax_s [] (inductionForm phi) := by
  simpa [rename_id] using
    BProv_Ax_s_inductionForm_rename phi (fun n : Nat => n)

/-- PA induction as a derived relative-proof rule in an arbitrary finite
context. -/
theorem BProv_Ax_s_induction_rule {G : List Formula} {phi : Formula}
    (hzero : BProv Ax_s G (subst substZero phi))
    (hsucc : BProv Ax_s G (all (imp phi (subst substSuccVar phi)))) :
    BProv Ax_s G (all phi) := by
  have hind_empty : BProv Ax_s [] (inductionForm phi) :=
    BProv_Ax_s_inductionForm phi
  have hind : BProv Ax_s G (inductionForm phi) :=
    BProv_mono Ax_s [] G (inductionForm phi)
      (fun x hx => by cases hx) hind_empty
  exact BProv_inductionForm_mp hind hzero hsucc

theorem sat_substZero {α : Type u} (M : Model α) (phi : Formula) (e : Nat → α) :
    Sat M e (subst substZero phi) ↔ Sat M (SetTheory.scons M.zero e) phi := by
  rw [Sat_subst]
  exact Sat_ext M phi (fun n => by cases n <;> rfl)

theorem sat_substSuccVar {α : Type u} (M : Model α) (phi : Formula)
    (e : Nat → α) (a : α) :
    Sat M (SetTheory.scons a e) (subst substSuccVar phi) ↔
      Sat M (SetTheory.scons (M.succ a) e) phi := by
  rw [Sat_subst]
  exact Sat_ext M phi (fun n => by cases n <;> rfl)

theorem sat_axiom {α : Type u} (M : Model α) (e : Nat → α) :
    ∀ f, Ax f → Sat M e f := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩
  · intro a b h
    exact M.succ_injective h
  · intro a h
    exact M.zero_not_succ a h
  · intro a
    exact M.add_zero a
  · intro a b
    exact M.add_succ a b
  · intro a
    exact M.mul_zero a
  · intro a b
    exact M.mul_succ a b
  · intro h a
    exact M.induction (fun x => Sat M (SetTheory.scons x e) phi)
      ((sat_substZero M phi e).mp h.1)
      (fun n ih => (sat_substSuccVar M phi e n).mp (h.2 n ih))
      a

theorem sat_axiom_s {α : Type u} (M : Model α) (e : Nat → α) :
    ∀ f, Ax_s f → Sat M e f := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩
  · exact (seal_valid M succInj).mpr (fun e => sat_axiom M e succInj (Or.inl rfl)) e
  · exact (seal_valid M zeroNotSucc).mpr
      (fun e => sat_axiom M e zeroNotSucc (Or.inr (Or.inl rfl))) e
  · exact (seal_valid M addZero).mpr
      (fun e => sat_axiom M e addZero (Or.inr (Or.inr (Or.inl rfl)))) e
  · exact (seal_valid M addSucc).mpr
      (fun e => sat_axiom M e addSucc (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) e
  · exact (seal_valid M mulZero).mpr
      (fun e => sat_axiom M e mulZero
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) e
  · exact (seal_valid M mulSucc).mpr
      (fun e => sat_axiom M e mulSucc
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) e
  · exact (seal_valid M (inductionForm phi)).mpr
      (fun e => sat_axiom M e (inductionForm phi)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨phi, rfl⟩))))))) e

/-- Granular PA proof obligations for the translated HF axioms.

This record intentionally contains proofs, not definitions: the Ackermann
membership translation remains fixed, and each field is one concrete PA theorem
that still has to be supplied by arithmetic reasoning. -/
structure TranslatedHFAxiomProofs where
  empty :
    BProv Ax_s [] (translateHFFormula (SetTheory.sealF AckermannHF.HF_empty_form))
  extensionality :
    BProv Ax_s [] (translateHFFormula
      (SetTheory.sealF AckermannHF.HF_extensionality_form))
  adjoin :
    BProv Ax_s [] (translateHFFormula (SetTheory.sealF AckermannHF.HF_adjoin_form))
  induction :
    ∀ phi : Form,
      BProv Ax_s [] (translateHFFormula
        (SetTheory.sealF (AckermannHF.HF_induction_form phi)))

/-- Granular PA proof obligations for the strengthened finite-HF theory. -/
structure TranslatedHFFinAxiomProofs extends TranslatedHFAxiomProofs where
  finite_induction :
    ∀ phi : Form,
      BProv Ax_s [] (translateHFFormula
        (SetTheory.sealF (AckermannHF.HF_finite_induction_form phi)))

/-- Assemble the translated-HF axiom predicate from its named PA proof
obligations. -/
theorem BProv_Ax_s_of_translatedHFAx_of_proofs
    (P : TranslatedHFAxiomProofs) {phi : Formula}
    (hphi : translatedHFAx phi) : BProv Ax_s [] phi := by
  rcases hphi with ⟨g, hg, rfl⟩
  rcases hg with rfl | rfl | rfl | ⟨psi, rfl⟩
  · exact P.empty
  · exact P.extensionality
  · exact P.adjoin
  · exact P.induction psi

/-- Assemble the translated finite-HF axiom predicate from its named PA proof
obligations. -/
theorem BProv_Ax_s_of_translatedHFFinAx_of_proofs
    (P : TranslatedHFFinAxiomProofs) {phi : Formula}
    (hphi : translatedHFFinAx phi) : BProv Ax_s [] phi := by
  rcases hphi with ⟨g, hg, rfl⟩
  rcases hg with hgHF | ⟨psi, rfl⟩
  · exact BProv_Ax_s_of_translatedHFAx_of_proofs
      P.toTranslatedHFAxiomProofs (translatedHFAx_intro hgHF)
  · exact P.finite_induction psi

end Formula

end PA

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
