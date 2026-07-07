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

theorem Sentences_HF : Sentences HFAx_s := by
  intro f hf
  rcases hf with rfl | rfl | rfl | ⟨phi, rfl⟩ <;> exact Sentence_seal _

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

/-- First-order semantic content of the sealed HF theory, without pretending
that first-order induction gives the second-order `AdjunctionModel.set_induction`
field. -/
structure FirstOrderHFModel (α : Type u) where
  mem : α → α → Prop
  extensional : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  empty_exists : ∃ e, ∀ x, ¬ mem x e
  adjoin_exists : ∀ a b, ∃ c, ∀ x, mem x c ↔ mem x a ∨ x = b
  induction_schema : ∀ phi e, Sat mem e (HF_induction_form phi)

def firstOrderHFModel_of_HFAx_s {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFAx_s g → Sat mem v g) :
    FirstOrderHFModel α where
  mem := mem
  extensional := semantic_extensionality_of_HFAx_s v hHF
  empty_exists := semantic_empty_of_HFAx_s v hHF
  adjoin_exists := semantic_adjoin_of_HFAx_s v hHF
  induction_schema := semantic_induction_schema_of_HFAx_s v hHF

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

theorem zeroGraph_domain (e : Nat → Nat)
    (hz : Sat Mem e zeroGraph) : Sat Mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hz' := (HF_emptyAt_empty standardModel e 0).mp hz
  rw [hz']
  exact OrdinalLike.empty standardModel

theorem succGraph_preserves_domain (e : Nat → Nat)
    (hin : Sat Mem e (HF_ordinalLikeAt 1))
    (hs : Sat Mem e succGraph) :
    Sat Mem e domainForm := by
  apply (HF_ordinalLikeAt_spec e 0).mpr
  have hin' := (HF_ordinalLikeAt_spec e 1).mp hin
  have hs' := (HF_succAt_spec standardModel e 0 1).mp hs
  exact OrdinalLike.adjoin_self standardModel hin' hs'

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

def numeralValue {α : Type u} (M : Model α) : Nat → α
  | 0 => M.zero
  | n+1 => M.succ (numeralValue M n)

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

theorem subst_instTerm_rename_up (phi : Formula) (r : Nat → Nat) (t : Term) :
    subst (instTerm (Term.rename r t)) (rename (SetTheory.up r) phi) =
      rename r (subst (instTerm t) phi) := by
  rw [subst_rename, rename_subst]
  exact subst_ext phi _ _ (fun n => by
    cases n with
    | zero => rfl
    | succ n => rfl)

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

/-- The PA-side theory consisting of syntactic translations of the sealed HF
axiom-scheme instances. -/
def translatedHFAx (phi : Formula) : Prop :=
  ∃ g, AckermannHF.HFAx_s g ∧ phi = translateHFFormula g

theorem translatedHFAx_intro {g : Form} (hg : AckermannHF.HFAx_s g) :
    translatedHFAx (translateHFFormula g) :=
  ⟨g, hg, rfl⟩

theorem Sentences_translatedHFAx : ∀ phi, translatedHFAx phi → Sentence phi := by
  intro phi hphi
  rcases hphi with ⟨g, hg, rfl⟩
  exact translated_HF_axiom_sentence g hg

theorem BProv_translatedHFAx_of_HFAx {g : Form} (hg : AckermannHF.HFAx_s g) :
    BProv translatedHFAx [] (translateHFFormula g) :=
  BProv_ax (translatedHFAx_intro hg)

theorem BProv_lift_translatedHFAx_to_PA
    (hAx : ∀ f, translatedHFAx f → BProv Ax_s [] f)
    {f : Formula} (h : BProv translatedHFAx [] f) : BProv Ax_s [] f :=
  BProv_lift h hAx (fun _ hg => nomatch hg)

theorem standard_sat_translatedHFAx (e : Nat → Nat) :
    ∀ g, translatedHFAx g → Sat natModel e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_HF_axiom_sat_nat phi hphi e

end Formula

namespace Formula

def substZero : Nat → Term
  | 0 => Term.zero
  | n+1 => Term.var n

def substSuccVar : Nat → Term
  | 0 => Term.succ (Term.var 0)
  | n+1 => Term.var (n+1)

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

theorem translated_PA_axiom_sentence (phi : PA.Formula)
    (hphi : PA.Formula.Ax_s phi) : Sentence (translateFormula phi) :=
  translateFormula_sentence_of_PA_sentence phi (PA.Formula.sentence_ax_s hphi)

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

theorem BProv_translatedPAAx_of_PAAx {phi : PA.Formula}
    (hphi : PA.Formula.Ax_s phi) :
    BProv translatedPAAx [] (translateFormula phi) :=
  BProv_ax (translatedPAAx_intro hphi)

theorem BProv_lift_translatedPAAx_to_HF
    (hAx : ∀ g, translatedPAAx g → BProv HFAx_s [] g)
    {g : Form} (h : BProv translatedPAAx [] g) : BProv HFAx_s [] g :=
  BProv_lift h hAx (fun _ hf => nomatch hf)

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

abbrev PAProvability :=
  (PA.Formula → Prop) → List PA.Formula → PA.Formula → Prop

/-- The exact target for the deductive PA/HF bi-interpretability theorem.

Unlike `StandardModelInterpretationCertificate`, this record is not inhabited
in this file.  It states the remaining proof obligations at the theory level:
both syntactic translations must transfer theorems between the PA axiom theory
and the HF axiom theory, and the two composites must be provably equivalent to
the identity translations on sentences. -/
structure DeductiveBiInterpretationCertificate (PAProv : PAProvability) where
  paInHf : TheoryInterpretation PA.Formula Form
    PA.Formula.Sentence Sentence
    PA.Formula.Ax_s HFAx_s
    PAProv BProv
  hfInPa : TheoryInterpretation Form PA.Formula
    Sentence PA.Formula.Sentence
    HFAx_s PA.Formula.Ax_s
    BProv PAProv
  pa_roundTrip : ∀ (phi : PA.Formula), phi.Sentence →
    PAProv PA.Formula.Ax_s []
      (PA.Formula.iffForm phi (hfInPa.translate (paInHf.translate phi)))
  hf_roundTrip : ∀ (phi : Form), Sentence phi →
    BProv HFAx_s []
      (fIff phi (paInHf.translate (hfInPa.translate phi)))

/-- The concrete deductive target using the PA natural-deduction calculus
defined above and the existing HF calculus from `SetTheory.Completeness`. -/
abbrev PAHFDeductiveBiInterpretationCertificate : Type :=
  DeductiveBiInterpretationCertificate PA.Formula.BProv

/-- A standard-model interpretation certificate with the actual syntactic
translations attached.  The exactness fields say that the translations have the
intended semantics in the standard PA and Ackermann-HF models; the axiom fields
say that each translated axiom theory is satisfied by the opposite standard
model; the `shallow` field carries the two round-trip isomorphisms. -/
structure StandardModelInterpretationCertificate where
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
  hfAxiom_sat : ∀ (phi : Form), HFAx_s phi → ∀ (v : Nat → Nat),
    PA.Formula.Sat PA.natModel v (hfToPa phi)
  translatedPA_sat : ∀ (e : Nat → Nat) (g : Form),
    PAInHF.translatedPAAx g → Sat Mem e g
  translatedHF_sat : ∀ (e : Nat → Nat) (f : PA.Formula),
    PA.Formula.translatedHFAx f → PA.Formula.Sat PA.natModel e f

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

theorem PA_standard_model_interpretable_with_HF :
    Nonempty StandardModelInterpretationCertificate :=
  ⟨standardModelInterpretation⟩

theorem PA_biinterpretable_with_HF_standard :
    Nonempty (PA.Iso PA.natModel ordinalPAModel) ∧
      Nonempty (AdjunctionIso standardModel ordinalHFModel) :=
  ⟨⟨standardShallowBiInterpretation.paRoundTrip⟩,
   ⟨standardShallowBiInterpretation.hfRoundTrip⟩⟩

end AckermannHF

end SetTheory
