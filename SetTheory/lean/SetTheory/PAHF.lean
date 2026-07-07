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
import SetTheory.Fol

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
  f = HF_empty_form ∨ f = HF_adjoin_form ∨ ∃ phi, f = HF_induction_form phi

/-- The sentence theory of HF, with every schema instance universally closed. -/
def HFAx_s (f : Form) : Prop :=
  f = sealF HF_empty_form ∨
  f = sealF HF_adjoin_form ∨
  ∃ phi, f = sealF (HF_induction_form phi)

theorem Sentences_HF : Sentences HFAx_s := by
  intro f hf
  rcases hf with rfl | rfl | ⟨phi, rfl⟩ <;> exact Sentence_seal _

theorem sat_HF_empty {α : Type} (M : AdjunctionModel α) (e : Nat → α) :
    Sat M.mem e HF_empty_form :=
  ⟨M.empty, fun x hx => M.empty_spec x hx⟩

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
  rcases hg with rfl | rfl | ⟨phi, rfl⟩
  · exact (seal_valid (mem := M.mem) HF_empty_form).mpr (sat_HF_empty M) v
  · exact (seal_valid (mem := M.mem) HF_adjoin_form).mpr (sat_HF_adjoin M) v
  · exact (seal_valid (mem := M.mem) (HF_induction_form phi)).mpr
      (sat_HF_induction M phi) v

theorem standard_sat_HF (v : Nat → Nat) :
    ∀ g, HFAx_s g → Sat Mem v g :=
  sat_HF_model standardModel v

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

end Term

namespace Formula

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

theorem Sentences_translatedPAAx : Sentences translatedPAAx := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_PA_axiom_sentence phi hphi

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

theorem PA_biinterpretable_with_HF_standard :
    Nonempty (PA.Iso PA.natModel ordinalPAModel) ∧
      Nonempty (AdjunctionIso standardModel ordinalHFModel) :=
  ⟨⟨standardShallowBiInterpretation.paRoundTrip⟩,
   ⟨standardShallowBiInterpretation.hfRoundTrip⟩⟩

end AckermannHF

end SetTheory
