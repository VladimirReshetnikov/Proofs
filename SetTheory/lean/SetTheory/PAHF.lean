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

/-! ### First PA-in-HF interpretation formulas already available -/

namespace PAInHF

/-- Domain formula for the PA interpretation in HF: finite ordinals. -/
def domainForm : Form := HF_ordinalLikeAt 0

/-- Graph formula for PA zero in HF.  Slot `0` is the candidate output. -/
def zeroGraph : Form := HF_emptyAt 0

/-- Graph formula for PA successor in HF.  Slot `0` is the output and slot `1`
is the input. -/
def succGraph : Form := HF_succAt 0 1

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

def bound : Term → Nat
  | var n => n + 1
  | zero => 0
  | succ t => bound t
  | add a b => bound a + bound b
  | mul a b => bound a + bound b

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

def closeN : Nat → Formula → Formula
  | 0, phi => phi
  | n+1, phi => closeN n (all phi)

def sealPA (phi : Formula) : Formula := closeN (bound phi) phi

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
