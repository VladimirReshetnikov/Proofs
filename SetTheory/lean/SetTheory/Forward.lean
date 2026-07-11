/- =====================================================================
    Forward.lean  —  Lean 4 port of ../Forward.v

    Vladimir Reshetnikov's "Closure" axiomatization of set theory:
    the FORWARD direction of its equivalence with ZF.

    We fix an abstract structure (V, mem) and assume only
        Extensionality, Separation, Powerset, Closure
    (Regularity is part of the theory T and is stated for faithfulness
     but plays no role below.  We work in ZF, not ZFC: the Axiom of
     Choice plays no role in the trade and is omitted from both
     theories.  Adding Choice back yields ZFC.)

    From these we DERIVE, as theorems:
        Pairing, Union, Replacement, Infinity.

    The linchpin is HOSTING: every set has a host, a ∈ host a.  That
    single fact makes every singleton-valued (more generally, suitably
    bounded) class relation set-like, which turns Closure into a fully
    general collection principle.  Hosting is ALL the trade uses of
    Powerset (a ∈ P(a) gives it); the explicit hypothesis lists of the
    four theorems below (the Lean rendering of the Coq `Check` audit)
    confirm none of the derivations touches Powerset itself.  Note
    Hosting is far weaker than Powerset and is NOT given by Powerset on
    finite sets, since the hosted predecessors (a, b, F x, x ∪ {x}) are
    arbitrary.

    Shallow embedding: schemas (Separation, Closure, and the derived
    Replacement) are rendered with the metatheory's predicates
    (V → Prop, V → V → Prop).  Every derivation instantiates a schema
    at one concrete, definable relation, so the proof is faithful to
    the first-order schematic argument.

    Self-contained: no imports (Lean core prelude only).  Classical
    logic enters through `Classical.em` and `Exists.choose` /
    `Exists.choose_spec`, the Lean counterparts of Coq's `classic` and
    `constructive_indefinite_description` from ClassicalEpsilon.

    Coq Section variables (V, mem, witness) and Hypotheses become
    explicit parameters here: the axiom schemas are named `def`s
    (`ExtAx`, `SepAx`, …) and every definition/theorem takes exactly
    the hypotheses it uses, so each statement carries its own
    dependency audit.

    Coq original header provenance:
    - Created (UTC): 2026-06-30T04:48:30Z
    - Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9
   ===================================================================== -/

namespace SetTheory.Forward

universe u

variable {V : Type u}

/-- `Sub mem a b` : `a` is a subset of `b`. -/
def Sub (mem : V → V → Prop) (a b : V) : Prop := ∀ x, mem x a → mem x b

/-- A class relation `R` is set-like when, at every node, some set contains
    all of its `R`-predecessors. -/
def SetLike (mem : V → V → Prop) (R : V → V → Prop) : Prop :=
  ∀ x, ∃ y, ∀ z, R z x → mem z y

private def Functional (R : V → V → Prop) : Prop := ∀ x y₁ y₂, R y₁ x → R y₂ x → y₁ = y₂

/- ------------------------- the surviving axioms ------------------------ -/
/- The axiom-schema statements, as named `def`s, so hypotheses stay readable
   and each theorem's parameter list is a literal dependency audit. -/

def ExtAx (mem : V → V → Prop) : Prop :=
  ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b

def SepAx (mem : V → V → Prop) : Prop :=
  ∀ (a : V) (P : V → Prop), ∃ s, ∀ x, mem x s ↔ mem x a ∧ P x

def PowAx (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a

/- Hosting: every set is a member of some set.  This is the ONLY consequence
   of Powerset that the forward trade uses (via a ∈ P(a); see
   `powerset_gives_hosting` below): to bound the singleton predecessor-class
   of a node we only need a set CONTAINING the predecessor.  It is far weaker
   than Powerset, and is NOT supplied by Powerset restricted to finite sets,
   since the predecessors we must bound (a, b, F x, x ∪ {x}) are arbitrary,
   possibly infinite, sets.  The four derivations below use only Hosting;
   their explicit parameter lists certify they are Powerset-free. -/
def HostAx (mem : V → V → Prop) : Prop := ∀ a, ∃ y, mem a y

def ClosureAx (mem : V → V → Prop) : Prop :=
  ∀ R : V → V → Prop, SetLike mem R →
    ∀ s, ∃ w, Sub mem s w ∧ ∀ u v, R u v → mem v w → mem u w

/- Part of T, but unused below (shared with ZF).  Stated for faithfulness. -/
def RegAx (mem : V → V → Prop) : Prop :=
  ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a

section
variable {mem : V → V → Prop}

/- ----------- derived operators via classical description -------------- -/

noncomputable def sep (hSep : SepAx mem) (a : V) (P : V → Prop) : V :=
  (hSep a P).choose

theorem sep_spec (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V) :
    mem x (sep hSep a P) ↔ mem x a ∧ P x :=
  (hSep a P).choose_spec x

theorem sep_intro (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V)
    (h1 : mem x a) (h2 : P x) : mem x (sep hSep a P) :=
  (sep_spec hSep a P x).mpr ⟨h1, h2⟩

theorem sep_elim1 (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V)
    (h : mem x (sep hSep a P)) : mem x a :=
  ((sep_spec hSep a P x).mp h).1

theorem sep_elim2 (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V)
    (h : mem x (sep hSep a P)) : P x :=
  ((sep_spec hSep a P x).mp h).2

theorem Sub_refl (a : V) : Sub mem a a := fun _ h => h

/- THE LINCHPIN, in its minimal form: every set has a host, a ∈ host a.
   This single fact is all the forward trade needs from Powerset; it makes
   every singleton-valued (suitably bounded) class relation set-like. -/
noncomputable def host (hHost : HostAx mem) (a : V) : V :=
  (hHost a).choose

theorem host_spec (hHost : HostAx mem) (a : V) : mem a (host hHost a) :=
  (hHost a).choose_spec

private theorem setLike_of_functional_host
    (bound : V → V) (hbound : ∀ a, mem a (bound a))
    (fallback : V) {R : V → V → Prop} (hfun : Functional R) : SetLike mem R := by
  intro x
  rcases Classical.em (∃ y, R y x) with ⟨y, hy⟩ | hnone
  · exact ⟨bound y, fun z hz => (hfun x z y hz hy).symm ▸ hbound y⟩
  · exact ⟨fallback, fun z hz => (hnone ⟨z, hz⟩).elim⟩

/- Powerset is one way to satisfy Hosting (a ∈ P(a)); Powerset restricted to
   finite sets is NOT, since it cannot host an infinite set.  This is the
   file's sole use of the Powerset hypothesis — the four derivations use only
   `host`, so their signatures show them free of Powerset. -/
theorem powerset_gives_hosting (hPow : PowAx mem) : ∀ a, ∃ y, mem a y := by
  intro a
  obtain ⟨p, Hp⟩ := hPow a
  exact ⟨p, (Hp a).mpr (Sub_refl a)⟩

/- --------------------------- empty set -------------------------------- -/
/- First-order logic works over a nonempty domain: `witness` plays the role
   of the Coq section variable of the same name. -/

noncomputable def emptyset (witness : V) (hSep : SepAx mem) : V :=
  sep hSep witness (fun _ => False)

theorem emptyset_spec (witness : V) (hSep : SepAx mem) (x : V) :
    ¬ mem x (emptyset witness hSep) :=
  fun h => sep_elim2 hSep witness (fun _ => False) x h

/- --------- the singleton {empty} and the two-node seed {empty,{empty}} ---
   Built from Hosting + Separation (+ a one-edge Closure for the 2-node seed),
   NOT from Powerset.  host empty contains empty, so Separation carves out
   {empty}; a one-edge Closure then merges empty into the seed {{empty}} to
   yield a set holding both empty and {empty}, from which Separation extracts
   {empty,{empty}}. -/

noncomputable def single_empty (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) : V :=
  sep hSep (host hHost (emptyset witness hSep)) (fun x => x = emptyset witness hSep)

theorem in_single_empty (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) (x : V) :
    mem x (single_empty witness hSep hHost) ↔ x = emptyset witness hSep := by
  constructor
  · intro H
    exact sep_elim2 hSep _ _ x H
  · intro H
    apply sep_intro hSep _ _ x
    · rw [H]
      exact host_spec hHost _
    · exact H

theorem empty_in_single (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) :
    mem (emptyset witness hSep) (single_empty witness hSep hHost) :=
  (in_single_empty witness hSep hHost _).mpr rfl

theorem empty_neq_single (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) :
    emptyset witness hSep ≠ single_empty witness hSep hHost := by
  intro Heq
  have H : mem (emptyset witness hSep) (single_empty witness hSep hHost) :=
    empty_in_single witness hSep hHost
  rw [← Heq] at H                     -- H : emptyset ∈ emptyset
  exact emptyset_spec witness hSep _ H

/- the singleton {{empty}}, the seed of the one-edge merge -/
noncomputable def seed_single (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) : V :=
  sep hSep (host hHost (single_empty witness hSep hHost))
    (fun x => x = single_empty witness hSep hHost)

theorem in_seed_single (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) (x : V) :
    mem x (seed_single witness hSep hHost) ↔ x = single_empty witness hSep hHost := by
  constructor
  · intro H
    exact sep_elim2 hSep _ _ x H
  · intro H
    apply sep_intro hSep _ _ x
    · rw [H]
      exact host_spec hHost _
    · exact H

/- the one-edge relation: empty is the sole predecessor of {empty} -/
def mergeRel (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) (z x : V) : Prop :=
  x = single_empty witness hSep hHost ∧ z = emptyset witness hSep

theorem mergeRel_setlike (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) :
    SetLike mem (mergeRel witness hSep hHost) := by
  intro x
  refine ⟨host hHost (emptyset witness hSep), ?_⟩
  intro z HR
  unfold mergeRel at HR
  obtain ⟨_, Hz⟩ := HR
  subst Hz
  exact host_spec hHost _

noncomputable def merge_w (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) : V :=
  (hClo (mergeRel witness hSep hHost) (mergeRel_setlike witness hSep hHost)
    (seed_single witness hSep hHost)).choose

theorem merge_w_spec (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    Sub mem (seed_single witness hSep hHost) (merge_w witness hSep hHost hClo) ∧
      ∀ u v, mergeRel witness hSep hHost u v →
        mem v (merge_w witness hSep hHost hClo) → mem u (merge_w witness hSep hHost hClo) :=
  (hClo (mergeRel witness hSep hHost) (mergeRel_setlike witness hSep hHost)
    (seed_single witness hSep hHost)).choose_spec

theorem single_in_merge_w (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    mem (single_empty witness hSep hHost) (merge_w witness hSep hHost hClo) :=
  (merge_w_spec witness hSep hHost hClo).1 _
    ((in_seed_single witness hSep hHost _).mpr rfl)

theorem empty_in_merge_w (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    mem (emptyset witness hSep) (merge_w witness hSep hHost hClo) :=
  (merge_w_spec witness hSep hHost hClo).2 (emptyset witness hSep)
    (single_empty witness hSep hHost) ⟨rfl, rfl⟩
    (single_in_merge_w witness hSep hHost hClo)

noncomputable def pair_empty (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) : V :=
  sep hSep (merge_w witness hSep hHost hClo)
    (fun x => x = emptyset witness hSep ∨ x = single_empty witness hSep hHost)

theorem empty_in_pair (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    mem (emptyset witness hSep) (pair_empty witness hSep hHost hClo) :=
  sep_intro hSep _ _ _ (empty_in_merge_w witness hSep hHost hClo) (Or.inl rfl)

theorem single_in_pair (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    mem (single_empty witness hSep hHost) (pair_empty witness hSep hHost hClo) :=
  sep_intro hSep _ _ _ (single_in_merge_w witness hSep hHost hClo) (Or.inr rfl)

/- ------------------------ the four relations -------------------------- -/

def pairRel (witness : V) (hSep : SepAx mem) (hHost : HostAx mem) (a b : V)
    (z x : V) : Prop :=
  (x = emptyset witness hSep ∧ z = a) ∨ (x = single_empty witness hSep hHost ∧ z = b)

end

def memRel (mem : V → V → Prop) (z x : V) : Prop := mem z x

def graphRel (mem : V → V → Prop) (F : V → V) (a : V) (z x : V) : Prop :=
  mem x a ∧ z = F x

def succRel (mem : V → V → Prop) (z x : V) : Prop :=
  ∀ t, mem t z ↔ (mem t x ∨ t = x)

section
variable {mem : V → V → Prop}

/- ============================== PAIRING ============================== -/

theorem Pairing (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    ∀ a b, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b) := by
  intro a b
  have hfun : Functional (pairRel witness hSep hHost a b) := by
    intro x z₁ z₂ hz₁ hz₂
    unfold pairRel at hz₁ hz₂
    rcases hz₁ with h₁ | h₁ <;> rcases hz₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · exact (empty_neq_single witness hSep hHost (h₁.1.symm.trans h₂.1)).elim
    · exact (empty_neq_single witness hSep hHost (h₂.1.symm.trans h₁.1)).elim
    · exact h₁.2.trans h₂.2.symm
  have HSL : SetLike mem (pairRel witness hSep hHost a b) :=
    setLike_of_functional_host (host hHost) (host_spec hHost) witness hfun
  obtain ⟨w, Hsub, Hclosed⟩ :=
    hClo (pairRel witness hSep hHost a b) HSL (pair_empty witness hSep hHost hClo)
  have Ha : mem a w := by
    apply Hclosed a (emptyset witness hSep)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Hsub _ (empty_in_pair witness hSep hHost hClo)
  have Hb : mem b w := by
    apply Hclosed b (single_empty witness hSep hHost)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Hsub _ (single_in_pair witness hSep hHost hClo)
  refine ⟨sep hSep w (fun x => x = a ∨ x = b), ?_⟩
  intro x
  constructor
  · intro H
    exact sep_elim2 hSep _ _ x H
  · intro H
    apply sep_intro hSep _ _ x
    · rcases H with H | H
      · subst H; exact Ha
      · subst H; exact Hb
    · exact H

/- =============================== UNION =============================== -/

theorem Union (hSep : SepAx mem) (hClo : ClosureAx mem) :
    ∀ s, ∃ u, ∀ x, mem x u ↔ ∃ v, mem x v ∧ mem v s := by
  intro s
  have HSL : SetLike mem (memRel mem) := by
    intro x
    refine ⟨x, ?_⟩
    intro z Hz
    unfold memRel at Hz
    exact Hz
  obtain ⟨w, Hsub, Hclosed⟩ := hClo (memRel mem) HSL s
  refine ⟨sep hSep w (fun x => ∃ v, mem x v ∧ mem v s), ?_⟩
  intro x
  constructor
  · intro H
    exact sep_elim2 hSep _ _ x H
  · intro H
    apply sep_intro hSep _ _ x
    · obtain ⟨v, Hxv, Hvs⟩ := H
      apply Hclosed x v
      · exact Hxv                      -- memRel mem x v unfolds to mem x v
      · exact Hsub v Hvs
    · exact H

/- ============================ REPLACEMENT =========================== -/

theorem Replacement (hSep : SepAx mem) (hHost : HostAx mem) (hClo : ClosureAx mem) :
    ∀ (F : V → V) (a : V), ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ y = F x := by
  intro F a
  have HSL : SetLike mem (graphRel mem F a) := by
    intro x
    refine ⟨host hHost (F x), ?_⟩
    intro z HR
    unfold graphRel at HR
    obtain ⟨_, Hz⟩ := HR
    subst Hz
    exact host_spec hHost (F x)
  obtain ⟨w, Hsub, Hclosed⟩ := hClo (graphRel mem F a) HSL a
  refine ⟨sep hSep w (fun y => ∃ x, mem x a ∧ y = F x), ?_⟩
  intro y
  constructor
  · intro H
    exact sep_elim2 hSep _ _ y H
  · intro H
    apply sep_intro hSep _ _ y
    · obtain ⟨x, Hxa, Hyf⟩ := H
      apply Hclosed y x
      · exact ⟨Hxa, Hyf⟩
      · exact Hsub x Hxa
    · exact H

/- ============================== INFINITY ============================ -/

theorem singleton_exists (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    ∀ x, ∃ s, ∀ t, mem t s ↔ t = x := by
  intro x
  obtain ⟨p, Hp⟩ := Pairing witness hSep hHost hClo x x
  refine ⟨p, ?_⟩
  intro t
  constructor
  · intro H
    rcases (Hp t).mp H with E | E <;> exact E
  · intro H
    exact (Hp t).mpr (Or.inl H)

theorem succ_exists (witness : V) (hSep : SepAx mem) (hHost : HostAx mem)
    (hClo : ClosureAx mem) :
    ∀ x, ∃ sx, ∀ t, mem t sx ↔ (mem t x ∨ t = x) := by
  intro x
  obtain ⟨sg, Hsg⟩ := singleton_exists witness hSep hHost hClo x
  obtain ⟨pr, Hpr⟩ := Pairing witness hSep hHost hClo x sg
  obtain ⟨u, Hu⟩ := Union hSep hClo pr
  refine ⟨u, ?_⟩
  intro t
  constructor
  · intro H
    obtain ⟨v, Htv, Hvpr⟩ := (Hu t).mp H
    rcases (Hpr v).mp Hvpr with Hvx | Hvsg
    · subst Hvx
      exact Or.inl Htv
    · subst Hvsg
      exact Or.inr ((Hsg t).mp Htv)
  · intro H
    apply (Hu t).mpr
    rcases H with Htx | Htx
    · exact ⟨x, Htx, (Hpr x).mpr (Or.inl rfl)⟩
    · exact ⟨sg, (Hsg t).mpr Htx, (Hpr sg).mpr (Or.inr rfl)⟩

theorem Infinity (witness : V) (hExt : ExtAx mem) (hSep : SepAx mem)
    (hHost : HostAx mem) (hClo : ClosureAx mem) :
    ∃ I,
      (∃ e, mem e I ∧ ∀ z, ¬ mem z e) ∧
      (∀ x, mem x I →
        ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) := by
  have hfun : Functional (succRel mem) := by
    intro x z₁ z₂ hz₁ hz₂
    apply hExt
    intro t
    rw [hz₁ t, hz₂ t]
  have HSL : SetLike mem (succRel mem) :=
    setLike_of_functional_host (host hHost) (host_spec hHost) witness hfun
  obtain ⟨w, Hsub, Hclosed⟩ := hClo (succRel mem) HSL (single_empty witness hSep hHost)
  refine ⟨w, ⟨emptyset witness hSep, ?_, ?_⟩, ?_⟩
  · exact Hsub _ (empty_in_single witness hSep hHost)
  · exact emptyset_spec witness hSep
  · intro x Hx
    obtain ⟨sx, Hsx⟩ := succ_exists witness hSep hHost hClo x
    refine ⟨sx, ?_, Hsx⟩
    apply Hclosed sx x
    · exact Hsx                        -- succRel mem sx x unfolds to Hsx
    · exact Hx

end

/- Each theorem above is universally quantified over the structure
   (V, mem, witness) and exactly the axioms in its explicit parameter list —
   the Lean rendering of the Coq post-section `Check` audit:

     Pairing     : witness, SepAx, HostAx, ClosureAx
     Union       :          SepAx,         ClosureAx
     Replacement :          SepAx, HostAx, ClosureAx
     Infinity    : witness, ExtAx, SepAx, HostAx, ClosureAx

   i.e. every model of {Ext, Sep, Pow, Closure} also models Pairing, Union,
   Replacement, Infinity — with Powerset entering only through Hosting
   (`powerset_gives_hosting`), and Regularity (RegAx) never used. -/

end SetTheory.Forward
