/- =====================================================================
    Reverse.lean  —  Lean 4 port of ../Reverse.v

    The REVERSE direction of the equivalence: ZF proves the Closure
    schema.  We fix an abstract structure (V, mem) and assume the
    ordinary ZF axioms
        Extensionality, Separation, Pairing, Union,
        Infinity, Replacement
    and DERIVE: for every set-like class relation R and every set s,
    there is a set w containing s and closed under R-predecessors.

    (The Coq original also *states* Powerset and Regularity for
     faithfulness as ZF axioms, but its trailing `Check Closure_holds`
     certifies that neither is used.  In this port the audit is carried
     by the explicit parameter lists themselves, so the two unused
     hypotheses are omitted outright: no statement below can even
     mention them.)

    The construction is the textbook one.  Let
        g(t) = t  ∪  { u : exists v in t, R u v }
    (a set: set-likeness yields a bounding function `boundf`, then
     Replacement + Union + Separation collect the predecessors), and
        W_n = g^n(s)        (iteration on the META-level Nat).
    To collect { W_n : n } into one object set we map the object
    numerals `onat n` (which live in the inductive set `Inf` from
    Infinity) to W_n via Replacement; pinning the index needs `onat`
    injective, Foundation-free, no Regularity needed.  Then
        w = Union (image) = Union_n W_n.

    Together with Forward.lean this gives both directions of
        {Ext, Reg, Sep, Pow, Closure}  ==  ZF.

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

namespace SetTheory.Reverse

universe u

variable {V : Type u}

/-- `Sub mem a b` : `a` is a subset of `b`. -/
def Sub (mem : V → V → Prop) (a b : V) : Prop := ∀ x, mem x a → mem x b

/-- A class relation `R` is set-like when, at every node, some set contains
    all of its `R`-predecessors. -/
def SetLike (mem : V → V → Prop) (R : V → V → Prop) : Prop :=
  ∀ x, ∃ y, ∀ z, R z x → mem z y

/- ------------------------------ ZF axioms ----------------------------- -/
/- Stated as named `def`s, so hypotheses stay readable and each theorem's
   parameter list is a literal dependency audit.  Powerset and Regularity —
   the two ZF axioms the reverse direction never touches — are deliberately
   not even defined here. -/

def ExtAx (mem : V → V → Prop) : Prop :=
  ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b

def SepAx (mem : V → V → Prop) : Prop :=
  ∀ (a : V) (P : V → Prop), ∃ s, ∀ x, mem x s ↔ mem x a ∧ P x

def PairAx (mem : V → V → Prop) : Prop :=
  ∀ a b, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b)

def UnionAx (mem : V → V → Prop) : Prop :=
  ∀ s, ∃ u, ∀ x, mem x u ↔ ∃ v, mem x v ∧ mem v s

def InfAx (mem : V → V → Prop) : Prop :=
  ∃ I,
    (∃ e, mem e I ∧ ∀ z, ¬ mem z e) ∧
    (∀ x, mem x I →
      ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x))

def ReplAx (mem : V → V → Prop) : Prop :=
  ∀ (F : V → V) (a : V), ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ y = F x

section
variable {mem : V → V → Prop}

theorem Sub_refl (a : V) : Sub mem a a := fun _ h => h

theorem Sub_trans (a b c : V) (Hab : Sub mem a b) (Hbc : Sub mem b c) :
    Sub mem a c :=
  fun x Hx => Hbc x (Hab x Hx)

theorem Sub_elim (a b x : V) (H : Sub mem a b) (Hx : mem x a) : mem x b :=
  H x Hx

/- --------------------- ZF operators as functions ----------------------
   (via classical description, i.e. `Exists.choose`) -/

noncomputable def sep (hSep : SepAx mem) (a : V) (P : V → Prop) : V :=
  (hSep a P).choose

theorem sep_spec (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V) :
    mem x (sep hSep a P) ↔ mem x a ∧ P x :=
  (hSep a P).choose_spec x

theorem sep_intro (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V)
    (h1 : mem x a) (h2 : P x) : mem x (sep hSep a P) :=
  (sep_spec hSep a P x).mpr ⟨h1, h2⟩

theorem sep_elim2 (hSep : SepAx mem) (a : V) (P : V → Prop) (x : V)
    (h : mem x (sep hSep a P)) : P x :=
  ((sep_spec hSep a P x).mp h).2

/- `witness` is the nonempty-domain convention of first-order logic: the Coq
   section variable of the same name, threaded explicitly. -/

noncomputable def emptyset (witness : V) (hSep : SepAx mem) : V :=
  sep hSep witness (fun _ => False)

theorem emptyset_spec (witness : V) (hSep : SepAx mem) (x : V) :
    ¬ mem x (emptyset witness hSep) :=
  fun h => sep_elim2 hSep witness (fun _ => False) x h

noncomputable def opair2 (hPair : PairAx mem) (a b : V) : V :=
  (hPair a b).choose

theorem opair2_spec (hPair : PairAx mem) (a b x : V) :
    mem x (opair2 hPair a b) ↔ (x = a ∨ x = b) :=
  (hPair a b).choose_spec x

noncomputable def osingle (hPair : PairAx mem) (a : V) : V := opair2 hPair a a

theorem osingle_spec (hPair : PairAx mem) (a x : V) :
    mem x (osingle hPair a) ↔ x = a := by
  constructor
  · intro H
    rcases (opair2_spec hPair a a x).mp H with H | H <;> exact H
  · intro H
    exact (opair2_spec hPair a a x).mpr (Or.inl H)

noncomputable def ounion (hUnion : UnionAx mem) (s : V) : V :=
  (hUnion s).choose

theorem ounion_spec (hUnion : UnionAx mem) (s x : V) :
    mem x (ounion hUnion s) ↔ ∃ v, mem x v ∧ mem v s :=
  (hUnion s).choose_spec x

noncomputable def obin (hPair : PairAx mem) (hUnion : UnionAx mem) (a b : V) : V :=
  ounion hUnion (opair2 hPair a b)

theorem obin_spec (hPair : PairAx mem) (hUnion : UnionAx mem) (a b x : V) :
    mem x (obin hPair hUnion a b) ↔ (mem x a ∨ mem x b) := by
  constructor
  · intro H
    obtain ⟨v, Hxv, Hv⟩ := (ounion_spec hUnion (opair2 hPair a b) x).mp H
    rcases (opair2_spec hPair a b v).mp Hv with rfl | rfl
    · exact Or.inl Hxv
    · exact Or.inr Hxv
  · intro H
    apply (ounion_spec hUnion (opair2 hPair a b) x).mpr
    rcases H with Ha | Hb
    · exact ⟨a, Ha, (opair2_spec hPair a b a).mpr (Or.inl rfl)⟩
    · exact ⟨b, Hb, (opair2_spec hPair a b b).mpr (Or.inr rfl)⟩

noncomputable def osucc (hPair : PairAx mem) (hUnion : UnionAx mem) (a : V) : V :=
  obin hPair hUnion a (osingle hPair a)

theorem osucc_spec (hPair : PairAx mem) (hUnion : UnionAx mem) (a x : V) :
    mem x (osucc hPair hUnion a) ↔ (mem x a ∨ x = a) := by
  constructor
  · intro H
    rcases (obin_spec hPair hUnion a (osingle hPair a) x).mp H with Ha | Hs
    · exact Or.inl Ha
    · exact Or.inr ((osingle_spec hPair a x).mp Hs)
  · intro H
    apply (obin_spec hPair hUnion a (osingle hPair a) x).mpr
    rcases H with Ha | He
    · exact Or.inl Ha
    · exact Or.inr ((osingle_spec hPair a x).mpr He)

theorem osucc_super (hPair : PairAx mem) (hUnion : UnionAx mem) (a : V) :
    Sub mem a (osucc hPair hUnion a) :=
  fun x Hx => (osucc_spec hPair hUnion a x).mpr (Or.inl Hx)

noncomputable def imageR (hRepl : ReplAx mem) (F : V → V) (a : V) : V :=
  (hRepl F a).choose

theorem imageR_spec (hRepl : ReplAx mem) (F : V → V) (a y : V) :
    mem y (imageR hRepl F a) ↔ ∃ x, mem x a ∧ y = F x :=
  (hRepl F a).choose_spec y

/- ----- Regularity is a CONVENIENCE here, not a necessity ---------------
   The construction below needs the numerals  onat n  to be pairwise
   distinct.  The original proof got this from Regularity, via the fact
   that no set is a member of itself.  But that global fact is far more
   than we need: the finite von Neumann numerals are distinct in ZF WITHOUT
   Foundation, because each onat n is a genuine ordinal — a transitive set
   on which membership is irreflexive — which we prove by induction on n
   (onat_trans, onat_no_self) using only Pairing/Union (osucc).  So
   Regularity, like Choice, is a passenger of the trade: `Closure_holds`
   below does not take it.  (In the Coq file the Regularity hypothesis is
   kept for completeness as a ZF axiom and simply never used; here it is
   omitted altogether.) -/

/- --------------------- object numerals onat : Nat → V ----------------- -/

noncomputable def onat (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) : Nat → V
  | 0 => emptyset witness hSep
  | n + 1 => osucc hPair hUnion (onat witness hSep hPair hUnion n)

/- The two defining equations, as `rfl` lemmas (the Lean counterpart of
   Coq's `simpl` steps on `onat`). -/
theorem onat_zero (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) :
    onat witness hSep hPair hUnion 0 = emptyset witness hSep := rfl

theorem onat_succ (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (n : Nat) :
    onat witness hSep hPair hUnion (n + 1) =
      osucc hPair hUnion (onat witness hSep hPair hUnion n) := rfl

theorem onat_self_in_succ (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (i : Nat) :
    mem (onat witness hSep hPair hUnion i) (onat witness hSep hPair hUnion (i + 1)) := by
  rw [onat_succ]
  exact (osucc_spec hPair hUnion _ _).mpr (Or.inr rfl)

theorem onat_mono (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) :
    ∀ j i, i ≤ j →
      Sub mem (onat witness hSep hPair hUnion i) (onat witness hSep hPair hUnion j) := by
  intro j
  induction j with
  | zero =>
    intro i Hij
    have Hi : i = 0 := by omega
    subst Hi
    exact Sub_refl _
  | succ j IHj =>
    intro i Hij
    rcases Classical.em (i = j + 1) with Heq | Hne
    · subst Heq
      exact Sub_refl _
    · have Hle : i ≤ j := by omega
      refine Sub_trans _ (onat witness hSep hPair hUnion j) _ (IHj i Hle) ?_
      rw [onat_succ]
      exact osucc_super hPair hUnion _

theorem onat_lt_mem (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (i j : Nat) (Hij : i < j) :
    mem (onat witness hSep hPair hUnion i) (onat witness hSep hPair hUnion j) :=
  Sub_elim (onat witness hSep hPair hUnion (i + 1)) (onat witness hSep hPair hUnion j)
    (onat witness hSep hPair hUnion i)
    (onat_mono witness hSep hPair hUnion j (i + 1) (by omega))
    (onat_self_in_succ witness hSep hPair hUnion i)

/- Each numeral is a transitive set — proved by induction, Foundation-free. -/
theorem onat_trans (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) :
    ∀ n x, mem x (onat witness hSep hPair hUnion n) →
      Sub mem x (onat witness hSep hPair hUnion n) := by
  intro n
  induction n with
  | zero =>
    intro x Hx
    exact absurd Hx (emptyset_spec witness hSep x)
  | succ n IHn =>
    intro x Hx
    rw [onat_succ] at Hx
    rcases (osucc_spec hPair hUnion (onat witness hSep hPair hUnion n) x).mp Hx
      with Hxin | Hxeq
    · rw [onat_succ]
      refine Sub_trans _ (onat witness hSep hPair hUnion n) _ (IHn x Hxin) ?_
      exact osucc_super hPair hUnion _
    · subst Hxeq
      rw [onat_succ]
      exact osucc_super hPair hUnion _

/- Hence no numeral is a member of itself — WITHOUT Regularity.  If
   onat n ∈ onat n then, since onat n is transitive, onat n would be a
   subset of itself containing itself, contradicting the inductive case. -/
theorem onat_no_self (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) :
    ∀ n, ¬ mem (onat witness hSep hPair hUnion n) (onat witness hSep hPair hUnion n) := by
  intro n
  induction n with
  | zero =>
    intro H
    exact emptyset_spec witness hSep _ H
  | succ n IHn =>
    intro H
    rw [onat_succ] at H
    rcases (osucc_spec hPair hUnion (onat witness hSep hPair hUnion n)
        (osucc hPair hUnion (onat witness hSep hPair hUnion n))).mp H with Hin | Heq
    · exact IHn (onat_trans witness hSep hPair hUnion n _ Hin _
        ((osucc_spec hPair hUnion _ _).mpr (Or.inr rfl)))
    · apply IHn
      have Hmem : mem (onat witness hSep hPair hUnion n)
          (osucc hPair hUnion (onat witness hSep hPair hUnion n)) :=
        (osucc_spec hPair hUnion _ _).mpr (Or.inr rfl)
      rw [Heq] at Hmem
      exact Hmem

theorem onat_inj (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (i j : Nat)
    (H : onat witness hSep hPair hUnion i = onat witness hSep hPair hUnion j) :
    i = j := by
  have Htri : i < j ∨ i = j ∨ j < i := by omega
  rcases Htri with Hlt | Heq | Hgt
  · exfalso
    have Hm : mem (onat witness hSep hPair hUnion i) (onat witness hSep hPair hUnion j) :=
      onat_lt_mem witness hSep hPair hUnion i j Hlt
    rw [← H] at Hm
    exact onat_no_self witness hSep hPair hUnion i Hm
  · exact Heq
  · exfalso
    have Hm : mem (onat witness hSep hPair hUnion j) (onat witness hSep hPair hUnion i) :=
      onat_lt_mem witness hSep hPair hUnion j i Hgt
    rw [H] at Hm
    exact onat_no_self witness hSep hPair hUnion j Hm

/- --------------------- an inductive set from Infinity ------------------ -/

noncomputable def Inf (hInf : InfAx mem) : V := Exists.choose hInf

theorem Inf_spec (hInf : InfAx mem) :
    (∃ e, mem e (Inf hInf) ∧ ∀ z, ¬ mem z e) ∧
    (∀ x, mem x (Inf hInf) →
      ∃ sx, mem sx (Inf hInf) ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) :=
  Exists.choose_spec hInf

theorem empty_in_Inf (witness : V) (hExt : ExtAx mem) (hSep : SepAx mem)
    (hInf : InfAx mem) :
    mem (emptyset witness hSep) (Inf hInf) := by
  obtain ⟨⟨e, He, Hemp⟩, _⟩ := Inf_spec hInf
  have Heq : e = emptyset witness hSep := by
    apply hExt
    intro t
    constructor
    · intro Ht
      exact absurd Ht (Hemp t)
    · intro Ht
      exact absurd Ht (emptyset_spec witness hSep t)
  subst Heq
  exact He

theorem osucc_in_Inf (hExt : ExtAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hInf : InfAx mem) (x : V) (Hx : mem x (Inf hInf)) :
    mem (osucc hPair hUnion x) (Inf hInf) := by
  obtain ⟨_, Hsucc⟩ := Inf_spec hInf
  obtain ⟨sx, Hsx, Hsxspec⟩ := Hsucc x Hx
  have Heq : sx = osucc hPair hUnion x := by
    apply hExt
    intro t
    constructor
    · intro Ht
      exact (osucc_spec hPair hUnion x t).mpr ((Hsxspec t).mp Ht)
    · intro Ht
      exact (Hsxspec t).mpr ((osucc_spec hPair hUnion x t).mp Ht)
  subst Heq
  exact Hsx

theorem onat_in_Inf (witness : V) (hExt : ExtAx mem) (hSep : SepAx mem)
    (hPair : PairAx mem) (hUnion : UnionAx mem) (hInf : InfAx mem) (n : Nat) :
    mem (onat witness hSep hPair hUnion n) (Inf hInf) := by
  induction n with
  | zero =>
    exact empty_in_Inf witness hExt hSep hInf
  | succ n IHn =>
    rw [onat_succ]
    exact osucc_in_Inf hExt hPair hUnion hInf _ IHn

/- ------------------- the one-step closure operator g ------------------- -/

/- set-likeness yields a bounding function for the predecessors -/
noncomputable def boundf (R : V → V → Prop) (HSL : SetLike mem R) : V → V :=
  fun x => (HSL x).choose

theorem boundf_spec (R : V → V → Prop) (HSL : SetLike mem R) (x z : V) (H : R z x) :
    mem z (boundf R HSL x) :=
  (HSL x).choose_spec z H

noncomputable def predsf (hSep : SepAx mem) (hUnion : UnionAx mem) (hRepl : ReplAx mem)
    (R : V → V → Prop) (HSL : SetLike mem R) (t : V) : V :=
  sep hSep (ounion hUnion (imageR hRepl (boundf R HSL) t))
    (fun u => ∃ v, mem v t ∧ R u v)

theorem predsf_spec (hSep : SepAx mem) (hUnion : UnionAx mem) (hRepl : ReplAx mem)
    (R : V → V → Prop) (HSL : SetLike mem R) (t u : V) :
    mem u (predsf hSep hUnion hRepl R HSL t) ↔ ∃ v, mem v t ∧ R u v := by
  constructor
  · intro H
    exact sep_elim2 hSep _ _ u H
  · intro H
    apply sep_intro hSep _ _ u
    · obtain ⟨v, Hvt, Hruv⟩ := H
      apply (ounion_spec hUnion (imageR hRepl (boundf R HSL) t) u).mpr
      refine ⟨boundf R HSL v, ?_, ?_⟩
      · exact boundf_spec R HSL v u Hruv
      · exact (imageR_spec hRepl (boundf R HSL) t (boundf R HSL v)).mpr
          ⟨v, Hvt, rfl⟩
    · exact H

noncomputable def gstep (hSep : SepAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hRepl : ReplAx mem) (R : V → V → Prop) (HSL : SetLike mem R) (t : V) : V :=
  obin hPair hUnion t (predsf hSep hUnion hRepl R HSL t)

theorem gstep_spec (hSep : SepAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hRepl : ReplAx mem) (R : V → V → Prop) (HSL : SetLike mem R) (t x : V) :
    mem x (gstep hSep hPair hUnion hRepl R HSL t) ↔
      (mem x t ∨ mem x (predsf hSep hUnion hRepl R HSL t)) :=
  obin_spec hPair hUnion t (predsf hSep hUnion hRepl R HSL t) x

/- ------------------------- iteration on meta Nat ---------------------- -/

def iterate (g : V → V) (s : V) : Nat → V
  | 0 => s
  | n + 1 => g (iterate g s n)

noncomputable def Iter (hSep : SepAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hRepl : ReplAx mem) (R : V → V → Prop) (HSL : SetLike mem R) (s : V) : Nat → V :=
  iterate (gstep hSep hPair hUnion hRepl R HSL) s

theorem Iter_S (hSep : SepAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hRepl : ReplAx mem) (R : V → V → Prop) (HSL : SetLike mem R) (s : V) (n : Nat) :
    Iter hSep hPair hUnion hRepl R HSL s (n + 1) =
      gstep hSep hPair hUnion hRepl R HSL (Iter hSep hPair hUnion hRepl R HSL s n) := rfl

/- --------------- map object numerals to their iterate ----------------- -/

/- Non-numerals map to stage 0, so every `Ffun` value is an iteration stage. -/
theorem Qtot (witness : V) (hSep : SepAx mem) (hPair : PairAx mem) (hUnion : UnionAx mem)
    (hRepl : ReplAx mem) (R : V → V → Prop) (HSL : SetLike mem R) (s m : V) :
    ∃ y,
      (∃ n, m = onat witness hSep hPair hUnion n ∧
        y = Iter hSep hPair hUnion hRepl R HSL s n)
      ∨ ((∀ n, m ≠ onat witness hSep hPair hUnion n) ∧
        y = Iter hSep hPair hUnion hRepl R HSL s 0) := by
  rcases Classical.em (∃ n, m = onat witness hSep hPair hUnion n) with ⟨n, Hn⟩ | Hno
  · exact ⟨Iter hSep hPair hUnion hRepl R HSL s n, Or.inl ⟨n, Hn, rfl⟩⟩
  · refine ⟨Iter hSep hPair hUnion hRepl R HSL s 0, Or.inr ⟨?_, rfl⟩⟩
    intro n Hmn
    exact Hno ⟨n, Hmn⟩

noncomputable def Ffun (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (hRepl : ReplAx mem) (R : V → V → Prop)
    (HSL : SetLike mem R) (s m : V) : V :=
  (Qtot witness hSep hPair hUnion hRepl R HSL s m).choose

theorem Ffun_spec (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (hRepl : ReplAx mem) (R : V → V → Prop)
    (HSL : SetLike mem R) (s m : V) :
    (∃ n, m = onat witness hSep hPair hUnion n ∧
      Ffun witness hSep hPair hUnion hRepl R HSL s m = Iter hSep hPair hUnion hRepl R HSL s n)
    ∨ ((∀ n, m ≠ onat witness hSep hPair hUnion n) ∧
      Ffun witness hSep hPair hUnion hRepl R HSL s m =
        Iter hSep hPair hUnion hRepl R HSL s 0) :=
  (Qtot witness hSep hPair hUnion hRepl R HSL s m).choose_spec

theorem F_onat (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (hRepl : ReplAx mem) (R : V → V → Prop)
    (HSL : SetLike mem R) (s : V) (k : Nat) :
    Ffun witness hSep hPair hUnion hRepl R HSL s (onat witness hSep hPair hUnion k) =
      Iter hSep hPair hUnion hRepl R HSL s k := by
  rcases Ffun_spec witness hSep hPair hUnion hRepl R HSL s (onat witness hSep hPair hUnion k)
    with ⟨n, Hn, Hy⟩ | ⟨Hno, _⟩
  · have Hkn : k = n := onat_inj witness hSep hPair hUnion k n Hn
    subst Hkn
    exact Hy
  · exact absurd rfl (Hno k)

theorem F_cases (witness : V) (hSep : SepAx mem) (hPair : PairAx mem)
    (hUnion : UnionAx mem) (hRepl : ReplAx mem) (R : V → V → Prop)
    (HSL : SetLike mem R) (s m : V) :
    ∃ n, Ffun witness hSep hPair hUnion hRepl R HSL s m =
      Iter hSep hPair hUnion hRepl R HSL s n := by
  rcases Ffun_spec witness hSep hPair hUnion hRepl R HSL s m with ⟨n, _, Hy⟩ | ⟨_, Hy⟩
  · exact ⟨n, Hy⟩
  · exact ⟨0, Hy⟩

/- ============================== CLOSURE ============================== -/

theorem Closure_holds (witness : V) (hExt : ExtAx mem) (hSep : SepAx mem)
    (hPair : PairAx mem) (hUnion : UnionAx mem) (hInf : InfAx mem)
    (hRepl : ReplAx mem) :
    ∀ R : V → V → Prop, SetLike mem R →
      ∀ s, ∃ w, Sub mem s w ∧ ∀ u v, R u v → mem v w → mem u w := by
  intro R HSL s
  refine ⟨ounion hUnion (imageR hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)),
    ?_, ?_⟩
  · -- Sub s w
    intro y Hy
    apply (ounion_spec hUnion
      (imageR hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)) y).mpr
    refine ⟨Iter hSep hPair hUnion hRepl R HSL s 0, ?_, ?_⟩
    · exact Hy                        -- Iter … 0 is definitionally s
    · apply (imageR_spec hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)
        (Iter hSep hPair hUnion hRepl R HSL s 0)).mpr
      exact ⟨onat witness hSep hPair hUnion 0,
        onat_in_Inf witness hExt hSep hPair hUnion hInf 0,
        (F_onat witness hSep hPair hUnion hRepl R HSL s 0).symm⟩
  · -- closed under R-predecessors
    intro u v Hruv Hvw
    obtain ⟨c, Hvc, Hcr⟩ := (ounion_spec hUnion
      (imageR hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)) v).mp Hvw
    obtain ⟨m, _, Hcm⟩ := (imageR_spec hRepl
      (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf) c).mp Hcr
    obtain ⟨n, Hn⟩ := F_cases witness hSep hPair hUnion hRepl R HSL s m
    rw [Hcm, Hn] at Hvc               -- Hvc : v ∈ Iter … n
    apply (ounion_spec hUnion
      (imageR hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)) u).mpr
    refine ⟨Iter hSep hPair hUnion hRepl R HSL s (n + 1), ?_, ?_⟩
    · rw [Iter_S hSep hPair hUnion hRepl R HSL s n]
      apply (gstep_spec hSep hPair hUnion hRepl R HSL
        (Iter hSep hPair hUnion hRepl R HSL s n) u).mpr
      refine Or.inr ?_
      apply (predsf_spec hSep hUnion hRepl R HSL
        (Iter hSep hPair hUnion hRepl R HSL s n) u).mpr
      exact ⟨v, Hvc, Hruv⟩
    · apply (imageR_spec hRepl (Ffun witness hSep hPair hUnion hRepl R HSL s) (Inf hInf)
        (Iter hSep hPair hUnion hRepl R HSL s (n + 1))).mpr
      exact ⟨onat witness hSep hPair hUnion (n + 1),
        onat_in_Inf witness hExt hSep hPair hUnion hInf (n + 1),
        (F_onat witness hSep hPair hUnion hRepl R HSL s (n + 1)).symm⟩

end

/- `Closure_holds` is universally quantified over the structure
   (V, mem, witness) and exactly {ExtAx, SepAx, PairAx, UnionAx, InfAx,
   ReplAx} — the Lean rendering of the Coq `Check Closure_holds` audit:
   neither Powerset nor Regularity appears (nor is even definable here). -/

end SetTheory.Reverse
