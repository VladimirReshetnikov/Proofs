/-
  Equivalence.lean

  THE CLOSURE AXIOMATIZATION T AND ITS EQUIVALENCE WITH ZF.  This is the
  only file specific to the axiomatization T = {Extensionality,
  Regularity, Separation, Powerset, Closure}.  Building on the generic
  modules (Fol, Calculus, Completeness) and the first-order ZF module
  (Zf), it proves:

   - the deep FORWARD trade: from the first-order schemas
     SeparationFO + ClosureFO (with Powerset and a nonempty domain),
     Pairing, Union, first-order Replacement, and Infinity are
     theorems — each schema instance exhibited as a concrete formula;
   - `ZF_provable_holds_in_T`: in any T-model, every ZF-provable
     formula holds (soundness + the forward trade);
   - the Closure schema as a closed formula (`Closure_form`) with its
     satisfaction bridge, and T as a sentence theory `Tax_s`;
   - `Tmodel_sat_ZF` / `ZFmodel_sat_T`: T and ZF have exactly the same
     models (the deep reverse uses `ClosureFO_of_ZF` — the internal
     recursion theorem);
   - the syntactic equivalence, both directions:
         ZF_implies_T, T_implies_ZF, and the headline T_iff_ZF.

  Lean 4 port of the Rocq/Coq development `SetTheory/ClosureAxiomatization/Coq/Equivalence.v`.
-/
import FirstOrder.Completeness
import ZF.Zf

namespace SetTheory

open Form

/-! ## The T-schemas as named axiom statements (mirroring the Coq Section
hypotheses, so each derived theorem's parameter list is its free
dependency audit). -/

universe u

def ExtAx {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b

def SepFOAx {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ (phi : Form) (e : Nat → V) (a : V),
    ∃ s, ∀ x, mem x s ↔ (mem x a ∧ Sat mem (scons x e) phi)

def PowAx {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a

def ClosureFOAx {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ (psi : Form) (e : Nat → V),
    SetLike mem (relOf mem psi e) →
    ∀ s, ∃ w, Sub mem s w ∧
      ∀ u v, relOf mem psi e u v → mem v w → mem u w

def RegAx {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a

/-! ## The deep forward direction: from the T-schemas over an abstract
structure (V, mem), the four generative ZF axioms with genuinely
first-order schema instances. -/

section DeepForward

variable {V : Type u} {mem : V → V → Prop}

/-! ### Operators -/

noncomputable def power (hPow : PowAx mem) (a : V) : V := (hPow a).choose

theorem power_spec (hPow : PowAx mem) (a x : V) :
    mem x (power hPow a) ↔ Sub mem x a := (hPow a).choose_spec x

theorem power_intro (hPow : PowAx mem) (a x : V) (h : Sub mem x a) :
    mem x (power hPow a) := (power_spec hPow a x).mpr h

theorem power_elim (hPow : PowAx mem) (a x : V) (h : mem x (power hPow a)) :
    Sub mem x a := (power_spec hPow a x).mp h

noncomputable def sepF (hSep : SepFOAx mem) (a : V) (phi : Form) (e : Nat → V) : V :=
  (hSep phi e a).choose

theorem sepF_spec (hSep : SepFOAx mem) (a : V) (phi : Form) (e : Nat → V) (x : V) :
    mem x (sepF hSep a phi e) ↔ (mem x a ∧ Sat mem (scons x e) phi) :=
  (hSep phi e a).choose_spec x

theorem Sub_refl (a : V) : Sub mem a a := fun _ h => h

theorem self_in_power (hPow : PowAx mem) (a : V) : mem a (power hPow a) :=
  power_intro hPow a a (Sub_refl a)

private theorem setLike_of_functional_host
    (bound : V → V) (hbound : ∀ a, mem a (bound a))
    (fallback : V) {R : V → V → Prop} (hfun : Functional R) : SetLike mem R := by
  intro x
  rcases Classical.em (∃ y, R y x) with ⟨y, hy⟩ | hnone
  · exact ⟨bound y, fun z hz => (hfun x z y hz hy).symm ▸ hbound y⟩
  · exact ⟨fallback, fun z hz => (hnone ⟨z, hz⟩).elim⟩

/-! ### Empty set -/

noncomputable def emptyset (hSep : SepFOAx mem) (witness : V) : V :=
  sepF hSep witness fBot (fun _ => witness)

theorem emptyset_spec (hSep : SepFOAx mem) (witness : V) (x : V) :
    ¬ mem x (emptyset hSep witness) := fun h =>
  ((sepF_spec hSep witness fBot (fun _ => witness) x).mp h).2

noncomputable def single_empty (hSep : SepFOAx mem) (hPow : PowAx mem)
    (witness : V) : V := power hPow (emptyset hSep witness)

noncomputable def pair_empty (hSep : SepFOAx mem) (hPow : PowAx mem)
    (witness : V) : V := power hPow (single_empty hSep hPow witness)

theorem in_single_empty (hExt : ExtAx mem) (hSep : SepFOAx mem) (hPow : PowAx mem)
    (witness : V) (x : V) :
    mem x (single_empty hSep hPow witness) ↔ x = emptyset hSep witness := by
  unfold single_empty
  constructor
  · intro h
    apply hExt
    intro y
    constructor
    · intro hy; exact power_elim hPow _ x h y hy
    · intro hy; exact absurd hy (emptyset_spec hSep witness y)
  · intro h
    subst h
    exact self_in_power hPow _

theorem empty_in_single (hExt : ExtAx mem) (hSep : SepFOAx mem) (hPow : PowAx mem)
    (witness : V) :
    mem (emptyset hSep witness) (single_empty hSep hPow witness) :=
  (in_single_empty hExt hSep hPow witness _).mpr rfl

theorem empty_neq_single (hExt : ExtAx mem) (hSep : SepFOAx mem) (hPow : PowAx mem)
    (witness : V) :
    emptyset hSep witness ≠ single_empty hSep hPow witness := by
  intro heq
  have h := empty_in_single hExt hSep hPow witness
  rw [← heq] at h
  exact emptyset_spec hSep witness _ h

theorem empty_in_pair (hSep : SepFOAx mem) (hPow : PowAx mem) (witness : V) :
    mem (emptyset hSep witness) (pair_empty hSep hPow witness) := by
  apply power_intro
  intro y hy
  exact absurd hy (emptyset_spec hSep witness y)

theorem single_in_pair (hSep : SepFOAx mem) (hPow : PowAx mem) (witness : V) :
    mem (single_empty hSep hPow witness) (pair_empty hSep hPow witness) :=
  power_intro hPow _ _ (Sub_refl _)

/-! ### PAIRING -/

/-- vars: 0=z, 1=x; params via e: e0=∅, e1=a, e2={∅}, e3=b -/
def psi_pair : Form :=
  fOr (fAnd (fEq 1 2) (fEq 0 3)) (fAnd (fEq 1 4) (fEq 0 5))

noncomputable def e_pair (hSep : SepFOAx mem) (hPow : PowAx mem) (witness : V)
    (a b : V) : Nat → V
  | 0 => emptyset hSep witness
  | 1 => a
  | 2 => single_empty hSep hPow witness
  | 3 => b
  | _+4 => witness

noncomputable def e_ab (witness : V) (a b : V) : Nat → V
  | 0 => a
  | 1 => b
  | _+2 => witness

theorem Hrel_pair (hSep : SepFOAx mem) (hPow : PowAx mem) (witness : V)
    (a b z x : V) :
    relOf mem psi_pair (e_pair hSep hPow witness a b) z x
      ↔ ((x = emptyset hSep witness ∧ z = a) ∨
         (x = single_empty hSep hPow witness ∧ z = b)) := Iff.rfl

theorem Pairing (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∀ a b : V, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b) := by
  intro a b
  have hfun : Functional (relOf mem psi_pair (e_pair hSep hPow witness a b)) := by
    intro x z₁ z₂ hz₁ hz₂
    rcases (Hrel_pair hSep hPow witness a b z₁ x).mp hz₁ with h₁ | h₁ <;>
      rcases (Hrel_pair hSep hPow witness a b z₂ x).mp hz₂ with h₂ | h₂
    · exact h₁.2.trans h₂.2.symm
    · exact (empty_neq_single hExt hSep hPow witness (h₁.1.symm.trans h₂.1)).elim
    · exact (empty_neq_single hExt hSep hPow witness (h₂.1.symm.trans h₁.1)).elim
    · exact h₁.2.trans h₂.2.symm
  have hSL : SetLike mem (relOf mem psi_pair (e_pair hSep hPow witness a b)) :=
    setLike_of_functional_host (power hPow) (self_in_power hPow) witness hfun
  obtain ⟨w, hsub, hclosed⟩ :=
    hClo psi_pair (e_pair hSep hPow witness a b) hSL (pair_empty hSep hPow witness)
  have ha : mem a w := by
    apply hclosed a (emptyset hSep witness)
    · exact (Hrel_pair hSep hPow witness a b a _).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact hsub _ (empty_in_pair hSep hPow witness)
  have hb : mem b w := by
    apply hclosed b (single_empty hSep hPow witness)
    · exact (Hrel_pair hSep hPow witness a b b _).mpr (Or.inr ⟨rfl, rfl⟩)
    · exact hsub _ (single_in_pair hSep hPow witness)
  refine ⟨sepF hSep w (fOr (fEq 0 1) (fEq 0 2)) (e_ab witness a b), fun x => ?_⟩
  constructor
  · intro h
    exact ((sepF_spec hSep w _ _ x).mp h).2
  · intro h
    apply (sepF_spec hSep w _ _ x).mpr
    refine ⟨?_, h⟩
    rcases h with rfl | rfl
    · exact ha
    · exact hb

/-! ### UNION -/

/-- membership relation: `relOf psi_mem e z x = mem z x` -/
def psi_mem : Form := fMem 0 1

theorem Hrel_mem (e : Nat → V) (z x : V) :
    relOf mem psi_mem e z x ↔ mem z x := Iff.rfl

/-- separation predicate for the union: element 0=x, param e0=s -/
def phi_un : Form := fEx (fAnd (fMem 1 0) (fMem 0 2))

noncomputable def e_un (witness : V) (s : V) : Nat → V
  | 0 => s
  | _+1 => witness

theorem Union (witness : V) (hSep : SepFOAx mem) (hClo : ClosureFOAx mem) :
    ∀ s : V, ∃ u, ∀ x, mem x u ↔ ∃ v, mem x v ∧ mem v s := by
  intro s
  have hSL : SetLike mem (relOf mem psi_mem (fun _ => witness)) := by
    intro x
    exact ⟨x, fun z hz => hz⟩
  obtain ⟨w, hsub, hclosed⟩ := hClo psi_mem (fun _ => witness) hSL s
  refine ⟨sepF hSep w phi_un (e_un witness s), fun x => ?_⟩
  constructor
  · intro h
    exact ((sepF_spec hSep w phi_un (e_un witness s) x).mp h).2
  · intro h
    apply (sepF_spec hSep w phi_un (e_un witness s) x).mpr
    refine ⟨?_, h⟩
    obtain ⟨v, hxv, hvs⟩ := h
    exact hclosed x v hxv (hsub v hvs)

/-! ### INFINITY -/

theorem singleton_exists (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∀ x : V, ∃ s, ∀ t, mem t s ↔ t = x := by
  intro x
  obtain ⟨p, hp⟩ := Pairing witness hExt hSep hPow hClo x x
  exact ⟨p, fun t => by simpa only [or_self] using hp t⟩

theorem succ_exists (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∀ x : V, ∃ sx, ∀ t, mem t sx ↔ (mem t x ∨ t = x) := by
  intro x
  obtain ⟨sg, hsg⟩ := singleton_exists witness hExt hSep hPow hClo x
  obtain ⟨pr, hpr⟩ := Pairing witness hExt hSep hPow hClo x sg
  obtain ⟨u, hu⟩ := Union witness hSep hClo pr
  refine ⟨u, fun t => ?_⟩
  constructor
  · intro h
    obtain ⟨v, htv, hvpr⟩ := (hu t).mp h
    rcases (hpr v).mp hvpr with rfl | rfl
    · exact Or.inl htv
    · exact Or.inr ((hsg t).mp htv)
  · intro h
    apply (hu t).mpr
    rcases h with htx | htx
    · exact ⟨x, htx, (hpr x).mpr (Or.inl rfl)⟩
    · exact ⟨sg, (hsg t).mpr htx, (hpr sg).mpr (Or.inr rfl)⟩

/-- successor relation: `relOf psi_succ e z x ↔ ∀ t, mem t z ↔ (mem t x ∨ t = x)` -/
def psi_succ : Form :=
  fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2)))

theorem Hrel_succ (e : Nat → V) (z x : V) :
    relOf mem psi_succ e z x ↔ (∀ t, mem t z ↔ (mem t x ∨ t = x)) := by
  constructor
  · intro h t; exact ⟨(h t).1, (h t).2⟩
  · intro h t; exact ⟨(h t).mp, (h t).mpr⟩

theorem Infinity (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∃ I : V, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
      (∀ x, mem x I →
        ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) := by
  have hfun : Functional (relOf mem psi_succ (fun _ => witness)) := by
    intro x z₁ z₂ hz₁ hz₂
    have h₁ := (Hrel_succ (fun _ => witness) z₁ x).mp hz₁
    have h₂ := (Hrel_succ (fun _ => witness) z₂ x).mp hz₂
    apply hExt
    intro t
    rw [h₁ t, h₂ t]
  have hSL : SetLike mem (relOf mem psi_succ (fun _ => witness)) :=
    setLike_of_functional_host (power hPow) (self_in_power hPow) witness hfun
  obtain ⟨w, hsub, hclosed⟩ :=
    hClo psi_succ (fun _ => witness) hSL (single_empty hSep hPow witness)
  refine ⟨w, ⟨emptyset hSep witness, ?_, emptyset_spec hSep witness⟩, ?_⟩
  · exact hsub _ (empty_in_single hExt hSep hPow witness)
  · intro x hx
    obtain ⟨sx, hsx⟩ := succ_exists witness hExt hSep hPow hClo x
    refine ⟨sx, ?_, hsx⟩
    apply hclosed sx x
    · exact (Hrel_succ (fun _ => witness) sx x).mpr hsx
    · exact hx

/-! ### REPLACEMENT -/

/-- swap vars 0,1 and shift the rest up by one (to pass a new binder) -/
def rhoRepl : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k+2 => k+3

/-- separation predicate for the image: "∃ x (=var0 here), x ∈ a ∧ psi(y,x)" -/
def chi (psi : Form) : Form := fEx (fAnd (fMem 0 2) (rename rhoRepl psi))

theorem rho_env (d y a : V) (e : Nat → V) :
    ∀ n, (scons d (scons y (scons a e))) (rhoRepl n) = (scons y (scons d e)) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _+2 => rfl

theorem chi_spec (psi : Form) (e : Nat → V) (a y : V) :
    Sat mem (scons y (scons a e)) (chi psi)
      ↔ ∃ d, mem d a ∧ relOf mem psi e y d := by
  constructor
  · intro ⟨d, hda, hpsi⟩
    refine ⟨d, hda, ?_⟩
    exact (Sat_rename_ext psi rhoRepl _ _ (rho_env d y a e)).mp hpsi
  · intro ⟨d, hda, hpsi⟩
    refine ⟨d, hda, ?_⟩
    exact (Sat_rename_ext psi rhoRepl _ _ (rho_env d y a e)).mpr hpsi

theorem ReplacementFO (witness : V) (hSep : SepFOAx mem) (hPow : PowAx mem)
    (hClo : ClosureFOAx mem) :
    ∀ (psi : Form) (e : Nat → V),
      Functional (relOf mem psi e) →
      ∀ a : V, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi e y x := by
  intro psi e hfun a
  have hSL : SetLike mem (relOf mem psi e) :=
    setLike_of_functional_host (power hPow) (self_in_power hPow) witness hfun
  obtain ⟨w, hsub, hclosed⟩ := hClo psi e hSL a
  refine ⟨sepF hSep w (chi psi) (scons a e), fun y => ?_⟩
  constructor
  · intro h
    exact (chi_spec psi e a y).mp ((sepF_spec hSep w (chi psi) (scons a e) y).mp h).2
  · intro h
    apply (sepF_spec hSep w (chi psi) (scons a e) y).mpr
    refine ⟨?_, (chi_spec psi e a y).mpr h⟩
    obtain ⟨x, hxa, hyx⟩ := h
    exact hclosed y x hyx (hsub x hxa)

/-! ### This T-model satisfies each ZF axiom -/

theorem sat_Ext (hExt : ExtAx mem) : ∀ e : Nat → V, Sat mem e Ext_form := by
  exact bridge_Ext.mpr (by simpa only [ExtAx] using hExt)

theorem sat_Pair (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∀ e : Nat → V, Sat mem e Pair_form := by
  exact bridge_Pair.mpr (Pairing witness hExt hSep hPow hClo)

theorem sat_Union (witness : V) (hSep : SepFOAx mem) (hClo : ClosureFOAx mem) :
    ∀ e : Nat → V, Sat mem e Union_form := by
  exact bridge_Union.mpr (Union witness hSep hClo)

theorem sat_Pow (hPow : PowAx mem) : ∀ e : Nat → V, Sat mem e Pow_form := by
  exact bridge_Pow.mpr (by simpa only [PowAx] using hPow)

theorem sat_Inf (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) :
    ∀ e : Nat → V, Sat mem e Inf_form := by
  intro e
  exact (bridge_Inf e).mpr (Infinity witness hExt hSep hPow hClo)

theorem sat_Reg (hReg : RegAx mem) : ∀ e : Nat → V, Sat mem e Reg_form := by
  exact bridge_Reg.mpr (by simpa only [RegAx] using hReg)

theorem sat_Sep (hSep : SepFOAx mem) :
    ∀ (phi : Form) (e : Nat → V), Sat mem e (Sep_form phi) := by
  exact bridge_Sep.mpr (by simpa only [SepFOAx] using hSep)

theorem sat_Repl (witness : V) (hSep : SepFOAx mem) (hPow : PowAx mem)
    (hClo : ClosureFOAx mem) :
    ∀ (psi : Form) (e : Nat → V), Sat mem e (Repl_form psi) := by
  intro psi e
  exact (bridge_Repl psi e).mpr (ReplacementFO witness hSep hPow hClo psi e)

theorem sat_ZFax (witness : V) (hExt : ExtAx mem) (hSep : SepFOAx mem)
    (hPow : PowAx mem) (hClo : ClosureFOAx mem) (hReg : RegAx mem) :
    ∀ f, ZFax f → ∀ e : Nat → V, Sat mem e f := by
  intro f hf e
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩
  · exact sat_Ext hExt e
  · exact sat_Pair witness hExt hSep hPow hClo e
  · exact sat_Union witness hSep hClo e
  · exact sat_Pow hPow e
  · exact sat_Inf witness hExt hSep hPow hClo e
  · exact sat_Reg hReg e
  · exact sat_Sep hSep phi e
  · exact sat_Repl witness hSep hPow hClo psi e

/-- In this (arbitrary) model of T, every ZF-provable formula holds. -/
theorem ZF_provable_holds_in_T (witness : V) (hExt : ExtAx mem)
    (hSep : SepFOAx mem) (hPow : PowAx mem) (hClo : ClosureFOAx mem)
    (hReg : RegAx mem) :
    ∀ phi, ZFprov phi → ∀ e : Nat → V, Sat mem e phi := by
  intro phi ⟨G, hG, hprov⟩ e
  apply soundness hprov e
  intro x hx
  exact sat_ZFax witness hExt hSep hPow hClo hReg x (hG x hx) e

end DeepForward

/-! ## The Closure schema as a closed formula, and its satisfaction bridge
to the abstract set-like/closure statement. -/

/-- set-like binders `∀ x, ∃ y, ∀ z` (z=0, y=1, x=2);
`psi(z,x)`: 0→0, 1→2, (2+j)→(3+j) -/
def r_sl : Nat → Nat
  | 0 => 0
  | 1 => 2
  | j+2 => j+3

/-- closure body binders `∀ s, ∃ w, ∀ d1, ∀ d2` (d2=0, d1=1, w=2, s=3);
`psi(d1,d2)`: 0→1, 1→0, (2+j)→(4+j) -/
def r_cl : Nat → Nat
  | 0 => 1
  | 1 => 0
  | j+2 => j+4

def SetLikeForm (psi : Form) : Form :=
  fAll (fEx (fAll (fImp (rename r_sl psi) (fMem 0 1))))

def ClosureBodyForm (psi : Form) : Form :=
  fAll (fEx (fAnd (fAll (fImp (fMem 0 2) (fMem 0 1)))
                  (fAll (fAll (fImp (fAnd (rename r_cl psi) (fMem 0 2)) (fMem 1 2))))))

def Closure_form (psi : Form) : Form :=
  fImp (SetLikeForm psi) (ClosureBodyForm psi)

section ClosureBridge

variable {V : Type u} {mem : V → V → Prop}

theorem r_sl_env (z y x : V) (e : Nat → V) :
    ∀ n, scons z (scons y (scons x e)) (r_sl n) = scons z (scons x e) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _+2 => rfl

theorem r_cl_env (d2 d1 w s : V) (e : Nat → V) :
    ∀ n, scons d2 (scons d1 (scons w (scons s e))) (r_cl n)
      = scons d1 (scons d2 e) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _+2 => rfl

/-- the rename-r_cl atom denotes `relOf psi e d1 d2` -/
theorem rcl_rel (psi : Form) (e : Nat → V) (d1 d2 w s : V) :
    Sat mem (scons d2 (scons d1 (scons w (scons s e)))) (rename r_cl psi)
      ↔ relOf mem psi e d1 d2 := by
  exact Sat_rename_relOf psi r_cl _ e d1 d2 (r_cl_env d2 d1 w s e)

theorem bridge_SetLike (psi : Form) (e : Nat → V) :
    Sat mem e (SetLikeForm psi) ↔ SetLike mem (relOf mem psi e) := by
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, fun z hz => ?_⟩
    apply hy z
    exact (Sat_rename_relOf psi r_sl _ e z x (r_sl_env z y x e)).mpr hz
  · intro h x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, fun z hz => ?_⟩
    apply hy z
    exact (Sat_rename_relOf psi r_sl _ e z x (r_sl_env z y x e)).mp hz

theorem bridge_ClosureBody (psi : Form) (e : Nat → V) :
    Sat mem e (ClosureBodyForm psi) ↔
      (∀ s, ∃ w, Sub mem s w ∧
        (∀ u v, relOf mem psi e u v → mem v w → mem u w)) := by
  constructor
  · intro h s
    obtain ⟨w, hsub, hcl⟩ := h s
    refine ⟨w, fun t ht => hsub t ht, fun u v hrel hvw => ?_⟩
    exact hcl u v ⟨(rcl_rel psi e u v w s).mpr hrel, hvw⟩
  · intro h s
    obtain ⟨w, hsub, hcl⟩ := h s
    refine ⟨w, fun t ht => hsub t ht, fun d1 d2 hc => ?_⟩
    have hc' : Sat mem (scons d2 (scons d1 (scons w (scons s e))))
        (rename r_cl psi) ∧ mem d2 w := hc
    exact hcl d1 d2 ((rcl_rel psi e d1 d2 w s).mp hc'.1) hc'.2

theorem bridge_Closure (psi : Form) (e : Nat → V) :
    Sat mem e (Closure_form psi) ↔
      (SetLike mem (relOf mem psi e) →
        ∀ s, ∃ w, Sub mem s w ∧
          (∀ u v, relOf mem psi e u v → mem v w → mem u w)) := by
  constructor
  · intro h hsl
    exact (bridge_ClosureBody psi e).mp (h ((bridge_SetLike psi e).mpr hsl))
  · intro h hsl
    exact (bridge_ClosureBody psi e).mpr (h ((bridge_SetLike psi e).mp hsl))

end ClosureBridge

/-! ## ZF and T as sentence theories -/

def Tax_s (f : Form) : Prop :=
  f = sealF Ext_form ∨ f = sealF Reg_form ∨ f = sealF Pow_form ∨
  (∃ phi, f = sealF (Sep_form phi)) ∨ (∃ psi, f = sealF (Closure_form psi))

theorem Sentences_Tax : Sentences Tax_s := by
  intro f hf
  rcases hf with rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩ <;> exact Sentence_seal _

theorem bridge_Closure_fwd {V : Type u} {mem : V → V → Prop}
    (H : ∀ (psi : Form) (e : Nat → V), Sat mem e (Closure_form psi)) :
    ∀ (psi : Form) (e : Nat → V), SetLike mem (relOf mem psi e) →
      ∀ s, ∃ w, Sub mem s w ∧
        (∀ u v, relOf mem psi e u v → mem v w → mem u w) :=
  fun psi e => (bridge_Closure psi e).mp (H psi e)

/-- every T-model is a ZF-model -/
theorem Tmodel_sat_ZF {V : Type u} {mem : V → V → Prop} (v : Nat → V)
    (hT : ∀ g, Tax_s g → Sat mem v g) :
    ∀ g, ZFax_s g → Sat mem v g := by
  have hE : ∀ e : Nat → V, Sat mem e Ext_form :=
    extract Tax_s v Ext_form hT (Or.inl rfl)
  have hR : ∀ e : Nat → V, Sat mem e Reg_form :=
    extract Tax_s v Reg_form hT (Or.inr (Or.inl rfl))
  have hP : ∀ e : Nat → V, Sat mem e Pow_form :=
    extract Tax_s v Pow_form hT (Or.inr (Or.inr (Or.inl rfl)))
  have hS : ∀ (phi : Form) (e : Nat → V), Sat mem e (Sep_form phi) := fun phi =>
    extract Tax_s v (Sep_form phi) hT
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩))))
  have hC : ∀ (psi : Form) (e : Nat → V), Sat mem e (Closure_form psi) := fun psi =>
    extract Tax_s v (Closure_form psi) hT
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨psi, rfl⟩))))
  have AxE : ExtAx mem := bridge_Ext_fwd hE
  have AxR : RegAx mem := bridge_Reg_fwd hR
  have AxP : PowAx mem := bridge_Pow_fwd hP
  have AxS : SepFOAx mem := bridge_Sep_fwd hS
  have AxC : ClosureFOAx mem := bridge_Closure_fwd hC
  intro g hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩
  · exact hT _ (Or.inl rfl)
  · exact hT _ (Or.inr (Or.inl rfl))
  · exact hT _ (Or.inr (Or.inr (Or.inl rfl)))
  · exact (closeN_valid (bound Pair_form) Pair_form).mpr
      (sat_Pair (v 0) AxE AxS AxP AxC) v
  · exact (closeN_valid (bound Union_form) Union_form).mpr
      (sat_Union (v 0) AxS AxC) v
  · exact (closeN_valid (bound Inf_form) Inf_form).mpr
      (sat_Inf (v 0) AxE AxS AxP AxC) v
  · exact hT _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩))))
  · exact (closeN_valid (bound (Repl_form psi)) (Repl_form psi)).mpr
      (sat_Repl (v 0) AxS AxP AxC psi) v

/-- FORWARD SYNTACTIC DIRECTION: everything ZF proves, T proves. -/
theorem ZF_implies_T (phi : Form) (_hphi : Sentence phi)
    (hZF : BProv ZFax_s [] phi) : BProv Tax_s [] phi := by
  exact theory_transfer ZFax_s Tax_s [] phi Sentences_Tax
    (fun _Dom _m v hTsat => Tmodel_sat_ZF v hTsat) hZF

/-! ## Part C.  Every first-order ZF model satisfies the Closure schema,
hence is a T-model; generic theory transfer yields the converse
syntactic direction and the full deductive equivalence. -/

/-- every ZF model satisfies every instance of the (open) Closure formula -/
theorem ZFmodel_sat_Closure {V : Type u} {mem : V → V → Prop} (v : Nat → V)
    (hZ : ∀ g, ZFax_s g → Sat mem v g) :
    ∀ (psi : Form) (e : Nat → V), Sat mem e (Closure_form psi) := by
  intro psi e
  have AxE : ExtAx mem := bridge_Ext_fwd
    (extract ZFax_s v Ext_form hZ (Or.inl rfl))
  have AxS : SepFOAx mem := bridge_Sep_fwd (fun phi =>
    extract ZFax_s v (Sep_form phi) hZ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩))))))))
  have AxP : ∀ a b : V, ∃ p, ∀ x, mem x p ↔ (x = a ∨ x = b) := bridge_Pair_fwd
    (extract ZFax_s v Pair_form hZ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have AxU : ∀ u : V, ∃ w, ∀ x, mem x w ↔ ∃ y, mem x y ∧ mem y u :=
    bridge_Union_fwd
      (extract ZFax_s v Union_form hZ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have AxI : ∃ I : V, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
      (∀ x, mem x I →
        ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ (mem t x ∨ t = x)) :=
    bridge_Inf_fwd v
      (extract ZFax_s v Inf_form hZ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) v)
  have AxR : ∀ (psi' : Form) (e' : Nat → V),
      Functional (relOf mem psi' e') →
      ∀ a, ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ relOf mem psi' e' y x :=
    bridge_Repl_fwd (fun psi' =>
      extract ZFax_s v (Repl_form psi') hZ
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨psi', rfl⟩))))))))
  apply (bridge_Closure psi e).mpr
  intro hSL s
  exact ClosureFO_of_ZF ⟨AxE, AxS, AxP, AxU, AxI, AxR⟩ psi e hSL s

/-- every ZF-model is a T-model (converse of `Tmodel_sat_ZF`) -/
theorem ZFmodel_sat_T {V : Type u} {mem : V → V → Prop} (v : Nat → V)
    (hZ : ∀ g, ZFax_s g → Sat mem v g) :
    ∀ g, Tax_s g → Sat mem v g := by
  intro g hg
  rcases hg with rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩
  · exact hZ _ (Or.inl rfl)
  · exact hZ _ (Or.inr (Or.inl rfl))
  · exact hZ _ (Or.inr (Or.inr (Or.inl rfl)))
  · exact hZ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩)))))))
  · exact (closeN_valid (bound (Closure_form psi)) (Closure_form psi)).mpr
      (fun e => ZFmodel_sat_Closure v hZ psi e) v

/-- T and ZF have exactly the same models -/
theorem T_ZF_same_models (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom) :
    (∀ g, Tax_s g → Sat m v g) ↔ (∀ g, ZFax_s g → Sat m v g) :=
  ⟨Tmodel_sat_ZF v, ZFmodel_sat_T v⟩

/-- THE CONVERSE SYNTACTIC DIRECTION: everything T proves, ZF proves. -/
theorem T_implies_ZF (phi : Form) (_hphi : Sentence phi)
    (hT : BProv Tax_s [] phi) : BProv ZFax_s [] phi := by
  exact theory_transfer Tax_s ZFax_s [] phi Sentences_ZF
    (fun _Dom _m v hZsat => ZFmodel_sat_T v hZsat) hT

/-- THE HEADLINE: deductive equivalence of T and ZF, both directions. -/
theorem T_iff_ZF (phi : Form) (hphi : Sentence phi) :
    BProv Tax_s [] phi ↔ BProv ZFax_s [] phi :=
  ⟨T_implies_ZF phi hphi, ZF_implies_T phi hphi⟩

/-- cross-check: the same equivalence, derived instead as an instance of
the general same-models theorem `theory_equiv` from Completeness.lean -/
theorem T_iff_ZF_via_theory_equiv (phi : Form) (hphi : Sentence phi) :
    BProv Tax_s [] phi ↔ BProv ZFax_s [] phi :=
  theory_equiv Tax_s ZFax_s Sentences_Tax Sentences_ZF T_ZF_same_models phi hphi

end SetTheory
