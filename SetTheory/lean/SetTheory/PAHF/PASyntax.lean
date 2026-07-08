/-
  SetTheory.PAHF.PASyntax

  First-order PA syntax (`Term`, `Formula`), the `BProv` Hilbert calculus, arithmetic macros, and the object-level `BProv_Ax_s_*` provability lemmas.  Depends on the semantic core for `AckermannHF.Mem`.
-/
import SetTheory.Completeness
import SetTheory.PAHF.AckermannHFCore

namespace SetTheory

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

/-- Term-parametric strict order.  This is the same relation as `ltAt`, but
the compared values may be arbitrary PA terms in the ambient context. -/
def ltTermAt (a b : Term) : Formula :=
  ex (eq (Term.add (Term.rename Nat.succ a) (Term.succ (Term.var 0)))
    (Term.rename Nat.succ b))

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

/-- Term-parametric remainder relation.  The remainder may be an arbitrary PA
term, while the dividend and modulus remain slots. -/
def remTermAt (rem : Term) (value modulus : Nat) : Formula :=
  ex (and
    (ltTermAt (Term.rename Nat.succ rem) (Term.var (modulus+1)))
    (eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.rename Nat.succ rem))))

def remEqAt (rem value modulus : Nat) : Formula :=
  ex (eq (Term.var (value+1))
    (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
      (Term.var (rem+1))))

/-- Term-parametric remainder equation, forgetting the strict bound but keeping
the same quotient witness. -/
def remTermEqAt (rem : Term) (value modulus : Nat) : Formula :=
  ex (eq (Term.var (value+1))
    (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
      (Term.rename Nat.succ rem)))

def betaModTerm (step idx : Nat) : Term :=
  Term.succ (Term.mul (Term.succ (Term.var idx)) (Term.var step))

def betaAt (out code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
    (remAt (out+1) (code+1) 0))

/-- Term-parametric beta entry.  This is `betaAt` with the output slot allowed
to be an arbitrary PA term. -/
def betaTermAt (out : Term) (code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
    (remTermAt (Term.rename Nat.succ out) (code+1) 0))

def betaAtConstIdx (out code step idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0))

/-- Constant-index beta entry with a term-parametric output. -/
def betaTermAtConstIdx (out : Term) (code step idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue)
    (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0))

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

/-- The actual membership formula obtained after the HF empty witness is
instantiated with the closed PA term `0`.  The element remains a slot; only the
set-code output in the initial beta entry is now a closed term. -/
def hfMemZeroSetAt (elem : Nat) : Formula :=
  ex (ex
    (and
      (betaTermAtConstIdx Term.zero 1 0 0)
      (and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex
          (and
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem+3)))))))

theorem subst_up_zero_hfMemAt_zero_set :
    subst (Term.upSubst (instTerm Term.zero)) (hfMemAt 0 1) =
      hfMemZeroSetAt 0 := by
  simp [hfMemZeroSetAt, hfMemAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaAtConstIdx, betaAt, remAt, ltAt,
    leAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt, betaDiv2BitAt,
    betaAtSuccIdx, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
    Term.rename]

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

/-- PA proves the left-zero law for addition. -/
theorem BProv_Ax_s_zero_add_all :
    BProv Ax_s []
      (all (eq (Term.add Term.zero (Term.var 0)) (Term.var 0))) := by
  let phi : Formula := eq (Term.add Term.zero (Term.var 0)) (Term.var 0)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.numeral] using BProv_Ax_s_addZero_term Term.zero
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    have hphi : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.var 0)) (Term.var 0)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi])
    have hstep : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.succ (Term.var 0)))
          (Term.succ (Term.add Term.zero (Term.var 0)))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms Term.zero (Term.var 0))
    have hsucc : BProv Ax_s [phi]
        (eq (Term.succ (Term.add Term.zero (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_eq_congr_succ hphi
    have htarget : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.succ (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_eqTrans hstep hsucc
    simpa [phi, substSuccVar, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename] using htarget
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

/-- Arbitrary-term instance of the PA left-zero law for addition. -/
theorem BProv_Ax_s_zero_add_term {G : List Formula} (t : Term) :
    BProv Ax_s G (eq (Term.add Term.zero t) t) := by
  have hall : BProv Ax_s G
      (all (eq (Term.add Term.zero (Term.var 0)) (Term.var 0))) :=
    BProv_weaken_nil BProv_Ax_s_zero_add_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := t) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst] using hinst

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

/-- PA proves that successor distributes over addition on the left. -/
theorem BProv_Ax_s_succ_add_all (x : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.add (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
          (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0))))) := by
  let phi : Formula :=
    eq
      (Term.add (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
      (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0)))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hleft : BProv Ax_s []
        (eq (Term.add (Term.succ x) Term.zero) (Term.succ x)) :=
      BProv_Ax_s_addZero_term (Term.succ x)
    have hright : BProv Ax_s []
        (eq (Term.succ (Term.add x Term.zero)) (Term.succ x)) :=
      BProv_eq_congr_succ (BProv_Ax_s_addZero_term x)
    have htarget : BProv Ax_s []
        (eq (Term.add (Term.succ x) Term.zero)
          (Term.succ (Term.add x Term.zero))) :=
      BProv_eqTrans hleft (BProv_eqSym hright)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    have hphi : BProv Ax_s [phi]
        (eq (Term.add (Term.succ xs) (Term.var 0))
          (Term.succ (Term.add xs (Term.var 0)))) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs])
    have hleft : BProv Ax_s [phi]
        (eq (Term.add (Term.succ xs) (Term.succ (Term.var 0)))
          (Term.succ (Term.add (Term.succ xs) (Term.var 0)))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addSucc_terms (Term.succ xs) (Term.var 0))
    have hmid : BProv Ax_s [phi]
        (eq (Term.succ (Term.add (Term.succ xs) (Term.var 0)))
          (Term.succ (Term.succ (Term.add xs (Term.var 0))))) :=
      BProv_eq_congr_succ hphi
    have hrightStep : BProv Ax_s [phi]
        (eq (Term.add xs (Term.succ (Term.var 0)))
          (Term.succ (Term.add xs (Term.var 0)))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms xs (Term.var 0))
    have hright : BProv Ax_s [phi]
        (eq (Term.succ (Term.succ (Term.add xs (Term.var 0))))
          (Term.succ (Term.add xs (Term.succ (Term.var 0))))) :=
      BProv_eq_congr_succ (BProv_eqSym hrightStep)
    have htarget : BProv Ax_s [phi]
        (eq (Term.add (Term.succ xs) (Term.succ (Term.var 0)))
          (Term.succ (Term.add xs (Term.succ (Term.var 0))))) :=
      BProv_eqTrans (BProv_eqTrans hleft hmid) hright
    simpa [phi, xs, substSuccVar, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of `S x + y = S (x + y)`. -/
theorem BProv_Ax_s_succ_add_terms {G : List Formula} (x y : Term) :
    BProv Ax_s G
      (eq (Term.add (Term.succ x) y) (Term.succ (Term.add x y))) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.add (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
          (Term.succ (Term.add (Term.rename Nat.succ x) (Term.var 0))))) :=
    BProv_weaken_nil (BProv_Ax_s_succ_add_all x)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := y) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- Cancel one successor from an equality between left-successor additions. -/
theorem BProv_Ax_s_succ_add_cancel_terms {G : List Formula}
    {x y z : Term}
    (h : BProv Ax_s G
      (eq (Term.add (Term.succ x) y) (Term.add (Term.succ x) z))) :
    BProv Ax_s G (eq (Term.add x y) (Term.add x z)) := by
  have hleft : BProv Ax_s G
      (eq (Term.add (Term.succ x) y) (Term.succ (Term.add x y))) :=
    BProv_Ax_s_succ_add_terms x y
  have hright : BProv Ax_s G
      (eq (Term.add (Term.succ x) z) (Term.succ (Term.add x z))) :=
    BProv_Ax_s_succ_add_terms x z
  have hsuccEq : BProv Ax_s G
      (eq (Term.succ (Term.add x y)) (Term.succ (Term.add x z))) :=
    BProv_eqTrans (BProv_eqTrans (BProv_eqSym hleft) h) hright
  have hinj : BProv Ax_s G
      (imp
        (eq (Term.succ (Term.add x y)) (Term.succ (Term.add x z)))
        (eq (Term.add x y) (Term.add x z))) :=
    BProv_weaken_nil
      (BProv_Ax_s_succInj_terms (Term.add x y) (Term.add x z))
  exact BProv_mp Ax_s G _ _ hinj hsuccEq

/-- PA proves left-cancellation for addition, uniformly in the left addend. -/
theorem BProv_Ax_s_add_cancel_left_all (y z : Term) :
    BProv Ax_s []
      (all
        (imp
          (eq
            (Term.add (Term.var 0) (Term.rename Nat.succ y))
            (Term.add (Term.var 0) (Term.rename Nat.succ z)))
          (eq (Term.rename Nat.succ y) (Term.rename Nat.succ z)))) := by
  let phi : Formula :=
    imp
      (eq
        (Term.add (Term.var 0) (Term.rename Nat.succ y))
        (Term.add (Term.var 0) (Term.rename Nat.succ z)))
      (eq (Term.rename Nat.succ y) (Term.rename Nat.succ z))
  have hzeroBody : BProv Ax_s
      [eq (Term.add Term.zero y) (Term.add Term.zero z)]
      (eq y z) := by
    have heq : BProv Ax_s
        [eq (Term.add Term.zero y) (Term.add Term.zero z)]
        (eq (Term.add Term.zero y) (Term.add Term.zero z)) :=
      BProv_ass (B := Ax_s)
        (G := [eq (Term.add Term.zero y) (Term.add Term.zero z)])
        (by simp)
    have hy : BProv Ax_s
        [eq (Term.add Term.zero y) (Term.add Term.zero z)]
        (eq (Term.add Term.zero y) y) :=
      BProv_Ax_s_zero_add_term y
    have hz : BProv Ax_s
        [eq (Term.add Term.zero y) (Term.add Term.zero z)]
        (eq (Term.add Term.zero z) z) :=
      BProv_Ax_s_zero_add_term z
    exact BProv_eqTrans (BProv_eqTrans (BProv_eqSym hy) heq) hz
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using
      BProv_impI hzeroBody
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let ys : Term := Term.rename Nat.succ y
    let zs : Term := Term.rename Nat.succ z
    let succEq : Formula :=
      eq (Term.add (Term.succ (Term.var 0)) ys)
        (Term.add (Term.succ (Term.var 0)) zs)
    have hinner : BProv Ax_s [succEq, phi] (eq ys zs) := by
      have heqSucc : BProv Ax_s [succEq, phi] succEq :=
        BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp)
      have hcancel : BProv Ax_s [succEq, phi]
          (eq (Term.add (Term.var 0) ys) (Term.add (Term.var 0) zs)) :=
        BProv_Ax_s_succ_add_cancel_terms heqSucc
      have hih : BProv Ax_s [succEq, phi]
          (imp
            (eq (Term.add (Term.var 0) ys) (Term.add (Term.var 0) zs))
            (eq ys zs)) := by
        have hphi : BProv Ax_s [succEq, phi] phi :=
          BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp [phi])
        simpa [phi, ys, zs] using hphi
      exact BProv_mp Ax_s [succEq, phi] _ _ hih hcancel
    have himp : BProv Ax_s [phi] (imp succEq (eq ys zs)) :=
      BProv_impI hinner
    simpa [phi, ys, zs, succEq, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using himp
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

/-- Modus-ponens form of left-cancellation for addition. -/
theorem BProv_Ax_s_add_cancel_left_terms {G : List Formula}
    {x y z : Term}
    (h : BProv Ax_s G (eq (Term.add x y) (Term.add x z))) :
    BProv Ax_s G (eq y z) := by
  have hall : BProv Ax_s G
      (all
        (imp
          (eq
            (Term.add (Term.var 0) (Term.rename Nat.succ y))
            (Term.add (Term.var 0) (Term.rename Nat.succ z)))
          (eq (Term.rename Nat.succ y) (Term.rename Nat.succ z)))) :=
    BProv_weaken_nil (BProv_Ax_s_add_cancel_left_all y z)
  have himp : BProv Ax_s G
      (imp (eq (Term.add x y) (Term.add x z)) (eq y z)) := by
    have hinst := BProv_allE (B := Ax_s) (G := G) (t := x) hall
    simpa [subst, instTerm, Term.subst, Term.upSubst,
      term_subst_instTerm_rename_succ] using hinst
  exact BProv_mp Ax_s G _ _ himp h

/-- PA proves right-cancellation for addition, uniformly in the common right
addend. -/
theorem BProv_Ax_s_add_cancel_right_all (x y : Term) :
    BProv Ax_s []
      (all
        (imp
          (eq
            (Term.add (Term.rename Nat.succ x) (Term.var 0))
            (Term.add (Term.rename Nat.succ y) (Term.var 0)))
          (eq (Term.rename Nat.succ x) (Term.rename Nat.succ y)))) := by
  let phi : Formula :=
    imp
      (eq
        (Term.add (Term.rename Nat.succ x) (Term.var 0))
        (Term.add (Term.rename Nat.succ y) (Term.var 0)))
      (eq (Term.rename Nat.succ x) (Term.rename Nat.succ y))
  have hzeroBody : BProv Ax_s
      [eq (Term.add x Term.zero) (Term.add y Term.zero)]
      (eq x y) := by
    have heq : BProv Ax_s
        [eq (Term.add x Term.zero) (Term.add y Term.zero)]
        (eq (Term.add x Term.zero) (Term.add y Term.zero)) :=
      BProv_ass (B := Ax_s)
        (G := [eq (Term.add x Term.zero) (Term.add y Term.zero)])
        (by simp)
    have hx : BProv Ax_s
        [eq (Term.add x Term.zero) (Term.add y Term.zero)]
        (eq (Term.add x Term.zero) x) :=
      BProv_weaken_nil (BProv_Ax_s_addZero_term x)
    have hy : BProv Ax_s
        [eq (Term.add x Term.zero) (Term.add y Term.zero)]
        (eq (Term.add y Term.zero) y) :=
      BProv_weaken_nil (BProv_Ax_s_addZero_term y)
    exact BProv_eqTrans (BProv_eqTrans (BProv_eqSym hx) heq) hy
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using
      BProv_impI hzeroBody
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let ys : Term := Term.rename Nat.succ y
    let succEq : Formula :=
      eq (Term.add xs (Term.succ (Term.var 0)))
        (Term.add ys (Term.succ (Term.var 0)))
    have hinner : BProv Ax_s [succEq, phi] (eq xs ys) := by
      have heqSucc : BProv Ax_s [succEq, phi] succEq :=
        BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp)
      have hxSucc : BProv Ax_s [succEq, phi]
          (eq (Term.add xs (Term.succ (Term.var 0)))
            (Term.succ (Term.add xs (Term.var 0)))) :=
        BProv_weaken_nil (BProv_Ax_s_addSucc_terms xs (Term.var 0))
      have hySucc : BProv Ax_s [succEq, phi]
          (eq (Term.add ys (Term.succ (Term.var 0)))
            (Term.succ (Term.add ys (Term.var 0)))) :=
        BProv_weaken_nil (BProv_Ax_s_addSucc_terms ys (Term.var 0))
      have hsuccEq : BProv Ax_s [succEq, phi]
          (eq (Term.succ (Term.add xs (Term.var 0)))
            (Term.succ (Term.add ys (Term.var 0)))) :=
        BProv_eqTrans (BProv_eqTrans (BProv_eqSym hxSucc) heqSucc) hySucc
      have hinj : BProv Ax_s [succEq, phi]
          (imp
            (eq (Term.succ (Term.add xs (Term.var 0)))
              (Term.succ (Term.add ys (Term.var 0))))
            (eq (Term.add xs (Term.var 0)) (Term.add ys (Term.var 0)))) :=
        BProv_weaken_nil
          (BProv_Ax_s_succInj_terms
            (Term.add xs (Term.var 0)) (Term.add ys (Term.var 0)))
      have hpredEq : BProv Ax_s [succEq, phi]
          (eq (Term.add xs (Term.var 0)) (Term.add ys (Term.var 0))) :=
        BProv_mp Ax_s _ _ _ hinj hsuccEq
      have hih : BProv Ax_s [succEq, phi]
          (imp
            (eq (Term.add xs (Term.var 0)) (Term.add ys (Term.var 0)))
            (eq xs ys)) := by
        have hphi : BProv Ax_s [succEq, phi] phi :=
          BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp [phi])
        simpa [phi, xs, ys] using hphi
      exact BProv_mp Ax_s _ _ _ hih hpredEq
    have himp : BProv Ax_s [phi] (imp succEq (eq xs ys)) :=
      BProv_impI hinner
    simpa [phi, xs, ys, succEq, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using himp
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

/-- Modus-ponens form of right-cancellation for addition. -/
theorem BProv_Ax_s_add_cancel_right_terms {G : List Formula}
    {x y z : Term}
    (h : BProv Ax_s G (eq (Term.add x z) (Term.add y z))) :
    BProv Ax_s G (eq x y) := by
  have hall : BProv Ax_s G
      (all
        (imp
          (eq
            (Term.add (Term.rename Nat.succ x) (Term.var 0))
            (Term.add (Term.rename Nat.succ y) (Term.var 0)))
          (eq (Term.rename Nat.succ x) (Term.rename Nat.succ y)))) :=
    BProv_weaken_nil (BProv_Ax_s_add_cancel_right_all x y)
  have himp : BProv Ax_s G
      (imp (eq (Term.add x z) (Term.add y z)) (eq x y)) := by
    have hinst := BProv_allE (B := Ax_s) (G := G) (t := z) hall
    simpa [subst, instTerm, Term.subst, Term.upSubst,
      term_subst_instTerm_rename_succ] using hinst
  exact BProv_mp Ax_s G _ _ himp h

/-- PA proves associativity of addition, uniformly in the third addend. -/
theorem BProv_Ax_s_add_assoc_all (x y : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.add
            (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.add (Term.rename Nat.succ x)
            (Term.add (Term.rename Nat.succ y) (Term.var 0))))) := by
  let phi : Formula :=
    eq
      (Term.add
        (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (Term.var 0))
      (Term.add (Term.rename Nat.succ x)
        (Term.add (Term.rename Nat.succ y) (Term.var 0)))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hleftZero : BProv Ax_s []
        (eq (Term.add (Term.add x y) Term.zero) (Term.add x y)) :=
      BProv_Ax_s_addZero_term (Term.add x y)
    have hyZero : BProv Ax_s []
        (eq (Term.add y Term.zero) y) :=
      BProv_Ax_s_addZero_term y
    have hrightZero : BProv Ax_s []
        (eq (Term.add x (Term.add y Term.zero)) (Term.add x y)) :=
      BProv_eq_congr_add_right x hyZero
    have htarget : BProv Ax_s []
        (eq (Term.add (Term.add x y) Term.zero)
          (Term.add x (Term.add y Term.zero))) :=
      BProv_eqTrans hleftZero (BProv_eqSym hrightZero)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let ys : Term := Term.rename Nat.succ y
    have hphi : BProv Ax_s [phi]
        (eq (Term.add (Term.add xs ys) (Term.var 0))
          (Term.add xs (Term.add ys (Term.var 0)))) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs, ys])
    have hleftSucc : BProv Ax_s [phi]
        (eq (Term.add (Term.add xs ys) (Term.succ (Term.var 0)))
          (Term.succ (Term.add (Term.add xs ys) (Term.var 0)))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addSucc_terms (Term.add xs ys) (Term.var 0))
    have hihSucc : BProv Ax_s [phi]
        (eq (Term.succ (Term.add (Term.add xs ys) (Term.var 0)))
          (Term.succ (Term.add xs (Term.add ys (Term.var 0))))) :=
      BProv_eq_congr_succ hphi
    have hySucc : BProv Ax_s [phi]
        (eq (Term.add ys (Term.succ (Term.var 0)))
          (Term.succ (Term.add ys (Term.var 0)))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addSucc_terms ys (Term.var 0))
    have hrightCong : BProv Ax_s [phi]
        (eq
          (Term.add xs (Term.add ys (Term.succ (Term.var 0))))
          (Term.add xs (Term.succ (Term.add ys (Term.var 0))))) :=
      BProv_eq_congr_add_right xs hySucc
    have hxSucc : BProv Ax_s [phi]
        (eq
          (Term.add xs (Term.succ (Term.add ys (Term.var 0))))
          (Term.succ (Term.add xs (Term.add ys (Term.var 0))))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addSucc_terms xs (Term.add ys (Term.var 0)))
    have hrightSucc : BProv Ax_s [phi]
        (eq
          (Term.add xs (Term.add ys (Term.succ (Term.var 0))))
          (Term.succ (Term.add xs (Term.add ys (Term.var 0))))) :=
      BProv_eqTrans hrightCong hxSucc
    have htarget : BProv Ax_s [phi]
        (eq
          (Term.add (Term.add xs ys) (Term.succ (Term.var 0)))
          (Term.add xs (Term.add ys (Term.succ (Term.var 0))))) :=
      BProv_eqTrans (BProv_eqTrans hleftSucc hihSucc)
        (BProv_eqSym hrightSucc)
    simpa [phi, xs, ys, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of PA addition associativity. -/
theorem BProv_Ax_s_add_assoc_terms {G : List Formula} (x y z : Term) :
    BProv Ax_s G
      (eq (Term.add (Term.add x y) z)
        (Term.add x (Term.add y z))) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.add
            (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.add (Term.rename Nat.succ x)
            (Term.add (Term.rename Nat.succ y) (Term.var 0))))) :=
    BProv_weaken_nil (BProv_Ax_s_add_assoc_all x y)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := z) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves commutativity of addition, uniformly in the right addend. -/
theorem BProv_Ax_s_add_comm_all (x : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.add (Term.rename Nat.succ x) (Term.var 0))
          (Term.add (Term.var 0) (Term.rename Nat.succ x)))) := by
  let phi : Formula :=
    eq
      (Term.add (Term.rename Nat.succ x) (Term.var 0))
      (Term.add (Term.var 0) (Term.rename Nat.succ x))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hxZero : BProv Ax_s []
        (eq (Term.add x Term.zero) x) :=
      BProv_Ax_s_addZero_term x
    have hzeroX : BProv Ax_s []
        (eq (Term.add Term.zero x) x) :=
      BProv_Ax_s_zero_add_term x
    have htarget : BProv Ax_s []
        (eq (Term.add x Term.zero) (Term.add Term.zero x)) :=
      BProv_eqTrans hxZero (BProv_eqSym hzeroX)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    have hphi : BProv Ax_s [phi]
        (eq (Term.add xs (Term.var 0)) (Term.add (Term.var 0) xs)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs])
    have hleft : BProv Ax_s [phi]
        (eq (Term.add xs (Term.succ (Term.var 0)))
          (Term.succ (Term.add xs (Term.var 0)))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms xs (Term.var 0))
    have hihSucc : BProv Ax_s [phi]
        (eq (Term.succ (Term.add xs (Term.var 0)))
          (Term.succ (Term.add (Term.var 0) xs))) :=
      BProv_eq_congr_succ hphi
    have hright : BProv Ax_s [phi]
        (eq (Term.add (Term.succ (Term.var 0)) xs)
          (Term.succ (Term.add (Term.var 0) xs))) :=
      BProv_Ax_s_succ_add_terms (Term.var 0) xs
    have htarget : BProv Ax_s [phi]
        (eq (Term.add xs (Term.succ (Term.var 0)))
          (Term.add (Term.succ (Term.var 0)) xs)) :=
      BProv_eqTrans (BProv_eqTrans hleft hihSucc) (BProv_eqSym hright)
    simpa [phi, xs, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of PA addition commutativity. -/
theorem BProv_Ax_s_add_comm_terms {G : List Formula} (x y : Term) :
    BProv Ax_s G (eq (Term.add x y) (Term.add y x)) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.add (Term.rename Nat.succ x) (Term.var 0))
          (Term.add (Term.var 0) (Term.rename Nat.succ x)))) :=
    BProv_weaken_nil (BProv_Ax_s_add_comm_all x)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := y) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves, uniformly in the left addend, that adding a successor on the
right never gives back the original left addend. -/
theorem BProv_Ax_s_add_succ_ne_self_all (y : Term) :
    BProv Ax_s []
      (all
        (imp
          (eq
            (Term.add (Term.var 0) (Term.succ (Term.rename Nat.succ y)))
            (Term.var 0))
          bot)) := by
  let phi : Formula :=
    imp
      (eq
        (Term.add (Term.var 0) (Term.succ (Term.rename Nat.succ y)))
        (Term.var 0))
      bot
  have hzeroBody : BProv Ax_s
      [eq (Term.add Term.zero (Term.succ y)) Term.zero]
      bot := by
    have hbad : BProv Ax_s
        [eq (Term.add Term.zero (Term.succ y)) Term.zero]
        (eq (Term.add Term.zero (Term.succ y)) Term.zero) :=
      BProv_ass (B := Ax_s)
        (G := [eq (Term.add Term.zero (Term.succ y)) Term.zero])
        (by simp)
    have hzeroAdd : BProv Ax_s
        [eq (Term.add Term.zero (Term.succ y)) Term.zero]
        (eq (Term.add Term.zero (Term.succ y)) (Term.succ y)) :=
      BProv_Ax_s_zero_add_term (Term.succ y)
    have hsuccZero : BProv Ax_s
        [eq (Term.add Term.zero (Term.succ y)) Term.zero]
        (eq (Term.succ y) Term.zero) :=
      BProv_eqTrans (BProv_eqSym hzeroAdd) hbad
    have hnot : BProv Ax_s
        [eq (Term.add Term.zero (Term.succ y)) Term.zero]
        (imp (eq (Term.succ y) Term.zero) bot) :=
      BProv_weaken_nil (BProv_Ax_s_zeroNotSucc_term y)
    exact BProv_mp Ax_s _ _ _ hnot hsuccZero
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using BProv_impI hzeroBody
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let ys : Term := Term.rename Nat.succ y
    let succEq : Formula :=
      eq (Term.add (Term.succ (Term.var 0)) (Term.succ ys))
        (Term.succ (Term.var 0))
    have hinner : BProv Ax_s [succEq, phi] bot := by
      have heqSucc : BProv Ax_s [succEq, phi] succEq :=
        BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp)
      have haddSucc : BProv Ax_s [succEq, phi]
          (eq (Term.add (Term.succ (Term.var 0)) (Term.succ ys))
            (Term.succ (Term.add (Term.var 0) (Term.succ ys)))) :=
        BProv_Ax_s_succ_add_terms (Term.var 0) (Term.succ ys)
      have hsuccEq : BProv Ax_s [succEq, phi]
          (eq (Term.succ (Term.add (Term.var 0) (Term.succ ys)))
            (Term.succ (Term.var 0))) :=
        BProv_eqTrans (BProv_eqSym haddSucc) heqSucc
      have hinj : BProv Ax_s [succEq, phi]
          (imp
            (eq (Term.succ (Term.add (Term.var 0) (Term.succ ys)))
              (Term.succ (Term.var 0)))
            (eq (Term.add (Term.var 0) (Term.succ ys)) (Term.var 0))) :=
        BProv_weaken_nil
          (BProv_Ax_s_succInj_terms
            (Term.add (Term.var 0) (Term.succ ys)) (Term.var 0))
      have hpredEq : BProv Ax_s [succEq, phi]
          (eq (Term.add (Term.var 0) (Term.succ ys)) (Term.var 0)) :=
        BProv_mp Ax_s _ _ _ hinj hsuccEq
      have hih : BProv Ax_s [succEq, phi]
          (imp
            (eq (Term.add (Term.var 0) (Term.succ ys)) (Term.var 0))
            bot) := by
        have hphi : BProv Ax_s [succEq, phi] phi :=
          BProv_ass (B := Ax_s) (G := [succEq, phi]) (by simp [phi])
        simpa [phi, ys] using hphi
      exact BProv_mp Ax_s _ _ _ hih hpredEq
    have himp : BProv Ax_s [phi] (imp succEq bot) :=
      BProv_impI hinner
    simpa [phi, ys, succEq, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using himp
  have hsuccImp : BProv Ax_s []
      (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccBody
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hsuccImp
  have hind : BProv Ax_s [] (inductionForm phi) := by
    simpa [rename_id] using
      BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) (fun n : Nat => n)
  simpa [phi] using BProv_inductionForm_mp hind hzero hsucc

/-- Modus-ponens form of `BProv_Ax_s_add_succ_ne_self_all`. -/
theorem BProv_Ax_s_add_succ_ne_self_terms {G : List Formula}
    {x y : Term}
    (h : BProv Ax_s G (eq (Term.add x (Term.succ y)) x)) :
    BProv Ax_s G bot := by
  have hall : BProv Ax_s G
      (all
        (imp
          (eq
            (Term.add (Term.var 0) (Term.succ (Term.rename Nat.succ y)))
            (Term.var 0))
          bot)) :=
    BProv_weaken_nil (BProv_Ax_s_add_succ_ne_self_all y)
  have himp : BProv Ax_s G
      (imp (eq (Term.add x (Term.succ y)) x) bot) := by
    have hinst := BProv_allE (B := Ax_s) (G := G) (t := x) hall
    simpa [subst, instTerm, Term.subst, Term.upSubst,
      term_subst_instTerm_rename_succ] using hinst
  exact BProv_mp Ax_s G _ _ himp h

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

/-- Modus-ponens form for the right summand: if `x + y = 0`, then `y = 0`. -/
theorem BProv_Ax_s_add_eq_zero_right_terms {G : List Formula}
    {x y : Term}
    (h : BProv Ax_s G (eq (Term.add x y) Term.zero)) :
    BProv Ax_s G (eq y Term.zero) := by
  have hxZero : BProv Ax_s G (eq x Term.zero) :=
    BProv_Ax_s_add_eq_zero_left_terms h
  have hxAddZero : BProv Ax_s G
      (eq (Term.add x y) (Term.add Term.zero y)) :=
    BProv_eq_congr_add_left y hxZero
  have hzeroAddZero : BProv Ax_s G
      (eq (Term.add Term.zero y) Term.zero) :=
    BProv_eqTrans (BProv_eqSym hxAddZero) h
  have hzeroAdd : BProv Ax_s G (eq (Term.add Term.zero y) y) :=
    BProv_Ax_s_zero_add_term y
  exact BProv_eqTrans (BProv_eqSym hzeroAdd) hzeroAddZero

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

/-- PA proves the left-zero law for multiplication. -/
theorem BProv_Ax_s_zero_mul_all :
    BProv Ax_s []
      (all (eq (Term.mul Term.zero (Term.var 0)) Term.zero)) := by
  let phi : Formula := eq (Term.mul Term.zero (Term.var 0)) Term.zero
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.numeral] using BProv_Ax_s_mulZero_term Term.zero
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    have hphi : BProv Ax_s [phi]
        (eq (Term.mul Term.zero (Term.var 0)) Term.zero) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi])
    have hstep : BProv Ax_s [phi]
        (eq (Term.mul Term.zero (Term.succ (Term.var 0)))
          (Term.add (Term.mul Term.zero (Term.var 0)) Term.zero)) :=
      BProv_weaken_nil
        (BProv_Ax_s_mulSucc_terms Term.zero (Term.var 0))
    have haddZero : BProv Ax_s [phi]
        (eq (Term.add (Term.mul Term.zero (Term.var 0)) Term.zero)
          (Term.mul Term.zero (Term.var 0))) :=
      BProv_weaken_nil
        (BProv_Ax_s_addZero_term (Term.mul Term.zero (Term.var 0)))
    have htarget : BProv Ax_s [phi]
        (eq (Term.mul Term.zero (Term.succ (Term.var 0))) Term.zero) :=
      BProv_eqTrans (BProv_eqTrans hstep haddZero) hphi
    simpa [phi, substSuccVar, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename] using htarget
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

/-- Arbitrary-term instance of `0 * x = 0`. -/
theorem BProv_Ax_s_zero_mul_term {G : List Formula} (t : Term) :
    BProv Ax_s G (eq (Term.mul Term.zero t) Term.zero) := by
  have hall : BProv Ax_s G
      (all (eq (Term.mul Term.zero (Term.var 0)) Term.zero)) :=
    BProv_weaken_nil BProv_Ax_s_zero_mul_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := t) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst] using hinst

/-- PA proves the left-successor normal form for multiplication. -/
theorem BProv_Ax_s_succ_mul_all (x : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.mul (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))
            (Term.var 0)))) := by
  let phi : Formula :=
    eq
      (Term.mul (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
      (Term.add
        (Term.mul (Term.rename Nat.succ x) (Term.var 0))
        (Term.var 0))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hleft : BProv Ax_s []
        (eq (Term.mul (Term.succ x) Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term (Term.succ x)
    have hxZero : BProv Ax_s []
        (eq (Term.mul x Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term x
    have haddZero : BProv Ax_s []
        (eq (Term.add (Term.mul x Term.zero) Term.zero)
          (Term.mul x Term.zero)) :=
      BProv_Ax_s_addZero_term (Term.mul x Term.zero)
    have hright : BProv Ax_s []
        (eq (Term.add (Term.mul x Term.zero) Term.zero) Term.zero) :=
      BProv_eqTrans haddZero hxZero
    have htarget : BProv Ax_s []
        (eq (Term.mul (Term.succ x) Term.zero)
          (Term.add (Term.mul x Term.zero) Term.zero)) :=
      BProv_eqTrans hleft (BProv_eqSym hright)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let y : Term := Term.var 0
    let A : Term := Term.mul xs y
    have hphi : BProv Ax_s [phi]
        (eq (Term.mul (Term.succ xs) y) (Term.add A y)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs, y, A])
    have hleftStep : BProv Ax_s [phi]
        (eq (Term.mul (Term.succ xs) (Term.succ y))
          (Term.add (Term.mul (Term.succ xs) y) (Term.succ xs))) :=
      BProv_weaken_nil
        (BProv_Ax_s_mulSucc_terms (Term.succ xs) y)
    have hleftCong : BProv Ax_s [phi]
        (eq
          (Term.add (Term.mul (Term.succ xs) y) (Term.succ xs))
          (Term.add (Term.add A y) (Term.succ xs))) :=
      BProv_eq_congr_add_left (Term.succ xs) hphi
    have hleftNorm : BProv Ax_s [phi]
        (eq (Term.mul (Term.succ xs) (Term.succ y))
          (Term.add (Term.add A y) (Term.succ xs))) :=
      BProv_eqTrans hleftStep hleftCong
    have hrightMul : BProv Ax_s [phi]
        (eq (Term.mul xs (Term.succ y)) (Term.add A xs)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms xs y)
    have hrightCong : BProv Ax_s [phi]
        (eq
          (Term.add (Term.mul xs (Term.succ y)) (Term.succ y))
          (Term.add (Term.add A xs) (Term.succ y))) :=
      BProv_eq_congr_add_left (Term.succ y) hrightMul
    have hleftSucc : BProv Ax_s [phi]
        (eq (Term.add (Term.add A y) (Term.succ xs))
          (Term.succ (Term.add (Term.add A y) xs))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms (Term.add A y) xs)
    have hassocLeft : BProv Ax_s [phi]
        (eq (Term.add (Term.add A y) xs)
          (Term.add A (Term.add y xs))) :=
      BProv_Ax_s_add_assoc_terms A y xs
    have hcommYX : BProv Ax_s [phi]
        (eq (Term.add y xs) (Term.add xs y)) :=
      BProv_Ax_s_add_comm_terms y xs
    have hcongYX : BProv Ax_s [phi]
        (eq (Term.add A (Term.add y xs))
          (Term.add A (Term.add xs y))) :=
      BProv_eq_congr_add_right A hcommYX
    have hassocRight : BProv Ax_s [phi]
        (eq (Term.add (Term.add A xs) y)
          (Term.add A (Term.add xs y))) :=
      BProv_Ax_s_add_assoc_terms A xs y
    have hswap : BProv Ax_s [phi]
        (eq (Term.add (Term.add A y) xs)
          (Term.add (Term.add A xs) y)) :=
      BProv_eqTrans (BProv_eqTrans hassocLeft hcongYX)
        (BProv_eqSym hassocRight)
    have hswapSucc : BProv Ax_s [phi]
        (eq
          (Term.succ (Term.add (Term.add A y) xs))
          (Term.succ (Term.add (Term.add A xs) y))) :=
      BProv_eq_congr_succ hswap
    have hrightSucc : BProv Ax_s [phi]
        (eq (Term.add (Term.add A xs) (Term.succ y))
          (Term.succ (Term.add (Term.add A xs) y))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms (Term.add A xs) y)
    have hnorm : BProv Ax_s [phi]
        (eq (Term.add (Term.add A y) (Term.succ xs))
          (Term.add (Term.add A xs) (Term.succ y))) :=
      BProv_eqTrans (BProv_eqTrans hleftSucc hswapSucc)
        (BProv_eqSym hrightSucc)
    have htarget : BProv Ax_s [phi]
        (eq (Term.mul (Term.succ xs) (Term.succ y))
          (Term.add (Term.mul xs (Term.succ y)) (Term.succ y))) :=
      BProv_eqTrans (BProv_eqTrans hleftNorm hnorm)
        (BProv_eqSym hrightCong)
    simpa [phi, xs, y, A, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of `S x * y = x * y + y`. -/
theorem BProv_Ax_s_succ_mul_terms {G : List Formula} (x y : Term) :
    BProv Ax_s G
      (eq (Term.mul (Term.succ x) y)
        (Term.add (Term.mul x y) y)) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.mul (Term.succ (Term.rename Nat.succ x)) (Term.var 0))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))
            (Term.var 0)))) :=
    BProv_weaken_nil (BProv_Ax_s_succ_mul_all x)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := y) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves commutativity of multiplication. -/
theorem BProv_Ax_s_mul_comm_all (x : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.mul (Term.rename Nat.succ x) (Term.var 0))
          (Term.mul (Term.var 0) (Term.rename Nat.succ x)))) := by
  let phi : Formula :=
    eq
      (Term.mul (Term.rename Nat.succ x) (Term.var 0))
      (Term.mul (Term.var 0) (Term.rename Nat.succ x))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hrightZero : BProv Ax_s []
        (eq (Term.mul x Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term x
    have hleftZero : BProv Ax_s []
        (eq (Term.mul Term.zero x) Term.zero) :=
      BProv_Ax_s_zero_mul_term x
    have htarget : BProv Ax_s []
        (eq (Term.mul x Term.zero) (Term.mul Term.zero x)) :=
      BProv_eqTrans hrightZero (BProv_eqSym hleftZero)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let y : Term := Term.var 0
    have hphi : BProv Ax_s [phi]
        (eq (Term.mul xs y) (Term.mul y xs)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs, y])
    have hleftStep : BProv Ax_s [phi]
        (eq (Term.mul xs (Term.succ y))
          (Term.add (Term.mul xs y) xs)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms xs y)
    have hleftCong : BProv Ax_s [phi]
        (eq
          (Term.add (Term.mul xs y) xs)
          (Term.add (Term.mul y xs) xs)) :=
      BProv_eq_congr_add_left xs hphi
    have hrightStep : BProv Ax_s [phi]
        (eq (Term.mul (Term.succ y) xs)
          (Term.add (Term.mul y xs) xs)) :=
      BProv_Ax_s_succ_mul_terms y xs
    have htarget : BProv Ax_s [phi]
        (eq (Term.mul xs (Term.succ y))
          (Term.mul (Term.succ y) xs)) :=
      BProv_eqTrans (BProv_eqTrans hleftStep hleftCong)
        (BProv_eqSym hrightStep)
    simpa [phi, xs, y, substSuccVar, subst, instTerm, Term.subst,
      Term.upSubst, Term.rename, term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of multiplication commutativity. -/
theorem BProv_Ax_s_mul_comm_terms {G : List Formula} (x y : Term) :
    BProv Ax_s G (eq (Term.mul x y) (Term.mul y x)) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.mul (Term.rename Nat.succ x) (Term.var 0))
          (Term.mul (Term.var 0) (Term.rename Nat.succ x)))) :=
    BProv_weaken_nil (BProv_Ax_s_mul_comm_all x)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := y) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves left-distributivity of multiplication over addition. -/
theorem BProv_Ax_s_mul_add_all (x y : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.mul (Term.rename Nat.succ x)
            (Term.add (Term.rename Nat.succ y) (Term.var 0)))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))))) := by
  let phi : Formula :=
    eq
      (Term.mul (Term.rename Nat.succ x)
        (Term.add (Term.rename Nat.succ y) (Term.var 0)))
      (Term.add
        (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (Term.mul (Term.rename Nat.succ x) (Term.var 0)))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hyZero : BProv Ax_s []
        (eq (Term.add y Term.zero) y) :=
      BProv_Ax_s_addZero_term y
    have hleft : BProv Ax_s []
        (eq (Term.mul x (Term.add y Term.zero)) (Term.mul x y)) :=
      BProv_eq_congr_mul_right x hyZero
    have hxZero : BProv Ax_s []
        (eq (Term.mul x Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term x
    have hrightMulZero : BProv Ax_s []
        (eq
          (Term.add (Term.mul x y) (Term.mul x Term.zero))
          (Term.add (Term.mul x y) Term.zero)) :=
      BProv_eq_congr_add_right (Term.mul x y) hxZero
    have hrightZero : BProv Ax_s []
        (eq (Term.add (Term.mul x y) Term.zero) (Term.mul x y)) :=
      BProv_Ax_s_addZero_term (Term.mul x y)
    have hright : BProv Ax_s []
        (eq
          (Term.add (Term.mul x y) (Term.mul x Term.zero))
          (Term.mul x y)) :=
      BProv_eqTrans hrightMulZero hrightZero
    have htarget : BProv Ax_s []
        (eq (Term.mul x (Term.add y Term.zero))
          (Term.add (Term.mul x y) (Term.mul x Term.zero))) :=
      BProv_eqTrans hleft (BProv_eqSym hright)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let ys : Term := Term.rename Nat.succ y
    let z : Term := Term.var 0
    let xy : Term := Term.mul xs ys
    let xz : Term := Term.mul xs z
    have hphi : BProv Ax_s [phi]
        (eq (Term.mul xs (Term.add ys z)) (Term.add xy xz)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs, ys, z, xy, xz])
    have hySucc : BProv Ax_s [phi]
        (eq (Term.add ys (Term.succ z)) (Term.succ (Term.add ys z))) :=
      BProv_weaken_nil (BProv_Ax_s_addSucc_terms ys z)
    have hleftArg : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.add ys (Term.succ z)))
          (Term.mul xs (Term.succ (Term.add ys z)))) :=
      BProv_eq_congr_mul_right xs hySucc
    have hmulSuccYZ : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.succ (Term.add ys z)))
          (Term.add (Term.mul xs (Term.add ys z)) xs)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms xs (Term.add ys z))
    have hihCong : BProv Ax_s [phi]
        (eq
          (Term.add (Term.mul xs (Term.add ys z)) xs)
          (Term.add (Term.add xy xz) xs)) :=
      BProv_eq_congr_add_left xs hphi
    have hleftNorm : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.add ys (Term.succ z)))
          (Term.add (Term.add xy xz) xs)) :=
      BProv_eqTrans hleftArg (BProv_eqTrans hmulSuccYZ hihCong)
    have hmulSuccZ : BProv Ax_s [phi]
        (eq (Term.mul xs (Term.succ z)) (Term.add xz xs)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms xs z)
    have hrightCong : BProv Ax_s [phi]
        (eq
          (Term.add xy (Term.mul xs (Term.succ z)))
          (Term.add xy (Term.add xz xs))) :=
      BProv_eq_congr_add_right xy hmulSuccZ
    have hassoc : BProv Ax_s [phi]
        (eq
          (Term.add (Term.add xy xz) xs)
          (Term.add xy (Term.add xz xs))) :=
      BProv_Ax_s_add_assoc_terms xy xz xs
    have htarget : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.add ys (Term.succ z)))
          (Term.add xy (Term.mul xs (Term.succ z)))) :=
      BProv_eqTrans hleftNorm
        (BProv_eqTrans hassoc (BProv_eqSym hrightCong))
    simpa [phi, xs, ys, z, xy, xz, substSuccVar, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of `x * (y + z) = x * y + x * z`. -/
theorem BProv_Ax_s_mul_add_terms {G : List Formula} (x y z : Term) :
    BProv Ax_s G
      (eq (Term.mul x (Term.add y z))
        (Term.add (Term.mul x y) (Term.mul x z))) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.mul (Term.rename Nat.succ x)
            (Term.add (Term.rename Nat.succ y) (Term.var 0)))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))))) :=
    BProv_weaken_nil (BProv_Ax_s_mul_add_all x y)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := z) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves right-distributivity of multiplication over addition. -/
theorem BProv_Ax_s_add_mul_all (x y : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.mul
            (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))
            (Term.mul (Term.rename Nat.succ y) (Term.var 0))))) := by
  let phi : Formula :=
    eq
      (Term.mul
        (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (Term.var 0))
      (Term.add
        (Term.mul (Term.rename Nat.succ x) (Term.var 0))
        (Term.mul (Term.rename Nat.succ y) (Term.var 0)))
  have hbody : BProv Ax_s [] phi := by
    let xs : Term := Term.rename Nat.succ x
    let ys : Term := Term.rename Nat.succ y
    let z : Term := Term.var 0
    have hcommLeft : BProv Ax_s []
        (eq (Term.mul (Term.add xs ys) z)
          (Term.mul z (Term.add xs ys))) :=
      BProv_Ax_s_mul_comm_terms (Term.add xs ys) z
    have hdist : BProv Ax_s []
        (eq (Term.mul z (Term.add xs ys))
          (Term.add (Term.mul z xs) (Term.mul z ys))) :=
      BProv_Ax_s_mul_add_terms z xs ys
    have hxComm : BProv Ax_s []
        (eq (Term.mul z xs) (Term.mul xs z)) :=
      BProv_Ax_s_mul_comm_terms z xs
    have hyComm : BProv Ax_s []
        (eq (Term.mul z ys) (Term.mul ys z)) :=
      BProv_Ax_s_mul_comm_terms z ys
    have hsum : BProv Ax_s []
        (eq
          (Term.add (Term.mul z xs) (Term.mul z ys))
          (Term.add (Term.mul xs z) (Term.mul ys z))) :=
      BProv_eq_congr_add hxComm hyComm
    have htarget : BProv Ax_s []
        (eq
          (Term.mul (Term.add xs ys) z)
          (Term.add (Term.mul xs z) (Term.mul ys z))) :=
      BProv_eqTrans (BProv_eqTrans hcommLeft hdist) hsum
    simpa [phi, xs, ys, z] using htarget
  exact BProv_allI_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbody

/-- Arbitrary-term instance of `(x + y) * z = x * z + y * z`. -/
theorem BProv_Ax_s_add_mul_terms {G : List Formula} (x y z : Term) :
    BProv Ax_s G
      (eq (Term.mul (Term.add x y) z)
        (Term.add (Term.mul x z) (Term.mul y z))) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.mul
            (Term.add (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.add
            (Term.mul (Term.rename Nat.succ x) (Term.var 0))
            (Term.mul (Term.rename Nat.succ y) (Term.var 0))))) :=
    BProv_weaken_nil (BProv_Ax_s_add_mul_all x y)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := z) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves associativity of multiplication. -/
theorem BProv_Ax_s_mul_assoc_all (x y : Term) :
    BProv Ax_s []
      (all
        (eq
          (Term.mul
            (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.mul
            (Term.rename Nat.succ x)
            (Term.mul (Term.rename Nat.succ y) (Term.var 0))))) := by
  let phi : Formula :=
    eq
      (Term.mul
        (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
        (Term.var 0))
      (Term.mul
        (Term.rename Nat.succ x)
        (Term.mul (Term.rename Nat.succ y) (Term.var 0)))
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hleftZero : BProv Ax_s []
        (eq (Term.mul (Term.mul x y) Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term (Term.mul x y)
    have hyZero : BProv Ax_s []
        (eq (Term.mul y Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term y
    have hrightArg : BProv Ax_s []
        (eq
          (Term.mul x (Term.mul y Term.zero))
          (Term.mul x Term.zero)) :=
      BProv_eq_congr_mul_right x hyZero
    have hxZero : BProv Ax_s []
        (eq (Term.mul x Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term x
    have hrightZero : BProv Ax_s []
        (eq (Term.mul x (Term.mul y Term.zero)) Term.zero) :=
      BProv_eqTrans hrightArg hxZero
    have htarget : BProv Ax_s []
        (eq
          (Term.mul (Term.mul x y) Term.zero)
          (Term.mul x (Term.mul y Term.zero))) :=
      BProv_eqTrans hleftZero (BProv_eqSym hrightZero)
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_substZero_rename_succ] using htarget
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    let xs : Term := Term.rename Nat.succ x
    let ys : Term := Term.rename Nat.succ y
    let z : Term := Term.var 0
    let xy : Term := Term.mul xs ys
    let yz : Term := Term.mul ys z
    have hphi : BProv Ax_s [phi]
        (eq (Term.mul xy z) (Term.mul xs yz)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi, xs, ys, z, xy, yz])
    have hleftStep : BProv Ax_s [phi]
        (eq (Term.mul xy (Term.succ z))
          (Term.add (Term.mul xy z) xy)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms xy z)
    have hihCong : BProv Ax_s [phi]
        (eq
          (Term.add (Term.mul xy z) xy)
          (Term.add (Term.mul xs yz) xy)) :=
      BProv_eq_congr_add_left xy hphi
    have hySucc : BProv Ax_s [phi]
        (eq (Term.mul ys (Term.succ z)) (Term.add yz ys)) :=
      BProv_weaken_nil (BProv_Ax_s_mulSucc_terms ys z)
    have hrightArg : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.mul ys (Term.succ z)))
          (Term.mul xs (Term.add yz ys))) :=
      BProv_eq_congr_mul_right xs hySucc
    have hdist : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.add yz ys))
          (Term.add (Term.mul xs yz) xy)) :=
      BProv_Ax_s_mul_add_terms xs yz ys
    have hrightNorm : BProv Ax_s [phi]
        (eq
          (Term.mul xs (Term.mul ys (Term.succ z)))
          (Term.add (Term.mul xs yz) xy)) :=
      BProv_eqTrans hrightArg hdist
    have htarget : BProv Ax_s [phi]
        (eq
          (Term.mul xy (Term.succ z))
          (Term.mul xs (Term.mul ys (Term.succ z)))) :=
      BProv_eqTrans (BProv_eqTrans hleftStep hihCong)
        (BProv_eqSym hrightNorm)
    simpa [phi, xs, ys, z, xy, yz, substSuccVar, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      term_substSuccVar_rename_succ] using htarget
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

/-- Arbitrary-term instance of multiplication associativity. -/
theorem BProv_Ax_s_mul_assoc_terms {G : List Formula} (x y z : Term) :
    BProv Ax_s G
      (eq (Term.mul (Term.mul x y) z)
        (Term.mul x (Term.mul y z))) := by
  have hall : BProv Ax_s G
      (all
        (eq
          (Term.mul
            (Term.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
            (Term.var 0))
          (Term.mul
            (Term.rename Nat.succ x)
            (Term.mul (Term.rename Nat.succ y) (Term.var 0))))) :=
    BProv_weaken_nil (BProv_Ax_s_mul_assoc_all x y)
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := z) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hinst

/-- PA proves the right-one law for multiplication. -/
theorem BProv_Ax_s_mul_one_all :
    BProv Ax_s []
      (all (eq (Term.mul (Term.var 0) (Term.numeral 1)) (Term.var 0))) := by
  have hbody : BProv Ax_s []
      (eq (Term.mul (Term.var 0) (Term.numeral 1)) (Term.var 0)) := by
    let x : Term := Term.var 0
    have hstep : BProv Ax_s []
        (eq (Term.mul x (Term.succ Term.zero))
          (Term.add (Term.mul x Term.zero) x)) :=
      BProv_Ax_s_mulSucc_terms x Term.zero
    have hzero : BProv Ax_s []
        (eq (Term.mul x Term.zero) Term.zero) :=
      BProv_Ax_s_mulZero_term x
    have hzeroCong : BProv Ax_s []
        (eq
          (Term.add (Term.mul x Term.zero) x)
          (Term.add Term.zero x)) :=
      BProv_eq_congr_add_left x hzero
    have hzeroAdd : BProv Ax_s []
        (eq (Term.add Term.zero x) x) :=
      BProv_Ax_s_zero_add_term x
    have htarget : BProv Ax_s []
        (eq (Term.mul x (Term.succ Term.zero)) x) :=
      BProv_eqTrans (BProv_eqTrans hstep hzeroCong) hzeroAdd
    simpa [x, Term.numeral] using htarget
  exact BProv_allI_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbody

/-- Arbitrary-term instance of `x * 1 = x`. -/
theorem BProv_Ax_s_mul_one_term {G : List Formula} (x : Term) :
    BProv Ax_s G (eq (Term.mul x (Term.numeral 1)) x) := by
  have hall : BProv Ax_s G
      (all (eq (Term.mul (Term.var 0) (Term.numeral 1)) (Term.var 0))) :=
    BProv_weaken_nil BProv_Ax_s_mul_one_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := x) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst] using hinst

/-- PA proves the left-one law for multiplication. -/
theorem BProv_Ax_s_one_mul_all :
    BProv Ax_s []
      (all (eq (Term.mul (Term.numeral 1) (Term.var 0)) (Term.var 0))) := by
  have hbody : BProv Ax_s []
      (eq (Term.mul (Term.numeral 1) (Term.var 0)) (Term.var 0)) := by
    have hcomm : BProv Ax_s []
        (eq
          (Term.mul (Term.numeral 1) (Term.var 0))
          (Term.mul (Term.var 0) (Term.numeral 1))) :=
      BProv_Ax_s_mul_comm_terms (Term.numeral 1) (Term.var 0)
    have hone : BProv Ax_s []
        (eq (Term.mul (Term.var 0) (Term.numeral 1)) (Term.var 0)) :=
      BProv_Ax_s_mul_one_term (Term.var 0)
    exact BProv_eqTrans hcomm hone
  exact BProv_allI_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbody

/-- Arbitrary-term instance of `1 * x = x`. -/
theorem BProv_Ax_s_one_mul_term {G : List Formula} (x : Term) :
    BProv Ax_s G (eq (Term.mul (Term.numeral 1) x) x) := by
  have hall : BProv Ax_s G
      (all (eq (Term.mul (Term.numeral 1) (Term.var 0)) (Term.var 0))) :=
    BProv_weaken_nil BProv_Ax_s_one_mul_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := x) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst] using hinst

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

/-- PA proves `a ≤ b` from a proof that the two slots are equal. -/
theorem BProv_Ax_s_leAt_of_eq {G : List Formula} {a b : Nat}
    (heq : BProv Ax_s G (eq (Term.var a) (Term.var b))) :
    BProv Ax_s G (leAt a b) := by
  have haddZero : BProv Ax_s G
      (eq (Term.add (Term.var a) Term.zero) (Term.var a)) :=
    BProv_weaken_nil (BProv_Ax_s_addZero_term (Term.var a))
  have htarget : BProv Ax_s G
      (eq (Term.add (Term.var a) Term.zero) (Term.var b)) :=
    BProv_eqTrans haddZero heq
  have hbody : BProv Ax_s G
      (subst (instTerm Term.zero)
        (eq (Term.add (Term.var (a+1)) (Term.var 0))
          (Term.var (b+1)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  simpa [leAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.add (Term.var (a+1)) (Term.var 0))
        (Term.var (b+1)))
      (t := Term.zero) hbody)

/-- If the left slot is `0`, PA proves it is below any right slot. -/
theorem BProv_Ax_s_leAt_of_eqConst_zero_left {G : List Formula} {a b : Nat}
    (ha : BProv Ax_s G (eqConstAt a 0)) :
    BProv Ax_s G (leAt a b) := by
  have hleft : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.var b))
        (Term.add Term.zero (Term.var b))) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eq_congr_add_left (Term.var b) ha
  have hzeroAdd : BProv Ax_s G
      (eq (Term.add Term.zero (Term.var b)) (Term.var b)) :=
    BProv_Ax_s_zero_add_term (Term.var b)
  have htarget : BProv Ax_s G
      (eq (Term.add (Term.var a) (Term.var b)) (Term.var b)) :=
    BProv_eqTrans hleft hzeroAdd
  have hbody : BProv Ax_s G
      (subst (instTerm (Term.var b))
        (eq (Term.add (Term.var (a+1)) (Term.var 0))
          (Term.var (b+1)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
  simpa [leAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.add (Term.var (a+1)) (Term.var 0))
        (Term.var (b+1)))
      (t := Term.var b) hbody)

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

/-- PA derives non-strict order from strict order by reusing the positive
successor witness as the additive difference. -/
theorem BProv_Ax_s_leAt_of_ltAt {G : List Formula} {a b : Nat}
    (hlt : BProv Ax_s G (ltAt a b)) :
    BProv Ax_s G (leAt a b) := by
  let ltBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.var (b+1))
  have hbody : BProv Ax_s (ltBody :: G.map (rename Nat.succ))
      (rename Nat.succ (leAt a b)) := by
    let C : List Formula := ltBody :: G.map (rename Nat.succ)
    have hltBody : BProv Ax_s C ltBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hinst : BProv Ax_s C
        (subst (instTerm (Term.succ (Term.var 0)))
          (eq (Term.add (Term.var (a+1+1)) (Term.var 0))
            (Term.var (b+1+1)))) := by
      simpa [subst, instTerm, Term.subst, Term.upSubst, ltBody] using hltBody
    have hex : BProv Ax_s C
        (ex (eq (Term.add (Term.var (a+1+1)) (Term.var 0))
          (Term.var (b+1+1)))) :=
      BProv_exI (B := Ax_s) (G := C)
        (a := eq (Term.add (Term.var (a+1+1)) (Term.var 0))
          (Term.var (b+1+1)))
        (t := Term.succ (Term.var 0)) hinst
    simpa [C, leAt, rename, Term.rename, SetTheory.up] using hex
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hlt (by
      simpa [ltAt, ltBody] using hbody)

/-- PA proves reflexivity of the syntactic non-strict order macro. -/
theorem BProv_Ax_s_leAt_refl {G : List Formula} {a : Nat} :
    BProv Ax_s G (leAt a a) :=
  BProv_Ax_s_leAt_of_eq (BProv_eqRefl (B := Ax_s) (G := G) (Term.var a))

/-- PA proves transitivity of the syntactic non-strict order macro. -/
theorem BProv_Ax_s_leAt_trans {G : List Formula} {a b c : Nat}
    (hab : BProv Ax_s G (leAt a b))
    (hbc : BProv Ax_s G (leAt b c)) :
    BProv Ax_s G (leAt a c) := by
  let abBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1))
  have habBody : BProv Ax_s (abBody :: G.map (rename Nat.succ))
      (rename Nat.succ (leAt a c)) := by
    let C : List Formula := abBody :: G.map (rename Nat.succ)
    let bcBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.var 0))
        (Term.var (c+1+1))
    have hbcRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (leAt b c)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbc Nat.succ
    have hbcC : BProv Ax_s C (rename Nat.succ (leAt b c)) :=
      BProv_context_cons hbcRen
    have hbcBody : BProv Ax_s (bcBody :: C.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ (leAt a c))) := by
      let D : List Formula := bcBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let z : Term := Term.var 0
      let bvar : Term := Term.var (b+1+1)
      let cvar : Term := Term.var (c+1+1)
      have habRaw : BProv Ax_s D (rename Nat.succ abBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have habEq : BProv Ax_s D (eq (Term.add x y) bvar) := by
        simpa [abBody, x, y, bvar, rename, Term.rename] using habRaw
      have hbcRaw : BProv Ax_s D bcBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hbcEq : BProv Ax_s D (eq (Term.add bvar z) cvar) := by
        simpa [bcBody, bvar, z, cvar] using hbcRaw
      have habAdd : BProv Ax_s D
          (eq (Term.add (Term.add x y) z) (Term.add bvar z)) :=
        BProv_eq_congr_add_left z habEq
      have hleft : BProv Ax_s D (eq (Term.add (Term.add x y) z) cvar) :=
        BProv_eqTrans habAdd hbcEq
      have hassoc : BProv Ax_s D
          (eq (Term.add (Term.add x y) z)
            (Term.add x (Term.add y z))) :=
        BProv_Ax_s_add_assoc_terms x y z
      have htarget : BProv Ax_s D
          (eq (Term.add x (Term.add y z)) cvar) :=
        BProv_eqTrans (BProv_eqSym hassoc) hleft
      have hinst : BProv Ax_s D
          (subst (instTerm (Term.add y z))
            (eq (Term.add (Term.var (a+1+1+1)) (Term.var 0))
              (Term.var (c+1+1+1)))) := by
        simpa [subst, instTerm, Term.subst, Term.upSubst, x, y, z, cvar]
          using htarget
      have hex : BProv Ax_s D
          (ex (eq (Term.add (Term.var (a+1+1+1)) (Term.var 0))
            (Term.var (c+1+1+1)))) :=
        BProv_exI (B := Ax_s) (G := D)
          (a := eq (Term.add (Term.var (a+1+1+1)) (Term.var 0))
            (Term.var (c+1+1+1)))
          (t := Term.add y z) hinst
      simpa [D, leAt, rename, Term.rename, SetTheory.up] using hex
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hbcC (by
        simpa [C, leAt, bcBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hbcBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hab (by
      simpa [leAt, abBody] using habBody)

/-- PA proves antisymmetry of the syntactic non-strict order macro. -/
theorem BProv_Ax_s_eq_of_leAt_leAt {G : List Formula} {a b : Nat}
    (hab : BProv Ax_s G (leAt a b))
    (hba : BProv Ax_s G (leAt b a)) :
    BProv Ax_s G (eq (Term.var a) (Term.var b)) := by
  let abBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1))
  have habBody : BProv Ax_s (abBody :: G.map (rename Nat.succ))
      (rename Nat.succ (eq (Term.var a) (Term.var b))) := by
    let C : List Formula := abBody :: G.map (rename Nat.succ)
    let baBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.var 0))
        (Term.var (a+1+1))
    have hbaRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (leAt b a)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hba Nat.succ
    have hbaC : BProv Ax_s C (rename Nat.succ (leAt b a)) :=
      BProv_context_cons hbaRen
    have hbaBody : BProv Ax_s (baBody :: C.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ
          (eq (Term.var a) (Term.var b)))) := by
      let D : List Formula := baBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let z : Term := Term.var 0
      let bvar : Term := Term.var (b+1+1)
      have habRaw : BProv Ax_s D (rename Nat.succ abBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have habEq : BProv Ax_s D (eq (Term.add x y) bvar) := by
        simpa [abBody, x, y, bvar, rename, Term.rename] using habRaw
      have hbaRaw : BProv Ax_s D baBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hbaEq : BProv Ax_s D (eq (Term.add bvar z) x) := by
        simpa [baBody, x, z, bvar] using hbaRaw
      have habAdd : BProv Ax_s D
          (eq (Term.add (Term.add x y) z) (Term.add bvar z)) :=
        BProv_eq_congr_add_left z habEq
      have hloop : BProv Ax_s D
          (eq (Term.add (Term.add x y) z) x) :=
        BProv_eqTrans habAdd hbaEq
      have hassoc : BProv Ax_s D
          (eq (Term.add (Term.add x y) z)
            (Term.add x (Term.add y z))) :=
        BProv_Ax_s_add_assoc_terms x y z
      have hloop' : BProv Ax_s D
          (eq (Term.add x (Term.add y z)) x) :=
        BProv_eqTrans (BProv_eqSym hassoc) hloop
      have hxZero : BProv Ax_s D (eq (Term.add x Term.zero) x) :=
        BProv_weaken_nil (BProv_Ax_s_addZero_term x)
      have hsumEqZero : BProv Ax_s D
          (eq (Term.add x (Term.add y z)) (Term.add x Term.zero)) :=
        BProv_eqTrans hloop' (BProv_eqSym hxZero)
      have hyzZero : BProv Ax_s D (eq (Term.add y z) Term.zero) :=
        BProv_Ax_s_add_cancel_left_terms
          (x := x) (y := Term.add y z) (z := Term.zero) hsumEqZero
      have hyZero : BProv Ax_s D (eq y Term.zero) :=
        BProv_Ax_s_add_eq_zero_left_terms
          (x := y) (y := z) hyzZero
      have hxyZero : BProv Ax_s D
          (eq (Term.add x y) (Term.add x Term.zero)) :=
        BProv_eq_congr_add_right x hyZero
      have hxb : BProv Ax_s D (eq x bvar) :=
        BProv_eqTrans
          (BProv_eqTrans (BProv_eqSym hxZero) (BProv_eqSym hxyZero))
          habEq
      simpa [D, rename, Term.rename, x, bvar] using hxb
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hbaC (by
        simpa [C, leAt, baBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hbaBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hab (by
      simpa [leAt, abBody] using habBody)

/-- PA proves transitivity of the syntactic strict order macro. -/
theorem BProv_Ax_s_ltAt_trans {G : List Formula} {a b c : Nat}
    (hab : BProv Ax_s G (ltAt a b))
    (hbc : BProv Ax_s G (ltAt b c)) :
    BProv Ax_s G (ltAt a c) := by
  let abBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.var (b+1))
  have habBody : BProv Ax_s (abBody :: G.map (rename Nat.succ))
      (rename Nat.succ (ltAt a c)) := by
    let C : List Formula := abBody :: G.map (rename Nat.succ)
    let bcBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.succ (Term.var 0)))
        (Term.var (c+1+1))
    have hbcRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (ltAt b c)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbc Nat.succ
    have hbcC : BProv Ax_s C (rename Nat.succ (ltAt b c)) :=
      BProv_context_cons hbcRen
    have hbcBody : BProv Ax_s (bcBody :: C.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ (ltAt a c))) := by
      let D : List Formula := bcBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let z : Term := Term.var 0
      let bvar : Term := Term.var (b+1+1)
      let cvar : Term := Term.var (c+1+1)
      have habRaw : BProv Ax_s D (rename Nat.succ abBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have habEq : BProv Ax_s D (eq (Term.add x (Term.succ y)) bvar) := by
        simpa [abBody, x, y, bvar, rename, Term.rename] using habRaw
      have hbcRaw : BProv Ax_s D bcBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hbcEq : BProv Ax_s D
          (eq (Term.add bvar (Term.succ z)) cvar) := by
        simpa [bcBody, bvar, z, cvar] using hbcRaw
      have habAdd : BProv Ax_s D
          (eq (Term.add (Term.add x (Term.succ y)) (Term.succ z))
            (Term.add bvar (Term.succ z))) :=
        BProv_eq_congr_add_left (Term.succ z) habEq
      have hloop : BProv Ax_s D
          (eq (Term.add (Term.add x (Term.succ y)) (Term.succ z)) cvar) :=
        BProv_eqTrans habAdd hbcEq
      have hassoc : BProv Ax_s D
          (eq
            (Term.add (Term.add x (Term.succ y)) (Term.succ z))
            (Term.add x (Term.add (Term.succ y) (Term.succ z)))) :=
        BProv_Ax_s_add_assoc_terms x (Term.succ y) (Term.succ z)
      have hsuccLeft : BProv Ax_s D
          (eq (Term.add (Term.succ y) (Term.succ z))
            (Term.succ (Term.add y (Term.succ z)))) :=
        BProv_Ax_s_succ_add_terms y (Term.succ z)
      have hsuccCong : BProv Ax_s D
          (eq
            (Term.add x (Term.add (Term.succ y) (Term.succ z)))
            (Term.add x (Term.succ (Term.add y (Term.succ z))))) :=
        BProv_eq_congr_add_right x hsuccLeft
      have htarget : BProv Ax_s D
          (eq (Term.add x (Term.succ (Term.add y (Term.succ z)))) cvar) :=
        BProv_eqTrans (BProv_eqTrans (BProv_eqSym hsuccCong)
          (BProv_eqSym hassoc)) hloop
      have hinst : BProv Ax_s D
          (subst (instTerm (Term.add y (Term.succ z)))
            (eq (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
              (Term.var (c+1+1+1)))) := by
        simpa [subst, instTerm, Term.subst, Term.upSubst, x, y, z, cvar]
          using htarget
      have hex : BProv Ax_s D
          (ex (eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))) :=
        BProv_exI (B := Ax_s) (G := D)
          (a := eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))
          (t := Term.add y (Term.succ z)) hinst
      simpa [D, ltAt, rename, Term.rename, SetTheory.up] using hex
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hbcC (by
        simpa [C, ltAt, bcBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hbcBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hab (by
      simpa [ltAt, abBody] using habBody)

/-- PA composes a strict order proof followed by a non-strict order proof. -/
theorem BProv_Ax_s_ltAt_leAt_trans {G : List Formula} {a b c : Nat}
    (hab : BProv Ax_s G (ltAt a b))
    (hbc : BProv Ax_s G (leAt b c)) :
    BProv Ax_s G (ltAt a c) := by
  let abBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.var (b+1))
  have habBody : BProv Ax_s (abBody :: G.map (rename Nat.succ))
      (rename Nat.succ (ltAt a c)) := by
    let C : List Formula := abBody :: G.map (rename Nat.succ)
    let bcBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.var 0))
        (Term.var (c+1+1))
    have hbcRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (leAt b c)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbc Nat.succ
    have hbcC : BProv Ax_s C (rename Nat.succ (leAt b c)) :=
      BProv_context_cons hbcRen
    have hbcBody : BProv Ax_s (bcBody :: C.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ (ltAt a c))) := by
      let D : List Formula := bcBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let z : Term := Term.var 0
      let bvar : Term := Term.var (b+1+1)
      let cvar : Term := Term.var (c+1+1)
      have habRaw : BProv Ax_s D (rename Nat.succ abBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have habEq : BProv Ax_s D (eq (Term.add x (Term.succ y)) bvar) := by
        simpa [abBody, x, y, bvar, rename, Term.rename] using habRaw
      have hbcRaw : BProv Ax_s D bcBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hbcEq : BProv Ax_s D (eq (Term.add bvar z) cvar) := by
        simpa [bcBody, bvar, z, cvar] using hbcRaw
      have habAdd : BProv Ax_s D
          (eq (Term.add (Term.add x (Term.succ y)) z) (Term.add bvar z)) :=
        BProv_eq_congr_add_left z habEq
      have hloop : BProv Ax_s D
          (eq (Term.add (Term.add x (Term.succ y)) z) cvar) :=
        BProv_eqTrans habAdd hbcEq
      have hassoc : BProv Ax_s D
          (eq
            (Term.add (Term.add x (Term.succ y)) z)
            (Term.add x (Term.add (Term.succ y) z))) :=
        BProv_Ax_s_add_assoc_terms x (Term.succ y) z
      have hsuccLeft : BProv Ax_s D
          (eq (Term.add (Term.succ y) z)
            (Term.succ (Term.add y z))) :=
        BProv_Ax_s_succ_add_terms y z
      have hsuccCong : BProv Ax_s D
          (eq
            (Term.add x (Term.add (Term.succ y) z))
            (Term.add x (Term.succ (Term.add y z)))) :=
        BProv_eq_congr_add_right x hsuccLeft
      have htarget : BProv Ax_s D
          (eq (Term.add x (Term.succ (Term.add y z))) cvar) :=
        BProv_eqTrans (BProv_eqTrans (BProv_eqSym hsuccCong)
          (BProv_eqSym hassoc)) hloop
      have hinst : BProv Ax_s D
          (subst (instTerm (Term.add y z))
            (eq (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
              (Term.var (c+1+1+1)))) := by
        simpa [subst, instTerm, Term.subst, Term.upSubst, x, y, z, cvar]
          using htarget
      have hex : BProv Ax_s D
          (ex (eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))) :=
        BProv_exI (B := Ax_s) (G := D)
          (a := eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))
          (t := Term.add y z) hinst
      simpa [D, ltAt, rename, Term.rename, SetTheory.up] using hex
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hbcC (by
        simpa [C, leAt, bcBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hbcBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hab (by
      simpa [ltAt, abBody] using habBody)

/-- PA composes a non-strict order proof followed by a strict order proof. -/
theorem BProv_Ax_s_leAt_ltAt_trans {G : List Formula} {a b c : Nat}
    (hab : BProv Ax_s G (leAt a b))
    (hbc : BProv Ax_s G (ltAt b c)) :
    BProv Ax_s G (ltAt a c) := by
  let abBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1))
  have habBody : BProv Ax_s (abBody :: G.map (rename Nat.succ))
      (rename Nat.succ (ltAt a c)) := by
    let C : List Formula := abBody :: G.map (rename Nat.succ)
    let bcBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.succ (Term.var 0)))
        (Term.var (c+1+1))
    have hbcRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (ltAt b c)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbc Nat.succ
    have hbcC : BProv Ax_s C (rename Nat.succ (ltAt b c)) :=
      BProv_context_cons hbcRen
    have hbcBody : BProv Ax_s (bcBody :: C.map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ (ltAt a c))) := by
      let D : List Formula := bcBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let z : Term := Term.var 0
      let bvar : Term := Term.var (b+1+1)
      let cvar : Term := Term.var (c+1+1)
      have habRaw : BProv Ax_s D (rename Nat.succ abBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have habEq : BProv Ax_s D (eq (Term.add x y) bvar) := by
        simpa [abBody, x, y, bvar, rename, Term.rename] using habRaw
      have hbcRaw : BProv Ax_s D bcBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hbcEq : BProv Ax_s D
          (eq (Term.add bvar (Term.succ z)) cvar) := by
        simpa [bcBody, bvar, z, cvar] using hbcRaw
      have habAdd : BProv Ax_s D
          (eq (Term.add (Term.add x y) (Term.succ z))
            (Term.add bvar (Term.succ z))) :=
        BProv_eq_congr_add_left (Term.succ z) habEq
      have hloop : BProv Ax_s D
          (eq (Term.add (Term.add x y) (Term.succ z)) cvar) :=
        BProv_eqTrans habAdd hbcEq
      have hassoc : BProv Ax_s D
          (eq
            (Term.add (Term.add x y) (Term.succ z))
            (Term.add x (Term.add y (Term.succ z)))) :=
        BProv_Ax_s_add_assoc_terms x y (Term.succ z)
      have hsuccRight : BProv Ax_s D
          (eq (Term.add y (Term.succ z))
            (Term.succ (Term.add y z))) :=
        BProv_weaken_nil (BProv_Ax_s_addSucc_terms y z)
      have hsuccCong : BProv Ax_s D
          (eq
            (Term.add x (Term.add y (Term.succ z)))
            (Term.add x (Term.succ (Term.add y z)))) :=
        BProv_eq_congr_add_right x hsuccRight
      have htarget : BProv Ax_s D
          (eq (Term.add x (Term.succ (Term.add y z))) cvar) :=
        BProv_eqTrans (BProv_eqTrans (BProv_eqSym hsuccCong)
          (BProv_eqSym hassoc)) hloop
      have hinst : BProv Ax_s D
          (subst (instTerm (Term.add y z))
            (eq (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
              (Term.var (c+1+1+1)))) := by
        simpa [subst, instTerm, Term.subst, Term.upSubst, x, y, z, cvar]
          using htarget
      have hex : BProv Ax_s D
          (ex (eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))) :=
        BProv_exI (B := Ax_s) (G := D)
          (a := eq
            (Term.add (Term.var (a+1+1+1)) (Term.succ (Term.var 0)))
            (Term.var (c+1+1+1)))
          (t := Term.add y z) hinst
      simpa [D, ltAt, rename, Term.rename, SetTheory.up] using hex
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hbcC (by
        simpa [C, ltAt, bcBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hbcBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hab (by
      simpa [leAt, abBody] using habBody)

/-- PA refutes an irreflexive strict order witness. -/
theorem BProv_Ax_s_ltAt_irrefl_bot {G : List Formula} {a : Nat}
    (hlt : BProv Ax_s G (ltAt a a)) :
    BProv Ax_s G bot := by
  let ltBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.var (a+1))
  have hbody : BProv Ax_s (ltBody :: G.map (rename Nat.succ))
      (rename Nat.succ bot) := by
    have heq : BProv Ax_s (ltBody :: G.map (rename Nat.succ))
        (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.var (a+1))) :=
      BProv_ass (B := Ax_s)
        (G := ltBody :: G.map (rename Nat.succ))
        (by simp [ltBody])
    have hbot : BProv Ax_s (ltBody :: G.map (rename Nat.succ)) bot :=
      BProv_Ax_s_add_succ_ne_self_terms heq
    simpa [rename] using hbot
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hlt (by
      simpa [ltAt, ltBody] using hbody)

/-- PA refutes simultaneous witnesses for `a < b` and `b ≤ a`. -/
theorem BProv_Ax_s_ltAt_leAt_bot {G : List Formula} {a b : Nat}
    (hlt : BProv Ax_s G (ltAt a b))
    (hle : BProv Ax_s G (leAt b a)) :
    BProv Ax_s G bot := by
  let ltBody : Formula :=
    eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
      (Term.var (b+1))
  have hbody : BProv Ax_s (ltBody :: G.map (rename Nat.succ))
      (rename Nat.succ bot) := by
    let C : List Formula := ltBody :: G.map (rename Nat.succ)
    let leBody : Formula :=
      eq (Term.add (Term.var (b+1+1)) (Term.var 0)) (Term.var (a+1+1))
    have hleRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (leAt b a)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hle Nat.succ
    have hleC : BProv Ax_s C (rename Nat.succ (leAt b a)) :=
      BProv_context_cons hleRen
    have hleBody : BProv Ax_s (leBody :: C.map (rename Nat.succ))
        (rename Nat.succ bot) := by
      let D : List Formula := leBody :: C.map (rename Nat.succ)
      let x : Term := Term.var (a+1+1)
      let y : Term := Term.var 1
      let d : Term := Term.var 0
      have hltRaw : BProv Ax_s D (rename Nat.succ ltBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have hltEq : BProv Ax_s D
          (eq (Term.add x (Term.succ y)) (Term.var (b+1+1))) := by
        simpa [ltBody, x, y, rename, Term.rename] using hltRaw
      have hleEq : BProv Ax_s D
          (eq (Term.add (Term.var (b+1+1)) d) x) := by
        have hraw : BProv Ax_s D leBody :=
          BProv_ass (B := Ax_s) (G := D) (by simp [D])
        simpa [leBody, x, d] using hraw
      have hltAdd : BProv Ax_s D
          (eq
            (Term.add (Term.add x (Term.succ y)) d)
            (Term.add (Term.var (b+1+1)) d)) :=
        BProv_eq_congr_add_left d hltEq
      have hloop : BProv Ax_s D
          (eq (Term.add (Term.add x (Term.succ y)) d) x) :=
        BProv_eqTrans hltAdd hleEq
      have hassoc : BProv Ax_s D
          (eq
            (Term.add (Term.add x (Term.succ y)) d)
            (Term.add x (Term.add (Term.succ y) d))) :=
        BProv_Ax_s_add_assoc_terms x (Term.succ y) d
      have hsuccLeft : BProv Ax_s D
          (eq (Term.add (Term.succ y) d)
            (Term.succ (Term.add y d))) :=
        BProv_Ax_s_succ_add_terms y d
      have hsuccCong : BProv Ax_s D
          (eq
            (Term.add x (Term.add (Term.succ y) d))
            (Term.add x (Term.succ (Term.add y d)))) :=
        BProv_eq_congr_add_right x hsuccLeft
      have hbad : BProv Ax_s D
          (eq (Term.add x (Term.succ (Term.add y d))) x) :=
        BProv_eqTrans (BProv_eqTrans (BProv_eqSym hsuccCong)
          (BProv_eqSym hassoc)) hloop
      have hbot : BProv Ax_s D bot :=
        BProv_Ax_s_add_succ_ne_self_terms hbad
      simpa [rename] using hbot
    exact BProv_exE_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf)
      hleC (by
        simpa [C, leAt, leBody, rename, Term.rename, SetTheory.up,
          List.map_map, Function.comp_def] using hleBody)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hlt (by
      simpa [ltAt, ltBody] using hbody)

/-- PA refutes simultaneous opposite strict-order witnesses. -/
theorem BProv_Ax_s_ltAt_asymm_bot {G : List Formula} {a b : Nat}
    (hab : BProv Ax_s G (ltAt a b))
    (hba : BProv Ax_s G (ltAt b a)) :
    BProv Ax_s G bot :=
  BProv_Ax_s_ltAt_leAt_bot hab (BProv_Ax_s_leAt_of_ltAt hba)

/-- PA refutes `a < b` once the same context proves `b = a`. -/
theorem BProv_Ax_s_ltAt_eq_bot {G : List Formula} {a b : Nat}
    (hlt : BProv Ax_s G (ltAt a b))
    (heq : BProv Ax_s G (eq (Term.var b) (Term.var a))) :
    BProv Ax_s G bot :=
  BProv_Ax_s_ltAt_leAt_bot hlt (BProv_Ax_s_leAt_of_eq heq)

/-- If the left slot is `0` and the right slot is a successor, PA proves the
strict order between them. -/
theorem BProv_Ax_s_ltAt_of_eqConst_zero_succPredAt {G : List Formula}
    {a b : Nat}
    (ha : BProv Ax_s G (eqConstAt a 0))
    (hb : BProv Ax_s G (succPredAt b)) :
    BProv Ax_s G (ltAt a b) := by
  let succBody : Formula := eq (Term.var (b+1)) (Term.succ (Term.var 0))
  have hbody : BProv Ax_s (succBody :: G.map (rename Nat.succ))
      (rename Nat.succ (ltAt a b)) := by
    let C : List Formula := succBody :: G.map (rename Nat.succ)
    have hsucc : BProv Ax_s C succBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have haRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ (eqConstAt a 0)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        ha Nat.succ
    have haC : BProv Ax_s C (eq (Term.var (a+1)) Term.zero) := by
      simpa [eqConstAt, rename, Term.rename, Term.numeral] using
        BProv_context_cons haRen
    have hleftZero : BProv Ax_s C
        (eq
          (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.add Term.zero (Term.succ (Term.var 0)))) :=
      BProv_eq_congr_add_left (Term.succ (Term.var 0)) haC
    have hzeroAdd : BProv Ax_s C
        (eq
          (Term.add Term.zero (Term.succ (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_Ax_s_zero_add_term (Term.succ (Term.var 0))
    have hleft : BProv Ax_s C
        (eq
          (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_eqTrans hleftZero hzeroAdd
    have htarget : BProv Ax_s C
        (eq
          (Term.add (Term.var (a+1)) (Term.succ (Term.var 0)))
          (Term.var (b+1))) :=
      BProv_eqTrans hleft (BProv_eqSym hsucc)
    have hinst : BProv Ax_s C
        (subst (instTerm (Term.var 0))
          (eq
            (Term.add (Term.var (a+2)) (Term.succ (Term.var 0)))
            (Term.var (b+2)))) := by
      simpa [subst, instTerm, Term.subst, Term.upSubst] using htarget
    have hex : BProv Ax_s C
        (ex
          (eq
            (Term.add (Term.var (a+2)) (Term.succ (Term.var 0)))
            (Term.var (b+2)))) :=
      BProv_exI (B := Ax_s) (G := C)
        (a := eq
          (Term.add (Term.var (a+2)) (Term.succ (Term.var 0)))
          (Term.var (b+2)))
        (t := Term.var 0) hinst
    simpa [C, ltAt, rename, Term.rename, SetTheory.up] using hex
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hb (by
      simpa [succPredAt, succBody] using hbody)

/-- PA proves the strict closed-one bound case: from `x < y` and `y = 1`,
derive `x = 0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_ltAt_eqConst_one {G : List Formula}
    {a b : Nat}
    (hlt : BProv Ax_s G (ltAt a b))
    (hb : BProv Ax_s G (eqConstAt b 1)) :
    BProv Ax_s G (eqConstAt a 0) := by
  have hleConst : BProv Ax_s G (leConstAt a 1) :=
    BProv_Ax_s_leConstAt_of_leAt_eqConst
      (BProv_Ax_s_leAt_of_ltAt hlt) hb
  have hcases : BProv Ax_s G (or (leConstAt a 0) (eqConstAt a 1)) :=
    BProv_Ax_s_leConstAt_succ_cases (n := 0) hleConst
  have hleft : BProv Ax_s (leConstAt a 0 :: G) (eqConstAt a 0) :=
    BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero
      (BProv_ass (B := Ax_s) (G := leConstAt a 0 :: G) (by simp))
  have hright : BProv Ax_s (eqConstAt a 1 :: G) (eqConstAt a 0) := by
    let C : List Formula := eqConstAt a 1 :: G
    have haOne : BProv Ax_s C (eqConstAt a 1) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hltC : BProv Ax_s C (ltAt a b) :=
      BProv_context_cons hlt
    have hbC : BProv Ax_s C (eqConstAt b 1) :=
      BProv_context_cons hb
    have heq : BProv Ax_s C (eq (Term.var b) (Term.var a)) := by
      simpa [eqConstAt, Term.numeral] using
        BProv_eqTrans hbC (BProv_eqSym haOne)
    exact BProv_botE
      (a := eqConstAt a 0)
      (BProv_Ax_s_ltAt_eq_bot hltC heq)
  exact BProv_orE hcases hleft hright

/-- PA proves the term-parametric strict closed-one bound case: from
`a < y` and `y = 1`, derive `a = 0`. -/
theorem BProv_Ax_s_eq_zero_of_ltTermAt_eqConst_one {G : List Formula}
    {a : Term} {b : Nat}
    (hlt : BProv Ax_s G (ltTermAt a (Term.var b)))
    (hb : BProv Ax_s G (eqConstAt b 1)) :
    BProv Ax_s G (eq a Term.zero) := by
  let ltBody : Formula :=
    eq (Term.add (Term.rename Nat.succ a) (Term.succ (Term.var 0)))
      (Term.rename Nat.succ (Term.var b))
  have hbody : BProv Ax_s (ltBody :: G.map (rename Nat.succ))
      (rename Nat.succ (eq a Term.zero)) := by
    let C : List Formula := ltBody :: G.map (rename Nat.succ)
    have hltBody : BProv Ax_s C ltBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (b+1) 1) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hb Nat.succ
    have hbC : BProv Ax_s C (eqConstAt (b+1) 1) :=
      BProv_context_cons hbRen
    have hltEq : BProv Ax_s C
        (eq (Term.add (Term.rename Nat.succ a) (Term.succ (Term.var 0)))
          (Term.var (b+1))) := by
      simpa [ltBody, Term.rename] using hltBody
    have hsumOne : BProv Ax_s C
        (eq (Term.add (Term.rename Nat.succ a) (Term.succ (Term.var 0)))
          (Term.succ Term.zero)) := by
      have hbOne : BProv Ax_s C
          (eq (Term.var (b+1)) (Term.succ Term.zero)) := by
        simpa [eqConstAt, Term.numeral, Term.numeral_succ] using hbC
      exact BProv_eqTrans hltEq hbOne
    have hcases : BProv Ax_s C
        (or (eq (Term.rename Nat.succ a) Term.zero)
          (ex (eq (Term.rename Nat.succ (Term.rename Nat.succ a))
            (Term.succ (Term.var 0))))) :=
      BProv_Ax_s_zeroOrSuccPred_term (G := C) (Term.rename Nat.succ a)
    have hzeroBranch : BProv Ax_s
        (eq (Term.rename Nat.succ a) Term.zero :: C)
        (rename Nat.succ (eq a Term.zero)) := by
      have hz : BProv Ax_s
          (eq (Term.rename Nat.succ a) Term.zero :: C)
          (eq (Term.rename Nat.succ a) Term.zero) :=
        BProv_ass (B := Ax_s)
          (G := eq (Term.rename Nat.succ a) Term.zero :: C) (by simp)
      simpa [rename, Term.rename] using hz
    let succBody : Formula :=
      eq (Term.rename Nat.succ (Term.rename Nat.succ a))
        (Term.succ (Term.var 0))
    have hsuccBranch : BProv Ax_s (ex succBody :: C)
        (rename Nat.succ (eq a Term.zero)) := by
      have hopened : BProv Ax_s
          (succBody :: (ex succBody :: C).map (rename Nat.succ)) bot := by
        let D : List Formula :=
          succBody :: (ex succBody :: C).map (rename Nat.succ)
        have hsucc : BProv Ax_s D succBody :=
          BProv_ass (B := Ax_s) (G := D) (by simp [D])
        have hsumRen : BProv Ax_s (C.map (rename Nat.succ))
            (rename Nat.succ
              (eq
                (Term.add (Term.rename Nat.succ a)
                  (Term.succ (Term.var 0)))
                (Term.succ Term.zero))) :=
          BProv_rename_of_sentences
            (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
            hsumOne Nat.succ
        have hsumD : BProv Ax_s D
            (rename Nat.succ
              (eq
                (Term.add (Term.rename Nat.succ a)
                  (Term.succ (Term.var 0)))
                (Term.succ Term.zero))) := by
          exact BProv_context_cons
            (BProv_context_cons (B := Ax_s) hsumRen)
        have hsum : BProv Ax_s D
            (eq
              (Term.add
                (Term.rename Nat.succ (Term.rename Nat.succ a))
                (Term.succ (Term.var 1)))
              (Term.succ Term.zero)) := by
          simpa [rename, Term.rename] using hsumD
        have hleft : BProv Ax_s D
            (eq
              (Term.add
                (Term.rename Nat.succ (Term.rename Nat.succ a))
                (Term.succ (Term.var 1)))
              (Term.add (Term.succ (Term.var 0))
                (Term.succ (Term.var 1)))) :=
          BProv_eq_congr_add_left (Term.succ (Term.var 1)) hsucc
        have hsumSucc : BProv Ax_s D
            (eq
              (Term.add (Term.succ (Term.var 0))
                (Term.succ (Term.var 1)))
              (Term.succ Term.zero)) :=
          BProv_eqTrans (BProv_eqSym hleft) hsum
        have hsuccAdd : BProv Ax_s D
            (eq
              (Term.add (Term.succ (Term.var 0))
                (Term.succ (Term.var 1)))
              (Term.succ
                (Term.add (Term.var 0) (Term.succ (Term.var 1))))) :=
          BProv_Ax_s_succ_add_terms (Term.var 0) (Term.succ (Term.var 1))
        have hsuccEq : BProv Ax_s D
            (eq
              (Term.succ
                (Term.add (Term.var 0) (Term.succ (Term.var 1))))
              (Term.succ Term.zero)) :=
          BProv_eqTrans (BProv_eqSym hsuccAdd) hsumSucc
        have hinj : BProv Ax_s D
            (imp
              (eq
                (Term.succ
                  (Term.add (Term.var 0) (Term.succ (Term.var 1))))
                (Term.succ Term.zero))
              (eq (Term.add (Term.var 0) (Term.succ (Term.var 1)))
                Term.zero)) :=
          BProv_weaken_nil
            (BProv_Ax_s_succInj_terms
              (Term.add (Term.var 0) (Term.succ (Term.var 1))) Term.zero)
        have hsumZero : BProv Ax_s D
            (eq (Term.add (Term.var 0) (Term.succ (Term.var 1)))
              Term.zero) :=
          BProv_mp Ax_s D _ _ hinj hsuccEq
        have hsuccZero : BProv Ax_s D
            (eq (Term.succ (Term.var 1)) Term.zero) :=
          BProv_Ax_s_add_eq_zero_right_terms
            (x := Term.var 0) (y := Term.succ (Term.var 1)) hsumZero
        have hnot : BProv Ax_s D
            (imp (eq (Term.succ (Term.var 1)) Term.zero) bot) :=
          BProv_weaken_nil (BProv_Ax_s_zeroNotSucc_term (Term.var 1))
        exact BProv_mp Ax_s D _ _ hnot hsuccZero
      have hbot : BProv Ax_s (ex succBody :: C) bot :=
        BProv_exE_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          (BProv_ass (B := Ax_s) (G := ex succBody :: C)
            (phi := ex succBody) (by simp))
          (by simpa [succBody, rename] using hopened)
      exact BProv_botE hbot
    exact BProv_orE hcases hzeroBranch (by simpa [succBody] using hsuccBranch)
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hlt (by
      simpa [ltTermAt, ltBody] using hbody)

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

/-- In a binary-halving step, current value `0` forces the half/next slot to
be `0`.  This is the local zero-propagation kernel for beta-coded halving
traces starting from the empty-set code. -/
theorem BProv_Ax_s_div2StepAt_zero_half_zero {G : List Formula}
    {value half bit : Nat}
    (hvalue : BProv Ax_s G (eqConstAt value 0))
    (hstep : BProv Ax_s G (div2StepAt value half bit)) :
    BProv Ax_s G (eqConstAt half 0) := by
  let double : Term := Term.add (Term.var half) (Term.var half)
  have hstepEq : BProv Ax_s G
      (eq (Term.var value) (Term.add double (Term.var bit))) := by
    simpa [div2StepAt, double] using
      (BProv_andE2 (a := boolAt bit)
        (b := eq (Term.var value)
          (Term.add (Term.add (Term.var half) (Term.var half))
            (Term.var bit))) hstep)
  have hrightZero : BProv Ax_s G
      (eq (Term.add double (Term.var bit)) Term.zero) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eqTrans (BProv_eqSym hstepEq) hvalue
  have hdoubleZero : BProv Ax_s G (eq double Term.zero) :=
    BProv_Ax_s_add_eq_zero_left_terms hrightZero
  have hhalfZero : BProv Ax_s G (eq (Term.var half) Term.zero) :=
    BProv_Ax_s_add_eq_zero_left_terms
      (x := Term.var half) (y := Term.var half) hdoubleZero
  simpa [eqConstAt, Term.numeral] using hhalfZero

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

/-- Eliminate a remainder proof to its strict boundedness component. -/
theorem BProv_Ax_s_ltAt_of_remAt {G : List Formula}
    {rem value modulus : Nat}
    (hrem : BProv Ax_s G (remAt rem value modulus)) :
    BProv Ax_s G (ltAt rem modulus) := by
  let body : Formula :=
    and
      (ltAt (rem+1) (modulus+1))
      (eq (Term.var (value+1))
        (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
          (Term.var (rem+1))))
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (ltAt rem modulus)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hlt : BProv Ax_s C (ltAt (rem+1) (modulus+1)) :=
      BProv_andE1 hbodyAss
    simpa [C, ltAt, rename, Term.rename, SetTheory.up] using hlt
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hrem (by
      simpa [remAt, body] using hbody)

/-- Eliminate a remainder proof to the existential quotient equation it
contains, forgetting only the strict bound. -/
theorem BProv_Ax_s_remEqAt_of_remAt {G : List Formula}
    {rem value modulus : Nat}
    (hrem : BProv Ax_s G (remAt rem value modulus)) :
    BProv Ax_s G (remEqAt rem value modulus) := by
  let body : Formula :=
    and
      (ltAt (rem+1) (modulus+1))
      (eq (Term.var (value+1))
        (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
          (Term.var (rem+1))))
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (remEqAt rem value modulus)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have heq : BProv Ax_s C
        (eq (Term.var (value+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.var (rem+1)))) :=
      BProv_andE2 hbodyAss
    have hinst : BProv Ax_s C
        (subst (instTerm (Term.var 0))
          (eq (Term.var (value+1+1))
            (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
              (Term.var (rem+1+1))))) := by
      simpa [subst, instTerm, Term.subst, Term.upSubst] using heq
    have hex : BProv Ax_s C
        (ex (eq (Term.var (value+1+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
            (Term.var (rem+1+1))))) :=
      BProv_exI (B := Ax_s) (G := C)
        (a := eq (Term.var (value+1+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
            (Term.var (rem+1+1))))
        (t := Term.var 0) hinst
    simpa [C, remEqAt, rename, Term.rename, SetTheory.up] using hex
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hrem (by
      simpa [remAt, body] using hbody)

/-- Eliminate a term-parametric remainder proof to its strict boundedness
component. -/
theorem BProv_Ax_s_ltTermAt_of_remTermAt {G : List Formula}
    {rem : Term} {value modulus : Nat}
    (hrem : BProv Ax_s G (remTermAt rem value modulus)) :
    BProv Ax_s G (ltTermAt rem (Term.var modulus)) := by
  let body : Formula :=
    and
      (ltTermAt (Term.rename Nat.succ rem) (Term.var (modulus+1)))
      (eq (Term.var (value+1))
        (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
          (Term.rename Nat.succ rem)))
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (ltTermAt rem (Term.var modulus))) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hlt : BProv Ax_s C
        (ltTermAt (Term.rename Nat.succ rem) (Term.var (modulus+1))) :=
      BProv_andE1 hbodyAss
    simpa [C, ltTermAt, rename, Term.rename, SetTheory.up,
      Term.rename_comp] using hlt
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hrem (by
      simpa [remTermAt, body] using hbody)

/-- Eliminate a term-parametric remainder proof to the existential quotient
equation it contains, forgetting only the strict bound. -/
theorem BProv_Ax_s_remTermEqAt_of_remTermAt {G : List Formula}
    {rem : Term} {value modulus : Nat}
    (hrem : BProv Ax_s G (remTermAt rem value modulus)) :
    BProv Ax_s G (remTermEqAt rem value modulus) := by
  let body : Formula :=
    and
      (ltTermAt (Term.rename Nat.succ rem) (Term.var (modulus+1)))
      (eq (Term.var (value+1))
        (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
          (Term.rename Nat.succ rem)))
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (remTermEqAt rem value modulus)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have heq : BProv Ax_s C
        (eq (Term.var (value+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.rename Nat.succ rem))) :=
      BProv_andE2 hbodyAss
    have hinst : BProv Ax_s C
        (subst (instTerm (Term.var 0))
          (eq (Term.var (value+1+1))
            (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
              (Term.rename Nat.succ (Term.rename Nat.succ rem))))) := by
      have hremSubst :
          Term.subst (instTerm (Term.var 0))
              (Term.rename (fun n => n + 1 + 1) rem) =
            Term.rename Nat.succ rem := by
        have hrename :
            Term.rename (fun n => n + 1 + 1) rem =
              Term.rename Nat.succ (Term.rename Nat.succ rem) := by
          rw [Term.rename_comp]
        rw [hrename]
        exact term_subst_instTerm_rename_succ (Term.rename Nat.succ rem)
          (Term.var 0)
      simpa [subst, instTerm, Term.subst, Term.upSubst,
        Term.rename_comp, hremSubst] using heq
    have hex : BProv Ax_s C
        (ex (eq (Term.var (value+1+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
            (Term.rename Nat.succ (Term.rename Nat.succ rem))))) :=
      BProv_exI (B := Ax_s) (G := C)
        (a := eq (Term.var (value+1+1))
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1+1)))
            (Term.rename Nat.succ (Term.rename Nat.succ rem))))
        (t := Term.var 0) hinst
    simpa [C, remTermEqAt, rename, Term.rename, SetTheory.up,
      Term.rename_comp] using hex
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hrem (by
      simpa [remTermAt, body] using hbody)

/-- A term-parametric remainder of zero-valued division is the zero term.  The
modulus is deliberately left unconstrained: the conclusion follows from the
quotient equation alone. -/
theorem BProv_Ax_s_eq_zero_of_remTermAt_eqConst_zero
    {G : List Formula} {rem : Term} {value modulus : Nat}
    (hrem : BProv Ax_s G (remTermAt rem value modulus))
    (hvalue : BProv Ax_s G (eqConstAt value 0)) :
    BProv Ax_s G (eq rem Term.zero) := by
  let eqBody : Formula :=
    eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.rename Nat.succ rem))
  have heqEx : BProv Ax_s G (remTermEqAt rem value modulus) :=
    BProv_Ax_s_remTermEqAt_of_remTermAt hrem
  have hbody : BProv Ax_s (eqBody :: G.map (rename Nat.succ))
      (rename Nat.succ (eq rem Term.zero)) := by
    let C : List Formula := eqBody :: G.map (rename Nat.succ)
    have heqBody : BProv Ax_s C eqBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hvalueRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (value+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hvalue Nat.succ
    have hvalueC : BProv Ax_s C (eqConstAt (value+1) 0) :=
      BProv_context_cons hvalueRen
    have hsumZero : BProv Ax_s C
        (eq
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.rename Nat.succ rem))
          Term.zero) := by
      simpa [eqConstAt, Term.numeral, eqBody] using
        BProv_eqTrans (BProv_eqSym heqBody) hvalueC
    have hremZero : BProv Ax_s C (eq (Term.rename Nat.succ rem) Term.zero) :=
      BProv_Ax_s_add_eq_zero_right_terms
        (x := Term.mul (Term.var 0) (Term.var (modulus+1)))
        (y := Term.rename Nat.succ rem) hsumZero
    simpa [C, rename, Term.rename, Term.numeral] using hremZero
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) heqEx (by
      simpa [remTermEqAt, eqBody] using hbody)

/-- A remainder of zero-valued division is zero.  The modulus is deliberately
left unconstrained: the conclusion follows from the quotient equation alone. -/
theorem BProv_Ax_s_eqConstAt_zero_of_remAt_eqConst_zero
    {G : List Formula} {rem value modulus : Nat}
    (hrem : BProv Ax_s G (remAt rem value modulus))
    (hvalue : BProv Ax_s G (eqConstAt value 0)) :
    BProv Ax_s G (eqConstAt rem 0) := by
  let eqBody : Formula :=
    eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.var (rem+1)))
  have heqEx : BProv Ax_s G (remEqAt rem value modulus) :=
    BProv_Ax_s_remEqAt_of_remAt hrem
  have hbody : BProv Ax_s (eqBody :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt rem 0)) := by
    let C : List Formula := eqBody :: G.map (rename Nat.succ)
    have heqBody : BProv Ax_s C eqBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hvalueRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (value+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hvalue Nat.succ
    have hvalueC : BProv Ax_s C (eqConstAt (value+1) 0) :=
      BProv_context_cons hvalueRen
    have hsumZero : BProv Ax_s C
        (eq
          (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
            (Term.var (rem+1)))
          Term.zero) := by
      simpa [eqConstAt, Term.numeral, eqBody] using
        BProv_eqTrans (BProv_eqSym heqBody) hvalueC
    have hremZero : BProv Ax_s C (eq (Term.var (rem+1)) Term.zero) :=
      BProv_Ax_s_add_eq_zero_right_terms
        (x := Term.mul (Term.var 0) (Term.var (modulus+1)))
        (y := Term.var (rem+1)) hsumZero
    simpa [C, eqConstAt, rename, Term.rename, Term.numeral] using hremZero
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) heqEx (by
      simpa [remEqAt, eqBody] using hbody)

/-- A remainder modulo `1` is `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_remAt_eqConst_modulus_one
    {G : List Formula} {rem value modulus : Nat}
    (hrem : BProv Ax_s G (remAt rem value modulus))
    (hmodulus : BProv Ax_s G (eqConstAt modulus 1)) :
    BProv Ax_s G (eqConstAt rem 0) :=
  BProv_Ax_s_eqConstAt_zero_of_ltAt_eqConst_one
    (BProv_Ax_s_ltAt_of_remAt hrem) hmodulus

/-- A term-parametric remainder modulo `1` is the zero term. -/
theorem BProv_Ax_s_eq_zero_of_remTermAt_eqConst_modulus_one
    {G : List Formula} {rem : Term} {value modulus : Nat}
    (hrem : BProv Ax_s G (remTermAt rem value modulus))
    (hmodulus : BProv Ax_s G (eqConstAt modulus 1)) :
    BProv Ax_s G (eq rem Term.zero) :=
  BProv_Ax_s_eq_zero_of_ltTermAt_eqConst_one
    (BProv_Ax_s_ltTermAt_of_remTermAt hrem) hmodulus

/-- No remainder can be strictly below modulus `0`. -/
theorem BProv_Ax_s_remAt_eqConst_modulus_zero_bot
    {G : List Formula} {rem value modulus : Nat}
    (hrem : BProv Ax_s G (remAt rem value modulus))
    (hmodulus : BProv Ax_s G (eqConstAt modulus 0)) :
    BProv Ax_s G bot := by
  have hlt : BProv Ax_s G (ltAt rem modulus) :=
    BProv_Ax_s_ltAt_of_remAt hrem
  have hremZero : BProv Ax_s G (eqConstAt rem 0) :=
    BProv_Ax_s_eqConstAt_zero_of_leAt_eqConst_zero
      (BProv_Ax_s_leAt_of_ltAt hlt) hmodulus
  have heq : BProv Ax_s G (eq (Term.var modulus) (Term.var rem)) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eqTrans hmodulus (BProv_eqSym hremZero)
  exact BProv_Ax_s_ltAt_eq_bot hlt heq

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

/-- If the beta step parameter is `0`, the beta modulus term is `1`, uniformly
in the index slot. -/
theorem BProv_Ax_s_betaModTerm_eq_one_of_eqConst_step_zero
    {G : List Formula} {step idx : Nat}
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eq (betaModTerm step idx) (Term.numeral 1)) := by
  let idxSucc : Term := Term.succ (Term.var idx)
  have hmulLeft : BProv Ax_s G
      (eq (Term.mul idxSucc (Term.var step))
        (Term.mul idxSucc Term.zero)) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eq_congr_mul_right idxSucc hstep
  have hmulZero : BProv Ax_s G
      (eq (Term.mul idxSucc Term.zero) Term.zero) :=
    BProv_weaken_nil (BProv_Ax_s_mulZero_term idxSucc)
  have hmul : BProv Ax_s G
      (eq (Term.mul idxSucc (Term.var step)) Term.zero) :=
    BProv_eqTrans hmulLeft hmulZero
  have hsucc : BProv Ax_s G
      (eq (Term.succ (Term.mul idxSucc (Term.var step)))
        (Term.succ Term.zero)) :=
    BProv_eq_congr_succ hmul
  simpa [betaModTerm, idxSucc, Term.numeral, Term.numeral_succ] using hsucc

/-- If the beta index is `0` and the beta step is a successor, the beta
modulus is that successor plus one. -/
theorem BProv_Ax_s_betaModTerm_idx_zero_of_step_succ
    {G : List Formula} {step idx pred : Nat}
    (hidx : BProv Ax_s G (eqConstAt idx 0))
    (hstep : BProv Ax_s G (eq (Term.var step) (Term.succ (Term.var pred)))) :
    BProv Ax_s G
      (eq (betaModTerm step idx) (Term.succ (Term.succ (Term.var pred)))) := by
  have hidxSucc : BProv Ax_s G
      (eq (Term.succ (Term.var idx)) (Term.numeral 1)) := by
    simpa [eqConstAt, Term.numeral, Term.numeral_succ] using
      BProv_eq_congr_succ hidx
  have hmul : BProv Ax_s G
      (eq
        (Term.mul (Term.succ (Term.var idx)) (Term.var step))
        (Term.mul (Term.numeral 1) (Term.succ (Term.var pred)))) :=
    BProv_eq_congr_mul hidxSucc hstep
  have hone : BProv Ax_s G
      (eq
        (Term.mul (Term.numeral 1) (Term.succ (Term.var pred)))
        (Term.succ (Term.var pred))) :=
    BProv_Ax_s_one_mul_term (Term.succ (Term.var pred))
  have hsucc : BProv Ax_s G
      (eq
        (Term.succ
          (Term.mul (Term.succ (Term.var idx)) (Term.var step)))
        (Term.succ (Term.succ (Term.var pred)))) :=
    BProv_eq_congr_succ (BProv_eqTrans hmul hone)
  simpa [betaModTerm] using hsucc

/-- A PA proof of `s = succ(t)` and `s = 0` closes the branch. -/
theorem BProv_Ax_s_eq_succ_eq_zero_bot
    {G : List Formula} {s t : Term}
    (hsucc : BProv Ax_s G (eq s (Term.succ t)))
    (hzero : BProv Ax_s G (eq s Term.zero)) :
    BProv Ax_s G bot := by
  have hbad : BProv Ax_s G (eq (Term.succ t) Term.zero) :=
    BProv_eqTrans (BProv_eqSym hsucc) hzero
  have hnot : BProv Ax_s G (imp (eq (Term.succ t) Term.zero) bot) :=
    BProv_weaken_nil (BProv_Ax_s_zeroNotSucc_term t)
  exact BProv_mp Ax_s G _ _ hnot hbad

/-- In a successor beta step, the zero-index beta modulus cannot be zero. -/
theorem BProv_Ax_s_betaModTerm_idx_zero_step_succ_ne_zero_bot
    {G : List Formula} {step idx pred : Nat}
    (hidx : BProv Ax_s G (eqConstAt idx 0))
    (hstep : BProv Ax_s G (eq (Term.var step) (Term.succ (Term.var pred))))
    (hzero : BProv Ax_s G (eq (betaModTerm step idx) Term.zero)) :
    BProv Ax_s G bot :=
  BProv_Ax_s_eq_succ_eq_zero_bot
    (BProv_Ax_s_betaModTerm_idx_zero_of_step_succ hidx hstep)
    hzero

/-- If an opened beta witness identifies its modulus variable with the
zero-index successor-step beta modulus, that modulus variable cannot be `0`. -/
theorem BProv_Ax_s_betaModTerm_modEq_zero_bot
    {G : List Formula} {modulus step idx pred : Nat}
    (hmodEq : BProv Ax_s G
      (eq (Term.var modulus) (betaModTerm step idx)))
    (hmodZero : BProv Ax_s G (eqConstAt modulus 0))
    (hidx : BProv Ax_s G (eqConstAt idx 0))
    (hstep : BProv Ax_s G
      (eq (Term.var step) (Term.succ (Term.var pred)))) :
    BProv Ax_s G bot := by
  have hbetaZero : BProv Ax_s G (eq (betaModTerm step idx) Term.zero) := by
    simpa [eqConstAt, Term.numeral] using
      BProv_eqTrans (BProv_eqSym hmodEq) hmodZero
  exact BProv_Ax_s_betaModTerm_idx_zero_step_succ_ne_zero_bot
    hidx hstep hbetaZero

/-- If a variable is explicitly equal to a successor term, PA proves the
corresponding `succPredAt` relation by using that predecessor as witness. -/
theorem BProv_Ax_s_succPredAt_of_eq_succ_term
    {G : List Formula} {a : Nat} {t : Term}
    (h : BProv Ax_s G (eq (Term.var a) (Term.succ t))) :
    BProv Ax_s G (succPredAt a) := by
  have hbody : BProv Ax_s G
      (subst (instTerm t)
        (eq (Term.var (a+1)) (Term.succ (Term.var 0)))) := by
    simpa [subst, instTerm, Term.subst, Term.upSubst] using h
  simpa [succPredAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.var (a+1)) (Term.succ (Term.var 0)))
      (t := t) hbody)

/-- If an opened beta witness identifies its modulus variable with the
zero-index successor-step beta modulus, PA proves the modulus is a successor. -/
theorem BProv_Ax_s_betaModTerm_modEq_succPredAt
    {G : List Formula} {modulus step idx pred : Nat}
    (hmodEq : BProv Ax_s G
      (eq (Term.var modulus) (betaModTerm step idx)))
    (hidx : BProv Ax_s G (eqConstAt idx 0))
    (hstep : BProv Ax_s G
      (eq (Term.var step) (Term.succ (Term.var pred)))) :
    BProv Ax_s G (succPredAt modulus) := by
  have hbetaSucc : BProv Ax_s G
      (eq (betaModTerm step idx) (Term.succ (Term.succ (Term.var pred)))) :=
    BProv_Ax_s_betaModTerm_idx_zero_of_step_succ hidx hstep
  have hmodSucc : BProv Ax_s G
      (eq (Term.var modulus) (Term.succ (Term.succ (Term.var pred)))) :=
    BProv_eqTrans hmodEq hbetaSucc
  exact BProv_Ax_s_succPredAt_of_eq_succ_term hmodSucc

/-- If a beta modulus variable is the zero-index successor-step beta modulus,
any slot proved to be `0` is strictly below that modulus. -/
theorem BProv_Ax_s_ltAt_zero_of_betaModTerm_modEq
    {G : List Formula} {zeroSlot modulus step idx pred : Nat}
    (hzero : BProv Ax_s G (eqConstAt zeroSlot 0))
    (hmodEq : BProv Ax_s G
      (eq (Term.var modulus) (betaModTerm step idx)))
    (hidx : BProv Ax_s G (eqConstAt idx 0))
    (hstep : BProv Ax_s G
      (eq (Term.var step) (Term.succ (Term.var pred)))) :
    BProv Ax_s G (ltAt zeroSlot modulus) :=
  BProv_Ax_s_ltAt_of_eqConst_zero_succPredAt hzero
    (BProv_Ax_s_betaModTerm_modEq_succPredAt hmodEq hidx hstep)

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

/-- Projection from the opened body of a raw `betaAt` witness to the modulus
equation. -/
theorem BProv_Ax_s_betaAt_opened_body_modEq
    {G : List Formula} {out code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
        (remAt (out+1) (code+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE1 hbody

/-- Projection from the opened body of a raw `betaAt` witness to its remainder
component. -/
theorem BProv_Ax_s_betaAt_opened_body_rem
    {G : List Formula} {out code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
        (remAt (out+1) (code+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (remAt (out+1) (code+1) 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE2 hbody

/-- Projection from the opened body of a term-output raw `betaTermAt` witness
to the modulus equation. -/
theorem BProv_Ax_s_betaTermAt_opened_body_modEq
    {G : List Formula} {out : Term} {code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
        (remTermAt (Term.rename Nat.succ out) (code+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE1 hbody

/-- Projection from the opened body of a term-output raw `betaTermAt` witness
to its remainder component. -/
theorem BProv_Ax_s_betaTermAt_opened_body_rem
    {G : List Formula} {out : Term} {code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
        (remTermAt (Term.rename Nat.succ out) (code+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE2 hbody

/-- Opened term-output raw-beta specialization of
`BProv_Ax_s_betaModTerm_modEq_zero_bot`. -/
theorem BProv_Ax_s_betaTermAt_opened_body_modulus_zero_bot
    {G : List Formula} {out : Term} {code step idx pred : Nat}
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred))))
    (hmodZero : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eqConstAt 0 0)) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      bot := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaTermAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_betaModTerm_modEq_zero_bot
    (G := C) (modulus := 0) (step := step+1) (idx := idx+1)
    (pred := pred)
    hmodEq
    (by simpa [body, C] using hmodZero)
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Opened term-output raw-beta successor-modulus projection for the zero-index,
successor-step case. -/
theorem BProv_Ax_s_betaTermAt_opened_body_modulus_succPredAt
    {G : List Formula} {out : Term} {code step idx pred : Nat}
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred)))) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (succPredAt 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaTermAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_betaModTerm_modEq_succPredAt
    (G := C) (modulus := 0) (step := step+1) (idx := idx+1)
    (pred := pred)
    hmodEq
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Opened term-output raw-beta positivity projection for the zero-index,
successor-step case. -/
theorem BProv_Ax_s_betaTermAt_opened_body_zero_lt_modulus
    {G : List Formula} {out : Term} {code step idx pred zeroSlot : Nat}
    (hzero : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eqConstAt zeroSlot 0))
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred)))) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remTermAt (Term.rename Nat.succ out) (code+1) 0)) ::
        G.map (rename Nat.succ))
      (ltAt zeroSlot 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaTermAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_ltAt_zero_of_betaModTerm_modEq
    (G := C) (zeroSlot := zeroSlot) (modulus := 0)
    (step := step+1) (idx := idx+1) (pred := pred)
    (by simpa [body, C] using hzero)
    hmodEq
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Opened raw-beta specialization of
`BProv_Ax_s_betaModTerm_modEq_zero_bot`. -/
theorem BProv_Ax_s_betaAt_opened_body_modulus_zero_bot
    {G : List Formula} {out code step idx pred : Nat}
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred))))
    (hmodZero : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eqConstAt 0 0)) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      bot := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_betaModTerm_modEq_zero_bot
    (G := C) (modulus := 0) (step := step+1) (idx := idx+1)
    (pred := pred)
    hmodEq
    (by simpa [body, C] using hmodZero)
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Opened raw-beta successor-modulus projection for the zero-index,
successor-step case. -/
theorem BProv_Ax_s_betaAt_opened_body_modulus_succPredAt
    {G : List Formula} {out code step idx pred : Nat}
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred)))) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (succPredAt 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_betaModTerm_modEq_succPredAt
    (G := C) (modulus := 0) (step := step+1) (idx := idx+1)
    (pred := pred)
    hmodEq
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Opened raw-beta positivity projection for the zero-index,
successor-step case. -/
theorem BProv_Ax_s_betaAt_opened_body_zero_lt_modulus
    {G : List Formula} {out code step idx pred zeroSlot : Nat}
    (hzero : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eqConstAt zeroSlot 0))
    (hidx : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eqConstAt (idx+1) 0))
    (hstep : BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (eq (Term.var (step+1)) (Term.succ (Term.var pred)))) :
    BProv Ax_s
      ((and
          (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
          (remAt (out+1) (code+1) 0)) :: G.map (rename Nat.succ))
      (ltAt zeroSlot 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  let C : List Formula := body :: G.map (rename Nat.succ)
  have hmodEqRaw : BProv Ax_s C
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
    BProv_Ax_s_betaAt_opened_body_modEq
      (G := G) (out := out) (code := code) (step := step) (idx := idx)
  have hmodEq : BProv Ax_s C
      (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
    simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
  exact BProv_Ax_s_ltAt_zero_of_betaModTerm_modEq
    (G := C) (zeroSlot := zeroSlot) (modulus := 0)
    (step := step+1) (idx := idx+1) (pred := pred)
    (by simpa [body, C] using hzero)
    hmodEq
    (by simpa [body, C] using hidx)
    (by simpa [body, C] using hstep)

/-- Projection from the opened body of a `betaAtConstIdx` wrapper to its closed
index equation. -/
theorem BProv_Ax_s_betaAtConstIdx_opened_body_idx
    {G : List Formula} {out code step idxValue : Nat} :
    let body : Formula :=
      and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ)) (eqConstAt 0 idxValue) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE1 hbody

/-- Projection from the opened body of a `betaAtConstIdx` wrapper to the raw
beta-entry component. -/
theorem BProv_Ax_s_betaAtConstIdx_opened_body_beta
    {G : List Formula} {out code step idxValue : Nat} :
    let body : Formula :=
      and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (betaAt (out+1) (code+1) (step+1) 0) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE2 hbody

/-- Projection from the opened body of a term-output `betaTermAtConstIdx`
wrapper to its closed index equation. -/
theorem BProv_Ax_s_betaTermAtConstIdx_opened_body_idx
    {G : List Formula} {out : Term} {code step idxValue : Nat} :
    let body : Formula :=
      and (eqConstAt 0 idxValue)
        (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ)) (eqConstAt 0 idxValue) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue)
      (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE1 hbody

/-- Projection from the opened body of a term-output `betaTermAtConstIdx`
wrapper to the raw term-output beta-entry component. -/
theorem BProv_Ax_s_betaTermAtConstIdx_opened_body_beta
    {G : List Formula} {out : Term} {code step idxValue : Nat} :
    let body : Formula :=
      and (eqConstAt 0 idxValue)
        (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue)
      (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE2 hbody

/-- Projection from the opened body of a `betaAtSuccIdx` wrapper to the
successor-index equation. -/
theorem BProv_Ax_s_betaAtSuccIdx_opened_body_idx
    {G : List Formula} {out code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
        (betaAt (out+1) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (eq (Term.var 0) (Term.succ (Term.var (idx+1)))) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
      (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE1 hbody

/-- Projection from the opened body of a `betaAtSuccIdx` wrapper to the raw
beta-entry component. -/
theorem BProv_Ax_s_betaAtSuccIdx_opened_body_beta
    {G : List Formula} {out code step idx : Nat} :
    let body : Formula :=
      and
        (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
        (betaAt (out+1) (code+1) (step+1) 0)
    BProv Ax_s (body :: G.map (rename Nat.succ))
      (betaAt (out+1) (code+1) (step+1) 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
      (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ)) body :=
    BProv_ass (B := Ax_s) (G := body :: G.map (rename Nat.succ)) (by simp)
  exact BProv_andE2 hbody

/-- If the beta code is `0`, every beta entry extracted from it is `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_code_zero
    {G : List Formula} {out code step idx : Nat}
    (hbeta : BProv Ax_s G (betaAt out code step idx))
    (hcode : BProv Ax_s G (eqConstAt code 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hrem : BProv Ax_s C (remAt (out+1) (code+1) 0) :=
      BProv_andE2 hbodyAss
    have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (code+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hcode Nat.succ
    have hcodeC : BProv Ax_s C (eqConstAt (code+1) 0) :=
      BProv_context_cons hcodeRen
    exact BProv_Ax_s_eqConstAt_zero_of_remAt_eqConst_zero
      (rem := out+1) (value := code+1) (modulus := 0) hrem hcodeC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAt, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta code is `0`, every term-output beta entry denotes `0`. -/
theorem BProv_Ax_s_eq_zero_of_betaTermAt_eqConst_code_zero
    {G : List Formula} {out : Term} {code step idx : Nat}
    (hbeta : BProv Ax_s G (betaTermAt out code step idx))
    (hcode : BProv Ax_s G (eqConstAt code 0)) :
    BProv Ax_s G (eq out Term.zero) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eq out Term.zero)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hrem : BProv Ax_s C
        (remTermAt (Term.rename Nat.succ out) (code+1) 0) :=
      BProv_andE2 hbodyAss
    have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (code+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hcode Nat.succ
    have hcodeC : BProv Ax_s C (eqConstAt (code+1) 0) :=
      BProv_context_cons hcodeRen
    exact BProv_Ax_s_eq_zero_of_remTermAt_eqConst_zero
      (rem := Term.rename Nat.succ out) (value := code+1)
      (modulus := 0) hrem hcodeC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaTermAt, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta step parameter is `0`, every raw beta entry has output `0`:
all beta moduli are then `1`, so the embedded remainder is modulo `1`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_step_zero
    {G : List Formula} {out code step idx : Nat}
    (hbeta : BProv Ax_s G (betaAt out code step idx))
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remAt (out+1) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hmodEqRaw : BProv Ax_s C
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
      BProv_andE1 hbodyAss
    have hmodEq : BProv Ax_s C
        (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
      simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
    have hrem : BProv Ax_s C (remAt (out+1) (code+1) 0) :=
      BProv_andE2 hbodyAss
    have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (step+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hstep Nat.succ
    have hstepC : BProv Ax_s C (eqConstAt (step+1) 0) :=
      BProv_context_cons hstepRen
    have hmodTermOne : BProv Ax_s C
        (eq (betaModTerm (step+1) (idx+1)) (Term.numeral 1)) :=
      BProv_Ax_s_betaModTerm_eq_one_of_eqConst_step_zero hstepC
    have hmodOne : BProv Ax_s C (eqConstAt 0 1) := by
      simpa [eqConstAt] using BProv_eqTrans hmodEq hmodTermOne
    exact BProv_Ax_s_eqConstAt_zero_of_remAt_eqConst_modulus_one
      hrem hmodOne
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAt, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta step parameter is `0`, every term-output raw beta entry
denotes `0`: all beta moduli are then `1`, so the embedded term remainder is
modulo `1`. -/
theorem BProv_Ax_s_eq_zero_of_betaTermAt_eqConst_step_zero
    {G : List Formula} {out : Term} {code step idx : Nat}
    (hbeta : BProv Ax_s G (betaTermAt out code step idx))
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eq out Term.zero) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
      (remTermAt (Term.rename Nat.succ out) (code+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eq out Term.zero)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hmodEqRaw : BProv Ax_s C
        (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx))) :=
      BProv_andE1 hbodyAss
    have hmodEq : BProv Ax_s C
        (eq (Term.var 0) (betaModTerm (step+1) (idx+1))) := by
      simpa [betaModTerm, rename, Term.rename] using hmodEqRaw
    have hrem : BProv Ax_s C
        (remTermAt (Term.rename Nat.succ out) (code+1) 0) :=
      BProv_andE2 hbodyAss
    have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (step+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hstep Nat.succ
    have hstepC : BProv Ax_s C (eqConstAt (step+1) 0) :=
      BProv_context_cons hstepRen
    have hmodTermOne : BProv Ax_s C
        (eq (betaModTerm (step+1) (idx+1)) (Term.numeral 1)) :=
      BProv_Ax_s_betaModTerm_eq_one_of_eqConst_step_zero hstepC
    have hmodOne : BProv Ax_s C (eqConstAt 0 1) := by
      simpa [eqConstAt] using BProv_eqTrans hmodEq hmodTermOne
    exact BProv_Ax_s_eq_zero_of_remTermAt_eqConst_modulus_one
      hrem hmodOne
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaTermAt, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta code is `0`, every constant-index beta wrapper also has
output `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAtConstIdx_eqConst_code_zero
    {G : List Formula} {out code step idxValue : Nat}
    (hbeta : BProv Ax_s G (betaAtConstIdx out code step idxValue))
    (hcode : BProv Ax_s G (eqConstAt code 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C (betaAt (out+1) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (code+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hcode Nat.succ
    have hcodeC : BProv Ax_s C (eqConstAt (code+1) 0) :=
      BProv_context_cons hcodeRen
    exact BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_code_zero
      hbetaRaw hcodeC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAtConstIdx, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta code is `0`, every term-output constant-index beta wrapper
also denotes `0`. -/
theorem BProv_Ax_s_eq_zero_of_betaTermAtConstIdx_eqConst_code_zero
    {G : List Formula} {out : Term} {code step idxValue : Nat}
    (hbeta : BProv Ax_s G (betaTermAtConstIdx out code step idxValue))
    (hcode : BProv Ax_s G (eqConstAt code 0)) :
    BProv Ax_s G (eq out Term.zero) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue)
      (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eq out Term.zero)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C
        (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (code+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hcode Nat.succ
    have hcodeC : BProv Ax_s C (eqConstAt (code+1) 0) :=
      BProv_context_cons hcodeRen
    exact BProv_Ax_s_eq_zero_of_betaTermAt_eqConst_code_zero
      hbetaRaw hcodeC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaTermAtConstIdx, body, eqConstAt, rename, Term.rename] using
        hbody)

/-- If the beta code is `0`, every successor-index beta wrapper also has
output `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAtSuccIdx_eqConst_code_zero
    {G : List Formula} {out code step idx : Nat}
    (hbeta : BProv Ax_s G (betaAtSuccIdx out code step idx))
    (hcode : BProv Ax_s G (eqConstAt code 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
      (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C (betaAt (out+1) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hcodeRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (code+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hcode Nat.succ
    have hcodeC : BProv Ax_s C (eqConstAt (code+1) 0) :=
      BProv_context_cons hcodeRen
    exact BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_code_zero
      hbetaRaw hcodeC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAtSuccIdx, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta step parameter is `0`, every constant-index beta wrapper also
has output `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAtConstIdx_eqConst_step_zero
    {G : List Formula} {out code step idxValue : Nat}
    (hbeta : BProv Ax_s G (betaAtConstIdx out code step idxValue))
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C (betaAt (out+1) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (step+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hstep Nat.succ
    have hstepC : BProv Ax_s C (eqConstAt (step+1) 0) :=
      BProv_context_cons hstepRen
    exact BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_step_zero
      hbetaRaw hstepC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAtConstIdx, body, eqConstAt, rename, Term.rename] using hbody)

/-- If the beta step parameter is `0`, every term-output constant-index beta
wrapper also denotes `0`. -/
theorem BProv_Ax_s_eq_zero_of_betaTermAtConstIdx_eqConst_step_zero
    {G : List Formula} {out : Term} {code step idxValue : Nat}
    (hbeta : BProv Ax_s G (betaTermAtConstIdx out code step idxValue))
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eq out Term.zero) := by
  let body : Formula :=
    and (eqConstAt 0 idxValue)
      (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eq out Term.zero)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C
        (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (step+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hstep Nat.succ
    have hstepC : BProv Ax_s C (eqConstAt (step+1) 0) :=
      BProv_context_cons hstepRen
    exact BProv_Ax_s_eq_zero_of_betaTermAt_eqConst_step_zero
      hbetaRaw hstepC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaTermAtConstIdx, body, eqConstAt, rename, Term.rename] using
        hbody)

/-- If the beta step parameter is `0`, every successor-index beta wrapper also
has output `0`. -/
theorem BProv_Ax_s_eqConstAt_zero_of_betaAtSuccIdx_eqConst_step_zero
    {G : List Formula} {out code step idx : Nat}
    (hbeta : BProv Ax_s G (betaAtSuccIdx out code step idx))
    (hstep : BProv Ax_s G (eqConstAt step 0)) :
    BProv Ax_s G (eqConstAt out 0) := by
  let body : Formula :=
    and
      (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
      (betaAt (out+1) (code+1) (step+1) 0)
  have hbody : BProv Ax_s (body :: G.map (rename Nat.succ))
      (rename Nat.succ (eqConstAt out 0)) := by
    let C : List Formula := body :: G.map (rename Nat.succ)
    have hbodyAss : BProv Ax_s C body :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hbetaRaw : BProv Ax_s C (betaAt (out+1) (code+1) (step+1) 0) :=
      BProv_andE2 hbodyAss
    have hstepRen : BProv Ax_s (G.map (rename Nat.succ))
        (eqConstAt (step+1) 0) := by
      simpa [eqConstAt, rename, Term.rename] using
        BProv_rename_of_sentences
          (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
          hstep Nat.succ
    have hstepC : BProv Ax_s C (eqConstAt (step+1) 0) :=
      BProv_context_cons hstepRen
    exact BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_step_zero
      hbetaRaw hstepC
  exact BProv_exE_of_sentences (B := Ax_s)
    (fun f hf => sentence_ax_s (f := f) hf) hbeta (by
      simpa [betaAtSuccIdx, body, eqConstAt, rename, Term.rename] using hbody)

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

/-- Opened beta-step zero propagation: inside the body of a
`betaDiv2StepWitnessAt`, current value `0` forces the next beta-entry witness
to be `0`. -/
theorem BProv_Ax_s_betaDiv2StepWitnessAt_body_zero_next_zero
    {G : List Formula} {code step idx : Nat}
    (hcurZero : BProv Ax_s G (eqConstAt 2 0))
    (hbody : BProv Ax_s G
      (and
        (betaAt 2 (code+3) (step+3) (idx+3))
        (and
          (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
          (div2StepAt 2 1 0)))) :
    BProv Ax_s G (eqConstAt 1 0) := by
  have htail : BProv Ax_s G
      (and
        (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
        (div2StepAt 2 1 0)) :=
    BProv_andE2 hbody
  have hstep : BProv Ax_s G (div2StepAt 2 1 0) :=
    BProv_andE2 htail
  exact BProv_Ax_s_div2StepAt_zero_half_zero
    (value := 2) (half := 1) (bit := 0) hcurZero hstep

/-- Eliminate a bounded beta-halving trace at a particular index. -/
theorem BProv_Ax_s_betaDiv2StepsThroughAt_step_of_le {G : List Formula}
    {code step last idx : Nat}
    (hsteps : BProv Ax_s G (betaDiv2StepsThroughAt code step last))
    (hle : BProv Ax_s G (leAt idx last)) :
    BProv Ax_s G (betaDiv2StepWitnessAt code step idx) := by
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := Term.var idx) hsteps
  have himp : BProv Ax_s G
      (imp (leAt idx last) (betaDiv2StepWitnessAt code step idx)) := by
    simpa [betaDiv2StepsThroughAt, leAt, betaDiv2StepWitnessAt,
      betaAtSuccIdx, betaAt, remAt, ltAt, div2StepAt, boolAt, zeroAt, oneAt,
      eqConstAt, betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename, term_subst_instTerm_rename_succ] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hle

/-- Eliminate a bounded beta-halving trace at an index known to be `0`. -/
theorem BProv_Ax_s_betaDiv2StepsThroughAt_step_of_eqConst_zero
    {G : List Formula} {code step last idx : Nat}
    (hsteps : BProv Ax_s G (betaDiv2StepsThroughAt code step last))
    (hidxZero : BProv Ax_s G (eqConstAt idx 0)) :
    BProv Ax_s G (betaDiv2StepWitnessAt code step idx) :=
  BProv_Ax_s_betaDiv2StepsThroughAt_step_of_le hsteps
    (BProv_Ax_s_leAt_of_eqConst_zero_left hidxZero)

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

/-- A final beta-bit witness with bit `1` is impossible when the beta step
parameter is `0`: in that case every beta entry is forced to be `0`, so the
opened current value contradicts the embedded binary-halving step. -/
theorem BProv_Ax_s_betaDiv2BitAt_step_zero_bot {G : List Formula}
    {bit code step idx : Nat}
    (hbitOne : BProv Ax_s G (eqConstAt bit 1))
    (hstepZero : BProv Ax_s G (eqConstAt step 0))
    (hbitAt : BProv Ax_s G (betaDiv2BitAt bit code step idx)) :
    BProv Ax_s G bot := by
  exact BProv_Ax_s_betaDiv2BitAt_current_zero_bot
    (G := G) (bit := bit) (code := code) (step := step) (idx := idx)
    hbitOne
    (by
      let body : Formula :=
        and
          (betaAt 1 (code+2) (step+2) (idx+2))
          (and
            (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
            (div2StepAt 1 0 (bit+2)))
      let C : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      have hbody : BProv Ax_s C body :=
        BProv_ass (B := Ax_s) (G := C) (by simp [C])
      have hcur : BProv Ax_s C (betaAt 1 (code+2) (step+2) (idx+2)) :=
        BProv_andE1 hbody
      have hstepRen1 : BProv Ax_s (G.map (rename Nat.succ))
          (eqConstAt (step+1) 0) := by
        simpa [eqConstAt, rename, Term.rename] using
          (BProv_rename_of_sentences
            (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
            hstepZero Nat.succ)
      have hstepRen2 : BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ))
          (eqConstAt (step+2) 0) := by
        simpa [eqConstAt, rename, Term.rename] using
          (BProv_rename_of_sentences
            (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
            hstepRen1 Nat.succ)
      have hstepC : BProv Ax_s C (eqConstAt (step+2) 0) := by
        simpa [C, List.map_map, Function.comp_def] using
          BProv_context_cons
            (BProv_context_cons (B := Ax_s) hstepRen2)
      exact BProv_Ax_s_eqConstAt_zero_of_betaAt_eqConst_step_zero
        hcur hstepC)
    hbitAt

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

/-- Projection from the opened code/step body of `hfMemAt` to its initial
beta-entry component. -/
theorem BProv_Ax_s_hfMemAt_opened_body_entry
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx (betaAtConstIdx (set+2) 1 0 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  exact BProv_andE1 hbody

/-- Projection from the opened code/step body of `hfMemAt` to its bounded
halving-trace component. -/
theorem BProv_Ax_s_hfMemAt_opened_body_steps
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  have htail : BProv Ax_s bodyCtx tail :=
    BProv_andE2 hbody
  exact BProv_andE1 htail

/-- Projection from the opened code/step body of `hfMemAt` to its final-bit
existential component. -/
theorem BProv_Ax_s_hfMemAt_opened_body_bitEx
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  have htail : BProv Ax_s bodyCtx tail :=
    BProv_andE2 hbody
  exact BProv_andE2 htail

/-- Projection from the opened code/step body of `hfMemZeroSetAt` to its
initial beta-entry component. -/
theorem BProv_Ax_s_hfMemZeroSetAt_opened_body_entry
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx (betaTermAtConstIdx Term.zero 1 0 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  exact BProv_andE1 hbody

/-- Projection from the opened code/step body of `hfMemZeroSetAt` to its
bounded halving-trace component. -/
theorem BProv_Ax_s_hfMemZeroSetAt_opened_body_steps
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  have htail : BProv Ax_s bodyCtx tail :=
    BProv_andE2 hbody
  exact BProv_andE1 htail

/-- Projection from the opened code/step body of `hfMemZeroSetAt` to its
final-bit existential component. -/
theorem BProv_Ax_s_hfMemZeroSetAt_opened_body_bitEx
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s bodyCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s bodyCtx body :=
    BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
  have htail : BProv Ax_s bodyCtx tail :=
    BProv_andE2 hbody
  exact BProv_andE2 htail

/-- In the successor branch of the opened `hfMemAt` code/step witnesses, the
initial beta-entry component of the membership body remains available. -/
theorem BProv_Ax_s_hfMemAt_succ_opened_body_entry
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx) (betaAtConstIdx (set+2) 1 0 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hentry : BProv Ax_s bodyCtx (betaAtConstIdx (set+2) 1 0 0) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemAt_opened_body_entry
        (G := G) (elem := elem) (set := set))
  exact BProv_context_cons (B := Ax_s) hentry

/-- In the successor branch of the opened `hfMemAt` code/step witnesses, the
bounded halving-trace component of the membership body remains available. -/
theorem BProv_Ax_s_hfMemAt_succ_opened_body_steps
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx) (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hsteps : BProv Ax_s bodyCtx (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemAt_opened_body_steps
        (G := G) (elem := elem) (set := set))
  exact BProv_context_cons (B := Ax_s) hsteps

/-- In the successor branch of the opened `hfMemAt` code/step witnesses, the
final-bit existential component of the membership body remains available. -/
theorem BProv_Ax_s_hfMemAt_succ_opened_body_bitEx
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx)
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbitEx : BProv Ax_s bodyCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemAt_opened_body_bitEx
        (G := G) (elem := elem) (set := set))
  exact BProv_context_cons (B := Ax_s) hbitEx

/-- Eliminate an `hfMemAt` proof to contradiction once the final opened
halving-current witness has been proved to be zero.

This theorem performs only the syntactic unpacking of the membership formula:
it opens the code/step witnesses, extracts the final `bit = 1` witness, and
delegates the trace invariant to the explicit `hcurZero` premise over the
fully opened final-bit context. -/
theorem BProv_Ax_s_hfMemAt_bot_of_opened_final_current_zero
    {G : List Formula} {elem set : Nat}
    (hcurZero :
      let bitBody : Formula :=
        and
          (oneAt 0)
          (betaDiv2BitAt 0 2 1 (elem+3))
      let tail : Formula :=
        and
          (betaDiv2StepsThroughAt 1 0 (elem+2))
          (ex bitBody)
      let body : Formula :=
        and
          (betaAtConstIdx (set+2) 1 0 0)
          tail
      let bitCtx : List Formula :=
        bitBody :: (body :: (ex body :: G.map (rename Nat.succ)).map
          (rename Nat.succ)).map (rename Nat.succ)
      let finalBody : Formula :=
        and
          (betaAt 1 (2+2) (1+2) ((elem+3)+2))
          (and
            (betaAtSuccIdx 0 (2+2) (1+2) ((elem+3)+2))
            (div2StepAt 1 0 (0+2)))
      BProv Ax_s
        (finalBody :: (ex finalBody :: bitCtx.map (rename Nat.succ)).map
          (rename Nat.succ))
        (eqConstAt 1 0))
    (hmem : BProv Ax_s G (hfMemAt elem set)) :
    BProv Ax_s G bot := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bitCtx : List Formula :=
    bitBody :: (body :: (ex body :: G.map (rename Nat.succ)).map
      (rename Nat.succ)).map (rename Nat.succ)
  let finalBody : Formula :=
    and
      (betaAt 1 (2+2) (1+2) ((elem+3)+2))
      (and
        (betaAtSuccIdx 0 (2+2) (1+2) ((elem+3)+2))
        (div2StepAt 1 0 (0+2)))
  have hcodeStep : BProv Ax_s (ex body :: G.map (rename Nat.succ)) bot := by
    have hstepEx : BProv Ax_s (ex body :: G.map (rename Nat.succ)) (ex body) :=
      BProv_ass (B := Ax_s)
        (G := ex body :: G.map (rename Nat.succ)) (by simp)
    have hopened : BProv Ax_s
        (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
        bot := by
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      have hbody : BProv Ax_s bodyCtx body :=
        BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
      have htail : BProv Ax_s bodyCtx tail :=
        BProv_andE2 hbody
      have hbitEx : BProv Ax_s bodyCtx (ex bitBody) :=
        BProv_andE2 htail
      have hbitOpened : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
          bot := by
        have hbitBody : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            bitBody :=
          BProv_ass (B := Ax_s)
            (G := bitBody :: bodyCtx.map (rename Nat.succ)) (by simp)
        have hone : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            (eqConstAt 0 1) := by
          simpa [oneAt] using BProv_andE1 hbitBody
        have hbitAt : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            (betaDiv2BitAt 0 2 1 (elem+3)) :=
          BProv_andE2 hbitBody
        exact BProv_Ax_s_betaDiv2BitAt_current_zero_bot
          (G := bitBody :: bodyCtx.map (rename Nat.succ))
          (bit := 0) (code := 2) (step := 1) (idx := elem+3)
          hone
          (by
            simpa [bitCtx, bodyCtx, finalBody, bitBody, body, tail] using
              hcurZero)
          hbitAt
      exact BProv_exE_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbitEx (by
          simpa [rename, bodyCtx, List.map_map, Function.comp_def] using
            hbitOpened)
    exact BProv_exE_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstepEx (by simpa [rename] using hopened)
  have hmem' : BProv Ax_s G (ex (ex body)) := by
    simpa [hfMemAt, body, tail, bitBody] using hmem
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hmem' (by simpa [rename] using hcodeStep)

/-- Eliminate an `hfMemAt` proof to contradiction once the opened halving-step
witness is proved to be `0`.

This is the zero-step case of the empty-set membership contradiction.  It keeps
the membership definition unchanged: callers supply the opened step fact in the
code/step context, and the theorem performs only the existential unpacking and
the final-bit refutation. -/
theorem BProv_Ax_s_hfMemAt_bot_of_opened_step_zero
    {G : List Formula} {elem set : Nat}
    (hstepZero :
      let bitBody : Formula :=
        and
          (oneAt 0)
          (betaDiv2BitAt 0 2 1 (elem+3))
      let tail : Formula :=
        and
          (betaDiv2StepsThroughAt 1 0 (elem+2))
          (ex bitBody)
      let body : Formula :=
        and
          (betaAtConstIdx (set+2) 1 0 0)
          tail
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      BProv Ax_s bodyCtx (eqConstAt 0 0))
    (hmem : BProv Ax_s G (hfMemAt elem set)) :
    BProv Ax_s G bot := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  have hcodeStep : BProv Ax_s (ex body :: G.map (rename Nat.succ)) bot := by
    have hstepEx : BProv Ax_s (ex body :: G.map (rename Nat.succ)) (ex body) :=
      BProv_ass (B := Ax_s)
        (G := ex body :: G.map (rename Nat.succ)) (by simp)
    have hopened : BProv Ax_s
        (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
        bot := by
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      have hbody : BProv Ax_s bodyCtx body :=
        BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
      have htail : BProv Ax_s bodyCtx tail :=
        BProv_andE2 hbody
      have hbitEx : BProv Ax_s bodyCtx (ex bitBody) :=
        BProv_andE2 htail
      have hbitOpened : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
          bot := by
        have hbitBody : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            bitBody :=
          BProv_ass (B := Ax_s)
            (G := bitBody :: bodyCtx.map (rename Nat.succ)) (by simp)
        have hone : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            (eqConstAt 0 1) := by
          simpa [oneAt] using BProv_andE1 hbitBody
        have hbitAt : BProv Ax_s (bitBody :: bodyCtx.map (rename Nat.succ))
            (betaDiv2BitAt 0 2 1 (elem+3)) :=
          BProv_andE2 hbitBody
        have hstepBodyCtx : BProv Ax_s bodyCtx (eqConstAt 0 0) := by
          simpa [bitBody, tail, body, bodyCtx] using hstepZero
        have hstepRenRaw : BProv Ax_s (bodyCtx.map (rename Nat.succ))
            (rename Nat.succ (eqConstAt 0 0)) :=
          BProv_rename_of_sentences
            (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
            hstepBodyCtx Nat.succ
        have hstepRen : BProv Ax_s (bodyCtx.map (rename Nat.succ))
            (eqConstAt 1 0) := by
          simpa [eqConstAt, rename, Term.rename] using hstepRenRaw
        have hstepBitCtx : BProv Ax_s
            (bitBody :: bodyCtx.map (rename Nat.succ)) (eqConstAt 1 0) :=
          BProv_context_cons (B := Ax_s) hstepRen
        exact BProv_Ax_s_betaDiv2BitAt_step_zero_bot
          (G := bitBody :: bodyCtx.map (rename Nat.succ))
          (bit := 0) (code := 2) (step := 1) (idx := elem+3)
          hone hstepBitCtx hbitAt
      exact BProv_exE_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hbitEx (by
          simpa [rename, bodyCtx, List.map_map, Function.comp_def] using
            hbitOpened)
    exact BProv_exE_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstepEx (by simpa [rename] using hopened)
  have hmem' : BProv Ax_s G (ex (ex body)) := by
    simpa [hfMemAt, body, tail, bitBody] using hmem
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hmem' (by simpa [rename] using hcodeStep)

/-- In the opened code/step body of `hfMemAt`, the zero branch of the step
case split is already contradictory.

The proof is the local version of
`BProv_Ax_s_hfMemAt_bot_of_opened_step_zero`: it starts with `zeroAt 0` added
to the opened body context, opens only the final-bit existential, and refutes
the final bit by renaming the step-zero assumption through that binder. -/
theorem BProv_Ax_s_hfMemAt_opened_body_step_zero_bot
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (zeroAt 0 :: bodyCtx) bot := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let zeroCtx : List Formula := zeroAt 0 :: bodyCtx
  have hzero : BProv Ax_s zeroCtx (eqConstAt 0 0) := by
    have hz : BProv Ax_s zeroCtx (zeroAt 0) :=
      BProv_ass (B := Ax_s) (G := zeroCtx) (by simp [zeroCtx])
    simpa [zeroAt] using hz
  have hbody : BProv Ax_s zeroCtx body := by
    have hbodyBase : BProv Ax_s bodyCtx body :=
      BProv_ass (B := Ax_s) (G := bodyCtx) (by simp [bodyCtx])
    exact BProv_context_cons (B := Ax_s) hbodyBase
  have htail : BProv Ax_s zeroCtx tail :=
    BProv_andE2 hbody
  have hbitEx : BProv Ax_s zeroCtx (ex bitBody) :=
    BProv_andE2 htail
  have hbitOpened : BProv Ax_s (bitBody :: zeroCtx.map (rename Nat.succ))
      bot := by
    have hbitBody : BProv Ax_s (bitBody :: zeroCtx.map (rename Nat.succ))
        bitBody :=
      BProv_ass (B := Ax_s)
        (G := bitBody :: zeroCtx.map (rename Nat.succ)) (by simp)
    have hone : BProv Ax_s (bitBody :: zeroCtx.map (rename Nat.succ))
        (eqConstAt 0 1) := by
      simpa [oneAt] using BProv_andE1 hbitBody
    have hbitAt : BProv Ax_s (bitBody :: zeroCtx.map (rename Nat.succ))
        (betaDiv2BitAt 0 2 1 (elem+3)) :=
      BProv_andE2 hbitBody
    have hstepRenRaw : BProv Ax_s (zeroCtx.map (rename Nat.succ))
        (rename Nat.succ (eqConstAt 0 0)) :=
      BProv_rename_of_sentences
        (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
        hzero Nat.succ
    have hstepRen : BProv Ax_s (zeroCtx.map (rename Nat.succ))
        (eqConstAt 1 0) := by
      simpa [eqConstAt, rename, Term.rename] using hstepRenRaw
    have hstepBitCtx : BProv Ax_s
        (bitBody :: zeroCtx.map (rename Nat.succ)) (eqConstAt 1 0) :=
      BProv_context_cons (B := Ax_s) hstepRen
    exact BProv_Ax_s_betaDiv2BitAt_step_zero_bot
      (G := bitBody :: zeroCtx.map (rename Nat.succ))
      (bit := 0) (code := 2) (step := 1) (idx := elem+3)
      hone hstepBitCtx hbitAt
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hbitEx (by
      simpa [rename, zeroCtx, bodyCtx, body, tail, bitBody, List.map_map,
        Function.comp_def] using hbitOpened)

/-- Reduce an `hfMemAt` contradiction to the successor branch of the opened
halving-step witness.

The theorem performs the zero/successor split for the opened `step` variable.
The zero branch is discharged by
`BProv_Ax_s_hfMemAt_opened_body_step_zero_bot`; callers only need to supply the
successor branch, where the real trace-functionality work remains. -/
theorem BProv_Ax_s_hfMemAt_bot_of_opened_step_successor
    {G : List Formula} {elem set : Nat}
    (hsucc :
      let bitBody : Formula :=
        and
          (oneAt 0)
          (betaDiv2BitAt 0 2 1 (elem+3))
      let tail : Formula :=
        and
          (betaDiv2StepsThroughAt 1 0 (elem+2))
          (ex bitBody)
      let body : Formula :=
        and
          (betaAtConstIdx (set+2) 1 0 0)
          tail
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      BProv Ax_s (succPredAt 0 :: bodyCtx) bot)
    (hmem : BProv Ax_s G (hfMemAt elem set)) :
    BProv Ax_s G bot := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  have hcodeStep : BProv Ax_s (ex body :: G.map (rename Nat.succ)) bot := by
    have hstepEx : BProv Ax_s (ex body :: G.map (rename Nat.succ)) (ex body) :=
      BProv_ass (B := Ax_s)
        (G := ex body :: G.map (rename Nat.succ)) (by simp)
    have hopened : BProv Ax_s
        (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
        bot := by
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      have hcases : BProv Ax_s bodyCtx (zeroOrSuccPredAt 0) :=
        BProv_Ax_s_zeroOrSuccPredAt (G := bodyCtx) 0
      have hzeroBranch : BProv Ax_s (zeroAt 0 :: bodyCtx) bot := by
        simpa [bitBody, tail, body, bodyCtx] using
          (BProv_Ax_s_hfMemAt_opened_body_step_zero_bot
            (G := G) (elem := elem) (set := set))
      have hsuccBranch : BProv Ax_s (succPredAt 0 :: bodyCtx) bot := by
        simpa [bitBody, tail, body, bodyCtx] using hsucc
      exact BProv_orE (B := Ax_s) (G := bodyCtx)
        (a := zeroAt 0) (b := succPredAt 0) (c := bot)
        (by simpa [zeroOrSuccPredAt] using hcases)
        hzeroBranch hsuccBranch
    exact BProv_exE_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstepEx (by simpa [rename] using hopened)
  have hmem' : BProv Ax_s G (ex (ex body)) := by
    simpa [hfMemAt, body, tail, bitBody] using hmem
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hmem' (by simpa [rename] using hcodeStep)

/-- Open the successor branch of the `hfMemAt` code/step witness.

This is a pure proof-plumbing lemma: it turns the abstract `succPredAt 0`
assumption into the explicit predecessor equation `step = succ pred` under one
more existential binder. -/
theorem BProv_Ax_s_hfMemAt_succ_opened_pred_bot
    {G : List Formula} {elem set : Nat}
    (hpred :
      let bitBody : Formula :=
        and
          (oneAt 0)
          (betaDiv2BitAt 0 2 1 (elem+3))
      let tail : Formula :=
        and
          (betaDiv2StepsThroughAt 1 0 (elem+2))
          (ex bitBody)
      let body : Formula :=
        and
          (betaAtConstIdx (set+2) 1 0 0)
          tail
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      let succCtx : List Formula := succPredAt 0 :: bodyCtx
      let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
      BProv Ax_s (succBody :: succCtx.map (rename Nat.succ)) bot) :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx) bot := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hsucc : BProv Ax_s succCtx (succPredAt 0) :=
    BProv_ass (B := Ax_s) (G := succCtx) (by simp [succCtx])
  have hbody : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ)) bot := by
    simpa [bitBody, tail, body, bodyCtx, succCtx, succBody] using hpred
  exact BProv_exE_of_sentences
    (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
    hsucc (by
      simpa [succCtx, bodyCtx, body, tail, bitBody, succPredAt, succBody,
        rename] using hbody)

/-- In the predecessor-opened successor branch of `hfMemAt`, the explicit
successor equation is available as the head assumption. -/
theorem BProv_Ax_s_hfMemAt_pred_opened_step_succ
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (eq (Term.var 1) (Term.succ (Term.var 0))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  exact BProv_ass (B := Ax_s)
    (G := succBody :: succCtx.map (rename Nat.succ))
    (by simp [succBody])

/-- In the predecessor-opened successor branch of `hfMemAt`, the initial
beta-entry component is still available, with all free slots shifted through
the predecessor binder. -/
theorem BProv_Ax_s_hfMemAt_pred_opened_body_entry
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (betaAtConstIdx (set+3) 2 1 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hentrySucc : BProv Ax_s succCtx
      (betaAtConstIdx (set+2) 1 0 0) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemAt_succ_opened_body_entry
        (G := G) (elem := elem) (set := set))
  have hentryRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaAtConstIdx (set+2) 1 0 0)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hentrySucc Nat.succ
  have hentryCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaAtConstIdx (set+2) 1 0 0)) :=
    BProv_context_cons (B := Ax_s) hentryRen
  simpa [betaAtConstIdx, betaAt, remAt, ltAt, eqConstAt, betaModTerm,
    rename, Term.rename, SetTheory.up, succBody, succCtx, bodyCtx, body,
    tail, bitBody] using hentryCtx

/-- In the predecessor-opened successor branch of `hfMemAt`, the bounded
halving trace component is still available, shifted through the predecessor
binder. -/
theorem BProv_Ax_s_hfMemAt_pred_opened_body_steps
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (betaDiv2StepsThroughAt 2 1 (elem+3)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hstepsSucc : BProv Ax_s succCtx
      (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemAt_succ_opened_body_steps
        (G := G) (elem := elem) (set := set))
  have hstepsRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughAt 1 0 (elem+2))) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstepsSucc Nat.succ
  have hstepsCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughAt 1 0 (elem+2))) :=
    BProv_context_cons (B := Ax_s) hstepsRen
  simpa [betaDiv2StepsThroughAt, leAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaAt, remAt, ltAt, div2StepAt, boolAt, zeroAt,
    oneAt, eqConstAt, betaModTerm, rename, Term.rename, SetTheory.up,
    succBody, succCtx, bodyCtx, body, tail, bitBody] using hstepsCtx

/-- In the predecessor-opened successor branch of `hfMemAt`, the final-bit
existential component is still available, shifted through the predecessor
binder. -/
theorem BProv_Ax_s_hfMemAt_pred_opened_body_bitEx
    {G : List Formula} {elem set : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaAtConstIdx (set+2) 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (ex (and (oneAt 0) (betaDiv2BitAt 0 3 2 (elem+4)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaAtConstIdx (set+2) 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hbitSucc : BProv Ax_s succCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemAt_succ_opened_body_bitEx
        (G := G) (elem := elem) (set := set))
  have hbitRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ
        (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3))))) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hbitSucc Nat.succ
  have hbitCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ
        (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3))))) :=
    BProv_context_cons (B := Ax_s) hbitRen
  simpa [betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, subst,
    instTerm, Term.subst, Term.upSubst, rename, Term.rename, SetTheory.up,
    succBody, succCtx, bodyCtx, body, tail, bitBody] using hbitCtx

/-- In the successor branch of the opened `hfMemZeroSetAt` code/step
witnesses, the initial term-output beta-entry component remains available. -/
theorem BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_entry
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx)
      (betaTermAtConstIdx Term.zero 1 0 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hentry : BProv Ax_s bodyCtx
      (betaTermAtConstIdx Term.zero 1 0 0) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_opened_body_entry
        (G := G) (elem := elem))
  exact BProv_context_cons (B := Ax_s) hentry

/-- In the successor branch of the opened `hfMemZeroSetAt` code/step
witnesses, the bounded halving-trace component remains available. -/
theorem BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_steps
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx)
      (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hsteps : BProv Ax_s bodyCtx
      (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_opened_body_steps
        (G := G) (elem := elem))
  exact BProv_context_cons (B := Ax_s) hsteps

/-- In the successor branch of the opened `hfMemZeroSetAt` code/step
witnesses, the final-bit existential component remains available. -/
theorem BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_bitEx
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    BProv Ax_s (succPredAt 0 :: bodyCtx)
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbitEx : BProv Ax_s bodyCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
    simpa [bitBody, tail, body, bodyCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_opened_body_bitEx
        (G := G) (elem := elem))
  exact BProv_context_cons (B := Ax_s) hbitEx

/-- In the predecessor-opened successor branch of `hfMemZeroSetAt`, the
explicit successor equation is available as the head assumption. -/
theorem BProv_Ax_s_hfMemZeroSetAt_pred_opened_step_succ
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (eq (Term.var 1) (Term.succ (Term.var 0))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  exact BProv_ass (B := Ax_s)
    (G := succBody :: succCtx.map (rename Nat.succ))
    (by simp [succBody])

/-- In the predecessor-opened successor branch of `hfMemZeroSetAt`, the
initial term-output beta-entry component is still available, shifted through
the predecessor binder. -/
theorem BProv_Ax_s_hfMemZeroSetAt_pred_opened_body_entry
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (betaTermAtConstIdx Term.zero 2 1 0) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hentrySucc : BProv Ax_s succCtx
      (betaTermAtConstIdx Term.zero 1 0 0) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_entry
        (G := G) (elem := elem))
  have hentryRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaTermAtConstIdx Term.zero 1 0 0)) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hentrySucc Nat.succ
  have hentryCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaTermAtConstIdx Term.zero 1 0 0)) :=
    BProv_context_cons (B := Ax_s) hentryRen
  simpa [betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaAtConstIdx, betaAt, remAt, ltAt, eqConstAt, betaModTerm,
    rename, Term.rename, SetTheory.up, succBody, succCtx, bodyCtx, body,
    tail, bitBody] using hentryCtx

/-- In the predecessor-opened successor branch of `hfMemZeroSetAt`, the
bounded halving trace component is still available, shifted through the
predecessor binder. -/
theorem BProv_Ax_s_hfMemZeroSetAt_pred_opened_body_steps
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (betaDiv2StepsThroughAt 2 1 (elem+3)) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hstepsSucc : BProv Ax_s succCtx
      (betaDiv2StepsThroughAt 1 0 (elem+2)) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_steps
        (G := G) (elem := elem))
  have hstepsRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughAt 1 0 (elem+2))) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hstepsSucc Nat.succ
  have hstepsCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ (betaDiv2StepsThroughAt 1 0 (elem+2))) :=
    BProv_context_cons (B := Ax_s) hstepsRen
  simpa [betaDiv2StepsThroughAt, leAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaAt, remAt, ltAt, div2StepAt, boolAt, zeroAt,
    oneAt, eqConstAt, betaModTerm, rename, Term.rename, SetTheory.up,
    succBody, succCtx, bodyCtx, body, tail, bitBody] using hstepsCtx

/-- In the predecessor-opened successor branch of `hfMemZeroSetAt`, the
final-bit existential component is still available, shifted through the
predecessor binder. -/
theorem BProv_Ax_s_hfMemZeroSetAt_pred_opened_body_bitEx
    {G : List Formula} {elem : Nat} :
    let bitBody : Formula :=
      and
        (oneAt 0)
        (betaDiv2BitAt 0 2 1 (elem+3))
    let tail : Formula :=
      and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex bitBody)
    let body : Formula :=
      and
        (betaTermAtConstIdx Term.zero 1 0 0)
        tail
    let bodyCtx : List Formula :=
      body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
    let succCtx : List Formula := succPredAt 0 :: bodyCtx
    let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
    BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (ex (and (oneAt 0) (betaDiv2BitAt 0 3 2 (elem+4)))) := by
  let bitBody : Formula :=
    and
      (oneAt 0)
      (betaDiv2BitAt 0 2 1 (elem+3))
  let tail : Formula :=
    and
      (betaDiv2StepsThroughAt 1 0 (elem+2))
      (ex bitBody)
  let body : Formula :=
    and
      (betaTermAtConstIdx Term.zero 1 0 0)
      tail
  let bodyCtx : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let succCtx : List Formula := succPredAt 0 :: bodyCtx
  let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
  have hbitSucc : BProv Ax_s succCtx
      (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3)))) := by
    simpa [bitBody, tail, body, bodyCtx, succCtx] using
      (BProv_Ax_s_hfMemZeroSetAt_succ_opened_body_bitEx
        (G := G) (elem := elem))
  have hbitRen : BProv Ax_s (succCtx.map (rename Nat.succ))
      (rename Nat.succ
        (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3))))) :=
    BProv_rename_of_sentences
      (B := Ax_s) (fun f hf => sentence_ax_s (f := f) hf)
      hbitSucc Nat.succ
  have hbitCtx : BProv Ax_s (succBody :: succCtx.map (rename Nat.succ))
      (rename Nat.succ
        (ex (and (oneAt 0) (betaDiv2BitAt 0 2 1 (elem+3))))) :=
    BProv_context_cons (B := Ax_s) hbitRen
  simpa [betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, subst,
    instTerm, Term.subst, Term.upSubst, rename, Term.rename, SetTheory.up,
    succBody, succCtx, bodyCtx, body, tail, bitBody] using hbitCtx

/-- Reduce an `hfMemAt` contradiction to the predecessor-opened successor
branch of the code/step witness. -/
theorem BProv_Ax_s_hfMemAt_bot_of_opened_step_pred
    {G : List Formula} {elem set : Nat}
    (hpred :
      let bitBody : Formula :=
        and
          (oneAt 0)
          (betaDiv2BitAt 0 2 1 (elem+3))
      let tail : Formula :=
        and
          (betaDiv2StepsThroughAt 1 0 (elem+2))
          (ex bitBody)
      let body : Formula :=
        and
          (betaAtConstIdx (set+2) 1 0 0)
          tail
      let bodyCtx : List Formula :=
        body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
      let succCtx : List Formula := succPredAt 0 :: bodyCtx
      let succBody : Formula := eq (Term.var 1) (Term.succ (Term.var 0))
      BProv Ax_s (succBody :: succCtx.map (rename Nat.succ)) bot)
    (hmem : BProv Ax_s G (hfMemAt elem set)) :
    BProv Ax_s G bot := by
  exact BProv_Ax_s_hfMemAt_bot_of_opened_step_successor
    (G := G) (elem := elem) (set := set)
    (by
      simpa using
        (BProv_Ax_s_hfMemAt_succ_opened_pred_bot
          (G := G) (elem := elem) (set := set) hpred))
    hmem

/-- Inner shell for the translated HF empty-set axiom.

After the empty witness is instantiated with the closed PA numeral `0`, the
only remaining task is to refute the corresponding closed-set membership
assumption for an arbitrary element. -/
theorem BProv_Ax_s_HF_empty_zero_body_of_member_bot
    (hmem : BProv Ax_s
      [subst (Term.upSubst (instTerm Term.zero)) (hfMemAt 0 1)]
      bot) :
    BProv Ax_s []
      (subst (instTerm Term.zero)
        (all (imp (hfMemAt 0 1) bot))) := by
  let memZero : Formula := subst (Term.upSubst (instTerm Term.zero)) (hfMemAt 0 1)
  have himp : BProv Ax_s [] (imp memZero bot) :=
    BProv_impI (by simpa [memZero] using hmem)
  have hall : BProv Ax_s [] (all (imp memZero bot)) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) himp
  simpa [memZero, subst, instTerm, Term.subst, Term.upSubst] using hall

/-- Outer shell for the translated HF empty-set axiom.

The remaining arithmetic obligation is exactly the body obtained by using the
closed PA numeral `0` as the empty-set witness.  Keeping that obligation as a
premise avoids hiding the membership-refutation work in the theorem statement. -/
theorem BProv_Ax_s_translated_HF_empty_of_zero_body
    (hbody : BProv Ax_s []
      (subst (instTerm Term.zero)
        (all (imp (hfMemAt 0 1) bot)))) :
    BProv Ax_s []
      (translateHFFormula (SetTheory.sealF AckermannHF.HF_empty_form)) := by
  let body : Formula := all (imp (hfMemAt 0 1) bot)
  have hex : BProv Ax_s [] (ex body) := by
    simpa [body] using
      (BProv_exI (B := Ax_s) (G := []) (a := body) (t := Term.zero) hbody)
  have h1 : BProv Ax_s [] (all (ex body)) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) hex
  have h2 : BProv Ax_s [] (all (all (ex body))) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) h1
  have h3 : BProv Ax_s [] (all (all (all (ex body)))) :=
    BProv_allI_of_sentences (B := Ax_s)
      (fun f hf => sentence_ax_s (f := f) hf) h2
  simpa [body, translateHFFormula, hfFormulaAt, AckermannHF.HF_empty_form,
    SetTheory.sealF, SetTheory.closeN, SetTheory.bound, hfUpVarMap] using h3

/-- Combined shell for the translated HF empty-set axiom: it remains only to
refute the membership formula for an arbitrary element and the closed zero set
code. -/
theorem BProv_Ax_s_translated_HF_empty_of_zero_member_bot
    (hmem : BProv Ax_s
      [subst (Term.upSubst (instTerm Term.zero)) (hfMemAt 0 1)]
      bot) :
    BProv Ax_s []
      (translateHFFormula (SetTheory.sealF AckermannHF.HF_empty_form)) :=
  BProv_Ax_s_translated_HF_empty_of_zero_body
    (BProv_Ax_s_HF_empty_zero_body_of_member_bot hmem)

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

end SetTheory
