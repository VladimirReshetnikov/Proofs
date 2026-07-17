import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Dioph

/-!
# Binary arithmetic is Diophantine

This file ports the arithmetic layer of the vendored Rocq module
`Undecidability.H10.Dio.dio_binary`.  It supplies the three ingredients used
by the finite cipher construction:

* the graph of `Nat.choose` is Diophantine;
* binary digit inclusion is a Diophantine relation; and
* Mathlib's bitwise conjunction `Nat.land` is a Diophantine function.

The binomial proof follows Rocq's `is_binomial_eq`.  Put
`q = 2^(n+1)`.  Newton's formula says

```
  (1 + q)^n = ∑ k ≤ n, Nat.choose n k * q^k,
```

and every coefficient is strictly below `q`.  Thus `Nat.choose n k` is the
`k`-th base-`q` digit of `(1+q)^n`.  The expression for a digit uses only
exponentiation, division, and remainder, all already closed under
`Dioph.DiophFn` in Mathlib.

The binary-inclusion proof is Lucas's theorem at the prime two.  Finally we
port Rocq's `nat_meet_dio` certificate.  Its residual witnesses make three
additions carry-free, so the certificate uses only addition and the already
Diophantine digit-inclusion relation.
-/

namespace PAListCoding
namespace BinaryDioph

open Fin2
open scoped BigOperators Dioph

/-! ## Binomial coefficients as digits -/

/-- The coefficients of `(1+X)^n`, in little-endian order.  Keeping the final
coefficient `choose n n = 1` makes the list a canonical base expansion: its
last digit is nonzero. -/
def chooseDigits (n : Nat) : List Nat :=
  List.ofFn fun i : Fin (n + 1) => n.choose i

/-- Newton's formula, phrased as reconstruction of `chooseDigits`. -/
theorem ofDigits_chooseDigits (n q : Nat) :
    Nat.ofDigits q (chooseDigits n) = (1 + q) ^ n := by
  rw [show 1 + q = q + 1 by omega, Nat.ofDigits_eq_sum_mapIdx, add_pow]
  simp only [chooseDigits, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn, one_pow, mul_one]
  calc
    (∑ i : Fin (n + 1), n.choose i * q ^ (i : Nat)) =
        ∑ i ∈ Finset.range (n + 1), n.choose i * q ^ i :=
      (Finset.sum_range (n := n + 1) (fun i => n.choose i * q ^ i)).symm
    _ = ∑ i ∈ Finset.range (n + 1), q ^ i * n.choose i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Nat.mul_comm _ _

theorem chooseDigits_getD_of_lt (n i : Nat) (hi : i < n + 1) :
    (chooseDigits n).getD i 0 = n.choose i := by
  have hil : i < (chooseDigits n).length := by
    simpa [chooseDigits] using hi
  rw [List.getD_eq_getElem (chooseDigits n) 0 hil]
  change (List.ofFn fun j : Fin (n + 1) => n.choose j)[i] = n.choose i
  rw [List.getElem_ofFn]

/-- The radix used in the Rocq binomial encoding. -/
def chooseRadix (n : Nat) : Nat :=
  2 ^ (n + 1)

theorem chooseRadix_gt_one (n : Nat) : 1 < chooseRadix n := by
  exact Nat.one_lt_two_pow (by omega)

/-- Every binomial coefficient is a valid digit in `chooseRadix n`. -/
theorem chooseDigits_lt_radix (n : Nat) :
    ∀ d ∈ chooseDigits n, d < chooseRadix n := by
  intro d hd
  rcases List.mem_ofFn.mp hd with ⟨i, rfl⟩
  exact lt_of_le_of_lt (Nat.choose_le_two_pow n i)
    (Nat.pow_lt_pow_right (by omega) (by omega))

theorem chooseDigits_last_ne_zero (n : Nat) :
    ∀ h : chooseDigits n ≠ [], (chooseDigits n).getLast h ≠ 0 := by
  intro h
  have hlast := List.getLast_ofFn_succ
    (fun i : Fin (n + 1) => n.choose i)
  have heq : (chooseDigits n).getLast h = 1 := by
    simpa [chooseDigits] using hlast
  rw [heq]
  exact Nat.one_ne_zero

/-- The base-`chooseRadix n` digits of `(1+chooseRadix n)^n` are exactly the
binomial coefficients in row `n` of Pascal's triangle. -/
theorem digits_choose (n : Nat) :
    Nat.digits (chooseRadix n) ((1 + chooseRadix n) ^ n) = chooseDigits n := by
  rw [← ofDigits_chooseDigits n (chooseRadix n)]
  exact Nat.digits_ofDigits (chooseRadix n) (chooseRadix_gt_one n)
    (chooseDigits n) (chooseDigits_lt_radix n) (chooseDigits_last_ne_zero n)

/-- Total lookup also covers `k > n`, where both sides are zero. -/
theorem chooseDigits_getD (n k : Nat) :
    (chooseDigits n).getD k 0 = n.choose k := by
  by_cases hk : k < n + 1
  · exact chooseDigits_getD_of_lt n k hk
  · rw [List.getD_eq_default]
    · exact (Nat.choose_eq_zero_of_lt (by omega)).symm
    · simpa [chooseDigits] using Nat.le_of_not_gt hk

/-- The executable base-`q` digit characterization corresponding to Rocq's
`is_binomial_eq`. -/
theorem choose_digit_characterization (n k : Nat) :
    n.choose k =
      ((1 + chooseRadix n) ^ n / chooseRadix n ^ k) % chooseRadix n := by
  have hq : 2 ≤ chooseRadix n := chooseRadix_gt_one n
  rw [← Nat.getD_digits ((1 + chooseRadix n) ^ n) k hq]
  rw [digits_choose, chooseDigits_getD]

/-- Substitution closure for the binomial-coefficient function.  This is the
Lean counterpart of Rocq's `dio_fun_binomial`. -/
theorem choose_diophFn {alpha : Type} {n k : (alpha → Nat) → Nat}
    (dn : Dioph.DiophFn n) (dk : Dioph.DiophFn k) :
    Dioph.DiophFn (fun v => Nat.choose (n v) (k v)) := by
  have done : Dioph.DiophFn (fun _ : alpha → Nat => 1) :=
    Dioph.const_dioph 1
  have dtwo : Dioph.DiophFn (fun _ : alpha → Nat => 2) :=
    Dioph.const_dioph 2
  have dn1 : Dioph.DiophFn (fun v => n v + 1) :=
    Dioph.add_dioph dn done
  have dq : Dioph.DiophFn (fun v => chooseRadix (n v)) := by
    simpa [chooseRadix] using Dioph.pow_dioph dtwo dn1
  have dbase : Dioph.DiophFn (fun v => 1 + chooseRadix (n v)) :=
    Dioph.add_dioph done dq
  have dc : Dioph.DiophFn (fun v => (1 + chooseRadix (n v)) ^ n v) :=
    Dioph.pow_dioph dbase dn
  have dplace : Dioph.DiophFn (fun v => chooseRadix (n v) ^ k v) :=
    Dioph.pow_dioph dq dk
  have dquot : Dioph.DiophFn
      (fun v => (1 + chooseRadix (n v)) ^ n v / chooseRadix (n v) ^ k v) :=
    Dioph.div_dioph dc dplace
  have ddigit : Dioph.DiophFn
      (fun v => ((1 + chooseRadix (n v)) ^ n v /
        chooseRadix (n v) ^ k v) % chooseRadix (n v)) :=
    Dioph.mod_dioph dquot dq
  convert ddigit using 1
  funext v
  exact choose_digit_characterization (n v) (k v)

/-! ## Binary digit inclusion and Lucas's theorem -/

/-- `BinaryLE n m` means that every active bit of `n` is active in `m`.
This is Rocq's `binary_le`, stated through Mathlib's `Nat.testBit`. -/
def BinaryLE (n m : Nat) : Prop :=
  ∀ i, n.testBit i = true → m.testBit i = true

/-- Split binary inclusion into its least-significant bit and shifted tail. -/
theorem binaryLE_iff_mod_div (n m : Nat) :
    BinaryLE n m ↔
      (n % 2 = 1 → m % 2 = 1) ∧ BinaryLE (n / 2) (m / 2) := by
  constructor
  · intro h
    constructor
    · intro hn
      have hz := h 0
      simp only [Nat.testBit_zero, decide_eq_true_eq] at hz
      exact hz hn
    · intro i hi
      have hs := h (i + 1) (by
        simpa only [Nat.testBit_add_one] using hi)
      simpa only [Nat.testBit_add_one] using hs
  · rintro ⟨hzero, htail⟩ i hi
    cases i with
    | zero =>
        simp only [Nat.testBit_zero, decide_eq_true_eq] at hi ⊢
        exact hzero hi
    | succ i =>
        simp only [Nat.testBit_succ] at hi ⊢
        exact htail i hi

theorem mul_mod_two_eq_one_iff (a b : Nat) :
    (a * b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [Nat.mul_mod, ha, hb]

/-- The one-digit factor in Lucas's theorem is one precisely when the lower
bit of `n` is allowed by the lower bit of `m`. -/
theorem choose_bit_mod_two_eq_one_iff (n m : Nat) :
    ((m % 2).choose (n % 2)) % 2 = 1 ↔
      (n % 2 = 1 → m % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    simp [hn, hm]

/-- One recursive step of Lucas's theorem at the prime two. -/
theorem choose_mod_two_rec (n m : Nat) :
    m.choose n % 2 = 1 ↔
      (n % 2 = 1 → m % 2 = 1) ∧ (m / 2).choose (n / 2) % 2 = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlucas :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := m) (k := n) (p := 2)
  change m.choose n % 2 =
    ((m % 2).choose (n % 2) * (m / 2).choose (n / 2)) % 2 at hlucas
  rw [hlucas, mul_mod_two_eq_one_iff, choose_bit_mod_two_eq_one_iff]

theorem binaryLE_zero_iff (n : Nat) : BinaryLE n 0 ↔ n = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    cases hn : n.testBit i with
    | false => rfl
    | true =>
        have hz := h i hn
        simpa only [Nat.zero_testBit] using hz.symm
  · rintro rfl
    simp [BinaryLE]

/-- Lucas's theorem at `p=2`: digitwise binary inclusion is exactly oddness
of the corresponding binomial coefficient.  This is Rocq's
`binary_le_binomial`. -/
theorem binaryLE_iff_choose_mod_two_eq_one (n m : Nat) :
    BinaryLE n m ↔ m.choose n % 2 = 1 := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        rw [binaryLE_zero_iff]
        cases n <;> simp
      · rw [binaryLE_iff_mod_div, choose_mod_two_rec]
        rw [ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega))]

/-- The binary-digit subset relation is Diophantine after substituting any
two Diophantine functions. -/
theorem binaryLE_dioph {alpha : Type} {x y : (alpha → Nat) → Nat}
    (dx : Dioph.DiophFn x) (dy : Dioph.DiophFn y) :
    Dioph {v : alpha → Nat | BinaryLE (x v) (y v)} := by
  have dchoose : Dioph.DiophFn (fun v => (y v).choose (x v)) :=
    choose_diophFn dy dx
  have dtwo : Dioph.DiophFn (fun _ : alpha → Nat => 2) :=
    Dioph.const_dioph 2
  have done : Dioph.DiophFn (fun _ : alpha → Nat => 1) :=
    Dioph.const_dioph 1
  have dparity : Dioph.DiophFn (fun v => (y v).choose (x v) % 2) :=
    Dioph.mod_dioph dchoose dtwo
  apply Dioph.ext (Dioph.eq_dioph dparity done)
  intro v
  exact (binaryLE_iff_choose_mod_two_eq_one (x v) (y v)).symm

/-! ## The carry-free arithmetic certificate for bitwise AND -/

/-- Adding `x` and `y` preserves all bits of `x` exactly when their supports
are disjoint.  This is the key carry invariant hidden in Rocq's list-of-bits
proof of `nat_meet_dio`. -/
theorem binaryLE_add_iff_land_eq_zero (x y : Nat) :
    BinaryLE x (x + y) ↔ x &&& y = 0 := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp [BinaryLE]
  | bit xb x ih =>
      induction y using Nat.binaryRec with
      | zero => simp [BinaryLE]
      | bit yb y _iy =>
          cases xb <;> cases yb
          all_goals rw [binaryLE_iff_mod_div, Nat.land_bit]
          all_goals simp [Nat.bit, ih, Nat.add_div] <;> omega

/-- Disjoint binary supports add without carries, so arithmetic addition and
bitwise union agree. -/
theorem add_eq_lor_of_land_eq_zero {x y : Nat} (h : x &&& y = 0) :
    x + y = x ||| y := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp
  | bit xb x ih =>
      induction y using Nat.binaryRec with
      | zero => simp
      | bit yb y _iy =>
          rw [Nat.land_bit] at h
          rw [Nat.lor_bit]
          cases xb <;> cases yb <;> simp [Nat.bit] at h ⊢
          all_goals
            have htail := ih h
            omega

theorem land_ldiff_eq_zero (a b : Nat) :
    (a &&& b) &&& Nat.ldiff a b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_ldiff, Nat.zero_testBit]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem lor_land_ldiff (a b : Nat) :
    (a &&& b) ||| Nat.ldiff a b = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, Nat.testBit_land, Nat.testBit_ldiff]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem ldiff_cross_land_eq_zero (a b : Nat) :
    Nat.ldiff a b &&& Nat.ldiff b a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_ldiff, Nat.zero_testBit]
  cases a.testBit i <;> cases b.testBit i <;> rfl

private theorem bool_and_or_pairwise (r x y : Bool)
    (hrx : (r && x) = false) (hry : (r && y) = false)
    (hxy : (x && y) = false) :
    ((r || x) && (r || y)) = r := by
  cases r <;> cases x <;> cases y <;> simp_all

theorem land_lor_pairwise_eq_left {r x y : Nat}
    (hrx : r &&& x = 0) (hry : r &&& y = 0)
    (hxy : x &&& y = 0) :
    (r ||| x) &&& (r ||| y) = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hrxi : (r.testBit i && x.testBit i) = false := by
    simpa only [Nat.testBit_land, Nat.zero_testBit] using
      congrArg (fun z : Nat => z.testBit i) hrx
  have hryi : (r.testBit i && y.testBit i) = false := by
    simpa only [Nat.testBit_land, Nat.zero_testBit] using
      congrArg (fun z : Nat => z.testBit i) hry
  have hxyi : (x.testBit i && y.testBit i) = false := by
    simpa only [Nat.testBit_land, Nat.zero_testBit] using
      congrArg (fun z : Nat => z.testBit i) hxy
  simp only [Nat.testBit_land, Nat.testBit_lor]
  exact bool_and_or_pairwise _ _ _ hrxi hryi hxyi

/-- Arithmetic certificate for bitwise AND, matching Rocq's `nat_meet_dio`.
The first two clauses split the inputs into their common part and residuals;
the three `BinaryLE` clauses state exactly that all three additions are
carry-free. -/
theorem land_certificate (r a b : Nat) :
    r = a &&& b ↔ ∃ x y,
      a = r + x ∧ b = r + y ∧
      BinaryLE r (r + x) ∧ BinaryLE r (r + y) ∧ BinaryLE x (x + y) := by
  constructor
  · intro hr
    let x := Nat.ldiff a b
    let y := Nat.ldiff b a
    refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
    · subst r
      rw [add_eq_lor_of_land_eq_zero (land_ldiff_eq_zero a b)]
      exact (lor_land_ldiff a b).symm
    · subst r
      rw [Nat.land_comm a b]
      rw [add_eq_lor_of_land_eq_zero (land_ldiff_eq_zero b a)]
      exact (lor_land_ldiff b a).symm
    · apply (binaryLE_add_iff_land_eq_zero _ _).mpr
      subst r
      exact land_ldiff_eq_zero a b
    · apply (binaryLE_add_iff_land_eq_zero _ _).mpr
      subst r
      rw [Nat.land_comm a b]
      exact land_ldiff_eq_zero b a
    · apply (binaryLE_add_iff_land_eq_zero _ _).mpr
      exact ldiff_cross_land_eq_zero a b
  · rintro ⟨x, y, ha, hb, hrx', hry', hxy'⟩
    have hrx : r &&& x = 0 :=
      (binaryLE_add_iff_land_eq_zero _ _).mp hrx'
    have hry : r &&& y = 0 :=
      (binaryLE_add_iff_land_eq_zero _ _).mp hry'
    have hxy : x &&& y = 0 :=
      (binaryLE_add_iff_land_eq_zero _ _).mp hxy'
    rw [ha, hb, add_eq_lor_of_land_eq_zero hrx,
      add_eq_lor_of_land_eq_zero hry]
    exact (land_lor_pairwise_eq_left hrx hry hxy).symm

/-! ## Diophantineness of `Nat.land` -/

/-- The binary bitwise-AND function in Mathlib's two-coordinate convention. -/
def landFunction (v : Vector3 Nat 2) : Nat :=
  v &0 &&& v &1

/-- Bitwise AND is Diophantine.  The two deleted coordinates are precisely
the residual witnesses `x` and `y` from `land_certificate`. -/
theorem landFunction_diophFn : Dioph.DiophFn landFunction := by
  have dr : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &2) := D&2
  have dx : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &1) := D&1
  have dy : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &0) := D&0
  have da : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &3) := D&3
  have db : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &4) := D&4
  have drx : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &2 + v &1) :=
    Dioph.add_dioph dr dx
  have dry : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &2 + v &0) :=
    Dioph.add_dioph dr dy
  have dxy : Dioph.DiophFn (fun v : Vector3 Nat 5 => v &1 + v &0) :=
    Dioph.add_dioph dx dy
  have hfive : Dioph {v : Vector3 Nat 5 |
      v &3 = v &2 + v &1 ∧
      v &4 = v &2 + v &0 ∧
      BinaryLE (v &2) (v &2 + v &1) ∧
      BinaryLE (v &2) (v &2 + v &0) ∧
      BinaryLE (v &1) (v &1 + v &0)} := by
    exact Dioph.inter (Dioph.eq_dioph da drx) <|
      Dioph.inter (Dioph.eq_dioph db dry) <|
      Dioph.inter (binaryLE_dioph dr drx) <|
      Dioph.inter (binaryLE_dioph dr dry) (binaryLE_dioph dx dxy)
  apply (Dioph.diophFn_vec landFunction).2
  apply Dioph.ext ((D∃) 3 <| (D∃) 4 hfive)
  intro v
  change
    (∃ x y,
      v &1 = v &0 + x ∧
      v &2 = v &0 + y ∧
      BinaryLE (v &0) (v &0 + x) ∧
      BinaryLE (v &0) (v &0 + y) ∧
      BinaryLE x (x + y)) ↔
    v &1 &&& v &2 = v &0
  rw [eq_comm]
  exact (land_certificate (v &0) (v &1) (v &2)).symm

/-- Substituting arbitrary Diophantine inputs preserves bitwise AND.  This is
the Lean counterpart of Rocq's `dio_fun_nat_meet`. -/
theorem land_diophFn {alpha : Type} {a b : (alpha → Nat) → Nat}
    (da : Dioph.DiophFn a) (db : Dioph.DiophFn b) :
    Dioph.DiophFn (fun v => Nat.land (a v) (b v)) := by
  exact Dioph.diophFn_comp2 da db landFunction_diophFn

end BinaryDioph
end PAListCoding
