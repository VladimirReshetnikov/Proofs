import PAFiniteBasisReduction.PolynomialDecodeTransport
import PAFiniteBasisReduction.HullTotalRowTable

/-!
# Functionality of standard evaluator rows in a Skolem hull

The induced finite-Skolem hull is not assumed to satisfy PA.  Nevertheless,
every child code occurring in a program row is explicitly bounded by its
parent.  At a standard parent code those bounds make all children standard;
the polynomial node equations can then be decoded externally.  Beta lookup
functionality and the semantic least/default selector graphs finish the
output-uniqueness argument inside the hull.

The descriptor below deliberately accepts recognized rows whose child codes
do not decode to genuine `Program`s.  Those rows are needed by the totalized
table construction for malformed standard codes.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-! ## Semantic inversion and standard polynomial normalization -/

/-- Invert a finite block of existential binders into simultaneous slots. -/
theorem sat_existsN_iff_slots {alpha : Type u} (M : PA.PreModel alpha)
    (n : Nat) (phi : PA.Formula) (e : Nat → alpha) :
    PA.Formula.Sat M e (existsN n phi) ↔
      ∃ slots : Fin n → alpha,
        PA.Formula.Sat M (slotEnv n slots e) phi := by
  constructor
  · intro h
    induction n generalizing e with
    | zero =>
        refine ⟨Fin.elim0, ?_⟩
        have henv : slotEnv 0 Fin.elim0 e = e := by
          funext i
          simp [slotEnv]
        rw [henv]
        simpa [existsN] using h
    | succ n ih =>
        simp only [existsN, PA.Formula.Sat] at h
        rcases h with ⟨last, h⟩
        rcases ih (e := scons last e) h with ⟨initial, hinitial⟩
        let slots : Fin (n + 1) → alpha := fun i =>
          if hi : i.val < n then initial ⟨i.val, hi⟩ else last
        refine ⟨slots, ?_⟩
        have henv : slotEnv (n + 1) slots e =
            slotEnv n initial (scons last e) := by
          funext i
          by_cases hi : i < n
          · have hi' : i < n + 1 := by omega
            rw [slotEnv_of_lt slots e hi', slotEnv_of_lt initial
              (scons last e) hi]
            simp [slots, hi]
          · by_cases hin : i = n
            · subst i
              rw [slotEnv_of_lt slots e (Nat.lt_succ_self n),
                slotEnv_of_not_lt initial (scons last e) hi]
              simp [slots, scons]
            · have hni : n < i := by omega
              have hi' : ¬i < n + 1 := by omega
              rw [slotEnv_of_not_lt slots e hi',
                slotEnv_of_not_lt initial (scons last e) hi]
              have hsub : i - n = (i - (n + 1)) + 1 := by omega
              rw [hsub]
              rfl
        rw [henv]
        exact hinitial
  · rintro ⟨slots, h⟩
    exact sat_existsN_of_slots M n phi slots e h

/-- Numerals remain injective after restriction to a Skolem hull. -/
theorem hull_numeralValue_injective {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M) :
    Function.Injective
      (PA.Term.numeralValue (preModel M S rank star)) := by
  intro m n hmn
  apply numeralValue_injective_of_pa hPA
  simpa only [hull_numeralValue_val_transport] using
    congrArg Subtype.val hmn

/-- Polynomial node normalization in the hull, after its two arguments have
already been identified as standard numerals. -/
theorem hull_eval_nodeTerm_standard {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (leftTerm rightTerm : PA.Term)
    (e : Nat → Carrier M S rank star) (left right : Nat)
    (hleft : PA.Term.eval (preModel M S rank star) e leftTerm =
      PA.Term.numeralValue (preModel M S rank star) left)
    (hright : PA.Term.eval (preModel M S rank star) e rightTerm =
      PA.Term.numeralValue (preModel M S rank star) right) :
    PA.Term.eval (preModel M S rank star) e
        (nodeTerm leftTerm rightTerm) =
      PA.Term.numeralValue (preModel M S rank star)
        (Program.nodeCode left right) := by
  apply Subtype.ext
  rw [termEval_val]
  have hleftAmbient : PA.Term.eval M (fun i => (e i).val) leftTerm =
      PA.Term.numeralValue M left := by
    simpa only [termEval_val, hull_numeralValue_val_transport] using
      congrArg Subtype.val hleft
  have hrightAmbient : PA.Term.eval M (fun i => (e i).val) rightTerm =
      PA.Term.numeralValue M right := by
    simpa only [termEval_val, hull_numeralValue_val_transport] using
      congrArg Subtype.val hright
  calc
    PA.Term.eval M (fun i => (e i).val) (nodeTerm leftTerm rightTerm) =
        PA.Term.eval M (fun i => (e i).val)
          (nodeTerm (PA.Term.numeral left) (PA.Term.numeral right)) := by
      simp only [eval_nodeTerm, PA.Term.eval_numeral]
      rw [hleftAmbient, hrightAmbient]
    _ = PA.Term.numeralValue M (Program.nodeCode left right) :=
      eval_nodeTerm_numerals hPA left right (fun i => (e i).val)
    _ = (PA.Term.numeralValue
          (preModel M S rank star) (Program.nodeCode left right)).val := by
      rw [hull_numeralValue_val_transport]

/-- Normalize a term-built list in the hull once all entries are standard. -/
theorem hull_eval_listTerm_standard_entries {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    {beta : Type} (xs : List beta) (term : beta → PA.Term)
    (value : beta → Nat) (e : Nat → Carrier M S rank star)
    (h : ∀ x ∈ xs,
      PA.Term.eval (preModel M S rank star) e (term x) =
        PA.Term.numeralValue (preModel M S rank star) (value x)) :
    PA.Term.eval (preModel M S rank star) e
        (listTerm (xs.map term)) =
      PA.Term.numeralValue (preModel M S rank star)
        (Program.listCode (xs.map value)) := by
  apply Subtype.ext
  rw [termEval_val]
  have hambient : ∀ x ∈ xs,
      PA.Term.eval M (fun i => (e i).val) (term x) =
        PA.Term.numeralValue M (value x) := by
    intro x hx
    simpa only [termEval_val, hull_numeralValue_val_transport] using
      congrArg Subtype.val (h x hx)
  rw [eval_listTerm_standard_entries hPA xs term value
    (fun i => (e i).val) hambient]
  exact (hull_numeralValue_val_transport M S rank star _).symm

/-- Fixed-length argument vectors normalize to the external vector code. -/
theorem hull_eval_argumentVectorTerm_standard {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (e : Nat → Carrier M S rank star) (codes : Fin rank → Nat)
    (hcodes : ∀ i : Fin rank,
      PA.Term.eval (preModel M S rank star) e (argumentCodeTerm i) =
        PA.Term.numeralValue (preModel M S rank star) (codes i)) :
    PA.Term.eval (preModel M S rank star) e (argumentVectorTerm rank) =
      PA.Term.numeralValue (preModel M S rank star)
        (Program.vectorCode codes) := by
  let indices : List (Fin rank) := List.ofFn (fun i : Fin rank => i)
  have h := hull_eval_listTerm_standard_entries M S rank star hPA indices
    (fun i => argumentCodeTerm i) (fun i => codes i) e (by
      intro i hi
      exact hcodes i)
  simpa [indices, argumentVectorTerm, Program.vectorCode, List.map_ofFn,
    Function.comp_def] using h

/-- Extensional form of injectivity for the external polynomial node code. -/
@[simp] theorem nodeCode_eq_nodeCode_iff {a b c d : Nat} :
    Program.nodeCode a b = Program.nodeCode c d ↔ a = c ∧ b = d := by
  constructor
  · exact Program.nodeCode_injective
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## A standard recognized-row descriptor -/

/-- A recognized row at the external standard parent code `target`.
Constructor equations are kept in the descriptor itself so downstream
strong-induction proofs can distinguish malformed and recognized codes
without eliminating proof data into `Type`. -/
inductive StandardRowWitness {alpha : Type u} (M : PA.PreModel alpha)
    (rank target : Nat) (betaCode betaStep star value : alpha) : Prop
  | star
      (target_eq : target = Program.nodeCode 0 0)
      (hvalue : value = star)
  | zero
      (target_eq : target = Program.nodeCode 1 0)
      (hvalue : value = M.zero)
  | succ (childCode : Nat) (childValue : alpha)
      (target_eq : target = Program.nodeCode 2 childCode)
      (hlookup : RawBetaEntry M childValue betaCode betaStep
        (PA.Term.numeralValue M childCode))
      (hvalue : value = M.succ childValue)
  | add (leftCode rightCode : Nat) (leftValue rightValue : alpha)
      (target_eq : target = Program.nodeCode 3
        (Program.nodeCode leftCode rightCode))
      (hleft : RawBetaEntry M leftValue betaCode betaStep
        (PA.Term.numeralValue M leftCode))
      (hright : RawBetaEntry M rightValue betaCode betaStep
        (PA.Term.numeralValue M rightCode))
      (hvalue : value = M.add leftValue rightValue)
  | mul (leftCode rightCode : Nat) (leftValue rightValue : alpha)
      (target_eq : target = Program.nodeCode 4
        (Program.nodeCode leftCode rightCode))
      (hleft : RawBetaEntry M leftValue betaCode betaStep
        (PA.Term.numeralValue M leftCode))
      (hright : RawBetaEntry M rightValue betaCode betaStep
        (PA.Term.numeralValue M rightCode))
      (hvalue : value = M.mul leftValue rightValue)
  | exSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
      (codes : Fin rank → Nat) (values : Fin rank → alpha)
      (target_eq : target = Program.nodeCode 5
        (Program.nodeCode (Program.formulaIndex rank body)
          (Program.vectorCode codes)))
      (hlookup : ∀ i,
        RawBetaEntry M (values i) betaCode betaStep
          (PA.Term.numeralValue M (codes i)))
      (hgraph : PA.Formula.Sat M
        (scons value (boundedEnv M rank values))
        (leastDefaultGraph body))
  | allSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.all body) ≤ rank)
      (codes : Fin rank → Nat) (values : Fin rank → alpha)
      (target_eq : target = Program.nodeCode 6
        (Program.nodeCode (Program.formulaIndex rank body)
          (Program.vectorCode codes)))
      (hlookup : ∀ i,
        RawBetaEntry M (values i) betaCode betaStep
          (PA.Term.numeralValue M (codes i)))
      (hgraph : PA.Formula.Sat M
        (scons value (boundedEnv M rank values))
        (leastCounterexampleGraph body))

/-! ## Inverting a standard row in the hull -/

/-- Every genuine-case witness at a standard parent code has one of the seven
standard semantic shapes above.  Strict child bounds, rather than any PA
assumption on the hull, are what make all child indices standard. -/
theorem standardRowWitness_of_sat_programCases {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (target : Nat) (code value betaCode betaStep starTerm : PA.Term)
    (e : Nat → Carrier M S rank generator)
    (hcode : PA.Term.eval (preModel M S rank generator) e code =
      PA.Term.numeralValue (preModel M S rank generator) target)
    (hSat : PA.Formula.Sat (preModel M S rank generator) e
      (programCases rank code value betaCode betaStep starTerm)) :
    StandardRowWitness (preModel M S rank generator) rank target
      (PA.Term.eval (preModel M S rank generator) e betaCode)
      (PA.Term.eval (preModel M S rank generator) e betaStep)
      (PA.Term.eval (preModel M S rank generator) e starTerm)
      (PA.Term.eval (preModel M S rank generator) e value) := by
  classical
  let KM := preModel M S rank generator
  change StandardRowWitness KM rank target
    (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
    (PA.Term.eval KM e starTerm) (PA.Term.eval KM e value)
  change PA.Term.eval KM e code = PA.Term.numeralValue KM target at hcode
  change PA.Formula.Sat KM e
    (programCases rank code value betaCode betaStep starTerm) at hSat
  rw [programCases, sat_disjunction] at hSat
  rcases hSat with ⟨branch, hbranchMem, hbranch⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbranchMem
  rcases hbranchMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- star
    simp only [starCase, PA.Formula.Sat] at hbranch
    refine .star ?_ hbranch.2
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM e
          (nodeTerm (PA.Term.numeral 0) (PA.Term.numeral 0)) := hbranch.1
      _ = PA.Term.numeralValue KM (Program.nodeCode 0 0) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 0 0
          (by simp only [PA.Term.eval_numeral])
          (by simp only [PA.Term.eval_numeral])
  · -- zero
    simp only [zeroCase, PA.Formula.Sat] at hbranch
    refine .zero ?_ hbranch.2
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM e
          (nodeTerm (PA.Term.numeral 1) (PA.Term.numeral 0)) := hbranch.1
      _ = PA.Term.numeralValue KM (Program.nodeCode 1 0) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 1 0
          (by simp only [PA.Term.eval_numeral])
          (by simp only [PA.Term.eval_numeral])
  · -- successor
    rcases (sat_existsN_iff_slots KM 2 _ e).mp hbranch with
      ⟨slots, hconj⟩
    have hall := (sat_conjunction KM (slotEnv 2 slots e) _).mp hconj
    have hrowCode := hall
      (PA.Formula.eq (liftTerm 2 code)
        (nodeTerm (PA.Term.numeral 2) (argumentCodeTerm 0))) (by simp)
    have hbound := hall
      (PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 2 code)) (by simp)
    have hlookup := hall
      (PA.Formula.betaTermTermAt (argumentValueTerm 0)
        (liftTerm 2 betaCode) (liftTerm 2 betaStep)
        (argumentCodeTerm 0)) (by simp)
    have hvalue := hall
      (PA.Formula.eq (liftTerm 2 value)
        (PA.Term.succ (argumentValueTerm 0))) (by simp)
    simp only [PA.Formula.Sat, eval_liftTerm_slotEnv] at hrowCode hvalue
    rw [sat_ltTermAt_iff_raw] at hbound
    simp only [eval_liftTerm_slotEnv] at hbound
    rw [hcode] at hbound
    let childValue := PA.Term.eval KM (slotEnv 2 slots e)
      (argumentValueTerm 0)
    let childIndex := PA.Term.eval KM (slotEnv 2 slots e)
      (argumentCodeTerm 0)
    rcases hull_rawLt_numeralValue_cases M S rank generator hPA target
      (by simpa [childIndex] using hbound) with
      ⟨childCode, childCodeLt, hchildIndex⟩
    rw [sat_betaTermTermAt_iff_raw] at hlookup
    simp only [eval_liftTerm_slotEnv] at hlookup
    have hlookup' : RawBetaEntry KM childValue
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM childCode) := by
      simpa [childValue, childIndex, hchildIndex] using hlookup
    have hvalue' : PA.Term.eval KM e value = KM.succ childValue := by
      simpa [childValue, PA.Term.eval] using hvalue
    refine .succ childCode childValue ?_ hlookup' hvalue'
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM (slotEnv 2 slots e)
          (nodeTerm (PA.Term.numeral 2) (argumentCodeTerm 0)) := hrowCode
      _ = PA.Term.numeralValue KM (Program.nodeCode 2 childCode) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _
          (slotEnv 2 slots e) 2 childCode
          (by simp only [PA.Term.eval_numeral])
          (by simpa [childIndex] using hchildIndex)
  · -- addition
    rcases (sat_existsN_iff_slots KM 4 _ e).mp hbranch with
      ⟨slots, hconj⟩
    have hall := (sat_conjunction KM (slotEnv 4 slots e) _).mp hconj
    have hrowCode := hall
      (PA.Formula.eq (liftTerm 4 code)
        (nodeTerm (PA.Term.numeral 3)
          (nodeTerm (argumentCodeTerm 0) (argumentCodeTerm 1)))) (by simp)
    have hleftBound := hall
      (PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 4 code)) (by simp)
    have hrightBound := hall
      (PA.Formula.ltTermAt (argumentCodeTerm 1) (liftTerm 4 code)) (by simp)
    have hleftLookup := hall
      (PA.Formula.betaTermTermAt (argumentValueTerm 0)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 0)) (by simp)
    have hrightLookup := hall
      (PA.Formula.betaTermTermAt (argumentValueTerm 1)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 1)) (by simp)
    have hvalue := hall
      (PA.Formula.eq (liftTerm 4 value)
        (PA.Term.add (argumentValueTerm 0) (argumentValueTerm 1))) (by simp)
    simp only [PA.Formula.Sat, eval_liftTerm_slotEnv] at hrowCode hvalue
    rw [sat_ltTermAt_iff_raw] at hleftBound hrightBound
    simp only [eval_liftTerm_slotEnv] at hleftBound hrightBound
    rw [hcode] at hleftBound hrightBound
    let leftValue := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentValueTerm 0)
    let rightValue := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentValueTerm 1)
    let leftIndex := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentCodeTerm 0)
    let rightIndex := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentCodeTerm 1)
    rcases hull_rawLt_numeralValue_cases M S rank generator hPA target
      (by simpa [leftIndex] using hleftBound) with
      ⟨leftCode, leftCodeLt, hleftIndex⟩
    rcases hull_rawLt_numeralValue_cases M S rank generator hPA target
      (by simpa [rightIndex] using hrightBound) with
      ⟨rightCode, rightCodeLt, hrightIndex⟩
    rw [sat_betaTermTermAt_iff_raw] at hleftLookup hrightLookup
    simp only [eval_liftTerm_slotEnv] at hleftLookup hrightLookup
    have hleftLookup' : RawBetaEntry KM leftValue
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM leftCode) := by
      simpa [leftValue, leftIndex, hleftIndex] using hleftLookup
    have hrightLookup' : RawBetaEntry KM rightValue
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM rightCode) := by
      simpa [rightValue, rightIndex, hrightIndex] using hrightLookup
    have hvalue' : PA.Term.eval KM e value = KM.add leftValue rightValue := by
      simpa [leftValue, rightValue, PA.Term.eval] using hvalue
    refine .add leftCode rightCode leftValue rightValue ?_
      hleftLookup' hrightLookup' hvalue'
    have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
      (argumentCodeTerm 0) (argumentCodeTerm 1) (slotEnv 4 slots e)
      leftCode rightCode (by simpa [leftIndex] using hleftIndex)
      (by simpa [rightIndex] using hrightIndex)
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM (slotEnv 4 slots e)
          (nodeTerm (PA.Term.numeral 3)
            (nodeTerm (argumentCodeTerm 0) (argumentCodeTerm 1))) := hrowCode
      _ = PA.Term.numeralValue KM
          (Program.nodeCode 3 (Program.nodeCode leftCode rightCode)) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _
          (slotEnv 4 slots e) 3 (Program.nodeCode leftCode rightCode)
          (by simp only [PA.Term.eval_numeral]) hinner
  · -- multiplication
    rcases (sat_existsN_iff_slots KM 4 _ e).mp hbranch with
      ⟨slots, hconj⟩
    have hall := (sat_conjunction KM (slotEnv 4 slots e) _).mp hconj
    have hrowCode := hall
      (PA.Formula.eq (liftTerm 4 code)
        (nodeTerm (PA.Term.numeral 4)
          (nodeTerm (argumentCodeTerm 0) (argumentCodeTerm 1)))) (by simp)
    have hleftBound := hall
      (PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 4 code)) (by simp)
    have hrightBound := hall
      (PA.Formula.ltTermAt (argumentCodeTerm 1) (liftTerm 4 code)) (by simp)
    have hleftLookup := hall
      (PA.Formula.betaTermTermAt (argumentValueTerm 0)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 0)) (by simp)
    have hrightLookup := hall
      (PA.Formula.betaTermTermAt (argumentValueTerm 1)
        (liftTerm 4 betaCode) (liftTerm 4 betaStep)
        (argumentCodeTerm 1)) (by simp)
    have hvalue := hall
      (PA.Formula.eq (liftTerm 4 value)
        (PA.Term.mul (argumentValueTerm 0) (argumentValueTerm 1))) (by simp)
    simp only [PA.Formula.Sat, eval_liftTerm_slotEnv] at hrowCode hvalue
    rw [sat_ltTermAt_iff_raw] at hleftBound hrightBound
    simp only [eval_liftTerm_slotEnv] at hleftBound hrightBound
    rw [hcode] at hleftBound hrightBound
    let leftValue := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentValueTerm 0)
    let rightValue := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentValueTerm 1)
    let leftIndex := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentCodeTerm 0)
    let rightIndex := PA.Term.eval KM (slotEnv 4 slots e)
      (argumentCodeTerm 1)
    rcases hull_rawLt_numeralValue_cases M S rank generator hPA target
      (by simpa [leftIndex] using hleftBound) with
      ⟨leftCode, leftCodeLt, hleftIndex⟩
    rcases hull_rawLt_numeralValue_cases M S rank generator hPA target
      (by simpa [rightIndex] using hrightBound) with
      ⟨rightCode, rightCodeLt, hrightIndex⟩
    rw [sat_betaTermTermAt_iff_raw] at hleftLookup hrightLookup
    simp only [eval_liftTerm_slotEnv] at hleftLookup hrightLookup
    have hleftLookup' : RawBetaEntry KM leftValue
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM leftCode) := by
      simpa [leftValue, leftIndex, hleftIndex] using hleftLookup
    have hrightLookup' : RawBetaEntry KM rightValue
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM rightCode) := by
      simpa [rightValue, rightIndex, hrightIndex] using hrightLookup
    have hvalue' : PA.Term.eval KM e value = KM.mul leftValue rightValue := by
      simpa [leftValue, rightValue, PA.Term.eval] using hvalue
    refine .mul leftCode rightCode leftValue rightValue ?_
      hleftLookup' hrightLookup' hvalue'
    have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
      (argumentCodeTerm 0) (argumentCodeTerm 1) (slotEnv 4 slots e)
      leftCode rightCode (by simpa [leftIndex] using hleftIndex)
      (by simpa [rightIndex] using hrightIndex)
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM (slotEnv 4 slots e)
          (nodeTerm (PA.Term.numeral 4)
            (nodeTerm (argumentCodeTerm 0) (argumentCodeTerm 1))) := hrowCode
      _ = PA.Term.numeralValue KM
          (Program.nodeCode 4 (Program.nodeCode leftCode rightCode)) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _
          (slotEnv 4 slots e) 4 (Program.nodeCode leftCode rightCode)
          (by simp only [PA.Term.eval_numeral]) hinner
  · -- existential Skolem selector
    rw [exSkolemCase, sat_disjunction] at hbranch
    rcases hbranch with ⟨selected, hselectedMem, hselected⟩
    rcases List.mem_map.mp hselectedMem with ⟨body, hbodyMem, rfl⟩
    have hRank : formulaRank (PA.Formula.ex body) ≤ rank := by
      have hfilter := (List.mem_filter.mp hbodyMem).2
      exact of_decide_eq_true hfilter
    rcases (sat_existsN_iff_slots KM (2 * rank) _ e).mp hselected with
      ⟨slots, hconj⟩
    have hall := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp hconj
    have hrowCode := hall
      (PA.Formula.eq (liftTerm (2 * rank) code)
        (nodeTerm (PA.Term.numeral 5)
          (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
            (argumentVectorTerm rank)))) (by simp)
    have hboundsConj := hall
      (conjunction (List.ofFn (fun i : Fin rank =>
        PA.Formula.ltTermAt (argumentCodeTerm i)
          (liftTerm (2 * rank) code)))) (by simp)
    have hlookupConj := hall
      (conjunction (List.ofFn (fun i : Fin rank =>
        PA.Formula.betaTermTermAt (argumentValueTerm i)
          (liftTerm (2 * rank) betaCode) (liftTerm (2 * rank) betaStep)
          (argumentCodeTerm i)))) (by simp)
    have hgraphSat := hall
      (graphAt rank (leastDefaultGraph body) (liftTerm (2 * rank) value)
        (fun i => argumentValueTerm i)) (by simp)
    simp only [PA.Formula.Sat, eval_liftTerm_slotEnv] at hrowCode
    have hbounds := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp
      hboundsConj
    have hlookups := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp
      hlookupConj
    let values : Fin rank → Carrier M S rank generator := fun i =>
      PA.Term.eval KM (slotEnv (2 * rank) slots e) (argumentValueTerm i)
    let indices : Fin rank → Carrier M S rank generator := fun i =>
      PA.Term.eval KM (slotEnv (2 * rank) slots e) (argumentCodeTerm i)
    have hstandard (i : Fin rank) : ∃ k, k < target ∧
        indices i = PA.Term.numeralValue KM k := by
      have hboundSat := hbounds _ ((List.mem_ofFn).mpr ⟨i, rfl⟩)
      rw [sat_ltTermAt_iff_raw] at hboundSat
      simp only [eval_liftTerm_slotEnv] at hboundSat
      rw [hcode] at hboundSat
      exact hull_rawLt_numeralValue_cases M S rank generator hPA target
        (by simpa [indices] using hboundSat)
    let codes : Fin rank → Nat := fun i => (hstandard i).choose
    have hcodesLt (i : Fin rank) : codes i < target :=
      (hstandard i).choose_spec.1
    have hindices (i : Fin rank) :
        indices i = PA.Term.numeralValue KM (codes i) :=
      (hstandard i).choose_spec.2
    have hlookup' (i : Fin rank) : RawBetaEntry KM (values i)
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM (codes i)) := by
      have hi := hlookups _ ((List.mem_ofFn).mpr ⟨i, rfl⟩)
      rw [sat_betaTermTermAt_iff_raw] at hi
      simp only [eval_liftTerm_slotEnv] at hi
      simpa [values, indices, hindices i] using hi
    have hgraph' : PA.Formula.Sat KM
        (scons (PA.Term.eval KM e value) (boundedEnv KM rank values))
        (leastDefaultGraph body) := by
      have hg := (sat_graphAt KM rank (leastDefaultGraph body)
        (liftTerm (2 * rank) value)
        (fun i => argumentValueTerm i)
        (slotEnv (2 * rank) slots e)).mp hgraphSat
      simpa [values, eval_liftTerm_slotEnv] using hg
    refine .exSkolem body hRank codes values ?_ hlookup' hgraph'
    have hvector := hull_eval_argumentVectorTerm_standard M S rank generator
      hPA (slotEnv (2 * rank) slots e) codes (by
        intro i
        simpa [indices] using hindices i)
    have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
      (PA.Term.numeral (Program.formulaIndex rank body))
      (argumentVectorTerm rank) (slotEnv (2 * rank) slots e)
      (Program.formulaIndex rank body) (Program.vectorCode codes)
      (by simp only [PA.Term.eval_numeral]) hvector
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM (slotEnv (2 * rank) slots e)
          (nodeTerm (PA.Term.numeral 5)
            (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
              (argumentVectorTerm rank))) := hrowCode
      _ = PA.Term.numeralValue KM
          (Program.nodeCode 5
            (Program.nodeCode (Program.formulaIndex rank body)
              (Program.vectorCode codes))) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _
          (slotEnv (2 * rank) slots e) 5
          (Program.nodeCode (Program.formulaIndex rank body)
            (Program.vectorCode codes))
          (by simp only [PA.Term.eval_numeral]) hinner
  · -- universal-counterexample selector
    rw [allSkolemCase, sat_disjunction] at hbranch
    rcases hbranch with ⟨selected, hselectedMem, hselected⟩
    rcases List.mem_map.mp hselectedMem with ⟨body, hbodyMem, rfl⟩
    have hRank : formulaRank (PA.Formula.all body) ≤ rank := by
      have hfilter := (List.mem_filter.mp hbodyMem).2
      exact of_decide_eq_true hfilter
    rcases (sat_existsN_iff_slots KM (2 * rank) _ e).mp hselected with
      ⟨slots, hconj⟩
    have hall := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp hconj
    have hrowCode := hall
      (PA.Formula.eq (liftTerm (2 * rank) code)
        (nodeTerm (PA.Term.numeral 6)
          (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
            (argumentVectorTerm rank)))) (by simp)
    have hboundsConj := hall
      (conjunction (List.ofFn (fun i : Fin rank =>
        PA.Formula.ltTermAt (argumentCodeTerm i)
          (liftTerm (2 * rank) code)))) (by simp)
    have hlookupConj := hall
      (conjunction (List.ofFn (fun i : Fin rank =>
        PA.Formula.betaTermTermAt (argumentValueTerm i)
          (liftTerm (2 * rank) betaCode) (liftTerm (2 * rank) betaStep)
          (argumentCodeTerm i)))) (by simp)
    have hgraphSat := hall
      (graphAt rank (leastCounterexampleGraph body)
        (liftTerm (2 * rank) value)
        (fun i => argumentValueTerm i)) (by simp)
    simp only [PA.Formula.Sat, eval_liftTerm_slotEnv] at hrowCode
    have hbounds := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp
      hboundsConj
    have hlookups := (sat_conjunction KM (slotEnv (2 * rank) slots e) _).mp
      hlookupConj
    let values : Fin rank → Carrier M S rank generator := fun i =>
      PA.Term.eval KM (slotEnv (2 * rank) slots e) (argumentValueTerm i)
    let indices : Fin rank → Carrier M S rank generator := fun i =>
      PA.Term.eval KM (slotEnv (2 * rank) slots e) (argumentCodeTerm i)
    have hstandard (i : Fin rank) : ∃ k, k < target ∧
        indices i = PA.Term.numeralValue KM k := by
      have hboundSat := hbounds _ ((List.mem_ofFn).mpr ⟨i, rfl⟩)
      rw [sat_ltTermAt_iff_raw] at hboundSat
      simp only [eval_liftTerm_slotEnv] at hboundSat
      rw [hcode] at hboundSat
      exact hull_rawLt_numeralValue_cases M S rank generator hPA target
        (by simpa [indices] using hboundSat)
    let codes : Fin rank → Nat := fun i => (hstandard i).choose
    have hcodesLt (i : Fin rank) : codes i < target :=
      (hstandard i).choose_spec.1
    have hindices (i : Fin rank) :
        indices i = PA.Term.numeralValue KM (codes i) :=
      (hstandard i).choose_spec.2
    have hlookup' (i : Fin rank) : RawBetaEntry KM (values i)
        (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
        (PA.Term.numeralValue KM (codes i)) := by
      have hi := hlookups _ ((List.mem_ofFn).mpr ⟨i, rfl⟩)
      rw [sat_betaTermTermAt_iff_raw] at hi
      simp only [eval_liftTerm_slotEnv] at hi
      simpa [values, indices, hindices i] using hi
    have hgraph' : PA.Formula.Sat KM
        (scons (PA.Term.eval KM e value) (boundedEnv KM rank values))
        (leastCounterexampleGraph body) := by
      have hg := (sat_graphAt KM rank (leastCounterexampleGraph body)
        (liftTerm (2 * rank) value)
        (fun i => argumentValueTerm i)
        (slotEnv (2 * rank) slots e)).mp hgraphSat
      simpa [values, eval_liftTerm_slotEnv] using hg
    refine .allSkolem body hRank codes values ?_ hlookup' hgraph'
    have hvector := hull_eval_argumentVectorTerm_standard M S rank generator
      hPA (slotEnv (2 * rank) slots e) codes (by
        intro i
        simpa [indices] using hindices i)
    have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
      (PA.Term.numeral (Program.formulaIndex rank body))
      (argumentVectorTerm rank) (slotEnv (2 * rank) slots e)
      (Program.formulaIndex rank body) (Program.vectorCode codes)
      (by simp only [PA.Term.eval_numeral]) hvector
    apply hull_numeralValue_injective M S rank generator hPA
    calc
      PA.Term.numeralValue KM target = PA.Term.eval KM e code := hcode.symm
      _ = PA.Term.eval KM (slotEnv (2 * rank) slots e)
          (nodeTerm (PA.Term.numeral 6)
            (nodeTerm (PA.Term.numeral (Program.formulaIndex rank body))
              (argumentVectorTerm rank))) := hrowCode
      _ = PA.Term.numeralValue KM
          (Program.nodeCode 6
            (Program.nodeCode (Program.formulaIndex rank body)
              (Program.vectorCode codes))) :=
        hull_eval_nodeTerm_standard M S rank generator hPA _ _
          (slotEnv (2 * rank) slots e) 6
          (Program.nodeCode (Program.formulaIndex rank body)
            (Program.vectorCode codes))
          (by simp only [PA.Term.eval_numeral]) hinner

/-! ## Cross-table uniqueness of recognized rows -/

/-- Two recognized rows at the same standard parent have the same output as
soon as their two beta tables agree on every strictly smaller child index.
This is the induction step needed for full evaluator functionality; unlike a
same-table beta-functionality lemma, it permits different beta-code and
beta-step witnesses on the two sides. -/
theorem standardRowWitness_output_eq_of_child_entries {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    (target : Nat)
    {betaCode₁ betaStep₁ betaCode₂ betaStep₂ star value₁ value₂ :
      Carrier M S rank generator}
    (hchildren : ∀ (child : Nat), child < target →
      ∀ {x y : Carrier M S rank generator},
        RawBetaEntry (preModel M S rank generator) x betaCode₁ betaStep₁
            (PA.Term.numeralValue (preModel M S rank generator) child) →
        RawBetaEntry (preModel M S rank generator) y betaCode₂ betaStep₂
            (PA.Term.numeralValue (preModel M S rank generator) child) →
        x = y)
    (h₁ : StandardRowWitness (preModel M S rank generator) rank target
      betaCode₁ betaStep₁ star value₁)
    (h₂ : StandardRowWitness (preModel M S rank generator) rank target
      betaCode₂ betaStep₂ star value₂) :
    value₁ = value₂ := by
  let KM := preModel M S rank generator
  change StandardRowWitness KM rank target betaCode₁ betaStep₁ star value₁ at h₁
  change StandardRowWitness KM rank target betaCode₂ betaStep₂ star value₂ at h₂
  cases h₁ <;> cases h₂ <;>
    simp_all [nodeCode_eq_nodeCode_iff] <;> try omega
  case succ.succ =>
    apply congrArg KM.succ
    apply Subtype.ext
    apply hchildren
    · exact Program.right_lt_nodeCode 2 _
    · assumption
    · assumption
  case add.add =>
    congr 1
    · apply Subtype.ext
      apply hchildren
      · exact Nat.lt_trans (Program.left_lt_nodeCode _ _)
          (Program.right_lt_nodeCode 3 _)
      · assumption
      · assumption
    · apply Subtype.ext
      apply hchildren
      · exact Nat.lt_trans (Program.right_lt_nodeCode _ _)
          (Program.right_lt_nodeCode 3 _)
      · assumption
      · assumption
  case mul.mul =>
    congr 1
    · apply Subtype.ext
      apply hchildren
      · exact Nat.lt_trans (Program.left_lt_nodeCode _ _)
          (Program.right_lt_nodeCode 4 _)
      · assumption
      · assumption
    · apply Subtype.ext
      apply hchildren
      · exact Nat.lt_trans (Program.right_lt_nodeCode _ _)
          (Program.right_lt_nodeCode 4 _)
      · assumption
      · assumption
  case exSkolem.exSkolem body₁ codes₁ values₁ body₂ codes₂ values₂
      hRank₁ hparts lookup₁ graph₁ hRank₂ htarget lookup₂ graph₂ =>
    have hbodyRank₁ : formulaRank body₁ ≤ rank := by
      simp only [formulaRank] at hRank₁
      omega
    have hbodyRank₂ : formulaRank body₂ ≤ rank := by
      simp only [formulaRank] at hRank₂
      omega
    have hbody : body₂ = body₁ :=
      Program.formulaIndex_injective_of_rank hbodyRank₂ hbodyRank₁
        hparts.1
    subst body₂
    have hcodes : codes₂ = codes₁ :=
      Program.vectorCode_injective hparts.2
    subst codes₂
    have hvalues : values₁ = values₂ := by
      funext i
      apply Subtype.ext
      apply hchildren (codes₁ i)
      · exact Nat.lt_trans (Program.vector_entry_lt_code codes₁ i)
          (Nat.lt_trans
            (Program.right_lt_nodeCode
              (Program.formulaIndex rank body₁)
              (Program.vectorCode codes₁))
            (Program.right_lt_nodeCode 5 _))
      · exact lookup₁ i
      · exact lookup₂ i
    subst values₂
    exact hull_leastDefaultGraph_functional_of_order M S rank generator hPA
      hLtRank body₁ (boundedEnv KM rank values₁) graph₁ graph₂
  case allSkolem.allSkolem body₁ codes₁ values₁ body₂ codes₂ values₂
      hRank₁ hparts lookup₁ graph₁ hRank₂ htarget lookup₂ graph₂ =>
    have hbodyRank₁ : formulaRank body₁ ≤ rank := by
      simp only [formulaRank] at hRank₁
      omega
    have hbodyRank₂ : formulaRank body₂ ≤ rank := by
      simp only [formulaRank] at hRank₂
      omega
    have hbody : body₂ = body₁ :=
      Program.formulaIndex_injective_of_rank hbodyRank₂ hbodyRank₁
        hparts.1
    subst body₂
    have hcodes : codes₂ = codes₁ :=
      Program.vectorCode_injective hparts.2
    subst codes₂
    have hvalues : values₁ = values₂ := by
      funext i
      apply Subtype.ext
      apply hchildren (codes₁ i)
      · exact Nat.lt_trans (Program.vector_entry_lt_code codes₁ i)
          (Nat.lt_trans
            (Program.right_lt_nodeCode
              (Program.formulaIndex rank body₁)
              (Program.vectorCode codes₁))
            (Program.right_lt_nodeCode 6 _))
      · exact lookup₁ i
      · exact lookup₂ i
    subst values₂
    exact hull_leastCounterexampleGraph_functional_of_order M S rank
      generator hPA hLtRank body₁ (boundedEnv KM rank values₁)
      graph₁ graph₂

/-! ## The canonical total-row witness -/

/-- A recognized row shape has a canonical witness whose output is the hull
value of `totalRowProgram`.  The supplied beta table need only contain those
canonical values at smaller indices. -/
theorem canonicalStandardRowWitness_of_shape {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (target : Nat)
    {shapeBetaCode shapeBetaStep shapeValue : Carrier M S rank generator}
    (hshape : StandardRowWitness (preModel M S rank generator) rank target
      shapeBetaCode shapeBetaStep
      (⟨generator, Hull.star⟩ : Carrier M S rank generator) shapeValue)
    {betaCode betaStep : Carrier M S rank generator}
    (htable : ∀ child, child < target →
      RawBetaEntry (preModel M S rank generator)
        (hullProgramValue M S rank generator (totalRowProgram rank child))
        betaCode betaStep
        (PA.Term.numeralValue (preModel M S rank generator) child)) :
    StandardRowWitness (preModel M S rank generator) rank target
      betaCode betaStep
      (⟨generator, Hull.star⟩ : Carrier M S rank generator)
      (hullProgramValue M S rank generator
        (totalRowProgram rank target)) := by
  let KM := preModel M S rank generator
  change StandardRowWitness KM rank target shapeBetaCode shapeBetaStep
    (⟨generator, Hull.star⟩ : Carrier M S rank generator) shapeValue at hshape
  change StandardRowWitness KM rank target betaCode betaStep
    (⟨generator, Hull.star⟩ : Carrier M S rank generator)
    (hullProgramValue M S rank generator (totalRowProgram rank target))
  cases hshape with
  | star htarget hvalue =>
      have houter : nodeComponents target = some (0, 0) :=
        nodeComponents_eq_some_iff.mpr htarget.symm
      refine .star htarget ?_
      rw [totalRowProgram_of_star_components houter]
      exact hullProgramValue_star M S rank generator
  | zero htarget hvalue =>
      have houter : nodeComponents target = some (1, 0) :=
        nodeComponents_eq_some_iff.mpr htarget.symm
      refine .zero htarget ?_
      rw [totalRowProgram_of_zero_components houter]
      exact hullProgramValue_zero M S rank generator
  | succ childCode childValue htarget hlookup hvalue =>
      have houter : nodeComponents target = some (2, childCode) :=
        nodeComponents_eq_some_iff.mpr htarget.symm
      refine .succ childCode
        (hullProgramValue M S rank generator
          (totalRowProgram rank childCode)) htarget ?_ ?_
      · apply htable childCode
        rw [htarget]
        exact Program.right_lt_nodeCode 2 childCode
      · rw [totalRowProgram_of_succ_components houter]
        exact hullProgramValue_succ M S rank generator _
  | add leftCode rightCode leftValue rightValue htarget hleft hright hvalue =>
      let payload := Program.nodeCode leftCode rightCode
      have houter : nodeComponents target = some (3, payload) :=
        nodeComponents_eq_some_iff.mpr (by simpa [payload] using htarget.symm)
      have hchildren : nodeComponents payload = some (leftCode, rightCode) :=
        nodeComponents_eq_some_iff.mpr (by simp [payload])
      refine .add leftCode rightCode
        (hullProgramValue M S rank generator (totalRowProgram rank leftCode))
        (hullProgramValue M S rank generator (totalRowProgram rank rightCode))
        htarget ?_ ?_ ?_
      · apply htable leftCode
        rw [htarget]
        exact Nat.lt_trans (Program.left_lt_nodeCode leftCode rightCode)
          (Program.right_lt_nodeCode 3 payload)
      · apply htable rightCode
        rw [htarget]
        exact Nat.lt_trans (Program.right_lt_nodeCode leftCode rightCode)
          (Program.right_lt_nodeCode 3 payload)
      · rw [totalRowProgram_of_add_components houter hchildren]
        exact hullProgramValue_add M S rank generator _ _
  | mul leftCode rightCode leftValue rightValue htarget hleft hright hvalue =>
      let payload := Program.nodeCode leftCode rightCode
      have houter : nodeComponents target = some (4, payload) :=
        nodeComponents_eq_some_iff.mpr (by simpa [payload] using htarget.symm)
      have hchildren : nodeComponents payload = some (leftCode, rightCode) :=
        nodeComponents_eq_some_iff.mpr (by simp [payload])
      refine .mul leftCode rightCode
        (hullProgramValue M S rank generator (totalRowProgram rank leftCode))
        (hullProgramValue M S rank generator (totalRowProgram rank rightCode))
        htarget ?_ ?_ ?_
      · apply htable leftCode
        rw [htarget]
        exact Nat.lt_trans (Program.left_lt_nodeCode leftCode rightCode)
          (Program.right_lt_nodeCode 4 payload)
      · apply htable rightCode
        rw [htarget]
        exact Nat.lt_trans (Program.right_lt_nodeCode leftCode rightCode)
          (Program.right_lt_nodeCode 4 payload)
      · rw [totalRowProgram_of_mul_components houter hchildren]
        exact hullProgramValue_mul M S rank generator _ _
  | exSkolem body hRank codes values htarget hlookup hgraph =>
      let vector := Program.vectorCode codes
      let payload := Program.nodeCode (Program.formulaIndex rank body) vector
      have houter : nodeComponents target = some (5, payload) :=
        nodeComponents_eq_some_iff.mpr (by simpa [payload, vector] using
          htarget.symm)
      have hnode : nodeComponents payload =
          some (Program.formulaIndex rank body, vector) :=
        nodeComponents_eq_some_iff.mpr (by simp [payload])
      have hargs : vectorComponents rank vector = some codes :=
        vectorComponents_eq_some_iff.mpr (by simp [vector])
      rcases exBodyAt_complete body hRank with ⟨entry, hentry, hentryBody⟩
      let canonicalValues : Fin rank → Carrier M S rank generator := fun i =>
        hullProgramValue M S rank generator (totalRowProgram rank (codes i))
      refine .exSkolem body hRank codes canonicalValues htarget ?_ ?_
      · intro i
        apply htable (codes i)
        rw [htarget]
        exact Nat.lt_trans (Program.vector_entry_lt_code codes i)
          (Nat.lt_trans
            (Program.right_lt_nodeCode (Program.formulaIndex rank body) vector)
            (Program.right_lt_nodeCode 5 payload))
      · have htotal := totalRowProgram_of_ex_components houter hnode hargs
          hentry
        have hg := hullProgramValue_exSkolem_graph M S rank generator
          entry.body entry.quantifiedRank
          (fun i => totalRowProgram rank (codes i))
        simpa [canonicalValues, hullProgramArgsEnv, htotal, hentryBody] using hg
  | allSkolem body hRank codes values htarget hlookup hgraph =>
      let vector := Program.vectorCode codes
      let payload := Program.nodeCode (Program.formulaIndex rank body) vector
      have houter : nodeComponents target = some (6, payload) :=
        nodeComponents_eq_some_iff.mpr (by simpa [payload, vector] using
          htarget.symm)
      have hnode : nodeComponents payload =
          some (Program.formulaIndex rank body, vector) :=
        nodeComponents_eq_some_iff.mpr (by simp [payload])
      have hargs : vectorComponents rank vector = some codes :=
        vectorComponents_eq_some_iff.mpr (by simp [vector])
      rcases allBodyAt_complete body hRank with ⟨entry, hentry, hentryBody⟩
      let canonicalValues : Fin rank → Carrier M S rank generator := fun i =>
        hullProgramValue M S rank generator (totalRowProgram rank (codes i))
      refine .allSkolem body hRank codes canonicalValues htarget ?_ ?_
      · intro i
        apply htable (codes i)
        rw [htarget]
        exact Nat.lt_trans (Program.vector_entry_lt_code codes i)
          (Nat.lt_trans
            (Program.right_lt_nodeCode (Program.formulaIndex rank body) vector)
            (Program.right_lt_nodeCode 6 payload))
      · have htotal := totalRowProgram_of_all_components houter hnode hargs
          hentry
        have hg := hullProgramValue_allSkolem_graph M S rank generator
          entry.body entry.quantifiedRank
          (fun i => totalRowProgram rank (codes i))
        simpa [canonicalValues, hullProgramArgsEnv, htotal, hentryBody] using hg

/-- Canonical-reference form of cross-table row uniqueness.  This packages
the canonical descriptor construction with the smaller-index induction
hypothesis used by an arbitrary competing table. -/
theorem standardRowWitness_output_eq_totalRow_of_child_entries
    {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ≤ rank)
    (target : Nat)
    {betaCode₁ betaStep₁ value : Carrier M S rank generator}
    (hrow : StandardRowWitness (preModel M S rank generator) rank target
      betaCode₁ betaStep₁
      (⟨generator, Hull.star⟩ : Carrier M S rank generator) value)
    {betaCode₂ betaStep₂ : Carrier M S rank generator}
    (hcanonical : ∀ child, child < target →
      RawBetaEntry (preModel M S rank generator)
        (hullProgramValue M S rank generator (totalRowProgram rank child))
        betaCode₂ betaStep₂
        (PA.Term.numeralValue (preModel M S rank generator) child))
    (hchildren : ∀ child, child < target →
      ∀ {x y : Carrier M S rank generator},
        RawBetaEntry (preModel M S rank generator) x betaCode₁ betaStep₁
            (PA.Term.numeralValue (preModel M S rank generator) child) →
        RawBetaEntry (preModel M S rank generator) y betaCode₂ betaStep₂
            (PA.Term.numeralValue (preModel M S rank generator) child) →
        x = y) :
    value = hullProgramValue M S rank generator
      (totalRowProgram rank target) := by
  have hcanonicalRow := canonicalStandardRowWitness_of_shape M S rank
    generator target hrow hcanonical
  exact standardRowWitness_output_eq_of_child_entries M S rank generator
    hPA hLtRank target hchildren hrow hcanonicalRow

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
