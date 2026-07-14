import CombinatoryLogic.Lambda
import Mathlib.Computability.Partrec

/-!
# Goedel coding for de Bruijn lambda terms

This module gives the intrinsically scoped terms from `Lambda` a simple
natural-number code.  The outer component of `Nat.pair` is a constructor tag:

* `0` is a variable;
* `1` is an application, whose payload is another pair;
* `2` is an abstraction.

Codes with another outer tag are deliberately left invalid.  The elementary
constructor and destructor operations are primitive recursive.  Immediate
subterm codes are strictly smaller than their parent; this is the recursion
measure used by the evaluator module.
-/

namespace CombinatoryLogic.Lambda

namespace Coding

/-- Natural-number Goedel codes for raw de Bruijn syntax. -/
abbrev Code := Nat

/-- Code a de Bruijn variable. -/
def var (index : Nat) : Code := Nat.pair 0 index

/-- Code an application. -/
def app (function argument : Code) : Code :=
  Nat.pair 1 (Nat.pair function argument)

/-- Code an abstraction. -/
def lam (body : Code) : Code := Nat.pair 2 body

/-- The outer constructor tag of a raw code. -/
def tag (code : Code) : Nat := code.unpair.1

/-- The outer constructor payload of a raw code. -/
def payload (code : Code) : Nat := code.unpair.2

/-- The prospective function child of an application code. -/
def appFunction (code : Code) : Code := (payload code).unpair.1

/-- The prospective argument child of an application code. -/
def appArgument (code : Code) : Code := (payload code).unpair.2

/-- Whether a natural number is one of the three raw-syntax codes. -/
def Valid (code : Code) : Prop := tag code ≤ 2

instance (code : Code) : Decidable (Valid code) :=
  inferInstanceAs (Decidable (tag code ≤ 2))

@[simp] theorem tag_var (index : Nat) : tag (var index) = 0 := by
  simp [tag, var]

@[simp] theorem payload_var (index : Nat) : payload (var index) = index := by
  simp [payload, var]

@[simp] theorem tag_app (function argument : Code) :
    tag (app function argument) = 1 := by
  simp [tag, app]

@[simp] theorem payload_app (function argument : Code) :
    payload (app function argument) = Nat.pair function argument := by
  simp [payload, app]

@[simp] theorem appFunction_app (function argument : Code) :
    appFunction (app function argument) = function := by
  simp [appFunction]

@[simp] theorem appArgument_app (function argument : Code) :
    appArgument (app function argument) = argument := by
  simp [appArgument]

@[simp] theorem tag_lam (body : Code) : tag (lam body) = 2 := by
  simp [tag, lam]

@[simp] theorem payload_lam (body : Code) : payload (lam body) = body := by
  simp [payload, lam]

@[simp] theorem valid_var (index : Nat) : Valid (var index) := by
  simp [Valid]

@[simp] theorem valid_app (function argument : Code) :
    Valid (app function argument) := by
  simp [Valid]

@[simp] theorem valid_lam (body : Code) : Valid (lam body) := by
  simp [Valid]

/-- Encode an intrinsically scoped lambda term as raw de Bruijn syntax. -/
def encode {n : Nat} : Term n -> Code
  | .var index => var index.val
  | .app function argument => app (encode function) (encode argument)
  | .lam body => lam (encode body)

@[simp] theorem encode_var {n : Nat} (index : Fin n) :
    encode (.var index) = var index.val := rfl

@[simp] theorem encode_app {n : Nat} (function argument : Term n) :
    encode (function ⬝ argument) = app (encode function) (encode argument) := rfl

@[simp] theorem encode_lam {n : Nat} (body : Term (n + 1)) :
    encode (.lam body) = lam (encode body) := rfl

/-- Every scoped term has a valid raw code. -/
theorem encode_valid {n : Nat} (term : Term n) : Valid (encode term) := by
  cases term <;> simp

/-- The Goedel encoding is injective at every fixed scope. -/
theorem encode_injective {n : Nat} : Function.Injective (@encode n) := by
  intro left
  induction left with
  | var leftIndex =>
      intro right equality
      cases right with
      | var rightIndex =>
          simp only [encode_var, var, Nat.pair_eq_pair] at equality
          exact congrArg Term.var (Fin.ext equality.2)
      | app function argument =>
          simp [var, app] at equality
      | lam body =>
          simp [var, lam] at equality
  | app leftFunction leftArgument functionIH argumentIH =>
      intro right equality
      cases right with
      | var index =>
          simp [var, app] at equality
      | app rightFunction rightArgument =>
          simp only [encode_app, app, Nat.pair_eq_pair] at equality
          have payloadEquality := equality.2
          exact congrArg₂ Term.app
            (functionIH payloadEquality.1)
            (argumentIH payloadEquality.2)
      | lam body =>
          simp [app, lam] at equality
  | lam leftBody bodyIH =>
      intro right equality
      cases right with
      | var index =>
          simp [var, lam] at equality
      | app function argument =>
          simp [app, lam] at equality
      | lam rightBody =>
          simp only [encode_lam, lam, Nat.pair_eq_pair] at equality
          exact congrArg Term.lam (bodyIH equality.2)

/-- A function child has a smaller code than its application parent. -/
theorem appFunction_lt (function argument : Code) :
    function < app function argument := by
  apply lt_of_le_of_lt (Nat.left_le_pair function argument)
  exact lt_of_lt_of_le (Nat.lt_succ_self (Nat.pair function argument))
    (by simpa [app, Nat.add_comm] using
      Nat.add_le_pair 1 (Nat.pair function argument))

/-- An argument child has a smaller code than its application parent. -/
theorem appArgument_lt (function argument : Code) :
    argument < app function argument := by
  apply lt_of_le_of_lt (Nat.right_le_pair function argument)
  exact lt_of_lt_of_le (Nat.lt_succ_self (Nat.pair function argument))
    (by simpa [app, Nat.add_comm] using
      Nat.add_le_pair 1 (Nat.pair function argument))

/-- An abstraction body has a smaller code than its parent. -/
theorem lamBody_lt (body : Code) : body < lam body := by
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_left (by decide : 0 < 2))
    (Nat.add_le_pair 2 body)

/-- Reconstruct an application code from a tag test. -/
theorem eq_app_of_tag_eq_one {code : Code} (h : tag code = 1) :
    code = app (appFunction code) (appArgument code) := by
  calc
    code = Nat.pair (tag code) (payload code) := by
      simp [tag, payload, Nat.pair_unpair]
    _ = Nat.pair 1 (payload code) := by rw [h]
    _ = app (appFunction code) (appArgument code) := by
      simp [app, appFunction, appArgument, Nat.pair_unpair]

/-- Reconstruct an abstraction code from a tag test. -/
theorem eq_lam_of_tag_eq_two {code : Code} (h : tag code = 2) :
    code = lam (payload code) := by
  calc
    code = Nat.pair (tag code) (payload code) := by
      simp [tag, payload, Nat.pair_unpair]
    _ = Nat.pair 2 (payload code) := by rw [h]
    _ = lam (payload code) := rfl

/-- The prospective function child decreases whenever the outer tag is `1`. -/
theorem appFunction_lt_of_tag_eq_one {code : Code} (h : tag code = 1) :
    appFunction code < code := by
  have codeEquality := eq_app_of_tag_eq_one h
  calc
    appFunction code = appFunction (app (appFunction code) (appArgument code)) :=
      congrArg appFunction codeEquality
    _ = appFunction code := appFunction_app _ _
    _ < app (appFunction code) (appArgument code) := appFunction_lt _ _
    _ = code := codeEquality.symm

/-- The prospective argument child decreases whenever the outer tag is `1`. -/
theorem appArgument_lt_of_tag_eq_one {code : Code} (h : tag code = 1) :
    appArgument code < code := by
  have codeEquality := eq_app_of_tag_eq_one h
  calc
    appArgument code = appArgument (app (appFunction code) (appArgument code)) :=
      congrArg appArgument codeEquality
    _ = appArgument code := appArgument_app _ _
    _ < app (appFunction code) (appArgument code) := appArgument_lt _ _
    _ = code := codeEquality.symm

/-- The prospective body decreases whenever the outer tag is `2`. -/
theorem payload_lt_of_tag_eq_two {code : Code} (h : tag code = 2) :
    payload code < code := by
  have codeEquality := eq_lam_of_tag_eq_two h
  calc
    payload code = payload (lam (payload code)) := congrArg payload codeEquality
    _ = payload code := payload_lam _
    _ < lam (payload code) := lamBody_lt _
    _ = code := codeEquality.symm

/-- Immediate children of a raw syntax code, used for well-founded recursion. -/
def children (code : Code) : List Code :=
  if tag code = 1 then [appFunction code, appArgument code]
  else if tag code = 2 then [payload code]
  else []

@[simp] theorem children_var (index : Nat) : children (var index) = [] := by
  simp [children]

@[simp] theorem children_app (function argument : Code) :
    children (app function argument) = [function, argument] := by
  simp [children]

@[simp] theorem children_lam (body : Code) : children (lam body) = [body] := by
  simp [children]

/-- Every listed child is strictly smaller than its parent code. -/
theorem mem_children_lt {child code : Code} (membership : child ∈ children code) :
    child < code := by
  by_cases tagEquality : tag code = 1
  · have childEquality :
        child = appFunction code ∨ child = appArgument code := by
      simpa [children, tagEquality] using membership
    rcases childEquality with rfl | rfl
    · exact appFunction_lt_of_tag_eq_one tagEquality
    · exact appArgument_lt_of_tag_eq_one tagEquality
  · by_cases tagEqualityTwo : tag code = 2
    · have childEquality : child = payload code := by
        simpa [children, tagEquality, tagEqualityTwo] using membership
      subst child
      exact payload_lt_of_tag_eq_two tagEqualityTwo
    · simp [children, tagEquality, tagEqualityTwo] at membership

/-- Variable coding is primitive recursive. -/
theorem primrec_var : Primrec var :=
  Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

/-- Application coding is primitive recursive in both arguments. -/
theorem primrec_app : Primrec₂ app :=
  Primrec₂.natPair.comp₂ (Primrec₂.const 1) Primrec₂.natPair

/-- Abstraction coding is primitive recursive. -/
theorem primrec_lam : Primrec lam :=
  Primrec₂.natPair.comp (Primrec.const 2) Primrec.id

/-- Reading the constructor tag is primitive recursive. -/
theorem primrec_tag : Primrec tag := by
  exact (Primrec.fst.comp Primrec.unpair).of_eq (fun _ => rfl)

/-- Reading the constructor payload is primitive recursive. -/
theorem primrec_payload : Primrec payload := by
  exact (Primrec.snd.comp Primrec.unpair).of_eq (fun _ => rfl)

/-- Reading an application function is primitive recursive. -/
theorem primrec_appFunction : Primrec appFunction := by
  exact (Primrec.fst.comp (Primrec.unpair.comp primrec_payload)).of_eq (fun _ => rfl)

/-- Reading an application argument is primitive recursive. -/
theorem primrec_appArgument : Primrec appArgument := by
  exact (Primrec.snd.comp (Primrec.unpair.comp primrec_payload)).of_eq (fun _ => rfl)

/-- Validity of a raw syntax code is a primitive-recursive predicate. -/
theorem primrecPred_valid : PrimrecPred Valid := by
  exact Primrec.nat_le.comp primrec_tag (Primrec.const 2)

/-- Listing immediate raw children is primitive recursive. -/
theorem primrec_children : Primrec children := by
  have tagIsOne : PrimrecPred (fun code : Code => tag code = 1) :=
    Primrec.eq.comp primrec_tag (Primrec.const 1)
  have tagIsTwo : PrimrecPred (fun code : Code => tag code = 2) :=
    Primrec.eq.comp primrec_tag (Primrec.const 2)
  have appChildren : Primrec (fun code : Code => [appFunction code, appArgument code]) :=
    Primrec.list_cons.comp primrec_appFunction
      (Primrec.list_cons.comp primrec_appArgument (Primrec.const []))
  have lamChildren : Primrec (fun code : Code => [payload code]) :=
    Primrec.list_cons.comp primrec_payload (Primrec.const [])
  exact Primrec.ite tagIsOne appChildren
    (Primrec.ite tagIsTwo lamChildren (Primrec.const []))

end Coding

end CombinatoryLogic.Lambda
