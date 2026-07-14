import CombinatoryLogic.SKI
import Mathlib.Computability.Partrec

/-!
# A bijective Goedel coding for SKI terms

The three primitive combinators receive codes `0`, `1`, and `2`.  An
application with child codes `f` and `x` receives code
`Nat.pair f x + 3`.  Consequently every natural number is the code of exactly
one SKI term: there are no malformed-code side conditions in the evaluator or
in finite reduction certificates.

Both application children have strictly smaller codes than their parent.  The
constructor and destructor functions are primitive recursive.
-/

namespace CombinatoryLogic.SKI.Term.Coding

/-- Natural-number codes for SKI syntax. -/
abbrev Code := Nat

/-- Code of the `S` combinator. -/
def s : Code := 0

/-- Code of the `K` combinator. -/
def k : Code := 1

/-- Code of the `I` combinator. -/
def i : Code := 2

/-- Code an application. -/
def app (function argument : Code) : Code :=
  Nat.pair function argument + 3

/-- Constructor tag: `0`, `1`, `2` for the atoms and `3` for application. -/
def tag (code : Code) : Nat := if code < 3 then code else 3

/-- Paired application payload; its value is immaterial on atom codes. -/
def payload (code : Code) : Nat := code - 3

/-- Prospective function child of an application code. -/
def appFunction (code : Code) : Code := (payload code).unpair.1

/-- Prospective argument child of an application code. -/
def appArgument (code : Code) : Code := (payload code).unpair.2

@[simp] theorem tag_s : tag s = 0 := by simp [tag, s]
@[simp] theorem tag_k : tag k = 1 := by simp [tag, k]
@[simp] theorem tag_i : tag i = 2 := by simp [tag, i]

@[simp] theorem tag_app (function argument : Code) :
    tag (app function argument) = 3 := by
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

/-- Encode a local SKI term. -/
def encode : Term → Code
  | .s => s
  | .k => k
  | .i => i
  | .app function argument => app (encode function) (encode argument)

@[simp] theorem encode_s : encode .s = s := rfl
@[simp] theorem encode_k : encode .k = k := rfl
@[simp] theorem encode_i : encode .i = i := rfl
@[simp] theorem encode_app (function argument : Term) :
    encode (function ⬝ argument) = app (encode function) (encode argument) := rfl

/-- Decode every natural number to its unique SKI term. -/
def decode : Code → Term
  | 0 => .s
  | 1 => .k
  | 2 => .i
  | payload + 3 => .app (decode payload.unpair.1) (decode payload.unpair.2)
termination_by code => code
decreasing_by
  · apply lt_of_le_of_lt
      (Nat.left_le_pair payload.unpair.1 payload.unpair.2)
    simpa only [Nat.pair_unpair] using
      (Nat.lt_add_of_pos_right (by decide : 0 < 3) : payload < payload + 3)
  · apply lt_of_le_of_lt
      (Nat.right_le_pair payload.unpair.1 payload.unpair.2)
    simpa only [Nat.pair_unpair] using
      (Nat.lt_add_of_pos_right (by decide : 0 < 3) : payload < payload + 3)

@[simp] theorem decode_s : decode s = .s := by simp [s, decode]
@[simp] theorem decode_k : decode k = .k := by simp [k, decode]
@[simp] theorem decode_i : decode i = .i := by simp [i, decode]

@[simp] theorem decode_app (function argument : Code) :
    decode (app function argument) = decode function ⬝ decode argument := by
  simp [app, decode]

/-- Decoding is a left inverse of encoding. -/
@[simp] theorem decode_encode (term : Term) : decode (encode term) = term := by
  induction term with
  | s | k | i => simp
  | app function argument functionIH argumentIH =>
      simp [functionIH, argumentIH]

/-- SKI term coding is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro left right equality
  simpa only [decode_encode] using congrArg decode equality

/-- Encoding is a left inverse of decoding. -/
@[simp] theorem encode_decode (code : Code) : encode (decode code) = code := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      cases code with
      | zero => simp [decode, s]
      | succ code =>
          cases code with
          | zero => simp [decode, k]
          | succ code =>
              cases code with
              | zero => simp [decode, i]
              | succ payload =>
                  simp only [decode, encode, app]
                  rw [inductionHypothesis payload.unpair.1
                      (lt_of_le_of_lt
                        (Nat.left_le_pair payload.unpair.1 payload.unpair.2)
                        (by simpa only [Nat.pair_unpair] using
                          (Nat.lt_add_of_pos_right (by decide : 0 < 3) :
                            payload < payload + 3))),
                    inductionHypothesis payload.unpair.2
                      (lt_of_le_of_lt
                        (Nat.right_le_pair payload.unpair.1 payload.unpair.2)
                        (by simpa only [Nat.pair_unpair] using
                          (Nat.lt_add_of_pos_right (by decide : 0 < 3) :
                            payload < payload + 3))),
                    Nat.pair_unpair]

/-- The explicit equivalence between local SKI terms and natural numbers. -/
def equivNat : Term ≃ Nat where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- The bijection supplies the recursion-theoretic coding used by Mathlib. -/
instance instPrimcodableTerm : Primcodable Term :=
  Primcodable.ofEquiv Nat equivNat

/-- A function child has a strictly smaller code than its application. -/
theorem appFunction_lt (function argument : Code) :
    function < app function argument := by
  exact lt_of_le_of_lt (Nat.left_le_pair function argument) (by simp [app])

/-- An argument child has a strictly smaller code than its application. -/
theorem appArgument_lt (function argument : Code) :
    argument < app function argument := by
  exact lt_of_le_of_lt (Nat.right_le_pair function argument) (by simp [app])

/-- Reconstruct an application code from its tag. -/
theorem eq_app_of_tag_eq_three {code : Code} (tagEquality : tag code = 3) :
    code = app (appFunction code) (appArgument code) := by
  have lowerBound : 3 ≤ code := by
    by_contra contrary
    have : code < 3 := Nat.lt_of_not_ge contrary
    rw [tag, if_pos this] at tagEquality
    exact (Nat.ne_of_lt this) tagEquality
  calc
    code = (code - 3) + 3 := (Nat.sub_add_cancel lowerBound).symm
    _ = Nat.pair (code - 3).unpair.1 (code - 3).unpair.2 + 3 := by
      rw [Nat.pair_unpair]
    _ = app (appFunction code) (appArgument code) := rfl

/-- The prospective function child decreases on application codes. -/
theorem appFunction_lt_of_tag_eq_three {code : Code}
    (tagEquality : tag code = 3) : appFunction code < code := by
  have codeEquality := eq_app_of_tag_eq_three tagEquality
  calc
    appFunction code =
        appFunction (app (appFunction code) (appArgument code)) :=
      congrArg appFunction codeEquality
    _ = appFunction code := appFunction_app _ _
    _ < app (appFunction code) (appArgument code) := appFunction_lt _ _
    _ = code := codeEquality.symm

/-- The prospective argument child decreases on application codes. -/
theorem appArgument_lt_of_tag_eq_three {code : Code}
    (tagEquality : tag code = 3) : appArgument code < code := by
  have codeEquality := eq_app_of_tag_eq_three tagEquality
  calc
    appArgument code =
        appArgument (app (appFunction code) (appArgument code)) :=
      congrArg appArgument codeEquality
    _ = appArgument code := appArgument_app _ _
    _ < app (appFunction code) (appArgument code) := appArgument_lt _ _
    _ = code := codeEquality.symm

/-- Immediate children of a raw SKI code. -/
def children (code : Code) : List Code :=
  if tag code = 3 then [appFunction code, appArgument code] else []

@[simp] theorem children_s : children s = [] := by simp [children]
@[simp] theorem children_k : children k = [] := by simp [children]
@[simp] theorem children_i : children i = [] := by simp [children]

@[simp] theorem children_app (function argument : Code) :
    children (app function argument) = [function, argument] := by
  simp [children]

/-- Every immediate child has a strictly smaller code. -/
theorem mem_children_lt {child code : Code} (membership : child ∈ children code) :
    child < code := by
  by_cases tagEquality : tag code = 3
  · have childEquality :
        child = appFunction code ∨ child = appArgument code := by
      simpa [children, tagEquality] using membership
    rcases childEquality with rfl | rfl
    · exact appFunction_lt_of_tag_eq_three tagEquality
    · exact appArgument_lt_of_tag_eq_three tagEquality
  · simp [children, tagEquality] at membership

/-- Application coding is primitive recursive. -/
theorem primrec_app : Primrec₂ app := by
  exact (Primrec.nat_add.comp₂ Primrec₂.natPair (Primrec₂.const 3)).of_eq
    (fun _ _ => rfl)

/-- Reading the constructor tag is primitive recursive. -/
theorem primrec_tag : Primrec tag := by
  have belowThree : PrimrecPred (fun code : Code => code < 3) :=
    Primrec.nat_lt.comp Primrec.id (Primrec.const 3)
  exact Primrec.ite belowThree Primrec.id (Primrec.const 3)

/-- Reading the application payload is primitive recursive. -/
theorem primrec_payload : Primrec payload := by
  exact Primrec.nat_sub.comp Primrec.id (Primrec.const 3)

/-- Reading the application function is primitive recursive. -/
theorem primrec_appFunction : Primrec appFunction := by
  exact (Primrec.fst.comp (Primrec.unpair.comp primrec_payload)).of_eq
    (fun _ => rfl)

/-- Reading the application argument is primitive recursive. -/
theorem primrec_appArgument : Primrec appArgument := by
  exact (Primrec.snd.comp (Primrec.unpair.comp primrec_payload)).of_eq
    (fun _ => rfl)

/-- Testing for an application code is primitive recursive. -/
theorem primrecPred_isApplication : PrimrecPred (fun code : Code => tag code = 3) :=
  Primrec.eq.comp primrec_tag (Primrec.const 3)

/-- Listing immediate children is primitive recursive. -/
theorem primrec_children : Primrec children := by
  have applicationChildren :
      Primrec (fun code : Code => [appFunction code, appArgument code]) :=
    Primrec.list_cons.comp primrec_appFunction
      (Primrec.list_cons.comp primrec_appArgument (Primrec.const []))
  exact Primrec.ite primrecPred_isApplication applicationChildren (Primrec.const [])

end CombinatoryLogic.SKI.Term.Coding
