/-
  SetTheory.PAHF.RiemannHypothesis

  A first-order Peano-arithmetic sentence whose standard interpretation is a
  classical arithmetic reformulation of the Riemann Hypothesis.
-/

import SetTheory.PAHF.PASyntax

namespace SetTheory
namespace PA
namespace Formula
namespace RiemannHypothesis

/-! ## Small formula combinators -/

/-- Object-language negation. -/
def notF (phi : Formula) : Formula :=
  imp phi bot

/-- Shift every free variable in a PA term through `k` freshly-bound variables. -/
def shiftTerm (k : Nat) (t : Term) : Term :=
  Term.rename (fun n => n + k) t

/-- Shift every free variable in a PA formula through `k` freshly-bound variables. -/
def shiftFormula (k : Nat) (phi : Formula) : Formula :=
  rename (fun n => n + k) phi

/-- Term-parametric divisibility. -/
def dvdTermAt (a b : Term) : Formula :=
  ex (eq (Term.mul (Term.rename Nat.succ a) (Term.var 0))
    (Term.rename Nat.succ b))

/-- Term-parametric evenness. -/
def evenTermAt (t : Term) : Formula :=
  ex (eq (Term.rename Nat.succ t)
    (Term.add (Term.var 0) (Term.var 0)))

/-- Term-parametric oddness. -/
def oddTermAt (t : Term) : Formula :=
  ex (eq (Term.rename Nat.succ t)
    (Term.succ (Term.add (Term.var 0) (Term.var 0))))

/-- Term-parametric primality, using the divisor definition. -/
def primeTermAt (p : Term) : Formula :=
  and (ltTermAt (Term.numeral 1) p)
    (all (imp
      (dvdTermAt (Term.var 0) (Term.rename Nat.succ p))
      (or (eqConstAt 0 1)
        (eq (Term.var 0) (Term.rename Nat.succ p)))))

/-- Term-parametric squarefreeness. -/
def squarefreeTermAt (n : Term) : Formula :=
  all (imp (primeTermAt (Term.var 0))
    (notF (dvdTermAt
      (Term.mul (Term.var 0) (Term.var 0))
      (Term.rename Nat.succ n))))

/-! ## Prime-factorization parity -/

/--
`completePrimeFactorizationTraceAt n len code step` says that `code, step`
beta-code a finite sequence `a_0, ..., a_len` such that `a_0 = n`,
`a_len = 1`, and each transition divides out one prime:
`a_i = p * a_{i+1}` for some prime `p`.

The parity of `len` is therefore the parity of the total number of prime
factors of `n` in the standard model.
-/
def completePrimeFactorizationTraceAt
    (n len code step : Term) : Formula :=
  and (betaTermTermAtConstIdx n code step 0)
    (and (betaTermTermAt (Term.numeral 1) code step len)
      (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 len))
        (ex (and (primeTermAt (Term.var 0))
          (ex (and
            (betaTermTermAt (Term.var 0)
              (shiftTerm 3 code) (shiftTerm 3 step)
              (Term.succ (Term.var 2)))
            (betaTermTermAt
              (Term.mul (Term.var 1) (Term.var 0))
              (shiftTerm 3 code) (shiftTerm 3 step)
              (Term.var 2)))))))))

/-- `n` has an even-length complete prime factorization. -/
def factorizationEvenTermAt (n : Term) : Formula :=
  ex (ex (ex
    (and
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (Term.var 2) (Term.var 1) (Term.var 0))
      (evenTermAt (Term.var 2)))))

/-- `n` has an odd-length complete prime factorization. -/
def factorizationOddTermAt (n : Term) : Formula :=
  ex (ex (ex
    (and
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (Term.var 2) (Term.var 1) (Term.var 0))
      (oddTermAt (Term.var 2)))))

/-- The Möbius value of `n` is `+1`: squarefree with even factorization length. -/
def mobiusPositiveTermAt (n : Term) : Formula :=
  and (squarefreeTermAt n) (factorizationEvenTermAt n)

/-- The Möbius value of `n` is `-1`: squarefree with odd factorization length. -/
def mobiusNegativeTermAt (n : Term) : Formula :=
  and (squarefreeTermAt n) (factorizationOddTermAt n)

/-! ## Prefix-count traces for the Mertens function -/

/--
The update relation for the two cumulative counts in the Mertens function.

At loop index `i`, the integer being inspected is `i+1`.  The positive count is
incremented when `mu(i+1)=+1`, the negative count is incremented when
`mu(i+1)=-1`, and both counts are preserved when the Möbius value is `0`.
-/
def mertensCountStepAt
    (posCode posStep negCode negStep : Term) : Formula :=
  let posCode' := shiftTerm 2 posCode
  let posStep' := shiftTerm 2 posStep
  let negCode' := shiftTerm 2 negCode
  let negStep' := shiftTerm 2 negStep
  let posCur := Term.var 1
  let negCur := Term.var 0
  let i' := Term.var 2
  let k' := Term.succ i'
  let positiveUpdate :=
    ex (ex (and (mobiusPositiveTermAt k')
      (and
        (betaTermTermAt posCur posCode' posStep' i')
        (and
          (betaTermTermAt (Term.succ posCur) posCode' posStep'
            (Term.succ i'))
          (and
            (betaTermTermAt negCur negCode' negStep' i')
            (betaTermTermAt negCur negCode' negStep'
              (Term.succ i')))))))
  let negativeUpdate :=
    ex (ex (and (mobiusNegativeTermAt k')
      (and
        (betaTermTermAt posCur posCode' posStep' i')
        (and
          (betaTermTermAt posCur posCode' posStep' (Term.succ i'))
          (and
            (betaTermTermAt negCur negCode' negStep' i')
            (betaTermTermAt (Term.succ negCur) negCode' negStep'
              (Term.succ i')))))))
  let zeroUpdate :=
    ex (ex (and (notF (mobiusPositiveTermAt k'))
      (and (notF (mobiusNegativeTermAt k'))
        (and
          (betaTermTermAt posCur posCode' posStep' i')
          (and
            (betaTermTermAt posCur posCode' posStep' (Term.succ i'))
            (and
              (betaTermTermAt negCur negCode' negStep' i')
              (betaTermTermAt negCur negCode' negStep'
                (Term.succ i'))))))))
  or positiveUpdate (or negativeUpdate zeroUpdate)

/--
`mertensCountsTraceAt n pos neg ...` says that `pos` and `neg` are the counts
of `k <= n` for which `mu(k)=+1` and `mu(k)=-1`, respectively.
-/
def mertensCountsTraceAt
    (n pos neg posCode posStep negCode negStep : Term) : Formula :=
  and (betaTermTermAtConstIdx (Term.numeral 0) posCode posStep 0)
    (and (betaTermTermAtConstIdx (Term.numeral 0) negCode negStep 0)
      (and (betaTermTermAt pos posCode posStep n)
        (and (betaTermTermAt neg negCode negStep n)
          (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 n))
            (mertensCountStepAt
              (shiftTerm 1 posCode) (shiftTerm 1 posStep)
              (shiftTerm 1 negCode) (shiftTerm 1 negStep)))))))

/-- Existential wrapper for Mertens positive/negative prefix counts. -/
def mertensCountsAt (n pos neg : Term) : Formula :=
  ex (ex (ex (ex
    (mertensCountsTraceAt (shiftTerm 4 n) (shiftTerm 4 pos)
      (shiftTerm 4 neg) (Term.var 3) (Term.var 2)
      (Term.var 1) (Term.var 0)))))

/-! ## Power traces and the arithmetized RH growth bound -/

/-- Beta-coded exponentiation trace: `out = base ^ exp`. -/
def powTraceAt (base exp out code step : Term) : Formula :=
  and (betaTermTermAtConstIdx (Term.numeral 1) code step 0)
    (and (betaTermTermAt out code step exp)
      (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 exp))
        (ex (and
          (betaTermTermAt (Term.var 0) (shiftTerm 2 code)
            (shiftTerm 2 step) (Term.var 1))
          (betaTermTermAt
            (Term.mul (Term.var 0) (shiftTerm 2 base))
            (shiftTerm 2 code) (shiftTerm 2 step)
            (Term.succ (Term.var 1))))))))

/-- Existential wrapper for `out = base ^ exp`. -/
def powRelAt (base exp out : Term) : Formula :=
  ex (ex (powTraceAt (shiftTerm 2 base) (shiftTerm 2 exp)
    (shiftTerm 2 out) (Term.var 1) (Term.var 0)))

/--
The integer inequality corresponding to
`|M(n)|^(2*q) <= C * n^(q+1)`.
-/
def mertensPowerBoundAt (n q C pos neg : Term) : Formula :=
  let diff := Term.var 0
  ex (and
    (or
      (eq (Term.add (shiftTerm 1 pos) diff) (shiftTerm 1 neg))
      (eq (Term.add (shiftTerm 1 neg) diff) (shiftTerm 1 pos)))
    (ex (and
      (powRelAt (Term.var 1)
        (Term.mul (Term.numeral 2) (shiftTerm 2 q))
        (Term.var 0))
      (ex (and
        (powRelAt (shiftTerm 3 n)
          (Term.succ (shiftTerm 3 q))
          (Term.var 0))
        (leTermAt (Term.var 1)
          (Term.mul (shiftTerm 3 C) (Term.var 0))))))))

/-- One `n`-instance of the arithmetized Mertens growth bound. -/
def mertensBoundAt (n q C : Term) : Formula :=
  ex (ex (and
    (mertensCountsAt (shiftTerm 2 n) (Term.var 1) (Term.var 0))
    (mertensPowerBoundAt
      (shiftTerm 2 n) (shiftTerm 2 q) (shiftTerm 2 C)
      (Term.var 1) (Term.var 0))))

/--
The PA sentence:

`forall q > 0, exists C, forall n,
  |M(n)|^(2*q) <= C * n^(q+1)`.

For each positive rational epsilon, choose `q` with `1/(2*q) < epsilon`.
Thus this is the integer-power form of the classical Littlewood/Mertens
criterion `M(n) = O(n^(1/2+epsilon))` for every epsilon > 0.
-/
def mertensRiemannHypothesisBody : Formula :=
  all (imp (nonzeroAt 0)
    (ex (all (mertensBoundAt (Term.var 0) (Term.var 2) (Term.var 1)))))

/-- The sealed PA sentence form of `mertensRiemannHypothesisBody`. -/
def mertensRiemannHypothesisSentence : Formula :=
  sealPA mertensRiemannHypothesisBody

theorem mertensRiemannHypothesisSentence_sentence :
    Sentence mertensRiemannHypothesisSentence :=
  sealPA_sentence _

end RiemannHypothesis
end Formula
end PA
end SetTheory
