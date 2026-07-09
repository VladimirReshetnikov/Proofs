(*
  Coq port of SetTheory.PAHF.RiemannHypothesis.

  This file mirrors the Lean syntax-level construction of a first-order PA
  sentence expressing the Littlewood/Mertens growth criterion for the Riemann
  Hypothesis.  As in the newly merged Lean module, the final certified fact
  here is that the arithmetized formula is a closed PA sentence.
*)

From Stdlib Require Import Arith.Arith.
From SetTheory Require Import PAHF.

Open Scope nat_scope.

Definition notF (phi : PA.formula) : PA.formula :=
  PA.pImp phi PA.pBot.

Definition shiftTerm (k : nat) (t : PA.term) : PA.term :=
  PA.Term.rename (fun n => n + k) t.

Definition shiftFormula (k : nat) (phi : PA.formula) : PA.formula :=
  PA.Formula.rename (fun n => n + k) phi.

Definition dvdTermAt (a b : PA.term) : PA.formula :=
  PA.pEx (PA.pEq
    (PA.tMul (PA.Term.rename S a) (PA.tVar 0))
    (PA.Term.rename S b)).

Definition evenTermAt (t : PA.term) : PA.formula :=
  PA.pEx (PA.pEq
    (PA.Term.rename S t)
    (PA.tAdd (PA.tVar 0) (PA.tVar 0))).

Definition oddTermAt (t : PA.term) : PA.formula :=
  PA.pEx (PA.pEq
    (PA.Term.rename S t)
    (PA.tSucc (PA.tAdd (PA.tVar 0) (PA.tVar 0)))).

Definition nonzeroTermAt (t : PA.term) : PA.formula :=
  PA.pEx (PA.pEq
    (PA.Term.rename S t)
    (PA.tSucc (PA.tVar 0))).

Definition remTermTermAt
    (rem value modulus : PA.term) : PA.formula :=
  PA.pEx (PA.pAnd
    (PA.Formula.ltTermAt
      (PA.Term.rename S rem)
      (PA.Term.rename S modulus))
    (PA.pEq (PA.Term.rename S value)
      (PA.tAdd
        (PA.tMul (PA.tVar 0) (PA.Term.rename S modulus))
        (PA.Term.rename S rem)))).

Definition betaModTermTerm (step idx : PA.term) : PA.term :=
  PA.tSucc (PA.tMul (PA.tSucc idx) step).

Definition betaTermTermAt
    (out code step idx : PA.term) : PA.formula :=
  PA.pEx (PA.pAnd
    (PA.pEq (PA.tVar 0)
      (PA.Term.rename S (betaModTermTerm step idx)))
    (remTermTermAt
      (PA.Term.rename S out)
      (PA.Term.rename S code)
      (PA.tVar 0))).

Definition betaTermTermAtConstIdx
    (out code step : PA.term) (idxValue : nat) : PA.formula :=
  PA.pEx (PA.pAnd (PA.Formula.eqConstAt 0 idxValue)
    (betaTermTermAt
      (PA.Term.rename S out)
      (PA.Term.rename S code)
      (PA.Term.rename S step)
      (PA.tVar 0))).

Definition properRemainderWitnessAt
    (value modulus : PA.term) : PA.formula :=
  PA.pEx (PA.pEx (PA.pAnd
    (PA.Formula.ltTermAt
      (PA.tSucc (PA.tVar 1))
      (shiftTerm 2 modulus))
    (PA.pEq (shiftTerm 2 value)
      (PA.tAdd
        (PA.tMul (PA.tVar 0) (shiftTerm 2 modulus))
        (PA.tSucc (PA.tVar 1)))))).

Definition primeTermAt (p : PA.term) : PA.formula :=
  PA.pAnd
    (PA.Formula.ltTermAt (PA.Term.numeral 1) p)
    (PA.pAll (PA.pImp
      (PA.pAnd
        (PA.Formula.ltTermAt (PA.Term.numeral 1) (PA.tVar 0))
        (PA.Formula.ltTermAt (PA.tVar 0) (shiftTerm 1 p)))
      (properRemainderWitnessAt (shiftTerm 1 p) (PA.tVar 0)))).

Definition squarefreeTermAt (n : PA.term) : PA.formula :=
  PA.pAll (PA.pImp
    (PA.pAnd
      (PA.Formula.ltTermAt (PA.tVar 0) (PA.tSucc (shiftTerm 1 n)))
      (primeTermAt (PA.tVar 0)))
    (properRemainderWitnessAt
      (shiftTerm 1 n)
      (PA.tMul (PA.tVar 0) (PA.tVar 0)))).

Definition completePrimeFactorizationTraceAt
    (n len code step : PA.term) : PA.formula :=
  PA.pAnd (betaTermTermAtConstIdx n code step 0)
    (PA.pAnd
      (betaTermTermAt (PA.Term.numeral 1) code step len)
      (PA.pAll (PA.pImp
        (PA.Formula.ltTermAt (PA.tVar 0) (shiftTerm 1 len))
        (PA.pEx (PA.pAnd
          (primeTermAt (PA.tVar 0))
          (PA.pEx (PA.pAnd
            (betaTermTermAt (PA.tVar 0)
              (shiftTerm 3 code) (shiftTerm 3 step)
              (PA.tSucc (PA.tVar 2)))
            (betaTermTermAt
              (PA.tMul (PA.tVar 1) (PA.tVar 0))
              (shiftTerm 3 code) (shiftTerm 3 step)
              (PA.tVar 2))))))))).

Definition factorizationEvenTraceTermAt (n : PA.term) : PA.formula :=
  PA.pEx (PA.pEx (PA.pEx
    (PA.pAnd
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (PA.tVar 2) (PA.tVar 1) (PA.tVar 0))
      (evenTermAt (PA.tVar 2))))).

Definition factorizationEvenTermAt (n : PA.term) : PA.formula :=
  PA.pOr
    (PA.pEq n (PA.Term.numeral 1))
    (factorizationEvenTraceTermAt n).

Definition factorizationOddTraceTermAt (n : PA.term) : PA.formula :=
  PA.pEx (PA.pEx (PA.pEx
    (PA.pAnd
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (PA.tVar 2) (PA.tVar 1) (PA.tVar 0))
      (oddTermAt (PA.tVar 2))))).

Definition factorizationOddTermAt (n : PA.term) : PA.formula :=
  PA.pOr (PA.pEq n (PA.Term.numeral 2))
    (PA.pOr
      (PA.pEq n (PA.Term.numeral 3))
      (factorizationOddTraceTermAt n)).

Definition mobiusPositiveTermAt (n : PA.term) : PA.formula :=
  PA.pAnd (squarefreeTermAt n) (factorizationEvenTermAt n).

Definition mobiusNegativeTermAt (n : PA.term) : PA.formula :=
  PA.pAnd (squarefreeTermAt n) (factorizationOddTermAt n).

Definition mertensCountStepAt
    (posCode posStep negCode negStep : PA.term) : PA.formula :=
  let posCode' := shiftTerm 2 posCode in
  let posStep' := shiftTerm 2 posStep in
  let negCode' := shiftTerm 2 negCode in
  let negStep' := shiftTerm 2 negStep in
  let posCur := PA.tVar 1 in
  let negCur := PA.tVar 0 in
  let i' := PA.tVar 2 in
  let k' := PA.tSucc i' in
  let positiveUpdate :=
    PA.pEx (PA.pEx (PA.pAnd (mobiusPositiveTermAt k')
      (PA.pAnd
        (betaTermTermAt posCur posCode' posStep' i')
        (PA.pAnd
          (betaTermTermAt (PA.tSucc posCur) posCode' posStep'
            (PA.tSucc i'))
          (PA.pAnd
            (betaTermTermAt negCur negCode' negStep' i')
            (betaTermTermAt negCur negCode' negStep'
              (PA.tSucc i'))))))) in
  let negativeUpdate :=
    PA.pEx (PA.pEx (PA.pAnd (mobiusNegativeTermAt k')
      (PA.pAnd
        (betaTermTermAt posCur posCode' posStep' i')
        (PA.pAnd
          (betaTermTermAt posCur posCode' posStep' (PA.tSucc i'))
          (PA.pAnd
            (betaTermTermAt negCur negCode' negStep' i')
            (betaTermTermAt (PA.tSucc negCur) negCode' negStep'
              (PA.tSucc i'))))))) in
  let zeroUpdate :=
    PA.pEx (PA.pEx (PA.pAnd (notF (mobiusPositiveTermAt k'))
      (PA.pAnd (notF (mobiusNegativeTermAt k'))
        (PA.pAnd
          (betaTermTermAt posCur posCode' posStep' i')
          (PA.pAnd
            (betaTermTermAt posCur posCode' posStep' (PA.tSucc i'))
            (PA.pAnd
              (betaTermTermAt negCur negCode' negStep' i')
              (betaTermTermAt negCur negCode' negStep'
                (PA.tSucc i')))))))) in
  PA.pOr positiveUpdate (PA.pOr negativeUpdate zeroUpdate).

Definition mertensCountsTraceAt
    (n pos neg posCode posStep negCode negStep : PA.term) : PA.formula :=
  PA.pAnd (betaTermTermAtConstIdx (PA.Term.numeral 0) posCode posStep 0)
    (PA.pAnd (betaTermTermAtConstIdx (PA.Term.numeral 0) negCode negStep 0)
      (PA.pAnd (betaTermTermAt pos posCode posStep n)
        (PA.pAnd (betaTermTermAt neg negCode negStep n)
          (PA.pAll (PA.pImp
            (PA.Formula.ltTermAt (PA.tVar 0) (shiftTerm 1 n))
            (mertensCountStepAt
              (shiftTerm 1 posCode) (shiftTerm 1 posStep)
              (shiftTerm 1 negCode) (shiftTerm 1 negStep))))))).

Definition mertensCountsTraceExistsAt
    (n pos neg : PA.term) : PA.formula :=
  PA.pEx (PA.pEx (PA.pEx (PA.pEx
    (mertensCountsTraceAt
      (shiftTerm 4 n) (shiftTerm 4 pos) (shiftTerm 4 neg)
      (PA.tVar 3) (PA.tVar 2) (PA.tVar 1) (PA.tVar 0))))).

Definition mertensCountsBaseAt
    (n pos neg : PA.term)
    (nValue posValue negValue : nat) : PA.formula :=
  PA.pAnd (PA.pEq n (PA.Term.numeral nValue))
    (PA.pAnd (PA.pEq pos (PA.Term.numeral posValue))
      (PA.pEq neg (PA.Term.numeral negValue))).

Definition mertensCountsAt
    (n pos neg : PA.term) : PA.formula :=
  PA.pOr (mertensCountsBaseAt n pos neg 1 1 0)
    (PA.pOr (mertensCountsBaseAt n pos neg 2 1 1)
      (PA.pOr (mertensCountsBaseAt n pos neg 3 1 2)
        (mertensCountsTraceExistsAt n pos neg))).

Definition mertensOneEqOneStatement : PA.formula :=
  PA.pAnd
    (mertensCountsAt
      (PA.Term.numeral 1) (PA.Term.numeral 1) (PA.Term.numeral 0))
    (PA.pEq (PA.Term.numeral 1)
      (PA.tAdd (PA.Term.numeral 0) (PA.Term.numeral 1))).

Definition mertensTwoEqZeroStatement : PA.formula :=
  PA.pAnd
    (mertensCountsAt
      (PA.Term.numeral 2) (PA.Term.numeral 1) (PA.Term.numeral 1))
    (PA.pEq (PA.Term.numeral 1) (PA.Term.numeral 1)).

Definition mertensThreeEqNegOneStatement : PA.formula :=
  PA.pAnd
    (mertensCountsAt
      (PA.Term.numeral 3) (PA.Term.numeral 1) (PA.Term.numeral 2))
    (PA.pEq (PA.Term.numeral 2)
      (PA.tAdd (PA.Term.numeral 1) (PA.Term.numeral 1))).

Definition powTraceAt
    (base exp out code step : PA.term) : PA.formula :=
  PA.pAnd (betaTermTermAtConstIdx (PA.Term.numeral 1) code step 0)
    (PA.pAnd (betaTermTermAt out code step exp)
      (PA.pAll (PA.pImp
        (PA.Formula.ltTermAt (PA.tVar 0) (shiftTerm 1 exp))
        (PA.pEx (PA.pAnd
          (betaTermTermAt (PA.tVar 0) (shiftTerm 2 code)
            (shiftTerm 2 step) (PA.tVar 1))
          (betaTermTermAt
            (PA.tMul (PA.tVar 0) (shiftTerm 2 base))
            (shiftTerm 2 code) (shiftTerm 2 step)
            (PA.tSucc (PA.tVar 1)))))))).

Definition powRelAt (base exp out : PA.term) : PA.formula :=
  PA.pEx (PA.pEx
    (powTraceAt
      (shiftTerm 2 base)
      (shiftTerm 2 exp)
      (shiftTerm 2 out)
      (PA.tVar 1)
      (PA.tVar 0))).

Definition mertensPowerBoundAt
    (n q C pos neg : PA.term) : PA.formula :=
  let diff := PA.tVar 0 in
  PA.pEx (PA.pAnd
    (PA.pOr
      (PA.pEq (PA.tAdd (shiftTerm 1 pos) diff) (shiftTerm 1 neg))
      (PA.pEq (PA.tAdd (shiftTerm 1 neg) diff) (shiftTerm 1 pos)))
    (PA.pEx (PA.pAnd
      (powRelAt (PA.tVar 1)
        (PA.tMul (PA.Term.numeral 2) (shiftTerm 2 q))
        (PA.tVar 0))
      (PA.pEx (PA.pAnd
        (powRelAt (shiftTerm 3 n)
          (PA.tSucc (shiftTerm 3 q))
          (PA.tVar 0))
        (PA.Formula.leTermAt (PA.tVar 1)
          (PA.tMul (shiftTerm 3 C) (PA.tVar 0)))))))).

Definition mertensBoundAt (n q C : PA.term) : PA.formula :=
  PA.pEx (PA.pEx (PA.pAnd
    (mertensCountsAt (shiftTerm 2 n) (PA.tVar 1) (PA.tVar 0))
    (mertensPowerBoundAt
      (shiftTerm 2 n) (shiftTerm 2 q) (shiftTerm 2 C)
      (PA.tVar 1) (PA.tVar 0)))).

Definition mertensRiemannHypothesisBody : PA.formula :=
  PA.pAll (PA.pImp (PA.Formula.nonzeroAt 0)
    (PA.pEx (PA.pAll
      (mertensBoundAt (PA.tVar 0) (PA.tVar 2) (PA.tVar 1))))).

Definition mertensRiemannHypothesisSentence : PA.formula :=
  PA.Formula.sealPA mertensRiemannHypothesisBody.

Theorem mertensRiemannHypothesisSentence_sentence :
  PA.Formula.Sentence mertensRiemannHypothesisSentence.
Proof.
  unfold mertensRiemannHypothesisSentence.
  apply PA.Formula.sealPA_sentence.
Qed.
