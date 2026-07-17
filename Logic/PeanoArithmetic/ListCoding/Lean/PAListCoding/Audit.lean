import PAListCoding

/-!
# Kernel audit for PA finite-list coding

Keep this list deliberately explicit.  A new relation is not part of the
public theorem surface merely because a definition happens to compile: its PA
formula, correctness theorem, and ordinary-list interpretation must all be
named here.
-/

-- The code is canonical and every valid standard code has one decoded list.
#check PAListCoding.encode_valid
#check PAListCoding.valid_iff_existsUnique_encode
#check PAListCoding.encode_injective
#check PAListCoding.decode_encode
#check PAListCoding.encode_decode

-- Actual PA formula witnesses and their standard-model correctness theorems.
#check PAListCoding.validFormula_spec
#check PAListCoding.lengthFormula_spec
#check PAListCoding.entryFormula_spec
#check PAListCoding.singletonFormula_spec
#check PAListCoding.concatFormula_spec
#check PAListCoding.concatAllFormula_spec
#check PAListCoding.occurrencesFormula_spec
#check PAListCoding.permutationFormula_spec
#check PAListCoding.substringFormula_spec
#check PAListCoding.subsequenceFormula_spec
#check PAListCoding.noDuplicatesFormula_spec
#check PAListCoding.nondecreasingFormula_spec
#check PAListCoding.lexSortedFormula_spec
#check PAListCoding.allPermutationsFormula_spec
#check PAListCoding.sumElementsFormula_spec
#check PAListCoding.productElementsFormula_spec
#check PAListCoding.greatestFormula_spec
#check PAListCoding.leastFormula_spec
#check PAListCoding.twiceMedianFormula_spec
#check PAListCoding.uniqueModeFormula_spec

-- Agreement of the arithmetic predicates with familiar external lists.
#check PAListCoding.valid_encode_iff
#check PAListCoding.hasLength_encode_iff
#check PAListCoding.entry_encode_iff
#check PAListCoding.singleton_encode_iff
#check PAListCoding.concat_encode_iff
#check PAListCoding.concatAll_encode_iff_flatten
#check PAListCoding.occurrences_encode_iff_count
#check PAListCoding.permutation_encode_iff
#check PAListCoding.substring_encode_iff
#check PAListCoding.subsequence_encode_iff
#check PAListCoding.noDuplicates_encode_iff
#check PAListCoding.nondecreasing_encode_iff
#check PAListCoding.lexSorted_encode_iff
#check PAListCoding.allPermutations_encode_iff
#check PAListCoding.sumElements_encode_iff_sum
#check PAListCoding.productElements_encode_iff_prod
#check PAListCoding.greatest_encode_iff
#check PAListCoding.least_encode_iff
#check PAListCoding.twiceMedian_encode_iff
#check PAListCoding.uniqueMode_encode_iff

-- The result relations are functional whenever they hold; sum and product
-- additionally exist on every valid standard code.
#check PAListCoding.sumElements_existsUnique
#check PAListCoding.productElements_existsUnique
#check PAListCoding.sumElements_existsUnique_of_valid
#check PAListCoding.productElements_existsUnique_of_valid
#check PAListCoding.greatest_exists_of_valid_of_decode_ne_nil
#check PAListCoding.least_exists_of_valid_of_decode_ne_nil
#check PAListCoding.twiceMedian_exists_of_valid_of_decode_ne_nil
#check PAListCoding.greatest_functional
#check PAListCoding.least_functional
#check PAListCoding.twiceMedian_functional
#check PAListCoding.uniqueMode_functional

-- Boundary and parity regressions make the intended conventions explicit.
#check PAListCoding.greatest_empty_false
#check PAListCoding.least_empty_false
#check PAListCoding.twiceMedian_empty_false
#check PAListCoding.uniqueMode_empty_false
#check PAListCoding.uniqueMode_tie_false
#check PAListCoding.twiceMedian_odd_example
#check PAListCoding.twiceMedian_even_example

-- The less immediate external-list bridges are also audited explicitly.
#print axioms PAListCoding.concatAll_encode_iff_flatten
#print axioms PAListCoding.occurrences_encode_iff_count
#print axioms PAListCoding.lexSorted_encode_iff
#print axioms PAListCoding.allPermutations_encode_iff
#print axioms PAListCoding.productElements_encode_iff_prod
#print axioms PAListCoding.twiceMedian_encode_iff
#print axioms PAListCoding.uniqueMode_encode_iff
#print axioms PAListCoding.twiceMedian_functional
#print axioms PAListCoding.uniqueMode_functional
#print axioms PAListCoding.greatest_exists_of_valid_of_decode_ne_nil
#print axioms PAListCoding.least_exists_of_valid_of_decode_ne_nil
#print axioms PAListCoding.twiceMedian_exists_of_valid_of_decode_ne_nil

-- Print the precise trusted assumptions of the coding boundary.
#print axioms PAListCoding.valid_iff_existsUnique_encode
#print axioms PAListCoding.encode_injective
#print axioms PAListCoding.decode_encode
#print axioms PAListCoding.encode_decode

-- Print assumptions for every formula-correctness theorem, including the
-- unrestricted formula used for the sound-and-complete permutation listing.
#print axioms PAListCoding.validFormula_spec
#print axioms PAListCoding.lengthFormula_spec
#print axioms PAListCoding.entryFormula_spec
#print axioms PAListCoding.singletonFormula_spec
#print axioms PAListCoding.concatFormula_spec
#print axioms PAListCoding.concatAllFormula_spec
#print axioms PAListCoding.occurrencesFormula_spec
#print axioms PAListCoding.permutationFormula_spec
#print axioms PAListCoding.substringFormula_spec
#print axioms PAListCoding.subsequenceFormula_spec
#print axioms PAListCoding.noDuplicatesFormula_spec
#print axioms PAListCoding.nondecreasingFormula_spec
#print axioms PAListCoding.lexSortedFormula_spec
#print axioms PAListCoding.allPermutationsFormula_spec
#print axioms PAListCoding.sumElementsFormula_spec
#print axioms PAListCoding.productElementsFormula_spec
#print axioms PAListCoding.greatestFormula_spec
#print axioms PAListCoding.leastFormula_spec
#print axioms PAListCoding.twiceMedianFormula_spec
#print axioms PAListCoding.uniqueModeFormula_spec

/-! ## Number-theoretic list data

The public aliases below retain the vocabulary of the theorem statement while
the shorter internal names remain available to existing clients.  Prime
indices are one-based, factor pairs are nested two-element list codes, digits
are most-significant-first, and divisor lists contain positive divisors only.
-/

-- Uniform relations and their concrete PA formula witnesses.
#check PAListCoding.Power
#check PAListCoding.NthPrime
#check PAListCoding.PrimeFactorization
#check PAListCoding.BaseDigits
#check PAListCoding.PositiveDivisors
#check PAListCoding.pairCodeFormula_spec
#check PAListCoding.strictlyIncreasingFormula_spec
#check PAListCoding.powerFormula_spec
#check PAListCoding.nthPrimeFormula_spec
#check PAListCoding.primeFactorizationFormula_spec
#check PAListCoding.baseDigitsFormula_spec
#check PAListCoding.positiveDivisorsFormula_spec

-- Standard-model interpretations of each coded relation.
#check PAListCoding.pairCode_encode_pair_iff
#check PAListCoding.strictlyIncreasing_encode_iff
#check PAListCoding.pow_iff
#check PAListCoding.nthPrime_iff_count
#check PAListCoding.nthPrime_iff_nth
#check PAListCoding.divisorList_encode_iff
#check PAListCoding.primeFactorization_encode_iff
#check PAListCoding.baseDigits_encode_iff_conditions
#check PAListCoding.baseDigits_encode_iff

-- Canonical results exist uniquely whenever their mathematical inputs permit
-- a result, and arbitrary valid codes are covered by the functionality proofs.
#check PAListCoding.pow_existsUnique
#check PAListCoding.nthPrime_functional_index
#check PAListCoding.nthPrime_functional_prime
#check PAListCoding.nthPrime_existsUnique
#check PAListCoding.nthPrime_index_existsUnique
#check PAListCoding.divisorList_functional
#check PAListCoding.divisorList_existsUnique
#check PAListCoding.primeFactorization_functional
#check PAListCoding.primeFactorization_existsUnique
#check PAListCoding.baseDigits_functional
#check PAListCoding.baseDigits_existsUnique

-- Boundary cases and small computations pin down all representation choices.
#check PAListCoding.pow_zero_exponent
#check PAListCoding.pow_zero_base_succ
#check PAListCoding.nthPrime_zero_false
#check PAListCoding.nthPrime_two_one
#check PAListCoding.divisorList_zero_false
#check PAListCoding.divisorList_one_example
#check PAListCoding.divisorList_twelve_example
#check PAListCoding.primeFactorization_zero_false
#check PAListCoding.primeFactorization_one_empty
#check PAListCoding.primeFactorization_360_example
#check PAListCoding.baseDigits_invalid_base_zero
#check PAListCoding.baseDigits_invalid_base_one
#check PAListCoding.baseDigits_zero
#check PAListCoding.baseDigits_13_binary

-- Audit the trusted assumptions of the less immediate semantic bridges and
-- arbitrary-code uniqueness arguments.
#print axioms PAListCoding.powerFormula_spec
#print axioms PAListCoding.nthPrimeFormula_spec
#print axioms PAListCoding.primeFactorizationFormula_spec
#print axioms PAListCoding.baseDigitsFormula_spec
#print axioms PAListCoding.positiveDivisorsFormula_spec
#print axioms PAListCoding.nthPrime_iff_nth
#print axioms PAListCoding.nthPrime_index_existsUnique
#print axioms PAListCoding.divisorList_encode_iff
#print axioms PAListCoding.divisorList_existsUnique
#print axioms PAListCoding.primeFactorization_encode_iff
#print axioms PAListCoding.canonicalFactorization_unique
#print axioms PAListCoding.primeFactorization_existsUnique
#print axioms PAListCoding.baseDigits_encode_iff
#print axioms PAListCoding.baseDigits_existsUnique

/-! ### Diophantine exponentiation

These declarations are distinct from the preceding PA multiplication-trace
formula: they state that the result-first graph is the existential zero set of
one integer polynomial. -/

#check PAListCoding.NaturalPowFunction
#check PAListCoding.NaturalPowGraph
#check PAListCoding.naturalPow_diophantineFunction
#check PAListCoding.naturalPowGraph_diophantine
#check PAListCoding.power_diophantine
#check PAListCoding.power_polynomial_exists

#print axioms PAListCoding.naturalPow_diophantineFunction
#print axioms PAListCoding.naturalPowGraph_diophantine
#print axioms PAListCoding.power_diophantine
#print axioms PAListCoding.power_polynomial_exists

/-! ## Ordinal notations below epsilon zero -/

-- The concrete square-shell code is a bijection on raw hereditary CNF syntax;
-- validity selects precisely Mathlib's normal ordinal notations.
#check PAListCoding.EpsilonZero.codeEquiv
#check PAListCoding.EpsilonZero.validCodeEquiv
#check PAListCoding.EpsilonZero.denote_injective_on_valid
#check PAListCoding.EpsilonZero.valid_denote_lt_epsilonZero
#check PAListCoding.EpsilonZero.exists_nonote_repr_of_lt_epsilonZero
#check PAListCoding.EpsilonZero.exists_valid_code_denote_iff

-- The public result-first graphs are total and functional on valid inputs and
-- agree with set-theoretic ordinal arithmetic.
#check PAListCoding.EpsilonZero.ordinalLT_iff
#check PAListCoding.EpsilonZero.ordinalAdd_existsUnique
#check PAListCoding.EpsilonZero.ordinalMul_existsUnique
#check PAListCoding.EpsilonZero.ordinalPow_existsUnique
#check PAListCoding.EpsilonZero.ordinalAdd_iff
#check PAListCoding.EpsilonZero.ordinalMul_iff
#check PAListCoding.EpsilonZero.ordinalPow_iff

-- Natural code-level laws, with the noncommutative orientation appropriate to
-- ordinal multiplication and exponentiation.
#check PAListCoding.EpsilonZero.ordinalLT_irrefl
#check PAListCoding.EpsilonZero.ordinalLT_trans
#check PAListCoding.EpsilonZero.ordinalLT_trichotomy
#check PAListCoding.EpsilonZero.addCode_assoc
#check PAListCoding.EpsilonZero.mulCode_assoc
#check PAListCoding.EpsilonZero.mulCode_addCode
#check PAListCoding.EpsilonZero.powCode_addCode
#check PAListCoding.EpsilonZero.powCode_mulCode

-- Genuine PA formula witnesses.  Arithmetic graphs use the documented
-- result-first order `(z, a, b)`; comparison uses `(a, b)`.
#check PAListCoding.EpsilonZero.validOrdinalCodeFormula
#check PAListCoding.EpsilonZero.ordinalLTFormula
#check PAListCoding.EpsilonZero.ordinalAddFormula
#check PAListCoding.EpsilonZero.ordinalMulFormula
#check PAListCoding.EpsilonZero.ordinalPowFormula
#check PAListCoding.EpsilonZero.validOrdinalCodeFormula_spec
#check PAListCoding.EpsilonZero.ordinalLTFormula_spec
#check PAListCoding.EpsilonZero.ordinalAddFormula_spec
#check PAListCoding.EpsilonZero.ordinalMulFormula_spec
#check PAListCoding.EpsilonZero.ordinalPowFormula_spec

#print axioms PAListCoding.EpsilonZero.codeEquiv
#print axioms PAListCoding.EpsilonZero.validCodeEquiv
#print axioms PAListCoding.EpsilonZero.valid_denote_lt_epsilonZero
#print axioms PAListCoding.EpsilonZero.exists_nonote_repr_of_lt_epsilonZero
#print axioms PAListCoding.EpsilonZero.exists_valid_code_denote_iff
#print axioms PAListCoding.EpsilonZero.ordinalLT_iff
#print axioms PAListCoding.EpsilonZero.ordinalAdd_iff
#print axioms PAListCoding.EpsilonZero.ordinalMul_iff
#print axioms PAListCoding.EpsilonZero.ordinalPow_iff
#print axioms PAListCoding.EpsilonZero.ordinalLT_trichotomy
#print axioms PAListCoding.EpsilonZero.addCode_assoc
#print axioms PAListCoding.EpsilonZero.mulCode_assoc
#print axioms PAListCoding.EpsilonZero.mulCode_addCode
#print axioms PAListCoding.EpsilonZero.powCode_addCode
#print axioms PAListCoding.EpsilonZero.powCode_mulCode
#print axioms PAListCoding.EpsilonZero.validOrdinalCodeFormula_spec
#print axioms PAListCoding.EpsilonZero.ordinalLTFormula_spec
#print axioms PAListCoding.EpsilonZero.ordinalAddFormula_spec
#print axioms PAListCoding.EpsilonZero.ordinalMulFormula_spec
#print axioms PAListCoding.EpsilonZero.ordinalPowFormula_spec
