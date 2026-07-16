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

-- The less immediate external-list bridges are also audited explicitly.
#print axioms PAListCoding.concatAll_encode_iff_flatten
#print axioms PAListCoding.occurrences_encode_iff_count
#print axioms PAListCoding.lexSorted_encode_iff
#print axioms PAListCoding.allPermutations_encode_iff

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
