import PAListCoding.Basic
import PAListCoding.Predicates
import PAListCoding.Standard
import PAListCoding.Aggregates
import PAListCoding.NumberTheory
import PAListCoding.ExponentiationDiophantine
import PAListCoding.EpsilonZero
import PAListCoding.EpsilonZeroCompleteness
import PAListCoding.EpsilonZeroLaws
import PAListCoding.EpsilonZeroFormulas

/-!
# Coding finite lists in Peano arithmetic

This facade exposes a coding of finite lists of natural numbers by single
natural numbers, together with arithmetic formulas defining the elementary
list relations used throughout arithmetization.

It also exposes hereditary Cantor-normal-form codes for all ordinals below
epsilon zero.  Their order and arithmetic are computed on canonical natural
codes; the companion formula module supplies the primitive-recursive bridge
used to arithmetize those graphs.

The standard-natural-number graph of exponentiation is additionally exposed
as a Diophantine relation through the formalized Matiyasevich theorem.
-/
