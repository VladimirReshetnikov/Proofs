(* ===================================================================== *)
(*  PAHFRoundTripArithmeticAssembly.v                                   *)
(*                                                                       *)
(*  Final arithmetic assembly for the PA composite round trip.           *)
(*                                                                       *)
(*  The range, injectivity, graph-functionality, term-constructor,        *)
(*  equality, and quantifier layers are all concrete here.  Only the     *)
(*  five proof objects named by the public constructors remain inputs.   *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFDeductiveAssembly
  PAHFOrdinalCodeTotalInduction
  PAHFRoundTripArithmetic PAHFRoundTripEquality PAHFRoundTripQuantifiers
  PAHFCompositeArithmetic
  PAHFOrdinalCodeTermCompatibility PAHFOrdinalCodeFunctional
  PAHFOrdinalCodeInjective PAHFOrdinalCodeRange
  PAHFOrdinalCodeRangeArithmetic PAHFOrdinalCodeTermOperations
  PAHFOrdinalCodeTermBase PAHFOrdinalCodeTermAdd PAHFOrdinalCodeTermMul.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** The range module and the functionality module use intentionally local
    names for the same Ackermann-adjoin output law. *)
Definition PAHFAdjoinOutputFunctionalProof_of_extensionality_assembly
    (hext : PAHFMembershipExtensionalityProof) :
  PAHFAdjoinOutputFunctionalProof.
Proof.
  intros G newCode1 newCode2 oldCode elemCode hgraph1 hgraph2.
  exact (PAHFAdjoinGraphFunctionalProof_of_extensionality
    hext G newCode1 newCode2 oldCode elemCode hgraph1 hgraph2).
Defined.

(** All graph infrastructure shared by term constructors and quantifiers. *)
Definition PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeGraphTotalProof :=
  PAOrdinalCodeGraphTotalProof_of_adjoinExistence hadjoin.

Definition PAOrdinalCodeGraphFunctionalProof_of_arithmetic_inputs
    (hext : PAHFMembershipExtensionalityProof) :
  PAOrdinalCodeGraphFunctionalProof :=
  PAOrdinalCodeGraphFunctionalProof_of_extensionality hext.

Definition PAOrdinalCodeGraphSuccClosureProof_of_arithmetic_inputs
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeGraphSuccClosureProof :=
  PAOrdinalCodeGraphSuccClosureProof_of_functionality
    (PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs hadjoin)
    (PAOrdinalCodeGraphFunctionalProof_of_arithmetic_inputs hext)
    (PAHFAdjoinOutputFunctionalProof_of_extensionality_assembly hext).

Definition PAOrdinalCodeGraphRangeProof_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeGraphRangeProof :=
  PAOrdinalCodeGraphRangeProof_of_adjoin_and_functionality
    P hadjoin
    (PAOrdinalCodeGraphFunctionalProof_of_arithmetic_inputs hext)
    (PAHFAdjoinOutputFunctionalProof_of_extensionality_assembly hext).

Definition PAOrdinalCodeGraphInjectiveProof_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalCodeGraphInjectiveProof :=
  PAOrdinalCodeGraphInjectiveProof_of_TranslatedHFFinAxiomProofs P.

(* --------------------------------------------------------------------- *)
(* Term graph.                                                           *)

Definition PAOrdinalCodeTermBaseCompatibilityProofs_of_arithmetic_inputs
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeTermBaseCompatibilityProofs :=
  PAOrdinalCodeTermBaseCompatibilityProofs_of_interfaces
    hext
    (PAOrdinalCodeGraphSuccClosureProof_of_arithmetic_inputs hext hadjoin)
    hadjoin.

Definition PAOrdinalCodeTermAddCompatibility_of_arithmetic_inputs
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility) :
  PAOrdinalCodeTermAddCompatibility :=
  PAOrdinalCodeTermAddCompatibility_of_total_core
    (PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs hadjoin)
    hadd.

Definition PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs
    (hadjoin : PAHFAdjoinExistence)
    (hmul : PAOrdinalCodeMulCoreProofs) :
  PAOrdinalCodeTermMulCompatibility :=
  PAOrdinalCodeTermMulCompatibility_of_total_cores
    (PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs hadjoin)
    hmul.

(** Concrete all-term graph theorem. *)
Definition PACompositeTermGraphProof_of_arithmetic_inputs
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofs) :
  PACompositeTermGraphProof :=
  PACompositeTermGraphProof_of_base_add_mul
    (PAOrdinalCodeTermBaseCompatibilityProofs_of_arithmetic_inputs
      hext hadjoin)
    (PAOrdinalCodeTermAddCompatibility_of_arithmetic_inputs
      hadjoin hadd)
    (PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs
      hadjoin hmul).

(* --------------------------------------------------------------------- *)
(* Equality, quantifiers, and the full PA formula round trip.             *)

Definition PACompositeEqualityProof_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofs) :
  PACompositeEqualityProof :=
  pa_composite_eq_exact_of_adjoin_injective_termGraph
    hadjoin
    (PAOrdinalCodeGraphInjectiveProof_of_arithmetic_inputs P)
    (PACompositeTermGraphProof_of_arithmetic_inputs
      hext hadjoin hadd hmul).

Definition PAOrdinalCodeQuantifierProofs_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence) :
  PAOrdinalCodeQuantifierProofs :=
  PAOrdinalCodeQuantifierProofs_of_adjoinExistence
    hadjoin
    (PAOrdinalCodeGraphRangeProof_of_arithmetic_inputs
      P hext hadjoin).

(** Concrete constructor record consumed by formula induction. *)
Definition PACompositeConstructorProofs_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofs) :
  PACompositeConstructorProofs :=
  PACompositeConstructorProofs_of_eq_and_quantifiers
    (PACompositeEqualityProof_of_arithmetic_inputs
      P hext hadjoin hadd hmul)
    (PAOrdinalCodeQuantifierProofs_of_arithmetic_inputs
      P hext hadjoin).

(** Final PA-side deductive round-trip theorem. *)
Definition PARoundTripProof_of_arithmetic_inputs
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofs) :
  PARoundTripProof :=
  PARoundTripProof_of_constructorProofs
    (PACompositeConstructorProofs_of_arithmetic_inputs
      P hext hadjoin hadd hmul).
