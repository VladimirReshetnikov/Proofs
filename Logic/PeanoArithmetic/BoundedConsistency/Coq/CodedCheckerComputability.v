(**
  Computability certificates for the restricted-proof checker.

  This cache boundary contains the comparatively expensive verified extraction
  of the coded syntax and proof decoders.  It exports computability instances
  used by the small formula-facing layer.
*)

From Stdlib Require Import Arith Bool Lia FunctionalExtensionality.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode ComputableFormula.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof.

From Undecidability.L.Datatypes Require Import LBool LNat LProd LOptions.
From Undecidability.L.Datatypes.List Require Import List_basics.
From Undecidability.L.Tactics Require Import Computable GenEncode.

Set Implicit Arguments.

Module PABoundedCodedDecoderComputability.

Import PA.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import GenEncode.

(** Extraction certificates for every project-specific inductive traversed by
    the checker are generated below.  The generic extraction library already
    supplies encodings for naturals, Booleans, lists, products, and options. *)
MetaRocq Run (tmGenEncode "pa_term_enc" PA.term).
#[export] Hint Resolve pa_term_enc_correct : Lrewrite.

#[export] Instance term_tVar : computable PA.tVar.
Proof. extract constructor. Qed.
#[export] Instance term_tZero : computable PA.tZero.
Proof. extract constructor. Qed.
#[export] Instance term_tSucc : computable PA.tSucc.
Proof. extract constructor. Qed.
#[export] Instance term_tAdd : computable PA.tAdd.
Proof. extract constructor. Qed.
#[export] Instance term_tMul : computable PA.tMul.
Proof. extract constructor. Qed.

MetaRocq Run (tmGenEncode "pa_formula_enc" PA.formula).
#[export] Hint Resolve pa_formula_enc_correct : Lrewrite.

#[export] Instance term_pEq : computable PA.pEq.
Proof. extract constructor. Qed.
#[export] Instance term_pBot : computable PA.pBot.
Proof. extract constructor. Qed.
#[export] Instance term_pImp : computable PA.pImp.
Proof. extract constructor. Qed.
#[export] Instance term_pAnd : computable PA.pAnd.
Proof. extract constructor. Qed.
#[export] Instance term_pOr : computable PA.pOr.
Proof. extract constructor. Qed.
#[export] Instance term_pAll : computable PA.pAll.
Proof. extract constructor. Qed.
#[export] Instance term_pEx : computable PA.pEx.
Proof. extract constructor. Qed.

MetaRocq Run (tmGenEncode "raw_proof_enc" RawProof).
#[export] Hint Resolve raw_proof_enc_correct : Lrewrite.

#[export] Instance term_RP_ass : computable RP_ass.
Proof. extract constructor. Qed.
#[export] Instance term_RP_impI : computable RP_impI.
Proof. extract constructor. Qed.
#[export] Instance term_RP_impE : computable RP_impE.
Proof. extract constructor. Qed.
#[export] Instance term_RP_botE : computable RP_botE.
Proof. extract constructor. Qed.
#[export] Instance term_RP_lem : computable RP_lem.
Proof. extract constructor. Qed.
#[export] Instance term_RP_andI : computable RP_andI.
Proof. extract constructor. Qed.
#[export] Instance term_RP_andE1 : computable RP_andE1.
Proof. extract constructor. Qed.
#[export] Instance term_RP_andE2 : computable RP_andE2.
Proof. extract constructor. Qed.
#[export] Instance term_RP_orI1 : computable RP_orI1.
Proof. extract constructor. Qed.
#[export] Instance term_RP_orI2 : computable RP_orI2.
Proof. extract constructor. Qed.
#[export] Instance term_RP_orE : computable RP_orE.
Proof. extract constructor. Qed.
#[export] Instance term_RP_allI : computable RP_allI.
Proof. extract constructor. Qed.
#[export] Instance term_RP_allE : computable RP_allE.
Proof. extract constructor. Qed.
#[export] Instance term_RP_exI : computable RP_exI.
Proof. extract constructor. Qed.
#[export] Instance term_RP_exE : computable RP_exE.
Proof. extract constructor. Qed.
#[export] Instance term_RP_eqRefl : computable RP_eqRefl.
Proof. extract constructor. Qed.
#[export] Instance term_RP_eqElim : computable RP_eqElim.
Proof. extract constructor. Qed.

MetaRocq Run (tmGenEncode "pa_axiom_witness_enc" PAAxiomWitness).
#[export] Hint Resolve pa_axiom_witness_enc_correct : Lrewrite.

#[export] Instance term_PAW_succInj : computable PAW_succInj.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_zeroNotSucc : computable PAW_zeroNotSucc.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_addZero : computable PAW_addZero.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_addSucc : computable PAW_addSucc.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_mulZero : computable PAW_mulZero.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_mulSucc : computable PAW_mulSucc.
Proof. extract constructor. Qed.
#[export] Instance term_PAW_induction : computable PAW_induction.
Proof. extract constructor. Qed.

(** The canonical list-code decoder is the bottom-most project-specific
    algorithm used by all three syntax decoders. *)
#[export] Instance term_seq_local : computable List.seq.
Proof. extract. Qed.
#[export] Instance term_list_prod_nat :
    computable (@List.list_prod nat nat).
Proof.
  apply computableExt with
    (x := fix rec (xs ys : list nat) : list (nat * nat) :=
      match xs with
      | [] => []
      | x :: xs' => List.app (map (pair x) ys) (rec xs' ys)
      end).
  - intros xs ys. induction xs; easy.
  - extract.
Qed.
#[export] Instance term_polynomialPairCandidates :
    computable PAListCode.polynomialPairCandidates.
Proof. extract. Qed.
#[export] Instance term_polynomialPair : computable PAListCode.polynomialPair.
Proof. extract. Qed.
#[export] Instance term_find_nat_pair :
    computable (@List.find (nat * nat)).
Proof. extract. Qed.

Definition pairOptionDefault (o : option (nat * nat)) : nat * nat :=
  match o with Some ab => ab | None => (0, 0) end.

#[export] Instance term_pairOptionDefault : computable pairOptionDefault.
Proof. extract. Qed.

Definition polynomialPairMatches (n : nat) (ab : nat * nat) : bool :=
  Nat.eqb (PAListCode.polynomialPair (fst ab) (snd ab)) n.

#[export] Instance term_polynomialPairMatches :
    computable polynomialPairMatches.
Proof. extract. Qed.

Definition findPolynomialPair (n : nat) : option (nat * nat) :=
  List.find (polynomialPairMatches n)
    (PAListCode.polynomialPairCandidates n).

#[export] Instance term_findPolynomialPair : computable findPolynomialPair.
Proof. extract. Qed.

Definition polynomialUnpairProgram (n : nat) : nat * nat :=
  pairOptionDefault (findPolynomialPair n).

#[export] Instance term_polynomialUnpairProgram :
    computable polynomialUnpairProgram.
Proof. extract. Qed.

#[export] Instance term_polynomialUnpair :
    computable PAListCode.polynomialUnpair.
Proof.
  apply computableExt with (x := polynomialUnpairProgram).
  - reflexivity.
  - typeclasses eauto.
Qed.
#[export] Instance term_polynomialSplit : computable PAListCode.polynomialSplit.
Proof. extract. Qed.
#[export] Instance term_listDecodeFuel : computable PAListCode.decodeFuel.
Proof. extract. Qed.
#[export] Instance term_listDecode : computable PAListCode.decode.
Proof. extract. Qed.

(** Coded PA syntax decoders. *)
#[export] Instance term_decodeTermFuel : computable decodeTermFuel.
Proof. extract. Qed.
#[export] Instance term_decodeTerm : computable decodeTerm.
Proof. extract. Qed.
#[export] Instance term_decodeFormulaFuel : computable decodeFormulaFuel.
Proof. extract. Qed.
#[export] Instance term_decodeFormula : computable decodeFormula.
Proof. extract. Qed.

(** Certificate decoders, from the leaves upward. *)
#[export] Instance term_decodeFormulaCodes : computable decodeFormulaCodes.
Proof. extract. Qed.
#[export] Instance term_decodeContext : computable decodeContext.
Proof. extract. Qed.
#[export] Instance term_decodeRawProofFuel : computable decodeRawProofFuel.
Proof. extract. Qed.
#[export] Instance term_decodeRawProof : computable decodeRawProof.
Proof. extract. Qed.
#[export] Instance term_decodeAxiomWitness : computable decodeAxiomWitness.
Proof. extract. Qed.
#[export] Instance term_decodeAxiomWitnessCodes :
    computable decodeAxiomWitnessCodes.
Proof. extract. Qed.
#[export] Instance term_decodeAxiomWitnessList :
    computable decodeAxiomWitnessList.
Proof. extract. Qed.
#[export] Instance term_decodeRestrictedPAProof :
    computable decodeRestrictedPAProof.
Proof. extract. Qed.

(** Keeping this decoder-heavy layer separate makes its proof term a reusable
    [.vo] cache boundary.  The decision-procedure instances live in the next,
    much smaller file. *)
End PABoundedCodedDecoderComputability.
