(**
  Occurrence-rank and final decision computability for the exact restricted-PA
  certificate checker.

  Decoder and structural validation extraction are imported through explicit
  cache boundaries, leaving only the paired hierarchy calculation and final
  Boolean composition in this unit.
*)

From Stdlib Require Import Arith Bool List Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof
  CodedCheckerComputability CodedCheckerStructuralComputability.

From Undecidability.L.Datatypes Require Import LBool LNat LProd LOptions.
From Undecidability.L.Datatypes.List Require Import List_enc.
From Undecidability.L.Tactics Require Import Computable.

Set Implicit Arguments.

Module PABoundedCodedCheckerDecisionComputability.

Import PA.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedCodedDecoderComputability.
Import PABoundedCodedCheckerStructuralComputability.

(** Complete all-occurrence hierarchy rank. *)
Fixpoint rankPairC (phi : formula) : nat * nat :=
  match phi with
  | pEq _ _ | pBot => (0, 0)
  | pImp a b =>
      let '(sa, pa) := rankPairC a in
      let '(sb, pb) := rankPairC b in
      (Nat.max pa sb, Nat.max sa pb)
  | pAnd a b | pOr a b =>
      let '(sa, pa) := rankPairC a in
      let '(sb, pb) := rankPairC b in
      (Nat.max sa sb, Nat.max pa pb)
  | pAll a =>
      let '(_, pa) := rankPairC a in
      (S (Nat.max 1 pa), Nat.max 1 pa)
  | pEx a =>
      let '(sa, _) := rankPairC a in
      (Nat.max 1 sa, S (Nat.max 1 sa))
  end.

Definition sigmaRankC (phi : formula) : nat := fst (rankPairC phi).
Definition piRankC (phi : formula) : nat := snd (rankPairC phi).

Lemma rankPairC_eq : forall phi,
  rankPairC phi = (sigmaRank phi, piRank phi).
Proof.
  induction phi; cbn;
    rewrite ?IHphi, ?IHphi1, ?IHphi2; reflexivity.
Qed.

Lemma rankPairC_spec : forall phi,
  fst (rankPairC phi) = sigmaRank phi /\
  snd (rankPairC phi) = piRank phi.
Proof.
  intro phi. rewrite rankPairC_eq. split; reflexivity.
Qed.

#[local] Instance term_rankPairC : computable rankPairC.
Proof. extract. Qed.
#[local] Instance term_sigmaRankC : computable sigmaRankC.
Proof. extract. Qed.
#[local] Instance term_piRankC : computable piRankC.
Proof. extract. Qed.

#[local] Instance term_sigmaRank : computable sigmaRank.
Proof.
  apply computableExt with (x := sigmaRankC).
  intro phi. unfold sigmaRankC. apply (proj1 (rankPairC_spec phi)).
  typeclasses eauto.
Qed.
#[local] Instance term_piRank : computable piRank.
Proof.
  apply computableExt with (x := piRankC).
  intro phi. unfold piRankC. apply (proj2 (rankPairC_spec phi)).
  typeclasses eauto.
Qed.
#[local] Instance term_quantifierGroups : computable quantifierGroups.
Proof. extract. Qed.

Definition formulaRankC (phi : formula) : nat :=
  let ranks := rankPairC phi in Nat.min (fst ranks) (snd ranks).

#[local] Instance term_formulaRankC : computable formulaRankC.
Proof. extract. Qed.

Definition contextRankStepC (acc : nat) (phi : formula) : nat :=
  Nat.max acc (formulaRankC phi).

#[local] Instance term_contextRankStepC : computable contextRankStepC.
Proof. extract. Qed.

Fixpoint contextRankAccC (acc : nat) (G : list formula) : nat :=
  match G with
  | [] => acc
  | phi :: G' => contextRankAccC (contextRankStepC acc phi) G'
  end.

Definition contextRankC (G : list formula) : nat := contextRankAccC 0 G.

Lemma formulaRankC_eq : forall phi, formulaRankC phi = quantifierGroups phi.
Proof.
  intro phi. unfold formulaRankC, quantifierGroups.
  rewrite rankPairC_eq. reflexivity.
Qed.

Lemma contextRankAccC_eq : forall acc G,
  contextRankAccC acc G = Nat.max acc (contextRank G).
Proof.
  intros acc G. revert acc. induction G as [|phi G IH]; intro acc; cbn.
  - symmetry. apply Nat.max_0_r.
  - unfold contextRankStepC. rewrite IH, formulaRankC_eq, Nat.max_assoc.
    reflexivity.
Qed.

Lemma contextRankC_eq : forall G, contextRankC G = contextRank G.
Proof.
  intro G. unfold contextRankC. rewrite contextRankAccC_eq.
  apply Nat.max_0_l.
Qed.

#[local] Instance term_contextRankAccC : computable contextRankAccC.
Proof. extract. Qed.
#[local] Instance term_contextRankC : computable contextRankC.
Proof. extract. Qed.
#[local] Instance term_contextRank : computable contextRank.
Proof.
  apply computableExt with (x := contextRankC).
  intro G. apply contextRankC_eq.
  typeclasses eauto.
Qed.
#[local] Instance term_rawProofOccurrenceRank :
    computable rawProofOccurrenceRank.
Proof. extract. Qed.
#[local] Instance term_rawProofAllBoundedb : computable rawProofAllBoundedb.
Proof. extract. Qed.

(** Exact computability certificate consumed by the formula layer. *)
#[export] Instance term_checkRestrictedPAProofCode :
    computable checkRestrictedPAProofCode.
Proof. extract. Qed.

End PABoundedCodedCheckerDecisionComputability.
