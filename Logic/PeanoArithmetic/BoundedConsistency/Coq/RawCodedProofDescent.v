(**
  PA-visible descent of recursive raw-proof codes.

  Every recursive child of [rawProofCode] occurs as a field of the enclosing
  polynomial list code.  This elementary fact is indispensable later: it
  lets PA induction on a possibly nonstandard proof-code bound invoke a
  soundness invariant for every premise of the current rule.

  The standard-model inequality is not enough.  We therefore prove directly
  in every raw model of PA that both coordinates lie below a list node, lift
  this to every member of a finite raw list code, and expose all recursive
  child obligations as one transparent PA formula.  Raw-model completeness
  finally closes the universally quantified descent statement into an actual
  object-level PA derivation.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAssignment
  RawCodedSyntaxConstructors RawCodedProofConstructors.

Import ListNotations.

Module PABoundedRawCodedProofDescent.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.

(** ------------------------------------------------------------------
    Polynomial list nodes dominate both coordinates. *)

Lemma raw_proof_zero_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M (raw_zero M) x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_zero_left [] (tVar 0)) e) as hle.
  change (rawLe M (raw_zero M) x) in hle. exact hle.
Qed.

Lemma raw_proof_le_refl : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M x x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_refl [] (tVar 0)) e) as hle.
  change (rawLe M x x) in hle. exact hle.
Qed.

(** Squaring cannot decrease a natural number.  The successor case uses
    [S p * S p = p * S p + S p], while zero is immediate. *)
Lemma raw_proof_self_le_square : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  rawLe M x (raw_mul M x x).
Proof.
  intros M hPA x.
  destruct (raw_assignment_zero_or_successor M hPA x)
    as [-> | [predecessor ->]].
  - apply raw_proof_zero_le. exact hPA.
  - exists (raw_mul M predecessor (raw_succ M predecessor)).
    rewrite (raw_add_comm M hPA
      (raw_succ M predecessor)
      (raw_mul M predecessor (raw_succ M predecessor))).
    symmetry. apply raw_succ_mul. exact hPA.
Qed.

Lemma raw_proof_left_le_sum : forall (M : RawPAModel),
  forall left right : M, rawLe M left (raw_add M left right).
Proof.
  intros M left right. exists right. reflexivity.
Qed.

Lemma raw_proof_right_le_sum : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right : M,
  rawLe M right (raw_add M left right).
Proof.
  intros M hPA left right. exists left.
  apply raw_add_comm. exact hPA.
Qed.

Lemma rawPolynomialPair_left_le_descent : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right : M,
  rawLe M left (rawPolynomialPair M left right).
Proof.
  intros M hPA left right.
  eapply raw_le_trans; [exact hPA | apply raw_proof_left_le_sum |].
  eapply raw_le_trans; [exact hPA | apply raw_proof_self_le_square; exact hPA |].
  apply rawPolynomialPair_lower_square.
Qed.

Lemma rawPolynomialPair_right_le_descent : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right : M,
  rawLe M right (rawPolynomialPair M left right).
Proof.
  intros M hPA left right.
  eapply raw_le_trans; [exact hPA | apply raw_proof_right_le_sum; exact hPA |].
  eapply raw_le_trans; [exact hPA | apply raw_proof_self_le_square; exact hPA |].
  apply rawPolynomialPair_lower_square.
Qed.

Lemma rawListNode_head_lt : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail : M,
  rawLt M head (rawListNode M head tail).
Proof.
  intros M hPA head tail. unfold rawListNode.
  apply raw_lt_succ_of_le; [exact hPA |].
  apply rawPolynomialPair_left_le_descent. exact hPA.
Qed.

Lemma rawListNode_tail_lt : forall (M : RawPAModel),
  RawPASatisfies M -> forall head tail : M,
  rawLt M tail (rawListNode M head tail).
Proof.
  intros M hPA head tail. unfold rawListNode.
  apply raw_lt_succ_of_le; [exact hPA |].
  apply rawPolynomialPair_right_le_descent. exact hPA.
Qed.

(** This is the arbitrary-model analogue of [listCode_member_lt].  The list
    itself is external and finite, but all entries may be nonstandard model
    elements. *)
Lemma rawProofListCode_member_lt : forall (M : RawPAModel),
  RawPASatisfies M -> forall (fields : list M) child,
  In child fields -> rawLt M child (rawListCode M fields).
Proof.
  intros M hPA fields. induction fields as [|head tail IH];
    intros child hchild; cbn [rawListCode] in *.
  - contradiction.
  - destruct hchild as [-> | hchild].
    + apply rawListNode_head_lt. exact hPA.
    + exact (raw_assignment_lt_trans M hPA
        child (rawListCode M tail) (rawListNode M head (rawListCode M tail))
        (IH child hchild)
        (rawListNode_tail_lt M hPA head (rawListCode M tail))).
Qed.

(** ------------------------------------------------------------------
    A transparent formula listing all recursive child obligations. *)

Fixpoint proofAllBelowTermAt (code : term) (children : list term) : formula :=
  match children with
  | [] => pEq tZero tZero
  | child :: tail =>
      pAnd (Formula.ltTermAt child code)
        (proofAllBelowTermAt code tail)
  end.

Lemma raw_sat_proofAllBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code children,
  raw_formula_sat M e (proofAllBelowTermAt code children) <->
  Forall
    (fun child => rawLt M (raw_term_eval M e child)
      (raw_term_eval M e code)) children.
Proof.
  intros M e code children. induction children as [|child tail IH].
  - cbn [proofAllBelowTermAt raw_formula_sat].
    split; intro; [constructor | reflexivity].
  - cbn [proofAllBelowTermAt raw_formula_sat].
    rewrite raw_sat_ltTermAt_iff, IH.
    split.
    + intros [hhead htail]. constructor; assumption.
    + intros hall. inversion hall; subst. split; assumption.
Qed.

Definition proofChildrenBelowCaseTermAt
    (code : term) (fields children : list term) : formula :=
  pImp
    (pEq code (proofCodeFieldsTerm fields))
    (proofAllBelowTermAt code children).

Definition RawProofChildrenBelowCase (M : RawPAModel)
    (code : M) (fields children : list M) : Prop :=
  code = rawListCode M fields ->
  Forall (fun child => rawLt M child code) children.

Arguments RawProofChildrenBelowCase M code fields children
  : clear implicits.

Lemma raw_sat_proofChildrenBelowCaseTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code fields children,
  raw_formula_sat M e
    (proofChildrenBelowCaseTermAt code fields children) <->
  RawProofChildrenBelowCase M
    (raw_term_eval M e code)
    (map (raw_term_eval M e) fields)
    (map (raw_term_eval M e) children).
Proof.
  intros M e code fields children.
  unfold proofChildrenBelowCaseTermAt, RawProofChildrenBelowCase.
  cbn [raw_formula_sat].
  rewrite raw_eval_proofCodeFieldsTerm,
    raw_sat_proofAllBelowTermAt_iff.
  rewrite Forall_map.
  reflexivity.
Qed.

Fixpoint proofFormulaConjunction (cases : list formula) : formula :=
  match cases with
  | [] => pEq tZero tZero
  | head :: tail => pAnd head (proofFormulaConjunction tail)
  end.

(** There are fourteen proof constructors with recursive premises.  Each
    entry records the complete constructor field list and exactly its child
    proof fields. *)
Definition proofRecursiveCasesTerms
    (context a b c t child1 child2 child3 : term)
    : list (list term * list term) :=
  [([Term.numeral 1; context; a; b; child1], [child1]);
   ([Term.numeral 2; context; a; b; child1; child2], [child1; child2]);
   ([Term.numeral 3; context; a; child1], [child1]);
   ([Term.numeral 5; context; a; b; child1; child2], [child1; child2]);
   ([Term.numeral 6; context; a; b; child1], [child1]);
   ([Term.numeral 7; context; a; b; child1], [child1]);
   ([Term.numeral 8; context; a; b; child1], [child1]);
   ([Term.numeral 9; context; a; b; child1], [child1]);
   ([Term.numeral 10; context; a; b; c; child1; child2; child3],
      [child1; child2; child3]);
   ([Term.numeral 11; context; a; child1], [child1]);
   ([Term.numeral 12; context; a; t; child1], [child1]);
   ([Term.numeral 13; context; a; t; child1], [child1]);
   ([Term.numeral 14; context; a; b; child1; child2], [child1; child2]);
   ([Term.numeral 16; context; a; b; c; child1; child2], [child1; child2])].

Definition rawProofRecursiveCases (M : RawPAModel)
    (context a b c t child1 child2 child3 : M)
    : list (list M * list M) :=
  [([rawNumeralValue M 1; context; a; b; child1], [child1]);
   ([rawNumeralValue M 2; context; a; b; child1; child2], [child1; child2]);
   ([rawNumeralValue M 3; context; a; child1], [child1]);
   ([rawNumeralValue M 5; context; a; b; child1; child2], [child1; child2]);
   ([rawNumeralValue M 6; context; a; b; child1], [child1]);
   ([rawNumeralValue M 7; context; a; b; child1], [child1]);
   ([rawNumeralValue M 8; context; a; b; child1], [child1]);
   ([rawNumeralValue M 9; context; a; b; child1], [child1]);
   ([rawNumeralValue M 10; context; a; b; c; child1; child2; child3],
      [child1; child2; child3]);
   ([rawNumeralValue M 11; context; a; child1], [child1]);
   ([rawNumeralValue M 12; context; a; t; child1], [child1]);
   ([rawNumeralValue M 13; context; a; t; child1], [child1]);
   ([rawNumeralValue M 14; context; a; b; child1; child2], [child1; child2]);
   ([rawNumeralValue M 16; context; a; b; c; child1; child2],
      [child1; child2])].

Definition rawProofConstructorDescentTermAt
    (code context a b c t child1 child2 child3 : term) : formula :=
  pAnd
    (rawProofConstructorCodeTermAt
      code context a b c t child1 child2 child3)
    (proofFormulaConjunction
      (map
        (fun entry =>
          proofChildrenBelowCaseTermAt code (fst entry) (snd entry))
        (proofRecursiveCasesTerms
          context a b c t child1 child2 child3))).

Definition RawProofConstructorDescent (M : RawPAModel)
    (code context a b c t child1 child2 child3 : M) : Prop :=
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 /\
  Forall
    (fun entry =>
      RawProofChildrenBelowCase M code (fst entry) (snd entry))
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3).

Arguments RawProofConstructorDescent
  M code context a b c t child1 child2 child3 : clear implicits.

Lemma raw_sat_proofChildrenCasesTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code cases,
  raw_formula_sat M e
    (proofFormulaConjunction
      (map
        (fun entry =>
          proofChildrenBelowCaseTermAt code (fst entry) (snd entry))
        cases)) <->
  Forall
    (fun entry => RawProofChildrenBelowCase M
      (raw_term_eval M e code) (fst entry) (snd entry))
    (map
      (fun entry =>
        (map (raw_term_eval M e) (fst entry),
         map (raw_term_eval M e) (snd entry)))
      cases).
Proof.
  intros M e code cases. induction cases as [|[fields children] tail IH].
  - change (raw_term_eval M e tZero = raw_term_eval M e tZero <->
      Forall
        (fun entry => RawProofChildrenBelowCase M
          (raw_term_eval M e code) (fst entry) (snd entry)) []).
    split; intro; [constructor | reflexivity].
  - change
      ((raw_formula_sat M e
          (proofChildrenBelowCaseTermAt code fields children) /\
        raw_formula_sat M e
          (proofFormulaConjunction
            (map
              (fun entry => proofChildrenBelowCaseTermAt
                code (fst entry) (snd entry)) tail))) <->
       Forall
         (fun entry => RawProofChildrenBelowCase M
           (raw_term_eval M e code) (fst entry) (snd entry))
         ((map (raw_term_eval M e) fields,
           map (raw_term_eval M e) children) ::
          map
            (fun entry =>
              (map (raw_term_eval M e) (fst entry),
               map (raw_term_eval M e) (snd entry))) tail)).
    rewrite raw_sat_proofChildrenBelowCaseTermAt_iff, IH.
    split.
    + intros [hhead htail]. constructor; assumption.
    + intros hall. inversion hall; subst. split; assumption.
Qed.

Lemma raw_eval_proofRecursiveCasesTerms : forall
    (M : RawPAModel) (e : nat -> M)
    context a b c t child1 child2 child3,
  map
    (fun entry =>
      (map (raw_term_eval M e) (fst entry),
       map (raw_term_eval M e) (snd entry)))
    (proofRecursiveCasesTerms
      context a b c t child1 child2 child3) =
  rawProofRecursiveCases M
    (raw_term_eval M e context) (raw_term_eval M e a)
    (raw_term_eval M e b) (raw_term_eval M e c)
    (raw_term_eval M e t) (raw_term_eval M e child1)
    (raw_term_eval M e child2) (raw_term_eval M e child3).
Proof.
  intros. cbn [proofRecursiveCasesTerms rawProofRecursiveCases].
  repeat rewrite raw_term_eval_numeral. reflexivity.
Qed.

Theorem raw_sat_rawProofConstructorDescentTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    code context a b c t child1 child2 child3,
  raw_formula_sat M e
    (rawProofConstructorDescentTermAt
      code context a b c t child1 child2 child3) <->
  RawProofConstructorDescent M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e t)
    (raw_term_eval M e child1) (raw_term_eval M e child2)
    (raw_term_eval M e child3).
Proof.
  intros. unfold rawProofConstructorDescentTermAt,
    RawProofConstructorDescent.
  cbn [raw_formula_sat].
  rewrite raw_sat_rawProofConstructorCodeTermAt_iff,
    raw_sat_proofChildrenCasesTermAt_iff,
    raw_eval_proofRecursiveCasesTerms.
  reflexivity.
Qed.

Lemma raw_proofChildrenBelowCase_of_members : forall
    (M : RawPAModel), RawPASatisfies M -> forall fields children code,
  (forall child, In child children -> In child fields) ->
  RawProofChildrenBelowCase M code fields children.
Proof.
  intros M hPA fields children code hmembers hcode.
  subst code. apply Forall_forall. intros child hchild.
  apply rawProofListCode_member_lt; [exact hPA |].
  exact (hmembers child hchild).
Qed.

(** The constructor equation alone forces all recursive descent clauses; no
    well-formedness or standardness assumption on the remaining fields is
    needed. *)
Theorem raw_proofConstructorCode_descent : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall code context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  RawProofConstructorDescent M
    code context a b c t child1 child2 child3.
Proof.
  intros M hPA code context a b c t child1 child2 child3 hconstructor.
  split; [exact hconstructor |].
  apply Forall_forall. intros [fields children] hentry.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: apply (raw_proofChildrenBelowCase_of_members M hPA); cbn; tauto.
Qed.

(** ------------------------------------------------------------------
    Object-level closure. *)

Definition rawProofConstructorDescentFormula : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pImp
      (rawProofConstructorCodeTermAt
        (tVar 8) (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (rawProofConstructorDescentTermAt
        (tVar 8) (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))))))))))).

Theorem rawProofConstructorDescentFormula_sentence :
  Formula.Sentence rawProofConstructorDescentFormula.
Proof.
  intros k hfree. unfold rawProofConstructorDescentFormula in hfree.
  cbn in hfree. lia.
Qed.

Theorem rawProofConstructorDescentFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e rawProofConstructorDescentFormula.
Proof.
  intros M hPA e.
  unfold rawProofConstructorDescentFormula.
  cbn [raw_formula_sat].
  intros code context a b c t child1 child2 child3 hconstructor.
  apply (proj2 (raw_sat_rawProofConstructorDescentTermAt_iff M
    (scons M child3 (scons M child2 (scons M child1
      (scons M t (scons M c (scons M b (scons M a
        (scons M context (scons M code e)))))))))
    (tVar 8) (tVar 7) (tVar 6) (tVar 5) (tVar 4)
    (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
  cbn [raw_term_eval scons].
  pose proof (proj1 (raw_sat_rawProofConstructorCodeTermAt_iff M
    (scons M child3 (scons M child2 (scons M child1
      (scons M t (scons M c (scons M b (scons M a
        (scons M context (scons M code e)))))))))
    (tVar 8) (tVar 7) (tVar 6) (tVar 5) (tVar 4)
    (tVar 3) (tVar 2) (tVar 1) (tVar 0)) hconstructor) as hraw.
  cbn [raw_term_eval scons] in hraw.
  exact (raw_proofConstructorCode_descent M hPA
    code context a b c t child1 child2 child3 hraw).
Qed.

Theorem PA_proves_rawProofConstructorDescentFormula :
  Formula.BProv Formula.Ax_s [] rawProofConstructorDescentFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact rawProofConstructorDescentFormula_sentence.
  - exact rawProofConstructorDescentFormula_raw_valid.
Qed.

End PABoundedRawCodedProofDescent.
