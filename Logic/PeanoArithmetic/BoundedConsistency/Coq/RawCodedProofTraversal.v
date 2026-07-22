(**
  A model-internal syntax traversal for arbitrary raw proof codes.

  A carrier element of a nonstandard model of PA cannot be decoded into a
  Rocq [RawProof].  Instead, a beta table marks exactly the proof codes that
  a certificate intends to expose.  Every marked code below the certificate
  bound must have an arithmetic constructor occurrence, and every recursive
  premise named by *any* occurrence of that constructor is marked at a
  strictly smaller code.

  Quantifying over every occurrence is intentional.  The existential half
  of a local row exposes one constructor tuple.  The universal half closes
  every tuple that denotes the same code.  Consequently two independently
  chosen support certificates can be compared without first proving a large
  seventeen-way constructor-decoding theorem: a constructor occurrence from
  either side is closed by both certificates.

  Nothing in this file asserts that every model element is a proof code.
  The public domain [RawProofSyntaxRealizable] is itself an independently
  arithmetized formula saying that suitable support data exist.  This is the
  honest totality boundary needed for later nonstandard proof soundness.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAssignment
  RawCodedSyntaxConstructors RawCodedProofConstructors
  RawCodedProofDescent.

Import ListNotations.

Module PABoundedRawCodedProofTraversal.

Import PA.
Import PAListRepresentability.
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
Import PABoundedRawCodedProofDescent.

(** ------------------------------------------------------------------
    Support flags. *)

Definition rawProofCodeSupported (M : RawPAModel)
    (supportCode supportStep code : M) : Prop :=
  RawCodedAssignmentLookup M supportCode supportStep code
    (rawNumeralValue M 1).

Arguments rawProofCodeSupported M supportCode supportStep code
  : clear implicits.

Definition proofCodeSupportedTermAt
    (supportCode supportStep code : term) : formula :=
  codedAssignmentLookupTermAt supportCode supportStep code
    (Term.numeral 1).

Lemma raw_sat_proofCodeSupportedTermAt_iff : forall
    (M : RawPAModel) e supportCode supportStep code,
  raw_formula_sat M e
    (proofCodeSupportedTermAt supportCode supportStep code) <->
  rawProofCodeSupported M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e code).
Proof.
  intros. unfold proofCodeSupportedTermAt, rawProofCodeSupported.
  rewrite raw_sat_codedAssignmentLookupTermAt_iff,
    raw_term_eval_numeral.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Closing all recursive children of one constructor occurrence. *)

Fixpoint proofAllChildrenClosedTermAt
    (code supportCode supportStep : term) (children : list term) : formula :=
  match children with
  | [] => pEq tZero tZero
  | child :: tail =>
      pAnd
        (pAnd
          (proofCodeSupportedTermAt supportCode supportStep child)
          (Formula.ltTermAt child code))
        (proofAllChildrenClosedTermAt
          code supportCode supportStep tail)
  end.

Lemma raw_sat_proofAllChildrenClosedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code supportCode supportStep children,
  raw_formula_sat M e
    (proofAllChildrenClosedTermAt
      code supportCode supportStep children) <->
  Forall
    (fun child =>
      rawProofCodeSupported M
        (raw_term_eval M e supportCode)
        (raw_term_eval M e supportStep)
        (raw_term_eval M e child) /\
      rawLt M (raw_term_eval M e child) (raw_term_eval M e code))
    children.
Proof.
  intros M e code supportCode supportStep children.
  induction children as [|child tail IH].
  - cbn [proofAllChildrenClosedTermAt raw_formula_sat].
    split; intro; [constructor | reflexivity].
  - cbn [proofAllChildrenClosedTermAt raw_formula_sat].
    rewrite raw_sat_proofCodeSupportedTermAt_iff,
      raw_sat_ltTermAt_iff, IH.
    split.
    + intros [[hsupported hbelow] htail].
      constructor; [split; assumption | assumption].
    + intros hall. inversion hall; subst. split; assumption.
Qed.

Definition proofChildrenClosedCaseTermAt
    (code supportCode supportStep : term)
    (fields children : list term) : formula :=
  pImp
    (pEq code (proofCodeFieldsTerm fields))
    (proofAllChildrenClosedTermAt
      code supportCode supportStep children).

Definition RawProofChildrenClosedCase (M : RawPAModel)
    (code supportCode supportStep : M)
    (fields children : list M) : Prop :=
  code = rawListCode M fields ->
  Forall
    (fun child =>
      rawProofCodeSupported M supportCode supportStep child /\
      rawLt M child code)
    children.

Arguments RawProofChildrenClosedCase
  M code supportCode supportStep fields children : clear implicits.

Lemma raw_sat_proofChildrenClosedCaseTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    code supportCode supportStep fields children,
  raw_formula_sat M e
    (proofChildrenClosedCaseTermAt
      code supportCode supportStep fields children) <->
  RawProofChildrenClosedCase M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (map (raw_term_eval M e) fields)
    (map (raw_term_eval M e) children).
Proof.
  intros M e code supportCode supportStep fields children.
  unfold proofChildrenClosedCaseTermAt, RawProofChildrenClosedCase.
  cbn [raw_formula_sat].
  rewrite raw_eval_proofCodeFieldsTerm,
    raw_sat_proofAllChildrenClosedTermAt_iff,
    Forall_map.
  reflexivity.
Qed.

Fixpoint proofChildrenCasesClosedTermAt
    (code supportCode supportStep : term)
    (cases : list (list term * list term)) : formula :=
  match cases with
  | [] => pEq tZero tZero
  | (fields, children) :: tail =>
      pAnd
        (proofChildrenClosedCaseTermAt
          code supportCode supportStep fields children)
        (proofChildrenCasesClosedTermAt
          code supportCode supportStep tail)
  end.

Lemma raw_sat_proofChildrenCasesClosedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code supportCode supportStep cases,
  raw_formula_sat M e
    (proofChildrenCasesClosedTermAt
      code supportCode supportStep cases) <->
  Forall
    (fun entry => RawProofChildrenClosedCase M
      (raw_term_eval M e code)
      (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
      (fst entry) (snd entry))
    (map
      (fun entry =>
        (map (raw_term_eval M e) (fst entry),
         map (raw_term_eval M e) (snd entry)))
      cases).
Proof.
  intros M e code supportCode supportStep cases.
  induction cases as [|[fields children] tail IH].
  - change (raw_term_eval M e tZero = raw_term_eval M e tZero <->
      Forall
        (fun entry => RawProofChildrenClosedCase M
          (raw_term_eval M e code)
          (raw_term_eval M e supportCode)
          (raw_term_eval M e supportStep)
          (fst entry) (snd entry)) []).
    split; intro; [constructor | reflexivity].
  - change
      ((raw_formula_sat M e
          (proofChildrenClosedCaseTermAt
            code supportCode supportStep fields children) /\
        raw_formula_sat M e
          (proofChildrenCasesClosedTermAt
            code supportCode supportStep tail)) <->
       Forall
         (fun entry => RawProofChildrenClosedCase M
           (raw_term_eval M e code)
           (raw_term_eval M e supportCode)
           (raw_term_eval M e supportStep)
           (fst entry) (snd entry))
         ((map (raw_term_eval M e) fields,
           map (raw_term_eval M e) children) ::
          map
            (fun entry =>
              (map (raw_term_eval M e) (fst entry),
               map (raw_term_eval M e) (snd entry))) tail)).
    rewrite raw_sat_proofChildrenClosedCaseTermAt_iff, IH.
    split.
    + intros [hhead htail]. constructor; assumption.
    + intros hall. inversion hall; subst. split; assumption.
Qed.

(** A closed occurrence carries the descent theorem itself and the support
    obligation for precisely the same fourteen recursive constructor cases.
    The two conjuncts deliberately share [rawProofRecursiveCases]. *)
Definition proofConstructorClosedTermAt
    (code supportCode supportStep context a b c t
      child1 child2 child3 : term) : formula :=
  pAnd
    (rawProofConstructorDescentTermAt
      code context a b c t child1 child2 child3)
    (proofChildrenCasesClosedTermAt code supportCode supportStep
      (proofRecursiveCasesTerms
        context a b c t child1 child2 child3)).

Definition RawProofConstructorClosed (M : RawPAModel)
    (code supportCode supportStep context a b c t
      child1 child2 child3 : M) : Prop :=
  RawProofConstructorDescent M
    code context a b c t child1 child2 child3 /\
  Forall
    (fun entry => RawProofChildrenClosedCase M
      code supportCode supportStep (fst entry) (snd entry))
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3).

Arguments RawProofConstructorClosed
  M code supportCode supportStep context a b c t
    child1 child2 child3 : clear implicits.

Lemma raw_sat_proofConstructorClosedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    code supportCode supportStep context a b c t child1 child2 child3,
  raw_formula_sat M e
    (proofConstructorClosedTermAt code supportCode supportStep
      context a b c t child1 child2 child3) <->
  RawProofConstructorClosed M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e context) (raw_term_eval M e a)
    (raw_term_eval M e b) (raw_term_eval M e c)
    (raw_term_eval M e t) (raw_term_eval M e child1)
    (raw_term_eval M e child2) (raw_term_eval M e child3).
Proof.
  intros. unfold proofConstructorClosedTermAt,
    RawProofConstructorClosed.
  cbn [raw_formula_sat].
  rewrite raw_sat_rawProofConstructorDescentTermAt_iff,
    raw_sat_proofChildrenCasesClosedTermAt_iff,
    raw_eval_proofRecursiveCasesTerms.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    A local proof-syntax row.

    Eight witnesses expose the complete constructor payload.  The universal
    block closes every alternative payload tuple denoting the same code; this
    is what makes the later cross-certificate lemmas table-independent. *)

Definition proofTraversalEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

Definition proofTraversalAll8 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))).

Lemma raw_proofTraversal_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_proofTraversal_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_proofTraversal_eval_liftTerm_eight : forall
    (M : RawPAModel) a b c d f g h i (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i e))))))))
    (liftTerm 8 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro j.
  replace (j + 8) with (S (S (S (S (S (S (S (S j)))))))) by lia.
  reflexivity.
Qed.

Definition proofSyntaxStepTermAt
    (code supportCode supportStep : term) : formula :=
  pAnd
    (proofTraversalEx8
      (rawProofConstructorCodeTermAt
        (liftTerm 8 code)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0)))
    (proofTraversalAll8
      (pImp
        (rawProofConstructorCodeTermAt
          (liftTerm 8 code)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (proofConstructorClosedTermAt
          (liftTerm 8 code) (liftTerm 8 supportCode)
          (liftTerm 8 supportStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Definition RawProofSyntaxStep (M : RawPAModel)
    (code supportCode supportStep : M) : Prop :=
  (exists context a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      code context a b c t child1 child2 child3) /\
  (forall context a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      code context a b c t child1 child2 child3 ->
    RawProofConstructorClosed M
      code supportCode supportStep
      context a b c t child1 child2 child3).

Arguments RawProofSyntaxStep M code supportCode supportStep
  : clear implicits.

Lemma raw_sat_proofSyntaxStepTermAt_iff : forall
    (M : RawPAModel) e code supportCode supportStep,
  raw_formula_sat M e
    (proofSyntaxStepTermAt code supportCode supportStep) <->
  RawProofSyntaxStep M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e code supportCode supportStep.
  unfold proofSyntaxStepTermAt, RawProofSyntaxStep,
    proofTraversalEx8, proofTraversalAll8.
  cbn [raw_formula_sat].
  split.
  - intros [hexists hall]. split.
    + destruct hexists as
        [context [a [b [c [t [child1 [child2 [child3 hcode]]]]]]]].
      exists context, a, b, c, t, child1, child2, child3.
      apply (proj1 (raw_sat_rawProofConstructorCodeTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M context e))))))))
        (liftTerm 8 code)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hcode.
      rewrite raw_proofTraversal_eval_liftTerm_eight in hcode.
      cbn [raw_term_eval scons] in hcode. exact hcode.
    + intros context a b c t child1 child2 child3 hcode.
      assert (hcodeSat : raw_formula_sat M
          (scons M child3 (scons M child2 (scons M child1
            (scons M t (scons M c (scons M b (scons M a
              (scons M context e))))))))
          (rawProofConstructorCodeTermAt
            (liftTerm 8 code)
            (tVar 7) (tVar 6) (tVar 5) (tVar 4)
            (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
      {
        apply (proj2 (raw_sat_rawProofConstructorCodeTermAt_iff M
          (scons M child3 (scons M child2 (scons M child1
            (scons M t (scons M c (scons M b (scons M a
              (scons M context e))))))))
          (liftTerm 8 code)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
        rewrite raw_proofTraversal_eval_liftTerm_eight.
        cbn [raw_term_eval scons]. exact hcode.
      }
      pose proof
        (hall context a b c t child1 child2 child3 hcodeSat) as hclosed.
      apply (proj1 (raw_sat_proofConstructorClosedTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M context e))))))))
        (liftTerm 8 code) (liftTerm 8 supportCode)
        (liftTerm 8 supportStep)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hclosed.
      rewrite !raw_proofTraversal_eval_liftTerm_eight in hclosed.
      cbn [raw_term_eval scons] in hclosed. exact hclosed.
  - intros [hexists hall]. split.
    + destruct hexists as
        [context [a [b [c [t [child1 [child2 [child3 hcode]]]]]]]].
      exists context, a, b, c, t, child1, child2, child3.
      apply (proj2 (raw_sat_rawProofConstructorCodeTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M context e))))))))
        (liftTerm 8 code)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
      rewrite raw_proofTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hcode.
    + intros context a b c t child1 child2 child3 hcodeSat.
      pose proof (proj1 (raw_sat_rawProofConstructorCodeTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M context e))))))))
        (liftTerm 8 code)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0)) hcodeSat) as hcode.
      rewrite raw_proofTraversal_eval_liftTerm_eight in hcode.
      cbn [raw_term_eval scons] in hcode.
      pose proof
        (hall context a b c t child1 child2 child3 hcode) as hclosed.
      apply (proj2 (raw_sat_proofConstructorClosedTermAt_iff M
        (scons M child3 (scons M child2 (scons M child1
          (scons M t (scons M c (scons M b (scons M a
            (scons M context e))))))))
        (liftTerm 8 code) (liftTerm 8 supportCode)
        (liftTerm 8 supportStep)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
      rewrite !raw_proofTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hclosed.
Qed.

(** ------------------------------------------------------------------
    Global traversal and the public honest-syntax domain. *)

Definition RawProofSyntaxTraversal (M : RawPAModel)
    (bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code,
    rawLt M code bound ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawProofSyntaxStep M code supportCode supportStep.

Arguments RawProofSyntaxTraversal M bound supportCode supportStep
  : clear implicits.

Definition proofSyntaxTraversalTermAt
    (bound supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (proofCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (proofSyntaxStepTermAt
            (tVar 0) (liftTerm 1 supportCode) (liftTerm 1 supportStep))))).

Lemma raw_sat_proofSyntaxTraversalTermAt_iff : forall
    (M : RawPAModel) e bound supportCode supportStep,
  raw_formula_sat M e
    (proofSyntaxTraversalTermAt bound supportCode supportStep) <->
  RawProofSyntaxTraversal M
    (raw_term_eval M e bound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound supportCode supportStep.
  unfold proofSyntaxTraversalTermAt, RawProofSyntaxTraversal.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  split.
  - intros [hdefined hrows]. split; [exact hdefined |].
    intros code hcode hsupported.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_proofTraversal_eval_liftTerm_one.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportedSat : raw_formula_sat M (scons M code e)
        (proofCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_proofCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_proofTraversal_eval_liftTerm_one.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    pose proof (hrows code hltSat hsupportedSat) as hstepSat.
    apply (proj1 (raw_sat_proofSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))) in hstepSat.
    rewrite !raw_proofTraversal_eval_liftTerm_one in hstepSat.
    cbn [raw_term_eval scons] in hstepSat. exact hstepSat.
  - intros [hdefined hrows]. split; [exact hdefined |].
    intros code hltSat hsupportedSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_proofTraversal_eval_liftTerm_one in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_proofCodeSupportedTermAt_iff M _ _ _ _)
      hsupportedSat) as hsupported.
    rewrite !raw_proofTraversal_eval_liftTerm_one in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    apply (proj2 (raw_sat_proofSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))).
    rewrite !raw_proofTraversal_eval_liftTerm_one.
    cbn [raw_term_eval scons].
    exact (hrows code hcode hsupported).
Qed.

Definition RawProofSyntaxCertificateWithSupport (M : RawPAModel)
    (root supportCode supportStep : M) : Prop :=
  RawProofSyntaxTraversal M (raw_succ M root) supportCode supportStep /\
  rawProofCodeSupported M supportCode supportStep root.

Arguments RawProofSyntaxCertificateWithSupport
  M root supportCode supportStep : clear implicits.

Definition proofSyntaxCertificateWithSupportTermAt
    (root supportCode supportStep : term) : formula :=
  pAnd
    (proofSyntaxTraversalTermAt (tSucc root) supportCode supportStep)
    (proofCodeSupportedTermAt supportCode supportStep root).

Lemma raw_sat_proofSyntaxCertificateWithSupportTermAt_iff : forall
    (M : RawPAModel) e root supportCode supportStep,
  raw_formula_sat M e
    (proofSyntaxCertificateWithSupportTermAt
      root supportCode supportStep) <->
  RawProofSyntaxCertificateWithSupport M
    (raw_term_eval M e root)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold proofSyntaxCertificateWithSupportTermAt,
    RawProofSyntaxCertificateWithSupport.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofSyntaxTraversalTermAt_iff,
    raw_sat_proofCodeSupportedTermAt_iff.
  reflexivity.
Qed.

Definition proofSyntaxRealizableTermAt (root : term) : formula :=
  pEx (pEx
    (proofSyntaxCertificateWithSupportTermAt
      (liftTerm 2 root) (tVar 1) (tVar 0))).

Definition RawProofSyntaxRealizable (M : RawPAModel) (root : M) : Prop :=
  exists supportCode supportStep : M,
    RawProofSyntaxCertificateWithSupport M root supportCode supportStep.

Arguments RawProofSyntaxRealizable M root : clear implicits.

Lemma raw_sat_proofSyntaxRealizableTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (proofSyntaxRealizableTermAt root) <->
  RawProofSyntaxRealizable M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold proofSyntaxRealizableTermAt, RawProofSyntaxRealizable.
  cbn [raw_formula_sat]. split.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj1
      (raw_sat_proofSyntaxCertificateWithSupportTermAt_iff M
        (scons M supportStep (scons M supportCode e))
        (liftTerm 2 root) (tVar 1) (tVar 0))) in hsyntax.
    rewrite raw_proofTraversal_eval_liftTerm_two in hsyntax.
    cbn [raw_term_eval scons] in hsyntax. exact hsyntax.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj2
      (raw_sat_proofSyntaxCertificateWithSupportTermAt_iff M
        (scons M supportStep (scons M supportCode e))
        (liftTerm 2 root) (tVar 1) (tVar 0))).
    rewrite raw_proofTraversal_eval_liftTerm_two.
    cbn [raw_term_eval scons]. exact hsyntax.
Qed.

(** ------------------------------------------------------------------
    Structural consequences of a traversal. *)

Lemma raw_proofSyntaxStep_constructor_exists : forall
    (M : RawPAModel) code supportCode supportStep,
  RawProofSyntaxStep M code supportCode supportStep ->
  exists context a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      code context a b c t child1 child2 child3.
Proof.
  intros M code supportCode supportStep [hexists _]. exact hexists.
Qed.

Lemma raw_proofSyntaxStep_closes_constructor : forall
    (M : RawPAModel) code supportCode supportStep,
  RawProofSyntaxStep M code supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  RawProofConstructorClosed M
    code supportCode supportStep
    context a b c t child1 child2 child3.
Proof.
  intros M code supportCode supportStep [_ hall]. exact hall.
Qed.

Corollary raw_proofSyntaxStep_constructor_descent : forall
    (M : RawPAModel) code supportCode supportStep,
  RawProofSyntaxStep M code supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  RawProofConstructorDescent M
    code context a b c t child1 child2 child3.
Proof.
  intros M code supportCode supportStep hstep
    context a b c t child1 child2 child3 hconstructor.
  exact (proj1 (raw_proofSyntaxStep_closes_constructor M
    code supportCode supportStep hstep
    context a b c t child1 child2 child3 hconstructor)).
Qed.

(** This generic eliminator is intentionally phrased using membership in
    [rawProofRecursiveCases].  It therefore covers all fourteen recursive
    constructors, including the three-premise disjunction eliminator, with
    no duplicated case split in downstream files. *)
Lemma raw_proofConstructorClosed_recursive_child : forall
    (M : RawPAModel)
    code supportCode supportStep context a b c t child1 child2 child3,
  RawProofConstructorClosed M
    code supportCode supportStep
    context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  code = rawListCode M fields ->
  forall child, In child children ->
    rawProofCodeSupported M supportCode supportStep child /\
    rawLt M child code.
Proof.
  intros M code supportCode supportStep context a b c t
    child1 child2 child3 [_ hcases]
    fields children hentry hcode child hchild.
  pose proof (proj1 (@Forall_forall (list M * list M)
    (fun entry => RawProofChildrenClosedCase M
      code supportCode supportStep (fst entry) (snd entry))
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3))
    hcases (fields, children) hentry) as hcase.
  cbn in hcase. specialize (hcase hcode).
  exact (proj1 (@Forall_forall M
    (fun child =>
      rawProofCodeSupported M supportCode supportStep child /\
      rawLt M child code) children)
    hcase child hchild).
Qed.

Lemma raw_proofSyntaxTraversal_supported_step : forall
    (M : RawPAModel) bound supportCode supportStep,
  RawProofSyntaxTraversal M bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  RawProofSyntaxStep M code supportCode supportStep.
Proof.
  intros M bound supportCode supportStep [_ hrows]. exact hrows.
Qed.

(** Every marked row has a constructor occurrence that is already closed.
    Thus later soundness arguments can destruct one witness tuple and use it
    both for rule analysis and for recursive-premise induction hypotheses. *)
Theorem raw_proofSyntaxTraversal_supported_occurrence : forall
    (M : RawPAModel) bound supportCode supportStep,
  RawProofSyntaxTraversal M bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  exists context a b c t child1 child2 child3 : M,
    RawProofConstructorClosed M
      code supportCode supportStep
      context a b c t child1 child2 child3.
Proof.
  intros M bound supportCode supportStep htraversal
    code hcode hsupported.
  pose proof (raw_proofSyntaxTraversal_supported_step M
    bound supportCode supportStep htraversal
    code hcode hsupported) as hstep.
  destruct (raw_proofSyntaxStep_constructor_exists M
    code supportCode supportStep hstep) as
    [context [a [b [c [t [child1 [child2 [child3 hconstructor]]]]]]]].
  exists context, a, b, c, t, child1, child2, child3.
  exact (raw_proofSyntaxStep_closes_constructor M
    code supportCode supportStep hstep
    context a b c t child1 child2 child3 hconstructor).
Qed.

Theorem raw_proofSyntaxTraversal_closes_constructor : forall
    (M : RawPAModel) bound supportCode supportStep,
  RawProofSyntaxTraversal M bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  RawProofConstructorClosed M
    code supportCode supportStep
    context a b c t child1 child2 child3.
Proof.
  intros M bound supportCode supportStep htraversal
    code hcode hsupported.
  apply (raw_proofSyntaxStep_closes_constructor M
    code supportCode supportStep).
  exact (raw_proofSyntaxTraversal_supported_step M
    bound supportCode supportStep htraversal code hcode hsupported).
Qed.

Corollary raw_proofSyntaxTraversal_recursive_child : forall
    (M : RawPAModel) bound supportCode supportStep,
  RawProofSyntaxTraversal M bound supportCode supportStep ->
  forall code,
  rawLt M code bound ->
  rawProofCodeSupported M supportCode supportStep code ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    code context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  code = rawListCode M fields ->
  forall child, In child children ->
    rawProofCodeSupported M supportCode supportStep child /\
    rawLt M child code.
Proof.
  intros M bound supportCode supportStep htraversal
    code hcode hsupported context a b c t child1 child2 child3
    hconstructor fields children hentry hfields child hchild.
  eapply raw_proofConstructorClosed_recursive_child;
    [| exact hentry | exact hfields | exact hchild].
  exact (raw_proofSyntaxTraversal_closes_constructor M
    bound supportCode supportStep htraversal code hcode hsupported
    context a b c t child1 child2 child3 hconstructor).
Qed.

(** Restriction changes only the arithmetic bound.  No support table is
    decoded or rebuilt, so it is valid just as well at nonstandard bounds. *)
Theorem raw_proofSyntaxTraversal_weaken : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall large small supportCode supportStep,
  RawProofSyntaxTraversal M large supportCode supportStep ->
  rawLe M small large ->
  RawProofSyntaxTraversal M small supportCode supportStep.
Proof.
  intros M hPA large small supportCode supportStep
    [hdefined hrows] hsmall.
  split.
  - intros index hindex. apply hdefined.
    exact (raw_lt_le_trans_pair M hPA index small large hindex hsmall).
  - intros code hcode hsupported. apply hrows; [| exact hsupported].
    exact (raw_lt_le_trans_pair M hPA code small large hcode hsmall).
Qed.

Theorem raw_proofSyntaxCertificate_root_occurrence : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root supportCode supportStep,
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep ->
  exists context a b c t child1 child2 child3 : M,
    RawProofConstructorClosed M
      root supportCode supportStep
      context a b c t child1 child2 child3.
Proof.
  intros M hPA root supportCode supportStep [htraversal hroot].
  exact (raw_proofSyntaxTraversal_supported_occurrence M
    (raw_succ M root) supportCode supportStep htraversal root
    (raw_assignment_lt_self_succ M hPA root) hroot).
Qed.

(** A recursive premise is itself certified by the same beta support table,
    restricted to its successor prefix.  The strict inequality supplied by
    constructor descent is precisely what justifies that restriction. *)
Theorem raw_proofSyntaxCertificate_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root supportCode supportStep,
  RawProofSyntaxCertificateWithSupport M root supportCode supportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
    RawProofSyntaxCertificateWithSupport M
      child supportCode supportStep /\
    rawLt M child root.
Proof.
  intros M hPA root supportCode supportStep
    [htraversal hroot]
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_proofSyntaxTraversal_recursive_child M
    (raw_succ M root) supportCode supportStep htraversal
    root (raw_assignment_lt_self_succ M hPA root) hroot
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildSupport hchildBelow].
  split; [split | exact hchildBelow].
  - apply (raw_proofSyntaxTraversal_weaken M hPA
      (raw_succ M root) (raw_succ M child)
      supportCode supportStep htraversal).
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root)
        (raw_assignment_lt_self_succ M hPA root)).
  - exact hchildSupport.
Qed.

(** ------------------------------------------------------------------
    Cross-certificate closure.

    The constructor tuple below may originate from either certificate (or
    from a third arithmetic proof).  Because a local row universally closes
    every occurrence, both certificates validate exactly the same recursive
    child.  No uniqueness or standard decoding assumption is involved. *)

Theorem raw_proofSyntaxCertificates_cross_constructor : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root leftSupportCode leftSupportStep
    rightSupportCode rightSupportStep,
  RawProofSyntaxCertificateWithSupport M
    root leftSupportCode leftSupportStep ->
  RawProofSyntaxCertificateWithSupport M
    root rightSupportCode rightSupportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  RawProofConstructorClosed M
      root leftSupportCode leftSupportStep
      context a b c t child1 child2 child3 /\
  RawProofConstructorClosed M
      root rightSupportCode rightSupportStep
      context a b c t child1 child2 child3.
Proof.
  intros M hPA root leftSupportCode leftSupportStep
    rightSupportCode rightSupportStep
    [hleftTraversal hleftRoot] [hrightTraversal hrightRoot]
    context a b c t child1 child2 child3 hconstructor.
  split.
  - exact (raw_proofSyntaxTraversal_closes_constructor M
      (raw_succ M root) leftSupportCode leftSupportStep
      hleftTraversal root (raw_assignment_lt_self_succ M hPA root)
      hleftRoot context a b c t child1 child2 child3 hconstructor).
  - exact (raw_proofSyntaxTraversal_closes_constructor M
      (raw_succ M root) rightSupportCode rightSupportStep
      hrightTraversal root (raw_assignment_lt_self_succ M hPA root)
      hrightRoot context a b c t child1 child2 child3 hconstructor).
Qed.

Theorem raw_proofSyntaxCertificates_cross_recursive_child : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root leftSupportCode leftSupportStep
    rightSupportCode rightSupportStep,
  RawProofSyntaxCertificateWithSupport M
    root leftSupportCode leftSupportStep ->
  RawProofSyntaxCertificateWithSupport M
    root rightSupportCode rightSupportStep ->
  forall context a b c t child1 child2 child3,
  RawProofConstructorCode M
    root context a b c t child1 child2 child3 ->
  forall fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      context a b c t child1 child2 child3) ->
  root = rawListCode M fields ->
  forall child, In child children ->
    RawProofSyntaxCertificateWithSupport M
      child leftSupportCode leftSupportStep /\
    RawProofSyntaxCertificateWithSupport M
      child rightSupportCode rightSupportStep /\
    rawLt M child root.
Proof.
  intros M hPA root leftSupportCode leftSupportStep
    rightSupportCode rightSupportStep hleft hright
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild.
  destruct (raw_proofSyntaxCertificate_recursive_child M hPA
    root leftSupportCode leftSupportStep hleft
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hleftChild hbelow].
  destruct (raw_proofSyntaxCertificate_recursive_child M hPA
    root rightSupportCode rightSupportStep hright
    context a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hrightChild _].
  exact (conj hleftChild (conj hrightChild hbelow)).
Qed.

(** ------------------------------------------------------------------
    Constructor occurrence totality on the arithmetized syntax domain. *)

Definition proofConstructorOccurrenceTermAt (code : term) : formula :=
  proofTraversalEx8
    (rawProofConstructorCodeTermAt
      (liftTerm 8 code)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawProofConstructorOccurrence (M : RawPAModel)
    (code : M) : Prop :=
  exists context a b c t child1 child2 child3 : M,
    RawProofConstructorCode M
      code context a b c t child1 child2 child3.

Arguments RawProofConstructorOccurrence M code : clear implicits.

Lemma raw_sat_proofConstructorOccurrenceTermAt_iff : forall
    (M : RawPAModel) e code,
  raw_formula_sat M e (proofConstructorOccurrenceTermAt code) <->
  RawProofConstructorOccurrence M (raw_term_eval M e code).
Proof.
  intros M e code.
  unfold proofConstructorOccurrenceTermAt,
    RawProofConstructorOccurrence, proofTraversalEx8.
  cbn [raw_formula_sat]. split.
  - intros [context [a [b [c [t [child1 [child2 [child3 hcode]]]]]]]].
    exists context, a, b, c, t, child1, child2, child3.
    apply (proj1 (raw_sat_rawProofConstructorCodeTermAt_iff M
      (scons M child3 (scons M child2 (scons M child1
        (scons M t (scons M c (scons M b (scons M a
          (scons M context e))))))))
      (liftTerm 8 code)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hcode.
    rewrite raw_proofTraversal_eval_liftTerm_eight in hcode.
    cbn [raw_term_eval scons] in hcode. exact hcode.
  - intros [context [a [b [c [t [child1 [child2 [child3 hcode]]]]]]]].
    exists context, a, b, c, t, child1, child2, child3.
    apply (proj2 (raw_sat_rawProofConstructorCodeTermAt_iff M
      (scons M child3 (scons M child2 (scons M child1
        (scons M t (scons M c (scons M b (scons M a
          (scons M context e))))))))
      (liftTerm 8 code)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    rewrite raw_proofTraversal_eval_liftTerm_eight.
    cbn [raw_term_eval scons]. exact hcode.
Qed.

Definition RawProofConstructorOccurrenceTotalityFor
    (M : RawPAModel) (domain : M -> Prop) : Prop :=
  forall code, domain code -> RawProofConstructorOccurrence M code.

Arguments RawProofConstructorOccurrenceTotalityFor M domain
  : clear implicits.

Theorem raw_proofConstructorOccurrence_totality_for_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawProofConstructorOccurrenceTotalityFor M
    (RawProofSyntaxRealizable M).
Proof.
  intros M hPA root [supportCode [supportStep hsyntax]].
  destruct (raw_proofSyntaxCertificate_root_occurrence M hPA
    root supportCode supportStep hsyntax) as
    [context [a [b [c [t [child1 [child2 [child3 hclosed]]]]]]]].
  exists context, a, b, c, t, child1, child2, child3.
  exact (proj1 (proj1 hclosed)).
Qed.

(** The final sentence states only the justified totality theorem:
    constructor exposure is total on [proofSyntaxRealizableTermAt], not on
    all carrier elements. *)
Definition proofSyntaxOccurrenceTotalityFormula : formula :=
  pAll
    (pImp
      (proofSyntaxRealizableTermAt (tVar 0))
      (proofConstructorOccurrenceTermAt (tVar 0))).

Lemma raw_sat_proofSyntaxOccurrenceTotalityFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e proofSyntaxOccurrenceTotalityFormula <->
  RawProofConstructorOccurrenceTotalityFor M
    (RawProofSyntaxRealizable M).
Proof.
  intros M e. unfold proofSyntaxOccurrenceTotalityFormula,
    RawProofConstructorOccurrenceTotalityFor.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofSyntaxRealizableTermAt_iff.
  setoid_rewrite raw_sat_proofConstructorOccurrenceTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem proofSyntaxOccurrenceTotalityFormula_sentence :
  Formula.Sentence proofSyntaxOccurrenceTotalityFormula.
Proof.
  intros k hfree.
  unfold proofSyntaxOccurrenceTotalityFormula,
    proofSyntaxRealizableTermAt,
    proofSyntaxCertificateWithSupportTermAt,
    proofSyntaxTraversalTermAt,
    proofCodeSupportedTermAt,
    proofSyntaxStepTermAt,
    proofConstructorClosedTermAt,
    proofChildrenCasesClosedTermAt,
    proofChildrenClosedCaseTermAt,
    proofAllChildrenClosedTermAt,
    proofConstructorOccurrenceTermAt,
    proofTraversalEx8, proofTraversalAll8 in hfree.
  cbn in hfree. lia.
Qed.

Theorem proofSyntaxOccurrenceTotalityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e proofSyntaxOccurrenceTotalityFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_proofSyntaxOccurrenceTotalityFormula_iff M e)).
  exact (raw_proofConstructorOccurrence_totality_for_syntax M hPA).
Qed.

Theorem PA_proves_proofSyntaxOccurrenceTotalityFormula :
  Formula.BProv Formula.Ax_s [] proofSyntaxOccurrenceTotalityFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact proofSyntaxOccurrenceTotalityFormula_sentence.
  - exact proofSyntaxOccurrenceTotalityFormula_raw_valid.
Qed.

End PABoundedRawCodedProofTraversal.
