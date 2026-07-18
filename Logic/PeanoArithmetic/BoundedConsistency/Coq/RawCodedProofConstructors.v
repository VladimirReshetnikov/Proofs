(**
  Transparent arithmetic constructors for canonical raw-proof codes.

  [CodedProof] assigns a polynomial list code to each of the seventeen
  natural-deduction constructors.  Its executable decoder is useful in the
  standard model, but a later nonstandard proof-soundness argument must see
  the constructor arithmetic itself.  This file writes that arithmetic as
  ordinary PA terms and proves exact evaluation in every law-free raw model.

  Context, formula, term, and child-proof fields are deliberately just
  carrier elements here.  Separate syntax traversals certify those fields;
  keeping this layer purely constructor-local makes its semantic theorem
  unconditional and reusable by a global proof traversal.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax CodedProof RawCodedSyntaxConstructors.

Import ListNotations.

Module PABoundedRawCodedProofConstructors.

Import PA.
Import PAListCode.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.

(** A meta-level list of object-language terms is folded with the same
    polynomial node used by [PAListCode.listCode].  This generic fold avoids
    seventeen error-prone hand-written nestings. *)
Fixpoint proofCodeFieldsTerm (fields : list term) : term :=
  match fields with
  | [] => tZero
  | field :: tail => nodeTerm field (proofCodeFieldsTerm tail)
  end.

Lemma raw_eval_proofCodeFieldsTerm : forall (M : RawPAModel)
    (e : nat -> M) fields,
  raw_term_eval M e (proofCodeFieldsTerm fields) =
  rawListCode M (map (raw_term_eval M e) fields).
Proof.
  intros M e fields. induction fields as [|field tail IH];
    cbn [proofCodeFieldsTerm rawListCode map].
  - reflexivity.
  - now rewrite raw_eval_nodeTerm, IH.
Qed.

(** The generic graph formula used by every constructor below. *)
Definition proofCodeFieldsTermAt (code : term) (fields : list term)
    : formula :=
  pEq code (proofCodeFieldsTerm fields).

Lemma raw_sat_proofCodeFieldsTermAt_iff : forall (M : RawPAModel)
    (e : nat -> M) code fields,
  raw_formula_sat M e (proofCodeFieldsTermAt code fields) <->
  raw_term_eval M e code =
    rawListCode M (map (raw_term_eval M e) fields).
Proof.
  intros M e code fields. unfold proofCodeFieldsTermAt.
  cbn [raw_formula_sat]. rewrite raw_eval_proofCodeFieldsTerm.
  reflexivity.
Qed.

(** Constructor tags match [rawProofCode] exactly. *)
Definition proofAssCodeTerm (context conclusion : term) : term :=
  proofCodeFieldsTerm [Term.numeral 0; context; conclusion].

Definition proofImpICodeTerm
    (context antecedent consequent child : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 1; context; antecedent; consequent; child].

Definition proofImpECodeTerm
    (context antecedent consequent impChild antecedentChild : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 2; context; antecedent; consequent;
      impChild; antecedentChild].

Definition proofBotECodeTerm
    (context conclusion child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 3; context; conclusion; child].

Definition proofLemCodeTerm (context body : term) : term :=
  proofCodeFieldsTerm [Term.numeral 4; context; body].

Definition proofAndICodeTerm
    (context left right leftChild rightChild : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 5; context; left; right; leftChild; rightChild].

Definition proofAndE1CodeTerm
    (context left right child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 6; context; left; right; child].

Definition proofAndE2CodeTerm
    (context left right child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 7; context; left; right; child].

Definition proofOrI1CodeTerm
    (context left right child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 8; context; left; right; child].

Definition proofOrI2CodeTerm
    (context left right child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 9; context; left; right; child].

Definition proofOrECodeTerm
    (context left right conclusion disjunctionChild leftChild rightChild
      : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 10; context; left; right; conclusion;
      disjunctionChild; leftChild; rightChild].

Definition proofAllICodeTerm
    (context body child : term) : term :=
  proofCodeFieldsTerm [Term.numeral 11; context; body; child].

Definition proofAllECodeTerm
    (context body witness child : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 12; context; body; witness; child].

Definition proofExICodeTerm
    (context body witness child : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 13; context; body; witness; child].

Definition proofExECodeTerm
    (context body conclusion existentialChild bodyChild : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 14; context; body; conclusion;
      existentialChild; bodyChild].

Definition proofEqReflCodeTerm (context witness : term) : term :=
  proofCodeFieldsTerm [Term.numeral 15; context; witness].

Definition proofEqElimCodeTerm
    (context source target body equalityChild bodyChild : term) : term :=
  proofCodeFieldsTerm
    [Term.numeral 16; context; source; target; body;
      equalityChild; bodyChild].

(** A right-associated finite disjunction keeps the complete constructor
    relation readable and makes it harder to miscount parentheses. *)
Fixpoint proofFormulaDisjunction (cases : list formula) : formula :=
  match cases with
  | [] => pBot
  | head :: tail => pOr head (proofFormulaDisjunction tail)
  end.

(** One relation exposes the complete constructor disjunction.  Witnesses
    are supplied by a later traversal, so this local formula contains no
    existential binders and is convenient under arbitrary binder layouts. *)
Definition rawProofConstructorCodeTermAt
    (code context a b c t child1 child2 child3 : term) : formula :=
  proofFormulaDisjunction
    [pEq code (proofAssCodeTerm context a);
     pEq code (proofImpICodeTerm context a b child1);
     pEq code (proofImpECodeTerm context a b child1 child2);
     pEq code (proofBotECodeTerm context a child1);
     pEq code (proofLemCodeTerm context a);
     pEq code (proofAndICodeTerm context a b child1 child2);
     pEq code (proofAndE1CodeTerm context a b child1);
     pEq code (proofAndE2CodeTerm context a b child1);
     pEq code (proofOrI1CodeTerm context a b child1);
     pEq code (proofOrI2CodeTerm context a b child1);
     pEq code (proofOrECodeTerm context a b c child1 child2 child3);
     pEq code (proofAllICodeTerm context a child1);
     pEq code (proofAllECodeTerm context a t child1);
     pEq code (proofExICodeTerm context a t child1);
     pEq code (proofExECodeTerm context a b child1 child2);
     pEq code (proofEqReflCodeTerm context t);
     pEq code (proofEqElimCodeTerm context a b c child1 child2)].

Definition RawProofConstructorCode (M : RawPAModel)
    (code context a b c t child1 child2 child3 : M) : Prop :=
  code = rawListCode M [rawNumeralValue M 0; context; a] \/
  code = rawListCode M
    [rawNumeralValue M 1; context; a; b; child1] \/
  code = rawListCode M
    [rawNumeralValue M 2; context; a; b; child1; child2] \/
  code = rawListCode M
    [rawNumeralValue M 3; context; a; child1] \/
  code = rawListCode M [rawNumeralValue M 4; context; a] \/
  code = rawListCode M
    [rawNumeralValue M 5; context; a; b; child1; child2] \/
  code = rawListCode M
    [rawNumeralValue M 6; context; a; b; child1] \/
  code = rawListCode M
    [rawNumeralValue M 7; context; a; b; child1] \/
  code = rawListCode M
    [rawNumeralValue M 8; context; a; b; child1] \/
  code = rawListCode M
    [rawNumeralValue M 9; context; a; b; child1] \/
  code = rawListCode M
    [rawNumeralValue M 10; context; a; b; c; child1; child2; child3] \/
  code = rawListCode M
    [rawNumeralValue M 11; context; a; child1] \/
  code = rawListCode M
    [rawNumeralValue M 12; context; a; t; child1] \/
  code = rawListCode M
    [rawNumeralValue M 13; context; a; t; child1] \/
  code = rawListCode M
    [rawNumeralValue M 14; context; a; b; child1; child2] \/
  code = rawListCode M [rawNumeralValue M 15; context; t] \/
  code = rawListCode M
    [rawNumeralValue M 16; context; a; b; c; child1; child2].

Arguments RawProofConstructorCode
  M code context a b c t child1 child2 child3 : clear implicits.

Theorem raw_sat_rawProofConstructorCodeTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    code context a b c t child1 child2 child3,
  raw_formula_sat M e
    (rawProofConstructorCodeTermAt
      code context a b c t child1 child2 child3) <->
  RawProofConstructorCode M
    (raw_term_eval M e code) (raw_term_eval M e context)
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e t)
    (raw_term_eval M e child1) (raw_term_eval M e child2)
    (raw_term_eval M e child3).
Proof.
  intros. unfold rawProofConstructorCodeTermAt,
    RawProofConstructorCode,
    proofAssCodeTerm, proofImpICodeTerm, proofImpECodeTerm,
    proofBotECodeTerm, proofLemCodeTerm, proofAndICodeTerm,
    proofAndE1CodeTerm, proofAndE2CodeTerm,
    proofOrI1CodeTerm, proofOrI2CodeTerm, proofOrECodeTerm,
    proofAllICodeTerm, proofAllECodeTerm, proofExICodeTerm,
    proofExECodeTerm, proofEqReflCodeTerm, proofEqElimCodeTerm.
  cbn [proofFormulaDisjunction raw_formula_sat].
  repeat rewrite raw_eval_proofCodeFieldsTerm.
  cbn [map].
  repeat rewrite raw_term_eval_numeral.
  tauto.
Qed.

(** Standard quotation into the raw carrier. *)
Fixpoint rawQuotedProofCode (M : RawPAModel) (d : RawProof) : M :=
  match d with
  | RP_ass G a =>
      rawListCode M [rawNumeralValue M 0;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a]
  | RP_impI G a b h =>
      rawListCode M [rawNumeralValue M 1;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedProofCode M h]
  | RP_impE G a b hImp hA =>
      rawListCode M [rawNumeralValue M 2;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedProofCode M hImp;
        rawQuotedProofCode M hA]
  | RP_botE G a h =>
      rawListCode M [rawNumeralValue M 3;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedProofCode M h]
  | RP_lem G a =>
      rawListCode M [rawNumeralValue M 4;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a]
  | RP_andI G a b hA hB =>
      rawListCode M [rawNumeralValue M 5;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedProofCode M hA;
        rawQuotedProofCode M hB]
  | RP_andE1 G a b h | RP_andE2 G a b h =>
      rawListCode M [rawNumeralValue M
        (match d with RP_andE1 _ _ _ _ => 6 | _ => 7 end);
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedProofCode M h]
  | RP_orI1 G a b h | RP_orI2 G a b h =>
      rawListCode M [rawNumeralValue M
        (match d with RP_orI1 _ _ _ _ => 8 | _ => 9 end);
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedProofCode M h]
  | RP_orE G a b c hOr hA hB =>
      rawListCode M [rawNumeralValue M 10;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M b; rawQuotedFormulaCode M c;
        rawQuotedProofCode M hOr; rawQuotedProofCode M hA;
        rawQuotedProofCode M hB]
  | RP_allI G a h =>
      rawListCode M [rawNumeralValue M 11;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedProofCode M h]
  | RP_allE G a t h =>
      rawListCode M [rawNumeralValue M 12;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedTermCode M t; rawQuotedProofCode M h]
  | RP_exI G a t h =>
      rawListCode M [rawNumeralValue M 13;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedTermCode M t; rawQuotedProofCode M h]
  | RP_exE G a c hEx hBody =>
      rawListCode M [rawNumeralValue M 14;
        rawNumeralValue M (contextCode G); rawQuotedFormulaCode M a;
        rawQuotedFormulaCode M c; rawQuotedProofCode M hEx;
        rawQuotedProofCode M hBody]
  | RP_eqRefl G t =>
      rawListCode M [rawNumeralValue M 15;
        rawNumeralValue M (contextCode G); rawQuotedTermCode M t]
  | RP_eqElim G s t a hEq hA =>
      rawListCode M [rawNumeralValue M 16;
        rawNumeralValue M (contextCode G); rawQuotedTermCode M s;
        rawQuotedTermCode M t; rawQuotedFormulaCode M a;
        rawQuotedProofCode M hEq; rawQuotedProofCode M hA]
  end.

Arguments rawQuotedProofCode M d : clear implicits.

Theorem rawQuotedProofCode_standard : forall (M : RawPAModel),
  RawPASatisfies M -> forall d,
  rawQuotedProofCode M d = rawNumeralValue M (rawProofCode d).
Proof.
  intros M hPA d. induction d; cbn [rawQuotedProofCode rawProofCode].
  all: repeat rewrite rawQuotedFormulaCode_standard by exact hPA.
  all: repeat rewrite rawQuotedTermCode_standard by exact hPA.
  all: repeat match goal with
  | IH : rawQuotedProofCode ?model ?child = _ |- _ => rewrite IH
  end.
  all: match goal with
  | |- rawListCode ?model ?values =
      rawNumeralValue ?model (listCode ?codes) =>
      change (rawListCode model (map (rawNumeralValue model) codes) =
        rawNumeralValue model (listCode codes));
      apply rawListCode_standard; exact hPA
  end.
Qed.

End PABoundedRawCodedProofConstructors.
