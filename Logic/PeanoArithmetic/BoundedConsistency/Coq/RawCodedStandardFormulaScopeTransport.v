(**
  Small free-variable transport lemmas for standard PA syntax.

  Keeping these generic inductions separate from the large dynamic checker
  formula prevents Rocq from unfolding that formula while checking routine
  renaming and substitution facts.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedScopedFormulaDiagonalSubstitution.

Module PABoundedRawCodedStandardFormulaScopeTransport.

Import PA.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.

Lemma standardTermFree_rename_preimage : forall input renaming index,
  Term.Free index (Term.rename renaming input) ->
  exists sourceIndex,
    Term.Free sourceIndex input /\ renaming sourceIndex = index.
Proof.
  intros input. induction input as [variable | | child IH |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    intros renaming index hfree; cbn [Term.rename Term.Free] in *.
  - exists variable. split; [reflexivity | symmetry; exact hfree].
  - contradiction.
  - exact (IH renaming index hfree).
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (IHrhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now right | exact heq].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (IHrhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now right | exact heq].
Qed.

Lemma standardFormulaFree_rename_preimage : forall input renaming index,
  Formula.Free index (Formula.rename renaming input) ->
  exists sourceIndex,
    Formula.Free sourceIndex input /\ renaming sourceIndex = index.
Proof.
  intros input. induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros renaming index hfree;
    cbn [Formula.rename Formula.Free] in *.
  - destruct hfree as [hfree | hfree].
    + destruct (standardTermFree_rename_preimage lhs renaming index hfree)
        as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (standardTermFree_rename_preimage rhs renaming index hfree)
        as [source [hsource heq]].
      exists source. split; [now right | exact heq].
  - contradiction.
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (IHrhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now right | exact heq].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (IHrhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now right | exact heq].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now left | exact heq].
    + destruct (IHrhs renaming index hfree) as [source [hsource heq]].
      exists source. split; [now right | exact heq].
  - destruct (IHchild (up renaming) (S index) hfree)
      as [[|source] [hsource heq]].
    + cbn [up] in heq. discriminate.
    + cbn [up] in heq. injection heq as heq.
      exists source. split; assumption.
  - destruct (IHchild (up renaming) (S index) hfree)
      as [[|source] [hsource heq]].
    + cbn [up] in heq. discriminate.
    + cbn [up] in heq. injection heq as heq.
      exists source. split; assumption.
Qed.

Lemma standardTermFree_substitution_preimage : forall input substitution index,
  Term.Free index (Term.subst substitution input) ->
  exists sourceIndex,
    Term.Free sourceIndex input /\
    Term.Free index (substitution sourceIndex).
Proof.
  intros input. induction input as [variable | | child IH |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    intros substitution index hfree;
    cbn [Term.subst Term.Free] in *.
  - exists variable. split; [reflexivity | exact hfree].
  - contradiction.
  - exact (IH substitution index hfree).
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (IHrhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now right | exact himage].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (IHrhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now right | exact himage].
Qed.

Lemma standardFormulaFree_substitution_preimage :
    forall input substitution index,
  Formula.Free index (Formula.subst substitution input) ->
  exists sourceIndex,
    Formula.Free sourceIndex input /\
    Term.Free index (substitution sourceIndex).
Proof.
  intros input. induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros substitution index hfree;
    cbn [Formula.subst Formula.Free] in *.
  - destruct hfree as [hfree | hfree].
    + destruct (standardTermFree_substitution_preimage
        lhs substitution index hfree) as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (standardTermFree_substitution_preimage
        rhs substitution index hfree) as [source [hsource himage]].
      exists source. split; [now right | exact himage].
  - contradiction.
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (IHrhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now right | exact himage].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (IHrhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now right | exact himage].
  - destruct hfree as [hfree | hfree].
    + destruct (IHlhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now left | exact himage].
    + destruct (IHrhs substitution index hfree)
        as [source [hsource himage]].
      exists source. split; [now right | exact himage].
  - destruct (IHchild (Term.upSubst substitution) (S index) hfree)
      as [[|source] [hsource himage]].
    + cbn [Term.upSubst Term.Free] in himage. discriminate.
    + cbn [Term.upSubst] in himage.
      destruct (standardTermFree_rename_preimage
        (substitution source) S (S index) himage)
        as [imageIndex [himageFree heq]].
      injection heq as heq. subst imageIndex.
      exists source. split; assumption.
  - destruct (IHchild (Term.upSubst substitution) (S index) hfree)
      as [[|source] [hsource himage]].
    + cbn [Term.upSubst Term.Free] in himage. discriminate.
    + cbn [Term.upSubst] in himage.
      destruct (standardTermFree_rename_preimage
        (substitution source) S (S index) himage)
        as [imageIndex [himageFree heq]].
      injection heq as heq. subst imageIndex.
      exists source. split; assumption.
Qed.

Lemma standardFormulaSubstitution_scoped : forall
    sourceScope targetScope input substitution,
  StandardFormulaScoped sourceScope input ->
  (forall sourceIndex,
    sourceIndex < sourceScope ->
    StandardTermScoped targetScope (substitution sourceIndex)) ->
  StandardFormulaScoped targetScope (Formula.subst substitution input).
Proof.
  intros sourceScope targetScope input substitution
    hinput hsubstitution index hfree.
  destruct (standardFormulaFree_substitution_preimage
    input substitution index hfree)
    as [sourceIndex [hsource himage]].
  exact (hsubstitution sourceIndex (hinput sourceIndex hsource)
    index himage).
Qed.

End PABoundedRawCodedStandardFormulaScopeTransport.
