(**
  First-order PA formulae for the canonical list coding from [ListCode].

  A beta table is used only as a finite certificate for following the
  strictly decreasing tail codes.  The public code of a list is the single,
  canonical number [PAListCode.listCode xs]; beta parameters never form part
  of that public code.
*)

From Stdlib Require Import
  List Arith Lia Bool PeanoNat
  Sorting.Permutation Sorting.Sorted.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.

Import ListNotations.

Module PAListFormulas.

Import PA.
Import PAListCode.
Import PAListRepresentability.

Definition pairTerm (a b : term) : term :=
  tAdd (tMul (tAdd a b) (tAdd a b)) a.

Definition nodeTerm (head tail : term) : term :=
  tSucc (pairTerm head tail).

Lemma eval_pairTerm : forall e a b,
  Term.eval natModel e (pairTerm a b) =
    polynomialPair (Term.eval natModel e a) (Term.eval natModel e b).
Proof. reflexivity. Qed.

Lemma eval_nodeTerm : forall e a b,
  Term.eval natModel e (nodeTerm a b) =
    S (polynomialPair (Term.eval natModel e a)
      (Term.eval natModel e b)).
Proof. reflexivity. Qed.

Definition pAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition pAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition pAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition pEx3 (body : formula) : formula := pEx (pEx (pEx body)).
Definition pEx4 (body : formula) : formula := pEx (pEx (pEx (pEx body))).

(** One constructor edge in a beta-certified tail trace. *)
Definition listStepTermAt
    (cur next head code step index : term) : formula :=
  pAnd3
    (Formula.betaTermTermAt cur code step index)
    (Formula.betaTermTermAt next code step (tSucc index))
    (pEq cur (nodeTerm head next)).

(** [listTraceFromTermAt p start len code step] follows [len] constructor
    edges, starting with tail code [p] at beta index [start], and ends at
    the empty-list code zero. *)
Definition listTraceFromTermAt
    (p start len code step : term) : formula :=
  pAnd3
    (Formula.betaTermTermAt p code step start)
    (Formula.betaTermTermAt tZero code step (tAdd start len))
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 len))
        (pEx3
          (listStepTermAt
            (tVar 2) (tVar 1) (tVar 0)
            (liftTerm 4 code) (liftTerm 4 step)
            (tAdd (liftTerm 4 start) (tVar 3)))))).

Definition ListTraceFrom
    (p start len code step : nat) : Prop :=
  Formula.BetaEntry code step start p /\
  Formula.BetaEntry code step (start + len) 0 /\
  forall i, i < len ->
    exists cur next head,
      Formula.BetaEntry code step (start + i) cur /\
      Formula.BetaEntry code step (S (start + i)) next /\
      cur = S (polynomialPair head next).

Lemma eval_liftTerm_scons : forall x e t,
  Term.eval natModel (scons nat x e) (liftTerm 1 t) =
  Term.eval natModel e t.
Proof.
  intros x e t. unfold liftTerm. rewrite Term.eval_rename.
  apply Term.eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma eval_liftTerm_scons2 : forall a b e t,
  Term.eval natModel (scons nat a (scons nat b e)) (liftTerm 2 t) =
  Term.eval natModel e t.
Proof.
  intros a b e t. unfold liftTerm. rewrite Term.eval_rename.
  apply Term.eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma eval_liftTerm_scons3 : forall a b c e t,
  Term.eval natModel (scons nat a (scons nat b (scons nat c e)))
    (liftTerm 3 t) = Term.eval natModel e t.
Proof.
  intros a b c e t. unfold liftTerm. rewrite Term.eval_rename.
  apply Term.eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma eval_liftTerm_scons4 : forall a b c d e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d e))))
    (liftTerm 4 t) =
  Term.eval natModel e t.
Proof.
  intros a b c d e t. unfold liftTerm. rewrite Term.eval_rename.
  apply Term.eval_ext. intro i.
  replace (i + 4) with (S (S (S (S i)))) by lia. reflexivity.
Qed.

Lemma eval_liftTerm_scons6 : forall a b c d f g e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c
      (scons nat d (scons nat f (scons nat g e))))))
    (liftTerm 6 t) = Term.eval natModel e t.
Proof.
  intros a b c d f g e t. unfold liftTerm. rewrite Term.eval_rename.
  apply Term.eval_ext. intro i.
  replace (i + 6) with (S (S (S (S (S (S i)))))) by lia. reflexivity.
Qed.

Lemma listStepTermAt_nat : forall e cur next head code step index,
  Formula.Sat natModel e
    (listStepTermAt cur next head code step index) <->
  Formula.BetaEntry
      (Term.eval natModel e code) (Term.eval natModel e step)
      (Term.eval natModel e index) (Term.eval natModel e cur) /\
  Formula.BetaEntry
      (Term.eval natModel e code) (Term.eval natModel e step)
      (S (Term.eval natModel e index)) (Term.eval natModel e next) /\
  Term.eval natModel e cur =
    S (polynomialPair (Term.eval natModel e head)
      (Term.eval natModel e next)).
Proof.
  intros. unfold listStepTermAt, pAnd3.
  cbn [Formula.Sat].
  rewrite !Formula.betaTermTermAt_nat_entry.
  rewrite eval_nodeTerm. reflexivity.
Qed.

Lemma listTraceFromTermAt_nat : forall e p start len code step,
  Formula.Sat natModel e
    (listTraceFromTermAt p start len code step) <->
  ListTraceFrom
    (Term.eval natModel e p) (Term.eval natModel e start)
    (Term.eval natModel e len) (Term.eval natModel e code)
    (Term.eval natModel e step).
Proof.
  intros e p start len code step.
  unfold listTraceFromTermAt, ListTraceFrom, pAnd3.
  cbn [Formula.Sat].
  rewrite !Formula.betaTermTermAt_nat_entry.
  split.
  - intros [hstart [hend hall]].
    split; [exact hstart |]. split.
    + replace (Term.eval natModel e start + Term.eval natModel e len)
        with (Term.eval natModel e (tAdd start len)) by reflexivity.
      exact hend.
    + intros i hi.
      assert (hlt : Formula.Sat natModel (scons nat i e)
          (Formula.ltTermAt (tVar 0) (liftTerm 1 len))).
      {
        apply (proj2 (Formula.ltTermAt_nat _ _ _)).
        simpl. rewrite eval_liftTerm_scons. exact hi.
      }
      destruct (hall i hlt) as [cur [next [head hbody]]].
      pose proof (proj1 (listStepTermAt_nat
        (scons nat head (scons nat next (scons nat cur (scons nat i e))))
        (tVar 2) (tVar 1) (tVar 0)
        (liftTerm 4 code) (liftTerm 4 step)
        (tAdd (liftTerm 4 start) (tVar 3))) hbody) as hs.
      simpl in hs.
      repeat rewrite eval_liftTerm_scons4 in hs.
      exists cur, next, head.
      replace (Term.eval natModel e start + i)
        with (Term.eval natModel e start + i) by reflexivity.
      exact hs.
  - intros [hstart [hend hall]].
    split; [exact hstart |]. split.
    + change (Formula.BetaEntry
        (Term.eval natModel e code) (Term.eval natModel e step)
        (Term.eval natModel e start + Term.eval natModel e len) 0).
      exact hend.
    + intros i hlt.
      pose proof (proj1 (Formula.ltTermAt_nat
        (scons nat i e) (tVar 0) (liftTerm 1 len)) hlt) as hi.
      simpl in hi. rewrite eval_liftTerm_scons in hi.
      destruct (hall i hi) as [cur [next [head hs]]].
      exists cur, next, head.
      apply (proj2 (listStepTermAt_nat
        (scons nat head (scons nat next (scons nat cur (scons nat i e))))
        (tVar 2) (tVar 1) (tVar 0)
        (liftTerm 4 code) (liftTerm 4 step)
        (tAdd (liftTerm 4 start) (tVar 3)))).
      simpl.
      repeat rewrite eval_liftTerm_scons4.
      exact hs.
Qed.

(** A trace beginning at index zero. *)
Definition listTraceTermAt (p len code step : term) : formula :=
  listTraceFromTermAt p tZero len code step.

Definition ListTrace (p len code step : nat) : Prop :=
  ListTraceFrom p 0 len code step.

Lemma listTraceTermAt_nat : forall e p len code step,
  Formula.Sat natModel e (listTraceTermAt p len code step) <->
  ListTrace
    (Term.eval natModel e p) (Term.eval natModel e len)
    (Term.eval natModel e code) (Term.eval natModel e step).
Proof.
  intros. unfold listTraceTermAt, ListTrace.
  rewrite listTraceFromTermAt_nat. simpl. reflexivity.
Qed.

(** A trace is an exact finite traversal of constructor codes.  The final
    conjunct records every intermediate tail code; it is the key fact used
    by the [nth] formula below. *)
Lemma ListTraceFrom_sound : forall len p start code step,
  ListTraceFrom p start len code step ->
  exists xs,
    length xs = len /\
    p = listCode xs /\
    forall i, i <= len ->
      Formula.BetaEntry code step (start + i)
        (listCode (skipn i xs)).
Proof.
  induction len as [|len IH]; intros p start code step htrace.
  - destruct htrace as [hstart [hend _]].
    assert (hp : p = 0).
    {
      apply (Formula.BetaEntry_functional code step start).
      - exact hstart.
      - replace start with (start + 0) by lia. exact hend.
    }
    exists []. split; [reflexivity |]. split.
    + exact hp.
    + intros i hi. assert (i = 0) by lia. subst i. simpl.
      rewrite hp in hstart.
      replace (start + 0) with start by lia. exact hstart.
  - destruct htrace as [hstart [hend hall]].
    destruct (hall 0 ltac:(lia)) as
      [cur [next [head [hcur [hnext hnode]]]]].
    assert (hpcur : p = cur).
    {
      apply (Formula.BetaEntry_functional code step start).
      - exact hstart.
      - replace start with (start + 0) by lia. exact hcur.
    }
    assert (hsub : ListTraceFrom next (S start) len code step).
    {
      split.
      - replace (S start) with (S (start + 0)) by lia. exact hnext.
      - split.
        + replace (S start + len) with (start + S len) by lia.
          exact hend.
        + intros i hi.
          destruct (hall (S i) ltac:(lia)) as
            [cur' [next' [head' [hc [hn heq]]]]].
          exists cur', next', head'.
          replace (S start + i) with (start + S i) by lia.
          replace (S (S start + i)) with (S (start + S i)) by lia.
          repeat split; assumption.
    }
    destruct (IH next (S start) code step hsub) as
      [xs [hlen [hnextCode hentries]]].
    assert (hpcode : p = listCode (head :: xs)).
    { simpl. rewrite <- hnextCode, <- hnode, <- hpcur. reflexivity. }
    exists (head :: xs). split.
    + simpl. now rewrite hlen.
    + split.
      * exact hpcode.
      * intros i hi. destruct i as [|i].
        -- change (Formula.BetaEntry code step (start + 0)
             (listCode (head :: xs))). rewrite <- hpcode.
           replace (start + 0) with start by lia. exact hstart.
        -- simpl skipn. specialize (hentries i ltac:(lia)).
           replace (start + S i) with (S start + i) by lia.
           exact hentries.
Qed.

Corollary ListTrace_sound : forall p len code step,
  ListTrace p len code step ->
  exists xs,
    length xs = len /\
    p = listCode xs /\
    forall i, i <= len ->
      Formula.BetaEntry code step i (listCode (skipn i xs)).
Proof.
  intros p len code step h.
  destruct (ListTraceFrom_sound len p 0 code step h) as
    [xs [hlen [hp hentries]]].
  exists xs. repeat split; try assumption.
Qed.

Lemma listCode_skipn_le : forall xs i,
  listCode (skipn i xs) <= listCode xs.
Proof.
  intros xs i. revert xs. induction i as [|i IH]; intros xs.
  - simpl. lia.
  - destruct xs as [|x xs].
    + simpl. lia.
    + simpl skipn. specialize (IH xs).
      pose proof (listCode_tail_lt x xs). lia.
Qed.

Lemma skipn_step : forall (xs : list nat) i,
  i < length xs ->
  exists head tail,
    skipn i xs = head :: tail /\
    skipn (S i) xs = tail.
Proof.
  intros xs i hi.
  destruct (skipn i xs) as [|head tail] eqn:hskip.
  - pose proof (length_skipn i xs).
    rewrite hskip in H. simpl in H. lia.
  - exists head, tail. split; [reflexivity |].
    pose proof (skipn_skipn 1 i xs) as h.
    rewrite hskip in h. simpl in h.
    replace (1 + i) with (S i) in h by lia. symmetry. exact h.
Qed.

Lemma ListTrace_complete : forall xs,
  exists code step,
    ListTrace (listCode xs) (length xs) code step /\
    forall i, i <= length xs ->
      Formula.BetaEntry code step i (listCode (skipn i xs)).
Proof.
  intro xs.
  set (n := length xs).
  set (scale := S (listCode xs)).
  set (step := Formula.betaFact n * scale).
  destruct (Formula.beta_entries_exist_through_mul_betaFact
    n scale (fun i => listCode (skipn i xs))) as [code hcode].
  {
    intros i hi. unfold Formula.BetaModulus.
    pose proof (listCode_skipn_le xs i).
    pose proof (Formula.betaFact_pos n).
    unfold step, scale. nia.
  }
  exists code, step. split.
  - unfold ListTrace, ListTraceFrom. split.
    + replace (listCode xs) with (listCode (skipn 0 xs)) by reflexivity.
      apply hcode. unfold n. lia.
    + split.
      * change (Formula.BetaEntry code step (length xs) 0).
        specialize (hcode (length xs) ltac:(unfold n; lia)).
        rewrite skipn_all in hcode. exact hcode.
      * intros i hi.
        destruct (skipn_step xs i hi) as
          [head [tail [hcurCode hnextCode]]].
        exists (listCode (skipn i xs)),
          (listCode (skipn (S i) xs)), head.
        split.
        -- replace (0 + i) with i by lia. apply hcode. unfold n. lia.
        -- split.
           ++ replace (S (0 + i)) with (S i) by lia.
              apply hcode. unfold n. lia.
           ++ rewrite hcurCode, hnextCode. reflexivity.
  - intros i hi. apply hcode. unfold n. exact hi.
Qed.

(** Length and validity formulae.  Quantifier order is beta step, beta code,
    then length in the innermost displayed body. *)
Definition hasLengthTermAt (v n : term) : formula :=
  pEx (pEx
    (listTraceTermAt
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))).

Definition validCodeTermAt (v : term) : formula :=
  pEx (hasLengthTermAt (liftTerm 1 v) (tVar 0)).

Definition nthElementTermAt (v k m : term) : formula :=
  pEx4
    (pAnd3
      (listTraceTermAt
        (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))
      (Formula.ltTermAt (liftTerm 4 k) (tVar 3))
      (Formula.betaTermTermAt
        (nodeTerm (liftTerm 4 m) (tVar 0))
        (tVar 1) (tVar 2) (liftTerm 4 k))).

(** The four witnesses above, from innermost to outermost, are the tail
    code at position [k], the beta code, the beta step, and the length. *)

Lemma hasLengthTermAt_nat : forall e v n,
  Formula.Sat natModel e (hasLengthTermAt v n) <->
  HasLength (Term.eval natModel e v) (Term.eval natModel e n).
Proof.
  intros e v n. unfold hasLengthTermAt.
  cbn [Formula.Sat]. split.
  - intros [step [code htrace]].
    apply (proj1 (listTraceTermAt_nat
      (scons nat code (scons nat step e))
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))) in htrace.
    simpl in htrace. repeat rewrite eval_liftTerm_scons2 in htrace.
    destruct (ListTrace_sound _ _ _ _ htrace) as
      [xs [hlen [hv _]]].
    exists xs. split.
    + apply decode_some_iff_listCode. symmetry. exact hv.
    + exact hlen.
  - intros [xs [hdecode hlen]].
    destruct (ListTrace_complete xs) as [code [step [htrace _]]].
    exists step, code.
    apply (proj2 (listTraceTermAt_nat
      (scons nat code (scons nat step e))
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))).
    simpl. repeat rewrite eval_liftTerm_scons2.
    apply decode_some_iff_listCode in hdecode.
    rewrite <- hdecode, <- hlen. exact htrace.
Qed.

Lemma validCodeTermAt_nat : forall e v,
  Formula.Sat natModel e (validCodeTermAt v) <->
  ValidCode (Term.eval natModel e v).
Proof.
  intros e v. unfold validCodeTermAt. cbn [Formula.Sat].
  split.
  - intros [n hn].
    apply (proj1 (hasLengthTermAt_nat
      (scons nat n e) (liftTerm 1 v) (tVar 0))) in hn.
    simpl in hn. rewrite eval_liftTerm_scons in hn.
    exact (HasLength_valid _ _ hn).
  - intros [xs hdecode]. exists (length xs).
    apply (proj2 (hasLengthTermAt_nat
      (scons nat (length xs) e) (liftTerm 1 v) (tVar 0))).
    simpl. rewrite eval_liftTerm_scons. exists xs. now split.
Qed.

Lemma nthElementTermAt_nat : forall e v k m,
  Formula.Sat natModel e (nthElementTermAt v k m) <->
  NthElement (Term.eval natModel e v)
    (Term.eval natModel e k) (Term.eval natModel e m).
Proof.
  intros e v k m. unfold nthElementTermAt, pEx4, pAnd3.
  cbn [Formula.Sat]. split.
  - intros [len [step [code [tail [htrace [hlt hentry]]]]]].
    apply (proj1 (listTraceTermAt_nat
      (scons nat tail (scons nat code (scons nat step (scons nat len e))))
      (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))) in htrace.
    simpl in htrace. repeat rewrite eval_liftTerm_scons4 in htrace.
    apply (proj1 (Formula.ltTermAt_nat _ _ _)) in hlt.
    simpl in hlt. repeat rewrite eval_liftTerm_scons4 in hlt.
    apply (proj1 (Formula.betaTermTermAt_nat_entry _ _ _ _ _)) in hentry.
    simpl in hentry. repeat rewrite eval_liftTerm_scons4 in hentry.
    destruct (ListTrace_sound _ _ _ _ htrace) as
      [xs [hlen [hv hentries]]].
    assert (hk : Term.eval natModel e k < length xs) by lia.
    destruct (skipn_step xs (Term.eval natModel e k) hk) as
      [head [rest [hskip _]]].
    specialize (hentries (Term.eval natModel e k) ltac:(lia)).
    assert (heq := Formula.BetaEntry_functional code step
      (Term.eval natModel e k) _ _ hentries hentry).
    rewrite hskip in heq. simpl in heq.
    inversion heq as [hpair].
    destruct (polynomialPair_injective head (listCode rest)
      (Term.eval natModel e m) tail hpair) as [hhead _].
    exists xs. split.
    + apply decode_some_iff_listCode. symmetry. exact hv.
    + rewrite <- hd_error_skipn, hskip. simpl. now rewrite hhead.
  - intros [xs [hdecode hnth]].
    apply decode_some_iff_listCode in hdecode.
    assert (hk : Term.eval natModel e k < length xs).
    { apply nth_error_Some. rewrite hnth. discriminate. }
    destruct (skipn_step xs (Term.eval natModel e k) hk) as
      [head [rest [hskip hskipS]]].
    assert (hhead : head = Term.eval natModel e m).
    {
      rewrite <- hd_error_skipn, hskip in hnth. simpl in hnth.
      inversion hnth. reflexivity.
    }
    destruct (ListTrace_complete xs) as
      [code [step [htrace hentries]]].
    exists (length xs), step, code, (listCode rest).
    split.
    + apply (proj2 (listTraceTermAt_nat
        (scons nat (listCode rest)
          (scons nat code (scons nat step (scons nat (length xs) e))))
        (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))).
      simpl. repeat rewrite eval_liftTerm_scons4.
      rewrite <- hdecode. exact htrace.
    + split.
      * apply (proj2 (Formula.ltTermAt_nat _ _ _)).
        simpl. repeat rewrite eval_liftTerm_scons4. exact hk.
      * apply (proj2 (Formula.betaTermTermAt_nat_entry _ _ _ _ _)).
        simpl. repeat rewrite eval_liftTerm_scons4.
        specialize (hentries (Term.eval natModel e k) ltac:(lia)).
        rewrite hskip in hentries. simpl in hentries.
        rewrite <- hhead. exact hentries.
Qed.

(** Elementary consequences of the two projection predicates. *)
Lemma HasLength_decode : forall v n xs,
  decode v = Some xs -> (HasLength v n <-> length xs = n).
Proof.
  intros v n xs hdecode. split.
  - intros [ys [hy hlen]].
    pose proof (decode_functional v ys xs hy hdecode). subst ys. exact hlen.
  - intro hlen. exists xs. now split.
Qed.

Lemma NthElement_decode : forall v k m xs,
  decode v = Some xs -> (NthElement v k m <-> nth_error xs k = Some m).
Proof.
  intros v k m xs hdecode. split.
  - intros [ys [hy hnth]].
    pose proof (decode_functional v ys xs hy hdecode). subst ys. exact hnth.
  - intro hnth. exists xs. now split.
Qed.

Definition singletonTermAt (v m : term) : formula :=
  pAnd
    (hasLengthTermAt v (Term.numeral 1))
    (nthElementTermAt v tZero m).

Lemma singletonTermAt_nat : forall e v m,
  Formula.Sat natModel e (singletonTermAt v m) <->
  SingletonCode (Term.eval natModel e v) (Term.eval natModel e m).
Proof.
  intros e v m. unfold singletonTermAt.
  cbn [Formula.Sat]. rewrite hasLengthTermAt_nat, nthElementTermAt_nat.
  split.
  - intros [[xs [hdecode hlen]] hnth].
    apply (NthElement_decode _ _ _ xs hdecode) in hnth.
    destruct xs as [|x xs]; simpl in hlen; try lia.
    destruct xs as [|y ys]; simpl in hlen; try lia.
    simpl in hnth. inversion hnth. subst x. exact hdecode.
  - intro hdecode. split.
    + exists [Term.eval natModel e m]. split; [exact hdecode | reflexivity].
    + exists [Term.eval natModel e m]. split; [exact hdecode | reflexivity].
Qed.

(** Position-wise characterization of append. *)
Definition ConcatPosition (v t u : nat) : Prop :=
  exists nt nu,
    HasLength t nt /\ HasLength u nu /\ HasLength v (nt + nu) /\
    (forall i m, i < nt -> NthElement t i m -> NthElement v i m) /\
    (forall i m, i < nu -> NthElement u i m ->
      NthElement v (nt + i) m).

Definition concatTermAt (v t u : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 t) (tVar 1))
      (hasLengthTermAt (liftTerm 2 u) (tVar 0))
      (hasLengthTermAt (liftTerm 2 v) (tAdd (tVar 1) (tVar 0)))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 t) (tVar 1) (tVar 0))
              (nthElementTermAt (liftTerm 4 v) (tVar 1) (tVar 0))))))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 1))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 u) (tVar 1) (tVar 0))
              (nthElementTermAt (liftTerm 4 v)
                (tAdd (tVar 3) (tVar 1)) (tVar 0)))))))).

Lemma concatTermAt_position : forall e v t u,
  Formula.Sat natModel e (concatTermAt v t u) <->
  ConcatPosition (Term.eval natModel e v)
    (Term.eval natModel e t) (Term.eval natModel e u).
Proof.
  intros e v t u. unfold concatTermAt, ConcatPosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn.
  setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    exists nt, nu. repeat split; try assumption.
    + intros i m hi hm. exact (hleft i hi m hm).
    + intros i m hi hm. exact (hright i hi m hm).
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    exists nt, nu. repeat split; try assumption.
    + intros i hi m hm. exact (hleft i m hi hm).
    + intros i hi m hm. exact (hright i m hi hm).
Qed.

Lemma nth_error_exists_of_lt {A : Type} : forall (xs : list A) i,
  i < length xs -> exists m, nth_error xs i = Some m.
Proof.
  intros xs i hi. destruct (nth_error xs i) as [m|] eqn:h.
  - now exists m.
  - apply nth_error_None in h. lia.
Qed.

Lemma ConcatPosition_iff : forall v t u,
  ConcatPosition v t u <-> ConcatenationCode v t u.
Proof.
  intros v t u. split.
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    destruct ht as [ys [ht hnty]].
    destruct hu as [zs [hu hnuz]].
    destruct hv as [xs [hv hnvx]].
    exists xs, ys, zs. repeat split; try assumption.
    apply nth_error_ext. intro j.
    assert (hlen : length xs = length ys + length zs) by lia.
    destruct (lt_dec j (length xs)) as [hjx | hjx].
    + destruct (lt_dec j (length ys)) as [hjy | hjy].
      * destruct (nth_error_exists_of_lt ys j hjy) as [m hm].
        assert (htnth : NthElement t j m).
        { apply (NthElement_decode t j m ys ht). exact hm. }
        specialize (hleft j m ltac:(lia) htnth).
        apply (NthElement_decode v j m xs hv) in hleft.
        rewrite hleft. rewrite nth_error_app1 by exact hjy.
        symmetry. exact hm.
      * set (q := j - length ys).
        assert (hq : q < length zs) by (unfold q; lia).
        destruct (nth_error_exists_of_lt zs q hq) as [m hm].
        assert (hunth : NthElement u q m).
        { apply (NthElement_decode u q m zs hu). exact hm. }
        specialize (hright q m ltac:(lia) hunth).
        assert (hindex : nt + q = j) by (unfold q; lia).
        rewrite hindex in hright.
        apply (NthElement_decode v j m xs hv) in hright.
        rewrite hright. symmetry.
        rewrite nth_error_app2 by lia. unfold q. exact hm.
    + assert (hxnone : nth_error xs j = None).
      { apply nth_error_None. lia. }
      assert (happnone : nth_error (ys ++ zs) j = None).
      { apply nth_error_None. rewrite app_length. lia. }
      now rewrite hxnone, happnone.
  - intros [xs [ys [zs [hv [ht [hu hcat]]]]]].
    exists (length ys), (length zs). repeat split.
    + exists ys. now split.
    + exists zs. now split.
    + exists xs. split; [exact hv |]. subst xs. rewrite app_length. lia.
    + intros i m hi htnth.
      apply (NthElement_decode t i m ys ht) in htnth.
      apply (NthElement_decode v i m xs hv).
      subst xs. rewrite nth_error_app1 by exact hi. exact htnth.
    + intros i m hi hunth.
      apply (NthElement_decode u i m zs hu) in hunth.
      apply (NthElement_decode v (length ys + i) m xs hv).
      subst xs. rewrite nth_error_app2 by lia.
      replace (length ys + i - length ys) with i by lia. exact hunth.
Qed.

Lemma concatTermAt_nat : forall e v t u,
  Formula.Sat natModel e (concatTermAt v t u) <->
  ConcatenationCode (Term.eval natModel e v)
    (Term.eval natModel e t) (Term.eval natModel e u).
Proof.
  intros. rewrite concatTermAt_position. apply ConcatPosition_iff.
Qed.

(** Pairwise inequality of indexed elements. *)
Definition NoDupPosition (v : nat) : Prop :=
  exists n,
    HasLength v n /\
    forall i j m,
      i < n -> j < n -> i < j ->
      NthElement v i m -> ~ NthElement v j m.

Definition noDuplicatesTermAt (v : term) : formula :=
  pEx
    (pAnd
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 1))
          (pAll
            (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
              (pImp (Formula.ltTermAt (tVar 1) (tVar 0))
                (pAll
                  (pImp
                    (nthElementTermAt (liftTerm 4 v)
                      (tVar 2) (tVar 0))
                    (pNot
                      (nthElementTermAt (liftTerm 4 v)
                        (tVar 1) (tVar 0))))))))))).

Lemma noDuplicatesTermAt_position : forall e v,
  Formula.Sat natModel e (noDuplicatesTermAt v) <->
  NoDupPosition (Term.eval natModel e v).
Proof.
  intros e v. unfold noDuplicatesTermAt, NoDupPosition, pNot.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i j m hi hj hij hni hnj.
    exact (h i hi j hj hij m hni hnj).
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i hi j hj hij m hni hnj.
    exact (h i j m hi hj hij hni hnj).
Qed.

Lemma NoDupPosition_iff : forall v,
  NoDupPosition v <-> NoDuplicatesCode v.
Proof.
  intro v. split.
  - intros [n [[xs [hdecode hlen]] hpos]].
    exists xs. split; [exact hdecode |].
    apply (proj2 (NoDup_nth_error xs)).
    intros i j hi heq.
    assert (hji : j < length xs).
    {
      apply nth_error_Some.
      rewrite <- heq. apply nth_error_Some. exact hi.
    }
    destruct (Nat.lt_trichotomy i j) as [hij | [hij | hij]]; [|exact hij|].
    + destruct (nth_error_exists_of_lt xs i hi) as [m hm].
      assert (hni : NthElement v i m).
      { apply (NthElement_decode v i m xs hdecode). exact hm. }
      assert (hnj : NthElement v j m).
      { apply (NthElement_decode v j m xs hdecode). now rewrite <- heq. }
      exfalso. exact (hpos i j m ltac:(lia) ltac:(lia) hij hni hnj).
    + destruct (nth_error_exists_of_lt xs j hji) as [m hm].
      assert (hnj : NthElement v j m).
      { apply (NthElement_decode v j m xs hdecode). exact hm. }
      assert (hni : NthElement v i m).
      { apply (NthElement_decode v i m xs hdecode). now rewrite heq. }
      exfalso. exact (hpos j i m ltac:(lia) ltac:(lia) hij hnj hni).
  - intros [xs [hdecode hnodup]].
    exists (length xs). split.
    + exists xs. now split.
    + intros i j m hi hj hij hni hnj.
      apply (NthElement_decode v i m xs hdecode) in hni.
      apply (NthElement_decode v j m xs hdecode) in hnj.
      pose proof (proj1 (NoDup_nth_error xs) hnodup i j hi) as heqidx.
      assert (i = j) by (apply heqidx; now rewrite hni, hnj).
      lia.
Qed.

Lemma noDuplicatesTermAt_nat : forall e v,
  Formula.Sat natModel e (noDuplicatesTermAt v) <->
  NoDuplicatesCode (Term.eval natModel e v).
Proof.
  intros. rewrite noDuplicatesTermAt_position. apply NoDupPosition_iff.
Qed.

(** Adjacent comparisons characterize nondecreasing finite lists. *)
Definition SortedPosition (v : nat) : Prop :=
  exists n,
    HasLength v n /\
    forall i a b,
      S i < n ->
      NthElement v i a -> NthElement v (S i) b -> a <= b.

Definition sortedTermAt (v : term) : formula :=
  pEx
    (pAnd
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tSucc (tVar 0)) (tVar 1))
          (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 v) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (liftTerm 4 v)
                  (tSucc (tVar 2)) (tVar 0))
                (Formula.ltTermAt (tVar 1) (tSucc (tVar 0)))))))))).

Lemma sortedTermAt_position : forall e v,
  Formula.Sat natModel e (sortedTermAt v) <->
  SortedPosition (Term.eval natModel e v).
Proof.
  intros e v. unfold sortedTermAt, SortedPosition.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i a b hi hia hib. pose proof (h i hi a b hia hib). lia.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i hi a b hia hib. pose proof (h i a b hi hia hib). lia.
Qed.

Lemma locallySorted_nth_error : forall xs,
  LocallySorted le xs <->
  forall i a b,
    nth_error xs i = Some a ->
    nth_error xs (S i) = Some b -> a <= b.
Proof.
  induction xs as [|x xs IH].
  - split.
    + intros _ i a b h. destruct i; discriminate.
    + intros _. constructor.
  - destruct xs as [|y ys].
    + split.
      * intros _ i a b h1 h2. destruct i; discriminate.
      * intros _. constructor.
    + split.
      * intros h i a b h1 h2.
        inversion h as [| |a0 b0 l htail hxy]; subst.
        destruct i as [|i].
        -- simpl in h1, h2. inversion h1; inversion h2; subst. exact hxy.
        -- simpl in h1, h2.
           apply (proj1 IH htail i a b h1 h2).
      * intro h. constructor.
        -- apply (proj2 IH). intros i a b h1 h2.
           apply (h (S i) a b); simpl; assumption.
        -- specialize (h 0 x y eq_refl eq_refl). exact h.
Qed.

Lemma SortedPosition_iff : forall v,
  SortedPosition v <-> SortedCode v.
Proof.
  intro v. split.
  - intros [n [[xs [hdecode hlen]] hpos]].
    exists xs. split; [exact hdecode |].
    unfold Nondecreasing. apply (proj2 (Sorted_LocallySorted_iff le xs)).
    apply (proj2 (locallySorted_nth_error xs)).
    intros i a b hia hib.
    assert (hi : S i < length xs).
    { apply nth_error_Some. rewrite hib. discriminate. }
    apply (hpos i a b ltac:(lia)).
    + apply (NthElement_decode v i a xs hdecode). exact hia.
    + apply (NthElement_decode v (S i) b xs hdecode). exact hib.
  - intros [xs [hdecode hsorted]].
    exists (length xs). split.
    + exists xs. now split.
    + intros i a b hi hia hib.
      apply (NthElement_decode v i a xs hdecode) in hia.
      apply (NthElement_decode v (S i) b xs hdecode) in hib.
      pose proof (proj1 (Sorted_LocallySorted_iff le xs) hsorted) as hlocal.
      exact (proj1 (locallySorted_nth_error xs) hlocal i a b hia hib).
Qed.

Lemma sortedTermAt_nat : forall e v,
  Formula.Sat natModel e (sortedTermAt v) <->
  SortedCode (Term.eval natModel e v).
Proof.
  intros. rewrite sortedTermAt_position. apply SortedPosition_iff.
Qed.

(** A substring is obtained by appending a prefix and a suffix. *)
Definition SubstringViaConcat (v w : nat) : Prop :=
  exists prefix suffix middle,
    ConcatenationCode middle prefix v /\
    ConcatenationCode w middle suffix.

Definition contiguousSubstringTermAt (v w : term) : formula :=
  pEx3
    (pAnd
      (concatTermAt (tVar 0) (tVar 2) (liftTerm 3 v))
      (concatTermAt (liftTerm 3 w) (tVar 0) (tVar 1))).

Lemma contiguousSubstringTermAt_via_concat : forall e v w,
  Formula.Sat natModel e (contiguousSubstringTermAt v w) <->
  SubstringViaConcat (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold contiguousSubstringTermAt, SubstringViaConcat, pEx3.
  cbn [Formula.Sat]. setoid_rewrite concatTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons3. reflexivity.
Qed.

Lemma SubstringViaConcat_iff : forall v w,
  SubstringViaConcat v w <-> ContiguousSubstringCode v w.
Proof.
  intros v w. split.
  - intros [prefix [suffix [middle [hfirst hsecond]]]].
    destruct hfirst as
      [mid1 [pre [needle [hmid1 [hpre [hv hfirst]]]]]].
    destruct hsecond as
      [hay [mid2 [suf [hw [hmid2 [hsuf hsecond]]]]]].
    pose proof (decode_functional middle mid1 mid2 hmid1 hmid2) as hmid.
    subst mid2. exists needle, hay. repeat split; try assumption.
    exists pre, suf. subst mid1. rewrite app_assoc. exact hsecond.
  - intros [needle [hay [hv [hw [pre [suf heq]]]]]].
    exists (listCode pre), (listCode suf), (listCode (pre ++ needle)).
    split.
    + exists (pre ++ needle), pre, needle. repeat split.
      * apply decode_listCode.
      * apply decode_listCode.
      * exact hv.
    + exists hay, (pre ++ needle), suf. repeat split.
      * exact hw.
      * apply decode_listCode.
      * apply decode_listCode.
      * rewrite <- app_assoc. exact heq.
Qed.

Lemma contiguousSubstringTermAt_nat : forall e v w,
  Formula.Sat natModel e (contiguousSubstringTermAt v w) <->
  ContiguousSubstringCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite contiguousSubstringTermAt_via_concat.
  apply SubstringViaConcat_iff.
Qed.

(** Prefix counts provide a first-order certificate for exact occurrence
    counts. *)
Definition OccurrencePosition (v n m : nat) : Prop :=
  exists len counts,
    HasLength v len /\
    HasLength counts (S len) /\
    NthElement counts 0 0 /\
    NthElement counts len n /\
    forall i x cur next,
      i < len ->
      NthElement v i x ->
      NthElement counts i cur ->
      NthElement counts (S i) next ->
      (x = m /\ next = S cur) \/ (x <> m /\ next = cur).

Definition occurrencesTermAt (v n m : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 n))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 v) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (pOr
                    (pAnd
                      (pEq (tVar 2) (liftTerm 6 m))
                      (pEq (tVar 0) (tSucc (tVar 1))))
                    (pAnd
                      (pNot (pEq (tVar 2) (liftTerm 6 m)))
                      (pEq (tVar 0) (tVar 1)))))))))))))).

Lemma occurrencesTermAt_position : forall e v n m,
  Formula.Sat natModel e (occurrencesTermAt v n m) <->
  OccurrencePosition (Term.eval natModel e v)
    (Term.eval natModel e n) (Term.eval natModel e m).
Proof.
  intros e v n m. unfold occurrencesTermAt, OccurrencePosition, pAnd5, pNot.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [counts [hv [hc [hzero [hend hstep]]]]]].
    exists len, counts. repeat split; try assumption.
    intros i x cur next hi hvi hci hcn.
    specialize (hstep i hi x cur next hvi hci hcn).
    destruct hstep as [[heq hnext] | [hne hnext]].
    + now left.
    + right. split; [intro heq; apply hne; now subst | exact hnext].
  - intros [len [counts [hv [hc [hzero [hend hstep]]]]]].
    exists len, counts. repeat split; try assumption.
    intros i hi x cur next hvi hci hcn.
    destruct (hstep i x cur next hi hvi hci hcn) as
      [[heq hnext] | [hne hnext]].
    + now left.
    + right. split; [intro heq; apply hne; exact heq | exact hnext].
Qed.

Definition prefixCounts (xs : list nat) (m : nat) : list nat :=
  map (fun i => count_occ Nat.eq_dec (firstn i xs) m)
    (seq 0 (S (length xs))).

Lemma prefixCounts_length : forall xs m,
  length (prefixCounts xs m) = S (length xs).
Proof. intros. unfold prefixCounts. rewrite map_length, seq_length. reflexivity. Qed.

Lemma prefixCounts_nth : forall xs m i,
  i <= length xs ->
  nth_error (prefixCounts xs m) i =
    Some (count_occ Nat.eq_dec (firstn i xs) m).
Proof.
  intros xs m i hi. unfold prefixCounts.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S (length xs)) eqn:h.
  - simpl. now replace (0 + i) with i by lia.
  - apply Nat.ltb_ge in h. lia.
Qed.

Lemma count_occ_firstn_step : forall xs m i x,
  i < length xs -> nth_error xs i = Some x ->
  count_occ Nat.eq_dec (firstn (S i) xs) m =
    if Nat.eq_dec x m
    then S (count_occ Nat.eq_dec (firstn i xs) m)
    else count_occ Nat.eq_dec (firstn i xs) m.
Proof.
  induction xs as [|y ys IH]; intros m i x hi hnth; [simpl in hi; lia |].
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst x. simpl.
    destruct (Nat.eq_dec y m); reflexivity.
  - simpl in hnth. simpl firstn. simpl count_occ.
    specialize (IH m i x ltac:(simpl in hi; lia) hnth).
    destruct (Nat.eq_dec y m); destruct (Nat.eq_dec x m);
      simpl in *; lia.
Qed.

Lemma OccurrencePosition_iff : forall v n m,
  OccurrencePosition v n m <-> OccurrencesCode v n m.
Proof.
  intros v n m. split.
  - intros [len [counts
      [[xs [hv hlen]] [[cs [hc hclen]] [hzero [hend hstep]]]]]].
    exists xs. split; [exact hv |].
    assert (hinv : forall i, i <= length xs ->
      nth_error cs i =
        Some (count_occ Nat.eq_dec (firstn i xs) m)).
    {
      intros i hi. induction i as [|i IHi].
      - apply (NthElement_decode counts 0 0 cs hc) in hzero.
        simpl. exact hzero.
      - assert (hil : i < length xs) by lia.
        specialize (IHi ltac:(lia)).
        destruct (nth_error_exists_of_lt xs i hil) as [x hx].
        assert (hcsnext : S i < length cs) by lia.
        destruct (nth_error_exists_of_lt cs (S i) hcsnext) as [next hn].
        assert (hvi : NthElement v i x).
        { apply (NthElement_decode v i x xs hv). exact hx. }
        assert (hci : NthElement counts i
          (count_occ Nat.eq_dec (firstn i xs) m)).
        { apply (NthElement_decode counts i _ cs hc). exact IHi. }
        assert (hcn : NthElement counts (S i) next).
        { apply (NthElement_decode counts (S i) next cs hc). exact hn. }
        destruct (hstep i x _ next ltac:(lia) hvi hci hcn) as
          [[hxm hnext] | [hxm hnext]].
        + subst x next. rewrite (count_occ_firstn_step xs m i m hil hx).
          destruct (Nat.eq_dec m m); [exact hn | contradiction].
        + subst next. rewrite (count_occ_firstn_step xs m i x hil hx).
          destruct (Nat.eq_dec x m); [contradiction | exact hn].
    }
    apply (NthElement_decode counts len n cs hc) in hend.
    specialize (hinv (length xs) ltac:(lia)).
    rewrite firstn_all in hinv. rewrite hlen in hinv.
    rewrite hend in hinv. inversion hinv. reflexivity.
  - intros [xs [hv hcount]].
    set (cs := prefixCounts xs m).
    set (counts := listCode cs).
    exists (length xs), counts. repeat split.
    + exists xs. now split.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. apply prefixCounts_length.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. apply prefixCounts_nth. lia.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. rewrite prefixCounts_nth by lia.
        rewrite firstn_all, hcount. reflexivity.
    + intros i x cur next hi hvi hci hcn.
      apply (NthElement_decode v i x xs hv) in hvi.
      apply (NthElement_decode counts i cur cs
        ltac:(unfold counts; apply decode_listCode)) in hci.
      apply (NthElement_decode counts (S i) next cs
        ltac:(unfold counts; apply decode_listCode)) in hcn.
      unfold cs in hci, hcn.
      rewrite prefixCounts_nth in hci by lia.
      rewrite prefixCounts_nth in hcn by lia.
      assert (hcur : cur = count_occ Nat.eq_dec (firstn i xs) m).
      { inversion hci. reflexivity. }
      assert (hnext : next = count_occ Nat.eq_dec (firstn (S i) xs) m).
      { inversion hcn. reflexivity. }
      pose proof (count_occ_firstn_step xs m i x hi hvi) as hstep.
      destruct (Nat.eq_dec x m) as [heq | hne].
      * left. split; [exact heq |]. subst x.
        destruct (Nat.eq_dec m m) in hstep; [|contradiction].
        rewrite hcur, hnext. exact hstep.
      * right. split; [exact hne |].
        destruct (Nat.eq_dec x m) in hstep; [contradiction |].
        rewrite hcur, hnext. exact hstep.
Qed.

Lemma occurrencesTermAt_nat : forall e v n m,
  Formula.Sat natModel e (occurrencesTermAt v n m) <->
  OccurrencesCode (Term.eval natModel e v)
    (Term.eval natModel e n) (Term.eval natModel e m).
Proof.
  intros. rewrite occurrencesTermAt_position. apply OccurrencePosition_iff.
Qed.

(** Equality of all multiplicities characterizes permutations. *)
Definition PermutationByCounts (v w : nat) : Prop :=
  ValidCode v /\ ValidCode w /\
  forall m n, OccurrencesCode v n m <-> OccurrencesCode w n m.

Definition permutationTermAt (v w : term) : formula :=
  pAnd3
    (validCodeTermAt v)
    (validCodeTermAt w)
    (pAll (pAll
      (pIff
        (occurrencesTermAt (liftTerm 2 v) (tVar 0) (tVar 1))
        (occurrencesTermAt (liftTerm 2 w) (tVar 0) (tVar 1))))).

Lemma permutationTermAt_counts : forall e v w,
  Formula.Sat natModel e (permutationTermAt v w) <->
  PermutationByCounts (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold permutationTermAt, PermutationByCounts, pAnd3, pIff.
  cbn [Formula.Sat].
  setoid_rewrite validCodeTermAt_nat.
  setoid_rewrite occurrencesTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  split.
  - intros [hv [hw h]]. split; [exact hv |]. split; [exact hw |].
    intros mm nn. specialize (h mm nn). tauto.
  - intros [hv [hw h]]. split; [exact hv |]. split; [exact hw |].
    intros mm nn. specialize (h mm nn). tauto.
Qed.

Lemma PermutationByCounts_iff : forall v w,
  PermutationByCounts v w <-> PermutationCode v w.
Proof.
  intros v w. split.
  - intros [[xs hv] [[ys hw] hcounts]].
    exists xs, ys. repeat split; try assumption.
    apply (proj2 (Permutation_count_occ Nat.eq_dec xs ys)). intro m.
    set (n := count_occ Nat.eq_dec xs m).
    assert (hocv : OccurrencesCode v n m).
    { exists xs. split; [exact hv | reflexivity]. }
    apply (proj1 (hcounts m n)) in hocv.
    destruct hocv as [ys' [hwy hcount]].
    pose proof (decode_functional w ys' ys hwy hw). subst ys'.
    exact (eq_sym hcount).
  - intros [xs [ys [hv [hw hperm]]]].
    split; [now exists xs |]. split; [now exists ys |].
    intros m n. split.
    + intros [xs' [hv' hcount]].
      pose proof (decode_functional v xs' xs hv' hv). subst xs'.
      exists ys. split; [exact hw |].
      rewrite <- hcount. symmetry.
      exact (proj1 (Permutation_count_occ Nat.eq_dec xs ys) hperm m).
    + intros [ys' [hw' hcount]].
      pose proof (decode_functional w ys' ys hw' hw). subst ys'.
      exists xs. split; [exact hv |].
      rewrite <- hcount.
      exact (proj1 (Permutation_count_occ Nat.eq_dec xs ys) hperm m).
Qed.

Lemma permutationTermAt_nat : forall e v w,
  Formula.Sat natModel e (permutationTermAt v w) <->
  PermutationCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite permutationTermAt_counts. apply PermutationByCounts_iff.
Qed.

(** Prefix concatenations certify flattening of a coded list of coded
    lists. *)
Definition FlattenPosition (v w : nat) : Prop :=
  exists len prefixes,
    HasLength w len /\
    HasLength prefixes (S len) /\
    NthElement prefixes 0 0 /\
    NthElement prefixes len v /\
    forall i inner prev next,
      i < len ->
      NthElement w i inner ->
      NthElement prefixes i prev ->
      NthElement prefixes (S i) next ->
      ConcatenationCode next prev inner.

Definition flattenTermAt (v w : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 w) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 v))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 w) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (concatTermAt (tVar 0) (tVar 1) (tVar 2)))))))))))).

Lemma flattenTermAt_position : forall e v w,
  Formula.Sat natModel e (flattenTermAt v w) <->
  FlattenPosition (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold flattenTermAt, FlattenPosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite concatTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [prefixes [hw [hp [hz [he hs]]]]]].
    exists len, prefixes. repeat split; try assumption.
    intros i inner prev next hi hwi hpi hpn.
    exact (hs i hi inner prev next hwi hpi hpn).
  - intros [len [prefixes [hw [hp [hz [he hs]]]]]].
    exists len, prefixes. repeat split; try assumption.
    intros i hi inner prev next hwi hpi hpn.
    exact (hs i inner prev next hi hwi hpi hpn).
Qed.

Lemma decodeCodes_exists_of_valid : forall codes,
  Forall ValidCode codes -> exists xss, decodeCodes codes = Some xss.
Proof.
  intros codes h. induction h as [|c codes hc hcodes IH].
  - exists []. reflexivity.
  - destruct hc as [xs hdecode]. destruct IH as [xss hxss].
    exists (xs :: xss). simpl. now rewrite hdecode, hxss.
Qed.

Lemma decodeCodes_nth : forall codes xss i xs,
  decodeCodes codes = Some xss ->
  nth_error xss i = Some xs ->
  exists c, nth_error codes i = Some c /\ decode c = Some xs.
Proof.
  induction codes as [|c codes IH]; intros xss i xs hdecode hnth.
  - simpl in hdecode. inversion hdecode; subst xss. destruct i; discriminate.
  - simpl in hdecode.
    destruct (decode c) as [ys|] eqn:hc; try discriminate.
    destruct (decodeCodes codes) as [yss|] eqn:hcs; try discriminate.
    inversion hdecode; subst xss. destruct i as [|i].
    + simpl in hnth. inversion hnth; subst xs. exists c. now split.
    + simpl in hnth. destruct (IH yss i xs eq_refl hnth) as [d [hd hdx]].
      exists d. split; [exact hd | exact hdx].
Qed.

Lemma decodeCodes_length : forall codes xss,
  decodeCodes codes = Some xss -> length codes = length xss.
Proof.
  intros codes xss h. pose proof (decodeCodes_sound codes xss h) as hm.
  rewrite <- hm, map_length. reflexivity.
Qed.

Lemma concat_firstn_step : forall (xss : list (list nat)) i (xs : list nat),
  i < length xss -> nth_error xss i = Some xs ->
  concat (firstn (S i) xss) = concat (firstn i xss) ++ xs.
Proof.
  induction xss as [|ys yss IH]; intros i xs hi hnth;
    [simpl in hi; lia |].
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst xs. simpl. now rewrite app_nil_r.
  - simpl in hnth. rewrite !firstn_cons. rewrite !concat_cons.
    rewrite (IH i xs ltac:(simpl in hi; lia) hnth).
    apply app_assoc.
Qed.

Definition prefixFlats (xss : list (list nat)) : list nat :=
  map (fun i => listCode (concat (firstn i xss)))
    (seq 0 (S (length xss))).

Lemma prefixFlats_length : forall xss,
  length (prefixFlats xss) = S (length xss).
Proof. intro. unfold prefixFlats. rewrite map_length, seq_length. reflexivity. Qed.

Lemma prefixFlats_nth : forall xss i,
  i <= length xss ->
  nth_error (prefixFlats xss) i =
    Some (listCode (concat (firstn i xss))).
Proof.
  intros xss i hi. unfold prefixFlats.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S (length xss)) eqn:h.
  - simpl. now replace (0 + i) with i by lia.
  - apply Nat.ltb_ge in h. lia.
Qed.

Lemma FlattenPosition_iff : forall v w,
  FlattenPosition v w <-> FlattenCode v w.
Proof.
  intros v w. split.
  - intros [len [prefixes
      [[codes [hw hlen]] [[ps [hp hplen]] [hzero [hend hstep]]]]]].
    assert (hvalid : Forall ValidCode codes).
    {
      apply Forall_forall. intros c hcIn.
      apply In_nth_error in hcIn. destruct hcIn as [i hci].
      assert (hi : i < len).
      { rewrite <- hlen. apply nth_error_Some. rewrite hci. discriminate. }
      destruct (nth_error_exists_of_lt ps i ltac:(lia)) as [prev hprev].
      destruct (nth_error_exists_of_lt ps (S i) ltac:(lia)) as [next hnext].
      assert (hwc : NthElement w i c).
      { apply (NthElement_decode w i c codes hw). exact hci. }
      assert (hpp : NthElement prefixes i prev).
      { apply (NthElement_decode prefixes i prev ps hp). exact hprev. }
      assert (hpn : NthElement prefixes (S i) next).
      { apply (NthElement_decode prefixes (S i) next ps hp). exact hnext. }
      pose proof (hstep i c prev next hi hwc hpp hpn) as hcat.
      exact (proj2 (proj2 (ConcatenationCode_valid _ _ _ hcat))).
    }
    destruct (decodeCodes_exists_of_valid codes hvalid) as [xss hxss].
    assert (hlens : length codes = length xss).
    { exact (decodeCodes_length codes xss hxss). }
    assert (hinv : forall i, i <= length xss ->
      NthElement prefixes i (listCode (concat (firstn i xss)))).
    {
      intros i hi. induction i as [|i IHi].
      - change (NthElement prefixes 0 0). exact hzero.
      - assert (hil : i < length xss) by lia.
        specialize (IHi ltac:(lia)).
        destruct (nth_error_exists_of_lt xss i hil) as [ys hys].
        destruct (decodeCodes_nth codes xss i ys hxss hys) as
          [c [hci hcdecode]].
        destruct (nth_error_exists_of_lt ps (S i) ltac:(lia)) as
          [next hnext].
        assert (hwc : NthElement w i c).
        { apply (NthElement_decode w i c codes hw). exact hci. }
        assert (hpn : NthElement prefixes (S i) next).
        { apply (NthElement_decode prefixes (S i) next ps hp). exact hnext. }
        pose proof (hstep i c (listCode (concat (firstn i xss))) next
          ltac:(lia) hwc IHi hpn) as hcat.
        destruct hcat as
          [out [pre [inner [hnextDecode [hpre [hinner hout]]]]]].
        pose proof (decode_functional _ pre (concat (firstn i xss))
          hpre (decode_listCode _)) as hpreEq. subst pre.
        pose proof (decode_functional _ inner ys hinner hcdecode) as hinnerEq.
        subst inner.
        assert (hnextCode : next =
          listCode (concat (firstn (S i) xss))).
        {
          apply eq_sym. apply listCode_decode in hnextDecode.
          rewrite <- hnextDecode, hout.
          f_equal. exact (concat_firstn_step xss i ys hil hys).
        }
        rewrite <- hnextCode.
        exact hpn.
    }
    specialize (hinv (length xss) ltac:(lia)).
    assert (hend' : NthElement prefixes (length xss) v).
    { rewrite <- hlens, hlen. exact hend. }
    apply (NthElement_decode prefixes _ _ ps hp) in hinv.
    apply (NthElement_decode prefixes _ _ ps hp) in hend'.
    rewrite hinv in hend'. inversion hend' as [hvcode].
    exists (concat xss), codes, xss. repeat split; try assumption.
    + rewrite firstn_all. apply decode_listCode.
  - intros [flat [codes [xss [hv [hw [hxss hflat]]]]]].
    set (ps := prefixFlats xss).
    set (prefixes := listCode ps).
    assert (hlens : length codes = length xss).
    { exact (decodeCodes_length codes xss hxss). }
    exists (length codes), prefixes. repeat split.
    + exists codes. now split.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_length. lia.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_nth by lia. reflexivity.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_nth by lia.
        rewrite hlens, firstn_all, <- hflat.
        apply listCode_decode in hv. now rewrite hv.
    + intros i inner prev next hi hwi hpi hpn.
      apply (NthElement_decode w i inner codes hw) in hwi.
      apply (NthElement_decode prefixes i prev ps
        ltac:(unfold prefixes; apply decode_listCode)) in hpi.
      apply (NthElement_decode prefixes (S i) next ps
        ltac:(unfold prefixes; apply decode_listCode)) in hpn.
      assert (hix : i < length xss) by lia.
      destruct (nth_error_exists_of_lt xss i hix) as [ys hys].
      destruct (decodeCodes_nth codes xss i ys hxss hys) as
        [c [hci hcdecode]].
      rewrite hci in hwi. inversion hwi; subst c.
      unfold ps in hpi, hpn.
      rewrite prefixFlats_nth in hpi by lia.
      rewrite prefixFlats_nth in hpn by lia.
      inversion hpi as [hprev]. inversion hpn as [hnext].
      subst prev next.
      exists (concat (firstn (S i) xss)),
        (concat (firstn i xss)), ys. repeat split.
      * apply decode_listCode.
      * apply decode_listCode.
      * exact hcdecode.
      * exact (concat_firstn_step xss i ys hix hys).
Qed.

Lemma flattenTermAt_nat : forall e v w,
  Formula.Sat natModel e (flattenTermAt v w) <->
  FlattenCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite flattenTermAt_position. apply FlattenPosition_iff.
Qed.

Definition validCodeFormula : formula := validCodeTermAt (tVar 0).
Definition hasLengthFormula : formula :=
  hasLengthTermAt (tVar 0) (tVar 1).
Definition nthElementFormula : formula :=
  nthElementTermAt (tVar 0) (tVar 1) (tVar 2).

End PAListFormulas.
