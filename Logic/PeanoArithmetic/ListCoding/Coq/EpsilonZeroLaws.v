(**
  Closure, order, and algebra laws for the epsilon-zero notation codes.

  The executable algorithms live in [EpsilonZero].  This file deliberately
  keeps their longer invariant proofs separate from the coding bijection, so
  the latter remains a small independently checkable kernel boundary.
*)

From Stdlib Require Import Arith Lia Bool PeanoNat.
From PAListCoding Require Import EpsilonZero.

Module PAEpsilonZeroLaws.

Import PAEpsilonZero.

(** * Structural comparison is a strict total order *)

Theorem onoteCompare_lt_trans : forall a b c,
  onoteCompare a b = Lt ->
  onoteCompare b c = Lt ->
  onoteCompare a c = Lt.
Proof.
  induction a as [|ae IHe ac ar IHr]; intros b c hab hbc.
  - destruct b, c; simpl in *; try discriminate; reflexivity.
  - destruct b as [|be bc br]; [simpl in hab; discriminate |].
    destruct c as [|ce cc cr]; [simpl in hbc; discriminate |].
    simpl in hab, hbc |-.
    destruct (onoteCompare ae be) eqn:heab.
    + apply onoteCompare_eq in heab. subst be.
      destruct (onoteCompare ae ce) eqn:heac.
      * apply onoteCompare_eq in heac. subst ce.
        simpl. rewrite onoteCompare_refl.
        destruct (Nat.compare ac bc) eqn:hcab.
        (* Equal first coefficient: the decision moves to the tail.  Compare
           the second coefficient before using tail transitivity. *)
        ++ apply Nat.compare_eq in hcab. subst bc.
           destruct (Nat.compare ac cc) eqn:hcac.
           ** apply Nat.compare_eq in hcac. subst cc.
              exact (IHr br cr hab hbc).
           ** reflexivity.
           ** discriminate.
        (* A smaller first coefficient stays smaller if the middle note is
           below the third one. *)
        ++ destruct (Nat.compare bc cc) eqn:hcbc.
           ** apply Nat.compare_eq in hcbc. subst cc. now rewrite hcab.
           ** apply Nat.compare_lt_iff in hcab.
              apply Nat.compare_lt_iff in hcbc.
              assert (hacc : Nat.compare ac cc = Lt).
              { apply Nat.compare_lt_iff. lia. }
              now rewrite hacc.
           ** discriminate.
        ++ discriminate.
      * simpl. now rewrite heac.
      * discriminate.
    + destruct (onoteCompare be ce) eqn:hebc.
      * apply onoteCompare_eq in hebc. subst ce.
        simpl. now rewrite heab.
      * simpl. rewrite (IHe be ce heab hebc). reflexivity.
      * discriminate.
    + discriminate.
Qed.

Theorem onoteCompare_trichotomy : forall a b,
  onoteCompare a b = Lt \/ a = b \/ onoteCompare b a = Lt.
Proof.
  intros a b.
  destruct (onoteCompare a b) eqn:hcmp.
  - right. left. now apply onoteCompare_eq.
  - now left.
  - right. right. now apply onoteCompare_gt_reverse.
Qed.

Theorem onoteCompare_lt_irrefl : forall a,
  onoteCompare a a <> Lt.
Proof. intros a h. rewrite onoteCompare_refl in h. discriminate. Qed.

(** * Normal-form closure of arithmetic helpers *)

Definition TopBelow (bound o : ONote) : Prop :=
  match o with
  | ozero => True
  | oadd e _ _ => onoteCompare e bound = Lt
  end.

Lemma NF_oadd_iff : forall e c r,
  NF (oadd e c r) <-> NF e /\ NF r /\ TopBelow e r.
Proof. reflexivity. Qed.

Lemma TopBelow_zero : forall bound, TopBelow bound ozero.
Proof. exact (fun _ => I). Qed.

Lemma TopBelow_oadd : forall bound e c r,
  TopBelow bound (oadd e c r) <-> onoteCompare e bound = Lt.
Proof. reflexivity. Qed.

Theorem onoteSub_nf : forall a b,
  NF a -> NF b -> NF (onoteSub a b).
Proof.
  induction a as [|ae IHe ac ar IHr]; intros b ha hb.
  - destruct b; exact NF_zero.
  - destruct b as [|be bc br].
    + exact ha.
    + destruct ha as [hae [har hbelowA]].
      destruct hb as [hbe [hbr hbelowB]].
      cbn [onoteSub].
      destruct (onoteCompare ae be) eqn:hcmp.
      * destruct (ac - bc) eqn:hdiff.
        (* Equal coefficients expose the recursive subtraction of tails;
           unequal coefficients truncate to zero. *)
        ++ destruct (Nat.eqb ac bc) eqn:hc.
           ** apply IHr; assumption.
           ** exact NF_zero.
        ++ repeat split; assumption.
      * exact NF_zero.
      * exact (conj hae (conj har hbelowA)).
Qed.

(** Removing the finite remainder does not change the leading exponent of a
    nonzero omega-divisible part. *)
Lemma onoteSplit_shape : forall o q n,
  onoteSplit o = (q, n) ->
  q = ozero \/
  exists e c r r', o = oadd e c r /\ q = oadd e c r'.
Proof.
  intros [|e c r] q n hsplit.
  - cbn [onoteSplit] in hsplit. inversion hsplit. now left.
  - destruct e as [|ee ec er].
    + cbn [onoteSplit] in hsplit. inversion hsplit. now left.
    + cbn [onoteSplit] in hsplit.
      destruct (onoteSplit r) as [r' k] eqn:hr.
      inversion hsplit; subst q n.
      right. exists (oadd ee ec er), c, r, r'. now split.
Qed.

Lemma onoteSplit_topBelow : forall bound o q n,
  TopBelow bound o -> onoteSplit o = (q, n) -> TopBelow bound q.
Proof.
  intros bound o q n htop hsplit.
  destruct (onoteSplit_shape o q n hsplit) as [hz | hshape].
  - subst q. exact I.
  - destruct hshape as [e [c [r [r' [ho hq]]]]].
    subst o q. exact htop.
Qed.

Theorem onoteSplit_nf : forall o q n,
  NF o -> onoteSplit o = (q, n) -> NF q.
Proof.
  induction o as [|e IHe c r IHr]; intros q n ho hsplit.
  - cbn [onoteSplit] in hsplit. inversion hsplit. exact NF_zero.
  - destruct ho as [he [hr htop]].
    destruct e as [|ee ec er].
    + cbn [onoteSplit] in hsplit. inversion hsplit. exact NF_zero.
    + cbn [onoteSplit] in hsplit.
      destruct (onoteSplit r) as [r' k] eqn:hsr.
      inversion hsplit; subst q n.
      apply (proj2 (NF_oadd_iff (oadd ee ec er) c r')).
      exact (conj he (conj
        (IHr r' k hr eq_refl)
        (onoteSplit_topBelow (oadd ee ec er) r r' k htop hsr))).
Qed.

(** Prefixing both sides by the same left ordinal is strictly monotone in the
    right argument.  The auxiliary lemma makes the threshold/merge behavior
    of one CNF term explicit. *)
Lemma onoteAddAux_strict : forall e c a b,
  onoteCompare a b = Lt ->
  onoteCompare (onoteAddAux e c a) (onoteAddAux e c b) = Lt.
Proof.
  intros e c [|ae ac ar] [|be bc br] hab; simpl in hab;
    try discriminate.
  - unfold onoteAddAux.
    destruct (onoteCompare e be) eqn:heb.
    + apply onoteCompare_eq in heb. subst be.
      simpl. rewrite onoteCompare_refl.
      assert (hc : Nat.compare c (S (c + bc)) = Lt).
      { apply Nat.compare_lt_iff. lia. }
      now rewrite hc.
    + simpl. now rewrite heb.
    + simpl. rewrite onoteCompare_refl, Nat.compare_refl. reflexivity.
  - unfold onoteAddAux.
    destruct (onoteCompare e ae) eqn:hea.
    + apply onoteCompare_eq in hea. subst ae.
      destruct (onoteCompare e be) eqn:heb.
      * apply onoteCompare_eq in heb. subst be.
        simpl in hab |-.
        destruct (Nat.compare ac bc) eqn:hcoeff.
        (* Equal coefficients leave the original tail comparison; unequal
           coefficients remain unequal after adding the common prefix. *)
        ++ apply Nat.compare_eq in hcoeff. subst bc.
           cbn [onoteCompare].
           rewrite onoteCompare_refl, Nat.compare_refl.
           exact hab.
        ++ apply Nat.compare_lt_iff in hcoeff.
           assert (hshift :
             Nat.compare (S (c + ac)) (S (c + bc)) = Lt).
           { apply Nat.compare_lt_iff. lia. }
           cbn [onoteCompare]. rewrite onoteCompare_refl.
           now rewrite hshift.
        ++ discriminate.
      * simpl. now rewrite heb.
      * simpl in hab. discriminate.
    + assert (heb : onoteCompare e be = Lt).
      {
        destruct (onoteCompare ae be) eqn:haeb.
        - apply onoteCompare_eq in haeb. subst be. exact hea.
        - exact (onoteCompare_lt_trans e ae be hea haeb).
        - simpl in hab. discriminate.
      }
      rewrite heb. exact hab.
    + destruct (onoteCompare e be) eqn:heb.
      * apply onoteCompare_eq in heb. subst be.
        simpl. rewrite onoteCompare_refl.
        assert (hc : Nat.compare c (S (c + bc)) = Lt).
        { apply Nat.compare_lt_iff. lia. }
        now rewrite hc.
      * simpl. now rewrite heb.
      * simpl. rewrite onoteCompare_refl, Nat.compare_refl.
        exact hab.
Qed.

Theorem onoteAdd_strict_right : forall prefix a b,
  onoteCompare a b = Lt ->
  onoteCompare (onoteAdd prefix a) (onoteAdd prefix b) = Lt.
Proof.
  induction prefix as [|e IHe c r IHr]; intros a b hab; simpl.
  - exact hab.
  - apply onoteAddAux_strict. exact (IHr a b hab).
Qed.

Lemma onoteMulNat_nf : forall o n,
  NF o -> NF (onoteMulNat o n).
Proof.
  intros [|e c r] [|n] ho; simpl; try exact NF_zero.
  exact ho.
Qed.

Theorem onoteScale_nf : forall x o,
  NF x -> NF o -> NF (onoteScale x o).
Proof.
  intros x o hx.
  induction o as [|e IHe c r IHr]; intro ho; simpl.
  - exact NF_zero.
  - destruct ho as [he [hr htop]].
    apply (proj2 (NF_oadd_iff (onoteAdd x e) c (onoteScale x r))).
    split.
    + now apply onoteAdd_nf.
    + split.
      * exact (IHr hr).
      * destruct r as [|re rc rr]; [exact I |].
        simpl in htop |-.
        exact (onoteAdd_strict_right x re e htop).
Qed.

Lemma onoteAdd_zero_r_nf : forall a,
  NF a -> onoteAdd a ozero = a.
Proof.
  induction a as [|e IHe c r IHr]; intro ha; [reflexivity |].
  destruct ha as [he [hr htop]].
  cbn [onoteAdd]. rewrite (IHr hr).
  destruct r as [|re rc rr].
  - reflexivity.
  - unfold onoteAddAux.
    assert (hrev : onoteCompare e re = Gt).
    {
      apply onoteCompare_lt_reverse in htop.
      exact htop.
    }
    now rewrite hrev.
Qed.

Lemma onoteCompare_add_nonzero_right : forall a b,
  NF a -> b <> ozero ->
  onoteCompare a (onoteAdd a b) = Lt.
Proof.
  intros a b ha hb.
  rewrite <- (onoteAdd_zero_r_nf a ha) at 1.
  apply onoteAdd_strict_right.
  destruct b; [contradiction | reflexivity].
Qed.

Theorem onoteMul_nf : forall a b,
  NF a -> NF b -> NF (onoteMul a b).
Proof.
  intros a b.
  revert a.
  induction b as [|be IHe bc br IHr]; intros a ha hb.
  - rewrite onoteMul_zero_r. exact NF_zero.
  - destruct a as [|ae ac ar].
    + rewrite onoteMul_zero_l. exact NF_zero.
    + destruct ha as [hae [har htopA]].
      destruct hb as [hbe [hbr htopB]].
      destruct be as [|bee bec ber].
      * cbn [onoteMul]. exact (conj hae (conj har htopA)).
      * cbn [onoteMul].
        apply (proj2 (NF_oadd_iff
          (onoteAdd ae (oadd bee bec ber)) bc
          (onoteMul (oadd ae ac ar) br))).
        constructor.
        { (* The new leading exponent is the ordinal sum of the old ones. *)
          apply onoteAdd_nf; assumption. }
        constructor.
        { (* Recursion is on the strictly shorter right-hand CNF tail. *)
          apply IHr; [exact (conj hae (conj har htopA)) | exact hbr]. }
        { destruct br as [|re rc rr].
          - exact I.
          - cbn [onoteMul].
            destruct re as [|ree rec rer].
            + apply onoteCompare_add_nonzero_right.
              exact hae. discriminate.
            + apply onoteAdd_strict_right.
              exact htopB. }
Qed.

Lemma NF_one : NF onoteOne.
Proof. unfold onoteOne. simpl. tauto. Qed.

Lemma NF_zero_exponent_tail : forall c r,
  NF (oadd ozero c r) -> r = ozero.
Proof.
  intros c [|e ec er] h; [reflexivity |].
  destruct h as [_ [_ htop]].
  destruct e; simpl in htop; discriminate.
Qed.

(** Left subtraction by one leaves every infinite notation unchanged and
    decrements only a genuinely finite coefficient.  Consequently it is
    strictly monotone on positive normal exponents. *)
Lemma onoteSub_one_strict_positive : forall a b,
  NF a -> NF b -> a <> ozero -> b <> ozero ->
  onoteCompare a b = Lt ->
  onoteCompare (onoteSub a onoteOne) (onoteSub b onoteOne) = Lt.
Proof.
  intros [|ae ac ar] [|be bc br] ha hb hapos hbpos hab;
    try contradiction.
  destruct ae as [|aee aec aer].
  - assert (har : ar = ozero).
    { apply (NF_zero_exponent_tail ac ar). exact ha. }
    subst ar.
    destruct be as [|bee bec ber].
    + assert (hbr : br = ozero).
      { apply (NF_zero_exponent_tail bc br). exact hb. }
      subst br.
      cbn [onoteCompare] in hab.
      destruct ac as [|ac']; destruct bc as [|bc'];
        cbn [onoteSub onoteOne onoteCompare] in hab |-;
        try discriminate.
      * reflexivity.
      * assert (hcoeff : Nat.compare (S ac') (S bc') = Lt).
        {
          destruct (Nat.compare (S ac') (S bc')) eqn:hc;
            simpl in hab; try discriminate; reflexivity.
        }
        apply Nat.compare_lt_iff in hcoeff.
        assert (hc : Nat.compare ac' bc' = Lt).
        { apply Nat.compare_lt_iff. lia. }
        change (onoteCompare (oadd ozero ac' ozero)
          (oadd ozero bc' ozero) = Lt).
        cbn [onoteCompare].
        now rewrite hc.
    + destruct ac as [|ac'];
        cbn [onoteSub onoteOne onoteCompare] in hab |-;
        reflexivity.
  - destruct be as [|bee bec ber].
    + cbn [onoteCompare] in hab. discriminate.
    + cbn [onoteSub onoteOne]. exact hab.
Qed.

Lemma onoteSplit'_shape : forall o q n,
  onoteSplit' o = (q, n) ->
  q = ozero \/
  exists e c r r',
    e <> ozero /\ o = oadd e c r /\
    q = oadd (onoteSub e onoteOne) c r'.
Proof.
  intros [|e c r] q n hsplit.
  - cbn [onoteSplit'] in hsplit. inversion hsplit. now left.
  - destruct e as [|ee ec er].
    + cbn [onoteSplit'] in hsplit. inversion hsplit. now left.
    + cbn [onoteSplit'] in hsplit.
      destruct (onoteSplit' r) as [r' k] eqn:hr.
      inversion hsplit; subst q n.
      right. exists (oadd ee ec er), c, r, r'.
      repeat split; discriminate || reflexivity.
Qed.

Theorem onoteSplit'_nf : forall o q n,
  NF o -> onoteSplit' o = (q, n) -> NF q.
Proof.
  induction o as [|e IHe c r IHr]; intros q n ho hsplit.
  - cbn [onoteSplit'] in hsplit. inversion hsplit. exact NF_zero.
  - destruct ho as [he [hr htop]].
    destruct e as [|ee ec er].
    + cbn [onoteSplit'] in hsplit. inversion hsplit. exact NF_zero.
    + cbn [onoteSplit'] in hsplit.
      destruct (onoteSplit' r) as [r' k] eqn:hsr.
      inversion hsplit; subst q n.
      apply (proj2 (NF_oadd_iff
        (onoteSub (oadd ee ec er) onoteOne) c r')).
      constructor.
      { apply onoteSub_nf; [exact he | exact NF_one]. }
      constructor.
      { apply IHr with (n := k); [exact hr | reflexivity]. }
      { destruct (onoteSplit'_shape r r' k hsr) as [hz | hshape].
        - subst r'. exact I.
        - destruct hshape as
            [re [rc [rr [rr' [hrepos [hrEq hr'Eq]]]]]].
          subst r r'.
          destruct hr as [hre [_ _]].
          cbn [TopBelow] in htop |-.
          apply onoteSub_one_strict_positive; try assumption.
          discriminate. }
Qed.

Theorem onotePowAux_nf : forall e a0 a k m,
  NF e -> NF a0 -> NF a ->
  NF (onotePowAux e a0 a k m).
Proof.
  intros e a0 a k.
  induction k as [|k IH]; intros m he ha0 ha.
  - destruct m as [|m]; simpl.
    + exact NF_zero.
    + apply (proj2 (NF_oadd_iff e m ozero)).
      exact (conj he (conj NF_zero I)).
  - destruct m as [|m]; simpl.
    + exact NF_zero.
    + apply onoteAdd_nf.
      * apply onoteScale_nf.
        (* Its exponent is a sum of two normal notations. *)
        ** apply onoteAdd_nf.
           exact he. now apply onoteMulNat_nf.
        ** exact ha.
      * apply IH; assumption.
Qed.

Theorem onotePowAux2_nf : forall exponent basePart finitePart,
  NF exponent -> NF basePart ->
  NF (onotePowAux2 exponent (basePart, finitePart)).
Proof.
  intros exponent [|a0 ac ar] finitePart hexponent hbase.
  - destruct finitePart as [|m].
    + destruct exponent; simpl; [exact NF_one | exact NF_zero].
    + destruct m as [|m].
      * exact NF_one.
      * cbn [onotePowAux2].
        destruct (onoteSplit' exponent) as [q k] eqn:hsplit'.
        apply (proj2 (NF_oadd_iff q
          (Nat.pred (Nat.pow (S (S m)) k)) ozero)).
        exact (conj (onoteSplit'_nf exponent q k hexponent hsplit')
          (conj NF_zero I)).
  - destruct hbase as [ha0 [har htopBase]].
    cbn [onotePowAux2].
    destruct (onoteSplit exponent) as [b k] eqn:hsplit.
    assert (hb : NF b).
    { exact (onoteSplit_nf exponent b k hexponent hsplit). }
    destruct k as [|k].
    + apply (proj2 (NF_oadd_iff (onoteMul a0 b) 0 ozero)).
      exact (conj (onoteMul_nf a0 b ha0 hb) (conj NF_zero I)).
    + apply onoteAdd_nf.
      * apply onoteScale_nf.
        (* The scale exponent is [a0*b + a0*k]. *)
        ** apply onoteAdd_nf.
           apply onoteMul_nf; assumption.
           now apply onoteMulNat_nf.
        ** exact (conj ha0 (conj har htopBase)).
      * apply onotePowAux_nf.
        ** apply onoteMul_nf; assumption.
        ** exact ha0.
        ** apply onoteMulNat_nf.
           exact (conj ha0 (conj har htopBase)).
Qed.

Theorem onotePow_nf : forall base exponent,
  NF base -> NF exponent -> NF (onotePow base exponent).
Proof.
  intros base exponent hbase hexponent.
  unfold onotePow.
  destruct (onoteSplit base) as [basePart finitePart] eqn:hsplit.
  apply onotePowAux2_nf.
  - exact hexponent.
  - exact (onoteSplit_nf base basePart finitePart hbase hsplit).
Qed.

(** The executable operations therefore map valid codes to valid codes.  These
    are the semantic closure facts used by the corresponding PA graph
    formulae: once their two inputs denote normal forms, so does the uniquely
    determined output. *)
Theorem addCode_valid : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  ValidOrdinalCode (addCode a b).
Proof.
  intros a b ha hb.
  unfold ValidOrdinalCode in *.
  rewrite decode_addCode.
  now apply onoteAdd_nf.
Qed.

Theorem mulCode_valid : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  ValidOrdinalCode (mulCode a b).
Proof.
  intros a b ha hb.
  unfold ValidOrdinalCode in *.
  rewrite decode_mulCode.
  now apply onoteMul_nf.
Qed.

Theorem powCode_valid : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  ValidOrdinalCode (powCode a b).
Proof.
  intros a b ha hb.
  unfold ValidOrdinalCode in *.
  rewrite decode_powCode.
  now apply onotePow_nf.
Qed.

Corollary ordinalAdd_result_valid : forall z a b,
  OrdinalAdd z a b -> ValidOrdinalCode z.
Proof.
  intros z a b [ha [hb hz]]. subst z.
  now apply addCode_valid.
Qed.

Corollary ordinalMul_result_valid : forall z a b,
  OrdinalMul z a b -> ValidOrdinalCode z.
Proof.
  intros z a b [ha [hb hz]]. subst z.
  now apply mulCode_valid.
Qed.

Corollary ordinalPow_result_valid : forall z a b,
  OrdinalPow z a b -> ValidOrdinalCode z.
Proof.
  intros z a b [ha [hb hz]]. subst z.
  now apply powCode_valid.
Qed.

(** * Distinguished codes and elementary identities *)

(** Keeping the constants as encoded notations makes their intended meaning
    explicit, while [zeroCode_eq] records that the reserved zero code really
    is the canonical code of ordinal zero. *)
Definition zeroCode : nat := encode ozero.
Definition oneCode : nat := encode onoteOne.

Lemma zeroCode_eq : zeroCode = 0.
Proof. reflexivity. Qed.

Lemma decode_zeroCode : decode zeroCode = ozero.
Proof. unfold zeroCode. apply decode_encode. Qed.

Lemma decode_oneCode : decode oneCode = onoteOne.
Proof. unfold oneCode. apply decode_encode. Qed.

Lemma zeroCode_valid : ValidOrdinalCode zeroCode.
Proof. unfold ValidOrdinalCode. rewrite decode_zeroCode. exact NF_zero. Qed.

Lemma oneCode_valid : ValidOrdinalCode oneCode.
Proof. unfold ValidOrdinalCode. rewrite decode_oneCode. exact NF_one. Qed.

Lemma coefficientProductPred_zero_r : forall c,
  coefficientProductPred c 0 = c.
Proof. intro c. unfold coefficientProductPred. lia. Qed.

Lemma coefficientProductPred_zero_l : forall c,
  coefficientProductPred 0 c = c.
Proof. intro c. unfold coefficientProductPred. lia. Qed.

Lemma coefficientProductPred_add : forall a b c,
  coefficientProductPred a (S (b + c)) =
  S (coefficientProductPred a b + coefficientProductPred a c).
Proof. intros a b c. unfold coefficientProductPred. nia. Qed.

Lemma coefficientProductPred_assoc : forall a b c,
  coefficientProductPred (coefficientProductPred a b) c =
  coefficientProductPred a (coefficientProductPred b c).
Proof. intros a b c. unfold coefficientProductPred. nia. Qed.

Lemma onoteMul_one_r : forall a, onoteMul a onoteOne = a.
Proof.
  intros [|e c r]; [reflexivity |].
  cbn [onoteOne onoteMul].
  now rewrite coefficientProductPred_zero_r.
Qed.

(** Left multiplication by one follows the right operand's CNF.  Normality
    rules out a spurious tail after a finite leading term. *)
Lemma onoteMul_one_l_nf : forall a,
  NF a -> onoteMul onoteOne a = a.
Proof.
  induction a as [|e IHe c r IHr]; intro ha; [reflexivity |].
  destruct ha as [he [hr htop]].
  destruct e as [|ee ec er].
  - assert (hr0 : r = ozero).
    { now apply NF_zero_exponent_tail with (c := c). }
    subst r. cbn [onoteOne onoteMul].
    now rewrite coefficientProductPred_zero_l.
  - cbn [onoteOne onoteMul].
    rewrite IHr by exact hr.
    reflexivity.
Qed.

Theorem zeroCode_add : forall a, addCode zeroCode a = a.
Proof.
  intro a. apply decode_injective.
  rewrite decode_addCode, decode_zeroCode, onoteAdd_zero_l.
  reflexivity.
Qed.

Theorem add_zeroCode : forall a,
  ValidOrdinalCode a -> addCode a zeroCode = a.
Proof.
  intros a ha. apply decode_injective.
  rewrite decode_addCode, decode_zeroCode.
  apply onoteAdd_zero_r_nf. exact ha.
Qed.

(** A lower leading term is absorbed by an already larger prefix.  This is
    the comparison fact that makes the right-associated addition scanner
    associative. *)
Lemma onoteAddAux_absorb_lt : forall e f c d x,
  onoteCompare e f = Lt ->
  onoteAddAux e c (onoteAddAux f d x) = onoteAddAux f d x.
Proof.
  intros e f c d [|xe xc xr] hef.
  - cbn [onoteAddAux]. now rewrite hef.
  - unfold onoteAddAux at 1 2 3.
    destruct (onoteCompare f xe) eqn:hfx.
    + now rewrite hef.
    + assert (hex : onoteCompare e xe = Lt).
      { now apply onoteCompare_lt_trans with (b := f). }
      now rewrite hex.
    + now rewrite hef.
Qed.

(** Two adjacent scanner calls at the same exponent merge their stored
    coefficients.  The extra successor accounts for predecessor storage. *)
Lemma onoteAddAux_fuse : forall e c d x,
  onoteAddAux e c (onoteAddAux e d x) =
  onoteAddAux e (S (c + d)) x.
Proof.
  intros e c d [|xe xc xr].
  - cbn [onoteAddAux]. rewrite onoteCompare_refl.
    now f_equal; lia.
  - unfold onoteAddAux at 1 2 3.
    destruct (onoteCompare e xe) eqn:hex.
    + repeat rewrite hex. rewrite onoteCompare_refl. now f_equal; lia.
    + now repeat rewrite hex.
    + repeat rewrite hex. rewrite onoteCompare_refl. now f_equal; lia.
Qed.

(** Pushing one scanner step through a later addition is the fundamental
    fusion equation for ordinal addition.  It holds even for raw syntax. *)
Lemma onoteAddAux_add : forall e c a b,
  onoteAddAux e c (onoteAdd a b) =
  onoteAdd (onoteAddAux e c a) b.
Proof.
  intros e c [|ae ac ar] b; [reflexivity |].
  unfold onoteAddAux at 2.
  destruct (onoteCompare e ae) eqn:hea.
  - apply onoteCompare_eq in hea. subst ae.
    cbn [onoteAdd]. apply onoteAddAux_fuse.
  - cbn [onoteAdd]. now apply onoteAddAux_absorb_lt.
  - reflexivity.
Qed.

Theorem onoteAdd_assoc : forall a b c,
  onoteAdd (onoteAdd a b) c = onoteAdd a (onoteAdd b c).
Proof.
  induction a as [|e IHe n r IHr]; intros b c; [reflexivity |].
  cbn [onoteAdd].
  rewrite <- onoteAddAux_add, IHr.
  reflexivity.
Qed.

Theorem addCode_assoc : forall a b c,
  ValidOrdinalCode a -> ValidOrdinalCode b -> ValidOrdinalCode c ->
  addCode (addCode a b) c = addCode a (addCode b c).
Proof.
  intros a b c _ _ _. apply decode_injective.
  rewrite !decode_addCode.
  apply onoteAdd_assoc.
Qed.

(** A scanner whose displayed exponent dominates its normal tail simply
    rebuilds the corresponding CNF node. *)
Lemma onoteAddAux_reconstruct_nf : forall e c r,
  NF (oadd e c r) -> onoteAddAux e c r = oadd e c r.
Proof.
  intros e c [|re rc rr] hnf; [reflexivity |].
  destruct hnf as [_ [_ htop]].
  unfold onoteAddAux.
  apply onoteCompare_lt_reverse in htop.
  now rewrite htop.
Qed.

Lemma onoteAddAux_topBelow : forall bound e c x,
  onoteCompare e bound = Lt -> TopBelow bound x ->
  TopBelow bound (onoteAddAux e c x).
Proof.
  intros bound e c [|xe xc xr] he hx; [exact he |].
  cbn [TopBelow] in hx |-.
  unfold onoteAddAux.
  destruct (onoteCompare e xe); assumption.
Qed.

Lemma NF_tail_topBelow : forall bound e c r,
  NF (oadd e c r) -> onoteCompare e bound = Lt ->
  TopBelow bound r.
Proof.
  intros bound e c [|re rc rr] hnf heb; [exact I |].
  destruct hnf as [_ [_ hre]].
  cbn [TopBelow].
  now apply onoteCompare_lt_trans with (b := e).
Qed.

(** If two normal CNFs lie below the same leading exponent, so does their
    sum.  This is the bound invariant needed when a preserved prefix is
    rebuilt after recursive addition. *)
Lemma onoteAdd_topBelow : forall bound a b,
  NF a -> NF b -> TopBelow bound a -> TopBelow bound b ->
  TopBelow bound (onoteAdd a b).
Proof.
  induction a as [|e IHe c r IHr]; intros b ha hb hab hbb.
  - exact hbb.
  - destruct ha as [he [hr htop]].
    cbn [TopBelow] in hab.
    cbn [onoteAdd].
    apply onoteAddAux_topBelow; [exact hab |].
    apply IHr.
    + exact hr.
    + exact hb.
    + apply NF_tail_topBelow with (e := e) (c := c).
      * exact (conj he (conj hr htop)).
      * exact hab.
    + exact hbb.
Qed.

(** Adding a normal form whose leading exponent is below [e] to a CNF node
    beginning at [e] discards the former completely. *)
Lemma onoteAdd_below_node : forall a e c r,
  NF a -> TopBelow e a ->
  onoteAdd a (oadd e c r) = oadd e c r.
Proof.
  induction a as [|ae IHe ac ar IHar]; intros e c r ha hae.
  - reflexivity.
  - destruct ha as [haeNF [har htail]].
    cbn [TopBelow] in hae.
    cbn [onoteAdd].
    assert (htar : TopBelow e ar).
    { apply NF_tail_topBelow with (e := ae) (c := ac).
      - exact (conj haeNF (conj har htail)).
      - exact hae. }
    rewrite IHar by assumption.
    unfold onoteAddAux. now rewrite hae.
Qed.

(** Closed form for adding two nonzero normal CNFs. *)
Lemma onoteAdd_nodes : forall be bc br ce cc cr,
  NF (oadd be bc br) -> NF (oadd ce cc cr) ->
  onoteAdd (oadd be bc br) (oadd ce cc cr) =
  match onoteCompare be ce with
  | Lt => oadd ce cc cr
  | Eq => oadd be (S (bc + cc)) cr
  | Gt => oadd be bc (onoteAdd br (oadd ce cc cr))
  end.
Proof.
  intros be bc br ce cc cr hb hc.
  destruct hb as [hbe [hbr htopB]].
  destruct hc as [hce [hcr htopC]].
  destruct (onoteCompare be ce) eqn:hcmp.
  - apply onoteCompare_eq in hcmp. subst ce.
    cbn [onoteAdd].
    assert (hbrBelow : TopBelow be br).
    { destruct br; [exact I | exact htopB]. }
    rewrite onoteAdd_below_node by assumption.
    unfold onoteAddAux. rewrite onoteCompare_refl. reflexivity.
  - apply onoteAdd_below_node.
    + exact (conj hbe (conj hbr htopB)).
    + exact hcmp.
  - cbn [onoteAdd].
    apply onoteAddAux_reconstruct_nf.
    apply (proj2 (NF_oadd_iff be bc
      (onoteAdd br (oadd ce cc cr)))).
    constructor; [exact hbe |].
    constructor.
    + apply onoteAdd_nf; [exact hbr |].
      exact (conj hce (conj hcr htopC)).
    + apply onoteAdd_topBelow.
      * exact hbr.
      * exact (conj hce (conj hcr htopC)).
      * destruct br; [exact I | exact htopB].
      * cbn [TopBelow]. now apply onoteCompare_gt_reverse.
Qed.

Theorem zeroCode_mul : forall a, mulCode zeroCode a = zeroCode.
Proof.
  intro a. apply decode_injective.
  rewrite decode_mulCode, !decode_zeroCode, onoteMul_zero_l.
  reflexivity.
Qed.

Theorem mul_zeroCode : forall a, mulCode a zeroCode = zeroCode.
Proof.
  intro a. apply decode_injective.
  rewrite decode_mulCode, !decode_zeroCode, onoteMul_zero_r.
  reflexivity.
Qed.

Theorem oneCode_mul : forall a,
  ValidOrdinalCode a -> mulCode oneCode a = a.
Proof.
  intros a ha. apply decode_injective.
  rewrite decode_mulCode, decode_oneCode.
  now apply onoteMul_one_l_nf.
Qed.

Theorem mul_oneCode : forall a,
  ValidOrdinalCode a -> mulCode a oneCode = a.
Proof.
  intros a _. apply decode_injective.
  rewrite decode_mulCode, decode_oneCode.
  apply onoteMul_one_r.
Qed.

(** Ordinal multiplication distributes over a sum in its right argument.
    The proof follows the leading-exponent comparison used by [onoteAdd].
    In the finite/finite branch the assertion reduces to distributivity of
    the stored positive coefficients; in the strict branches, strict
    monotonicity of exponent addition selects the same surviving prefix. *)
Theorem onoteMul_add : forall a b c,
  NF a -> NF b -> NF c ->
  onoteMul a (onoteAdd b c) =
  onoteAdd (onoteMul a b) (onoteMul a c).
Proof.
  intros a b. revert a.
  induction b as [|be IHbe bc br IHbr]; intros a c ha hb hc.
  - rewrite onoteAdd_zero_l, onoteMul_zero_r, onoteAdd_zero_l.
    reflexivity.
  - destruct c as [|ce cc cr].
    + rewrite onoteAdd_zero_r_nf by exact hb.
      rewrite onoteMul_zero_r.
      rewrite onoteAdd_zero_r_nf.
      * reflexivity.
      * now apply onoteMul_nf.
    + destruct a as [|ae ac ar].
      { repeat rewrite onoteMul_zero_l. reflexivity. }
      pose proof ha as haFull.
      pose proof hb as hbFull.
      pose proof hc as hcFull.
      destruct ha as [hae [har htopA]].
      destruct hb as [hbe [hbr htopB]].
      destruct hc as [hce [hcr htopC]].
      assert (hmulB :
        NF (onoteMul (oadd ae ac ar) (oadd be bc br))).
      { apply onoteMul_nf; exact haFull || exact hbFull. }
      assert (hmulC :
        NF (onoteMul (oadd ae ac ar) (oadd ce cc cr))).
      { apply onoteMul_nf; exact haFull || exact hcFull. }
      destruct be as [|bee bec ber].
      * assert (hbr0 : br = ozero).
        { now apply NF_zero_exponent_tail with (c := bc). }
        subst br.
        destruct ce as [|cee cec cer].
        -- assert (hcr0 : cr = ozero).
           { now apply NF_zero_exponent_tail with (c := cc). }
           subst cr.
           rewrite (onoteAdd_nodes ozero bc ozero ozero cc ozero
             hbFull hcFull), onoteCompare_refl.
           cbn [onoteMul].
           rewrite (onoteAdd_nodes ae
             (coefficientProductPred ac bc) ar ae
             (coefficientProductPred ac cc) ar hmulB hmulC),
             onoteCompare_refl.
           now rewrite coefficientProductPred_add.
        -- rewrite (onoteAdd_nodes ozero bc ozero
             (oadd cee cec cer) cc cr hbFull hcFull).
           cbn [onoteCompare].
           cbn [onoteMul].
           assert (hhead : onoteCompare ae
             (onoteAdd ae (oadd cee cec cer)) = Lt).
           { apply onoteCompare_add_nonzero_right; [exact hae | discriminate]. }
           rewrite (onoteAdd_nodes ae
             (coefficientProductPred ac bc) ar
             (onoteAdd ae (oadd cee cec cer)) cc
             (onoteMul (oadd ae ac ar) cr) hmulB hmulC).
           now rewrite hhead.
      * destruct ce as [|cee cec cer].
        -- assert (hcr0 : cr = ozero).
           { now apply NF_zero_exponent_tail with (c := cc). }
           subst cr.
           rewrite (onoteAdd_nodes (oadd bee bec ber) bc br
             ozero cc ozero hbFull hcFull).
           cbn [onoteCompare].
           cbn [onoteMul].
           assert (hheadLt : onoteCompare ae
             (onoteAdd ae (oadd bee bec ber)) = Lt).
           { apply onoteCompare_add_nonzero_right; [exact hae | discriminate]. }
           apply onoteCompare_lt_reverse in hheadLt.
           rewrite (onoteAdd_nodes
             (onoteAdd ae (oadd bee bec ber)) bc
             (onoteMul (oadd ae ac ar) br) ae
             (coefficientProductPred ac cc) ar hmulB hmulC).
           rewrite hheadLt.
           f_equal.
           apply IHbr; try assumption.
        -- destruct (onoteCompare (oadd bee bec ber)
             (oadd cee cec cer)) eqn:hcmp.
           ++ apply onoteCompare_eq in hcmp.
              replace (oadd cee cec cer) with (oadd bee bec ber) in *
                by exact hcmp.
              rewrite (onoteAdd_nodes (oadd bee bec ber) bc br
                (oadd bee bec ber) cc cr hbFull hcFull),
                onoteCompare_refl.
              cbn [onoteMul].
              rewrite (onoteAdd_nodes
                (onoteAdd ae (oadd bee bec ber)) bc
                (onoteMul (oadd ae ac ar) br)
                (onoteAdd ae (oadd bee bec ber)) cc
                (onoteMul (oadd ae ac ar) cr) hmulB hmulC),
                onoteCompare_refl.
              reflexivity.
           ++ assert (hhead : onoteCompare
                (onoteAdd ae (oadd bee bec ber))
                (onoteAdd ae (oadd cee cec cer)) = Lt).
              { apply onoteAdd_strict_right; assumption. }
              rewrite (onoteAdd_nodes (oadd bee bec ber) bc br
                (oadd cee cec cer) cc cr hbFull hcFull), hcmp.
              cbn [onoteMul].
              rewrite (onoteAdd_nodes
                (onoteAdd ae (oadd bee bec ber)) bc
                (onoteMul (oadd ae ac ar) br)
                (onoteAdd ae (oadd cee cec cer)) cc
                (onoteMul (oadd ae ac ar) cr) hmulB hmulC), hhead.
              reflexivity.
           ++ assert (hrev : onoteCompare (oadd cee cec cer)
                (oadd bee bec ber) = Lt).
              { now apply onoteCompare_gt_reverse. }
              assert (hheadRev : onoteCompare
                (onoteAdd ae (oadd cee cec cer))
                (onoteAdd ae (oadd bee bec ber)) = Lt).
              { apply onoteAdd_strict_right; assumption. }
              apply onoteCompare_lt_reverse in hheadRev.
              rewrite (onoteAdd_nodes (oadd bee bec ber) bc br
                (oadd cee cec cer) cc cr hbFull hcFull), hcmp.
              cbn [onoteMul].
              rewrite (onoteAdd_nodes
                (onoteAdd ae (oadd bee bec ber)) bc
                (onoteMul (oadd ae ac ar) br)
                (onoteAdd ae (oadd cee cec cer)) cc
                (onoteMul (oadd ae ac ar) cr) hmulB hmulC), hheadRev.
              f_equal.
              apply IHbr; try assumption.
Qed.

Theorem mulCode_addCode : forall a b c,
  ValidOrdinalCode a -> ValidOrdinalCode b -> ValidOrdinalCode c ->
  mulCode a (addCode b c) =
  addCode (mulCode a b) (mulCode a c).
Proof.
  intros a b c ha hb hc. apply decode_injective.
  rewrite decode_mulCode, !decode_addCode, !decode_mulCode.
  apply onoteMul_add; assumption.
Qed.

(** Associativity of multiplication is especially transparent from the CNF
    recursion on the third operand.  A finite multiplier associates by
    [coefficientProductPred_assoc].  A positive leading exponent associates
    because its new exponent is an ordinal sum, already known associative;
    the recursive tails are covered by the induction hypothesis. *)
Theorem onoteMul_assoc : forall a b c,
  NF a -> NF b -> NF c ->
  onoteMul (onoteMul a b) c = onoteMul a (onoteMul b c).
Proof.
  intros a b c. revert a b.
  induction c as [|ce IHce cc cr IHcr]; intros a b ha hb hc.
  - repeat rewrite onoteMul_zero_r. reflexivity.
  - destruct a as [|ae ac ar].
    { repeat rewrite onoteMul_zero_l. reflexivity. }
    destruct b as [|be bc br].
    { rewrite onoteMul_zero_r, !onoteMul_zero_l, onoteMul_zero_r.
      reflexivity. }
    pose proof ha as haFull.
    pose proof hb as hbFull.
    destruct hc as [hce [hcr htopC]].
    destruct ce as [|cee cec cer].
    + assert (hcr0 : cr = ozero).
      { now apply NF_zero_exponent_tail with (c := cc). }
      subst cr.
      destruct be as [|bee bec ber].
      * assert (hbr0 : br = ozero).
        { now apply NF_zero_exponent_tail with (c := bc). }
        subst br.
        cbn [onoteMul].
        now rewrite coefficientProductPred_assoc.
      * cbn [onoteMul]. reflexivity.
    + destruct be as [|bee bec ber].
      * assert (hbr0 : br = ozero).
        { now apply NF_zero_exponent_tail with (c := bc). }
        subst br.
        cbn [onoteMul onoteAdd].
        f_equal.
        change (onoteMul
          (onoteMul (oadd ae ac ar) (oadd ozero bc ozero)) cr =
          onoteMul (oadd ae ac ar)
            (onoteMul (oadd ozero bc ozero) cr)).
        exact (IHcr (oadd ae ac ar) (oadd ozero bc ozero)
          haFull hbFull hcr).
      * cbn [onoteMul].
        rewrite onoteAdd_assoc.
        assert (hsumNonzero :
          onoteAdd (oadd bee bec ber) (oadd cee cec cer) <> ozero).
        { intro hzero.
          pose proof (onoteCompare_add_nonzero_right
            (oadd bee bec ber) (oadd cee cec cer) (proj1 hbFull)
            ltac:(discriminate))
            as hstrict.
          rewrite hzero in hstrict. discriminate. }
        remember (onoteAdd (oadd bee bec ber) (oadd cee cec cer))
          as exponentSum eqn:hsum.
        destruct exponentSum as [|sumE sumC sumR].
        { contradiction. }
        cbn [onoteMul].
        f_equal.
        change (onoteMul
          (onoteMul (oadd ae ac ar) (oadd (oadd bee bec ber) bc br)) cr =
          onoteMul (oadd ae ac ar)
            (onoteMul (oadd (oadd bee bec ber) bc br) cr)).
        exact (IHcr (oadd ae ac ar)
          (oadd (oadd bee bec ber) bc br) haFull hbFull hcr).
Qed.

Theorem mulCode_assoc : forall a b c,
  ValidOrdinalCode a -> ValidOrdinalCode b -> ValidOrdinalCode c ->
  mulCode (mulCode a b) c = mulCode a (mulCode b c).
Proof.
  intros a b c ha hb hc. apply decode_injective.
  rewrite !decode_mulCode.
  apply onoteMul_assoc; assumption.
Qed.

(** * Exponentiation identities *)

(** Canonical finite CNFs, using the same predecessor coefficient convention
    as every other notation node. *)
Definition onoteNat (n : nat) : ONote :=
  match n with
  | 0 => ozero
  | S k => oadd ozero k ozero
  end.

Lemma onoteNat_nf : forall n, NF (onoteNat n).
Proof. intros [|n]; simpl; tauto. Qed.

Lemma onotePowAux_k_zero : forall e a0 a m,
  onotePowAux e a0 a 0 m =
  match m with
  | 0 => ozero
  | S k => oadd e k ozero
  end.
Proof. intros e a0 a [|m]; reflexivity. Qed.

Lemma onoteMulNat_zero_r : forall o, onoteMulNat o 0 = ozero.
Proof. intros [|e c r]; reflexivity. Qed.

Lemma onoteScale_zero : forall o, onoteScale ozero o = o.
Proof.
  induction o as [|e IHe c r IHr]; [reflexivity |].
  cbn [onoteScale onoteAdd]. now rewrite IHr.
Qed.

(** [onoteSplit] is not merely shape preserving: on a normal notation its
    two outputs reconstruct the original ordinal as the omega-divisible part
    followed by its canonical finite remainder. *)
Lemma onoteSplit_reconstruct : forall o q n,
  NF o -> onoteSplit o = (q, n) ->
  o = onoteAdd q (onoteNat n).
Proof.
  induction o as [|e IHe c r IHr]; intros q n ho hsplit.
  - cbn [onoteSplit] in hsplit. inversion hsplit. reflexivity.
  - pose proof ho as hoFull.
    destruct ho as [he [hr htop]].
    destruct e as [|ee ec er].
    + assert (hr0 : r = ozero).
      { now apply NF_zero_exponent_tail with (c := c). }
      subst r. cbn [onoteSplit] in hsplit.
      inversion hsplit; subst q n. reflexivity.
    + cbn [onoteSplit] in hsplit.
      destruct (onoteSplit r) as [r' k] eqn:hrsplit.
      inversion hsplit; subst q n.
      cbn [onoteAdd].
      rewrite <- (IHr r' k hr eq_refl).
      symmetry. apply onoteAddAux_reconstruct_nf. exact hoFull.
Qed.

Theorem onotePow_zero : forall base,
  onotePow base ozero = onoteOne.
Proof.
  intros [|e c r]; [reflexivity |].
  destruct e as [|ee ec er].
  - destruct c as [|c]; cbn [onotePow onoteSplit onotePowAux2 onoteSplit'];
      reflexivity.
  - unfold onotePow.
    cbn [onoteSplit].
    destruct (onoteSplit r) as [q n].
    cbn [onotePowAux2 onoteSplit onoteMul onoteOne].
    reflexivity.
Qed.

Theorem onotePow_one_nf : forall base,
  NF base -> onotePow base onoteOne = base.
Proof.
  intros base hbase.
  unfold onotePow.
  destruct (onoteSplit base) as [q n] eqn:hsplit.
  pose proof (onoteSplit_reconstruct base q n hbase hsplit) as hreconstruct.
  destruct q as [|a0 ac ar].
  - destruct n as [|n].
    + cbn [onotePowAux2 onoteOne].
      symmetry. exact hreconstruct.
    + destruct n as [|n].
      * cbn [onotePowAux2 onoteOne onoteNat] in hreconstruct |-.
        symmetry. exact hreconstruct.
      * cbn [onotePowAux2 onoteOne onoteSplit' onoteNat].
        rewrite Nat.pow_1_r, Nat.pred_succ.
        symmetry. exact hreconstruct.
  - cbn [onotePowAux2 onoteOne onoteSplit onoteMul onoteMulNat].
    change (onoteAdd
      (onoteScale
        (onoteAdd (onoteMul a0 ozero) (onoteMulNat a0 0))
        (oadd a0 ac ar))
      (onotePowAux (onoteMul a0 ozero) a0
        (onoteMulNat (oadd a0 ac ar) n) 0 n) = base).
    rewrite !onoteMul_zero_r.
    rewrite onoteMulNat_zero_r, !onoteAdd_zero_l.
    rewrite onoteScale_zero, onotePowAux_k_zero.
    symmetry. exact hreconstruct.
Qed.

Theorem pow_zeroCode : forall a,
  ValidOrdinalCode a -> powCode a zeroCode = oneCode.
Proof.
  intros a _. apply decode_injective.
  rewrite decode_powCode, decode_zeroCode, decode_oneCode.
  apply onotePow_zero.
Qed.

Theorem pow_oneCode : forall a,
  ValidOrdinalCode a -> powCode a oneCode = a.
Proof.
  intros a ha. apply decode_injective.
  rewrite decode_powCode, decode_oneCode.
  apply onotePow_one_nf. exact ha.
Qed.

Corollary zeroCode_pow_zeroCode :
  powCode zeroCode zeroCode = oneCode.
Proof. apply pow_zeroCode. exact zeroCode_valid. Qed.

End PAEpsilonZeroLaws.
