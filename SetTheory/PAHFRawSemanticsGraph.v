(* ===================================================================== *)
(*  PAHFRawSemanticsGraph.v                                             *)
(*                                                                       *)
(*  Connect the lightweight ordinal PA algebra with translated HF term   *)
(*  graphs and formulas.  Functionality is isolated as a semantic law so *)
(*  the structural proof-translation argument stays independent of the  *)
(*  internal trace-uniqueness implementation.                            *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List ClassicalEpsilon.
From SetTheory Require Import Fol Calculus Completeness PAHF
  PAHFInterpretations PAHFTermGraphModel PAHFTermGraphTotal
  PAHFRawSemantics.

Import ListNotations.

Definition FOFAMTermGraphFunctionalLaw {V : Type}
    (M : FirstOrderFiniteAdjunctionModel V) : Prop :=
  forall (t : PA.term) (rho1 rho2 : nat -> nat) out1 out2
    (e1 e2 : nat -> V),
  (forall n, PA.Term.Free n t -> e1 (rho1 n) = e2 (rho2 n)) ->
  (forall n, PA.Term.Free n t ->
    OrdinalLike (foam_mem V M) (e1 (rho1 n))) ->
  Sat V (foam_mem V M) e1 (termGraphAt rho1 out1 t) ->
  Sat V (foam_mem V M) e2 (termGraphAt rho2 out2 t) ->
  e1 out1 = e2 out2.

(* The chosen raw-algebra evaluator is realized by the graph relation. *)
Theorem fofamPATermEval_graph :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (t : PA.term) (rho : nat -> nat) (e : nat -> V)
    (v : nat -> FOFAMOrdinal M),
  (forall n, PA.Term.Free n t -> e (rho n) = proj1_sig (v n)) ->
  Sat V (foam_mem V M)
    (scons V (proj1_sig (fofamPATermEval M v t)) e)
    (termGraphAt (fun n => S (rho n)) 0 t).
Proof.
  intros V M t.
  induction t as [n | | t IH | a IHa b IHb | a IHa b IHb];
    intros rho e v hvars.
  - simpl.
    symmetry.
    apply hvars. reflexivity.
  - simpl.
    apply (proj2 (foam_HF_emptyAt_empty V M
      (scons V (foam_empty V M) e) 0)).
    reflexivity.
  - pose (x := fofamPATermEval M v t).
    pose (sx := fofamOrdinalSucc M x).
    assert (hxGraph :
        Sat V (foam_mem V M) (scons V (proj1_sig x) e)
          (termGraphAt (fun n => S (rho n)) 0 t)).
    {
      apply IH.
      exact hvars.
    }
    change (Sat V (foam_mem V M) (scons V (proj1_sig sx) e)
      (termGraphAt (fun n => S (rho n)) 0 (PA.tSucc t))).
    simpl.
    exists (proj1_sig x).
    split.
    + pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) t rho e (proj1_sig x) (proj1_sig sx)
        hxGraph) as h.
      replace (termGraphAt (fun n => S (rho n + 1)) 0 t)
        with (termGraphAt (fun n => S (S (rho n))) 0 t).
      * exact h.
      * apply termGraphAt_map_ext. intro k. lia.
    + apply (proj2 (foam_HF_succAt_spec V M
        (scons V (proj1_sig x) (scons V (proj1_sig sx) e)) 1 0)).
      unfold sx, fofamOrdinalSucc.
      reflexivity.
  - pose (x := fofamPATermEval M v a).
    pose (y := fofamPATermEval M v b).
    pose (z := fofamOrdinalAdd M x y).
    assert (hxGraph :
        Sat V (foam_mem V M) (scons V (proj1_sig x) e)
          (termGraphAt (fun n => S (rho n)) 0 a)).
    {
      apply IHa.
      intros n hn. apply hvars. now left.
    }
    assert (hyGraph :
        Sat V (foam_mem V M) (scons V (proj1_sig y) e)
          (termGraphAt (fun n => S (rho n)) 0 b)).
    {
      apply IHb.
      intros n hn. apply hvars. now right.
    }
    destruct (fofamOrdinalAdd_spec V M x y) as [f [hf hz]].
    pose (E := scons V (proj1_sig y)
      (scons V (proj1_sig x) (scons V (proj1_sig z) e))).
    assert (hxGraphE : Sat V (foam_mem V M) E
        (termGraphAt (fun n => S (rho n) + 2) 1 a)).
    {
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) a rho e (proj1_sig x) (proj1_sig z)
        hxGraph) as h1.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) a (fun n => S (S (rho n))) 0
        (scons V (proj1_sig x) (scons V (proj1_sig z) e))
        (proj1_sig y) h1) as h2.
      unfold E.
      rewrite (termGraphAt_map_ext a
        (fun n => S (rho n) + 2)
        (fun n => S (S (S (rho n)))) 1).
      - exact h2.
      - intro k. lia.
    }
    assert (hyGraphE : Sat V (foam_mem V M) E
        (termGraphAt (fun n => S (rho n) + 2) 0 b)).
    {
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) b rho e (proj1_sig y) (proj1_sig z)
        hyGraph) as h1.
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) b (fun n => S (rho n))
        (scons V (proj1_sig z) e) (proj1_sig y) (proj1_sig x)
        h1) as h2.
      unfold E.
      rewrite (termGraphAt_map_ext b
        (fun n => S (rho n) + 2)
        (fun n => S (S (S (rho n)))) 0).
      - exact h2.
      - intro k. lia.
    }
    change (Sat V (foam_mem V M) (scons V (proj1_sig z) e)
      (termGraphAt (fun n => S (rho n)) 0 (PA.tAdd a b))).
    simpl.
    exists (proj1_sig x), (proj1_sig y).
    repeat split.
    + exact hxGraphE.
    + exact hyGraphE.
    + apply (addGraphAt_of_succRecApprox_model V M E 2 1 0 f).
      * change (foam_succ_rec_approx V M
          (proj1_sig x) f (proj1_sig y)). exact hf.
      * change (foam_mem V M
          (foam_kpair_obj V M (proj1_sig y) (proj1_sig z)) f).
        exact hz.
  - pose (x := fofamPATermEval M v a).
    pose (y := fofamPATermEval M v b).
    pose (z := fofamOrdinalMul M x y).
    assert (hxGraph :
        Sat V (foam_mem V M) (scons V (proj1_sig x) e)
          (termGraphAt (fun n => S (rho n)) 0 a)).
    {
      apply IHa.
      intros n hn. apply hvars. now left.
    }
    assert (hyGraph :
        Sat V (foam_mem V M) (scons V (proj1_sig y) e)
          (termGraphAt (fun n => S (rho n)) 0 b)).
    {
      apply IHb.
      intros n hn. apply hvars. now right.
    }
    destruct (fofamOrdinalMul_spec V M x y) as [f [hf hz]].
    pose (E := scons V (proj1_sig z)
      (scons V (proj1_sig x)
        (scons V (proj1_sig y) (scons V (proj1_sig z) e)))).
    assert (hxGraphE : Sat V (foam_mem V M) E
        (termGraphAt (fun n => S (rho n) + 3) 1 a)).
    {
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) a rho e (proj1_sig x) (proj1_sig z)
        hxGraph) as h1.
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) a (fun n => S (rho n))
        (scons V (proj1_sig z) e) (proj1_sig x) (proj1_sig y)
        h1) as h2.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) a (fun n => S (S (S (rho n)))) 0
        (scons V (proj1_sig x)
          (scons V (proj1_sig y) (scons V (proj1_sig z) e)))
        (proj1_sig z) h2) as h3.
      unfold E.
      rewrite (termGraphAt_map_ext a
        (fun n => S (rho n) + 3)
        (fun n => S (S (S (S (rho n))))) 1).
      - exact h3.
      - intro k. lia.
    }
    assert (hyGraphE : Sat V (foam_mem V M) E
        (termGraphAt (fun n => S (rho n) + 3) 2 b)).
    {
      pose proof (Sat_termGraphAt_insert_after_output
        V (foam_mem V M) b rho e (proj1_sig y) (proj1_sig z)
        hyGraph) as h1.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) b (fun n => S (S (rho n))) 0
        (scons V (proj1_sig y) (scons V (proj1_sig z) e))
        (proj1_sig x) h1) as h2.
      pose proof (Sat_termGraphAt_shift_front
        V (foam_mem V M) b (fun n => S (S (S (rho n)))) 1
        (scons V (proj1_sig x)
          (scons V (proj1_sig y) (scons V (proj1_sig z) e)))
        (proj1_sig z) h2) as h3.
      unfold E.
      rewrite (termGraphAt_map_ext b
        (fun n => S (rho n) + 3)
        (fun n => S (S (S (S (rho n))))) 2).
      - exact h3.
      - intro k. lia.
    }
    change (Sat V (foam_mem V M) (scons V (proj1_sig z) e)
      (termGraphAt (fun n => S (rho n)) 0 (PA.tMul a b))).
    simpl.
    exists (proj1_sig y), (proj1_sig x), (proj1_sig z).
    repeat split.
    + exact hxGraphE.
    + exact hyGraphE.
    + apply (mulGraphAt_of_mulRecApprox_model V M E 0 1 2 f).
      * change (foam_mul_rec_approx V M
          (proj1_sig x) f (proj1_sig y)). exact hf.
      * change (foam_mem V M
          (foam_kpair_obj V M (proj1_sig y) (proj1_sig z)) f).
        exact hz.
Qed.

Lemma FOFAMOrdinal_eq :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V)
    (a b : FOFAMOrdinal M),
  proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros V M [a ha] [b hb] hab.
  simpl in hab. subst b.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma fofamPATermEval_graph_value :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  FOFAMTermGraphFunctionalLaw M ->
  forall t rho (e : nat -> V) (v : nat -> FOFAMOrdinal M) x,
  (forall n, PA.Term.Free n t -> e (rho n) = proj1_sig (v n)) ->
  Sat V (foam_mem V M) (scons V x e)
    (termGraphAt (fun n => S (rho n)) 0 t) ->
  x = proj1_sig (fofamPATermEval M v t).
Proof.
  intros V M hfun t rho e v x hvars hgraph.
  apply (hfun t
    (fun n => S (rho n)) (fun n => S (rho n)) 0 0
    (scons V x e)
    (scons V (proj1_sig (fofamPATermEval M v t)) e)).
  - intros n hn. reflexivity.
  - intros n hn.
    change (OrdinalLike (foam_mem V M) (e (rho n))).
    rewrite hvars by exact hn.
    exact (proj2_sig (v n)).
  - exact hgraph.
  - apply fofamPATermEval_graph.
    exact hvars.
Qed.

Theorem fofamPATermEval_graph_iff :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  FOFAMTermGraphFunctionalLaw M ->
  forall t rho (e : nat -> V) (v : nat -> FOFAMOrdinal M) x,
  (forall n, PA.Term.Free n t -> e (rho n) = proj1_sig (v n)) ->
  (Sat V (foam_mem V M) (scons V x e)
      (termGraphAt (fun n => S (rho n)) 0 t) <->
    x = proj1_sig (fofamPATermEval M v t)).
Proof.
  intros V M hfun t rho e v x hvars.
  split.
  - apply (fofamPATermEval_graph_value V M hfun t rho e v x hvars).
  - intro hx. subst x.
    apply fofamPATermEval_graph.
    exact hvars.
Qed.

(* The formula translation is exactly raw satisfaction in the ordinal
   algebra.  Quantifiers are the only interesting case: domainForm converts
   between raw HF witnesses and the ordinal subtype. *)
Theorem formulaAt_iff_fofamPAFormulaSat :
  forall (V : Type) (M : FirstOrderFiniteAdjunctionModel V),
  FOFAMTermGraphFunctionalLaw M ->
  forall phi rho (e : nat -> V) (v : nat -> FOFAMOrdinal M),
  (forall n, PA.Formula.Free n phi ->
    e (rho n) = proj1_sig (v n)) ->
  (Sat V (foam_mem V M) e (formulaAt rho phi) <->
    fofamPAFormulaSat M v phi).
Proof.
  intros V M hfun phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    intros rho e v hvars; simpl.
  - split.
    + intros [x [y [ha [hb hxy]]]].
      pose (va := fofamPATermEval M v a).
      pose (vb := fofamPATermEval M v b).
      assert (hga : Sat V (foam_mem V M)
          (scons V (proj1_sig va) e)
          (termGraphAt (fun n => S (rho n)) 0 a)).
      {
        apply fofamPATermEval_graph.
        intros n hn. apply hvars. now left.
      }
      assert (hgb : Sat V (foam_mem V M)
          (scons V (proj1_sig vb) e)
          (termGraphAt (fun n => S (rho n)) 0 b)).
      {
        apply fofamPATermEval_graph.
        intros n hn. apply hvars. now right.
      }
      assert (hxa : x = proj1_sig va).
      {
        apply (hfun a
          (fun n => rho n + 2) (fun n => S (rho n)) 1 0
          (scons V y (scons V x e))
          (scons V (proj1_sig va) e)).
        - intros n hn.
          replace (rho n + 2) with (S (S (rho n))) by lia.
          reflexivity.
        - intros n hn.
          replace (rho n + 2) with (S (S (rho n))) by lia.
          change (OrdinalLike (foam_mem V M) (e (rho n))).
          rewrite hvars by (now left).
          exact (proj2_sig (v n)).
        - exact ha.
        - exact hga.
      }
      assert (hyb : y = proj1_sig vb).
      {
        apply (hfun b
          (fun n => rho n + 2) (fun n => S (rho n)) 0 0
          (scons V y (scons V x e))
          (scons V (proj1_sig vb) e)).
        - intros n hn.
          replace (rho n + 2) with (S (S (rho n))) by lia.
          reflexivity.
        - intros n hn.
          replace (rho n + 2) with (S (S (rho n))) by lia.
          change (OrdinalLike (foam_mem V M) (e (rho n))).
          rewrite hvars by (now right).
          exact (proj2_sig (v n)).
        - exact hb.
        - exact hgb.
      }
      apply (FOFAMOrdinal_eq V M va vb).
      rewrite <- hxa, <- hyb.
      exact hxy.
    + intro hab.
      pose (va := fofamPATermEval M v a).
      pose (vb := fofamPATermEval M v b).
      assert (hga : Sat V (foam_mem V M)
          (scons V (proj1_sig va) e)
          (termGraphAt (fun n => S (rho n)) 0 a)).
      {
        apply fofamPATermEval_graph.
        intros n hn. apply hvars. now left.
      }
      assert (hgb : Sat V (foam_mem V M)
          (scons V (proj1_sig vb) e)
          (termGraphAt (fun n => S (rho n)) 0 b)).
      {
        apply fofamPATermEval_graph.
        intros n hn. apply hvars. now right.
      }
      pose (E := scons V (proj1_sig vb) (scons V (proj1_sig va) e)).
      assert (hgaE : Sat V (foam_mem V M) E
          (termGraphAt (fun n => rho n + 2) 1 a)).
      {
        pose proof (Sat_termGraphAt_shift_front V (foam_mem V M)
          a (fun n => S (rho n)) 0 (scons V (proj1_sig va) e)
          (proj1_sig vb) hga) as h.
        unfold E.
        rewrite (termGraphAt_map_ext a
          (fun n => rho n + 2) (fun n => S (S (rho n))) 1).
        - exact h.
        - intro n. lia.
      }
      assert (hgbE : Sat V (foam_mem V M) E
          (termGraphAt (fun n => rho n + 2) 0 b)).
      {
        pose proof (Sat_termGraphAt_insert_after_output V (foam_mem V M)
          b rho e (proj1_sig vb) (proj1_sig va) hgb) as h.
        unfold E.
        rewrite (termGraphAt_map_ext b
          (fun n => rho n + 2) (fun n => S (S (rho n))) 0).
        - exact h.
        - intro n. lia.
      }
      exists (proj1_sig va), (proj1_sig vb).
      repeat split.
      * exact hgaE.
      * exact hgbE.
      * change (va = vb) in hab.
        exact (f_equal (@proj1_sig V
          (fun q => OrdinalLike (foam_mem V M) q)) hab).
  - reflexivity.
  - specialize (IHa rho e v (fun n hn => hvars n (or_introl hn))).
    specialize (IHb rho e v (fun n hn => hvars n (or_intror hn))).
    tauto.
  - specialize (IHa rho e v (fun n hn => hvars n (or_introl hn))).
    specialize (IHb rho e v (fun n hn => hvars n (or_intror hn))).
    tauto.
  - specialize (IHa rho e v (fun n hn => hvars n (or_introl hn))).
    specialize (IHb rho e v (fun n hn => hvars n (or_intror hn))).
    tauto.
  - split.
    + intros hall x.
      pose proof (IHa (upVarMap rho)
        (scons V (proj1_sig x) e) (scons _ x v)
        (fun n hn => match n as q return
          PA.Formula.Free q a ->
          scons V (proj1_sig x) e (upVarMap rho q) =
            proj1_sig (scons _ x v q) with
        | 0 => fun _ => eq_refl
        | S k => fun hk => hvars k hk
        end hn)) as hiff.
      apply (proj1 hiff).
      apply hall.
        apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V (proj1_sig x) e) 0)).
        exact (proj2_sig x).
    + intros hall d hdDomain.
      assert (hdOrd : OrdinalLike (foam_mem V M) d).
      {
        exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V d e) 0) hdDomain).
      }
      pose (x := (exist _ d hdOrd : FOFAMOrdinal M)).
      pose proof (IHa (upVarMap rho) (scons V d e) (scons _ x v)
        (fun n hn => match n as q return
          PA.Formula.Free q a ->
          scons V d e (upVarMap rho q) = proj1_sig (scons _ x v q) with
        | 0 => fun _ => eq_refl
        | S k => fun hk => hvars k hk
        end hn)) as hiff.
      apply (proj2 hiff).
      exact (hall x).
  - split.
    + intros [d [hdDomain hbody]].
      assert (hdOrd : OrdinalLike (foam_mem V M) d).
      {
        exact (proj1 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V d e) 0) hdDomain).
      }
      pose (x := (exist _ d hdOrd : FOFAMOrdinal M)).
      exists x.
      pose proof (IHa (upVarMap rho) (scons V d e) (scons _ x v)
        (fun n hn => match n as q return
          PA.Formula.Free q a ->
          scons V d e (upVarMap rho q) = proj1_sig (scons _ x v q) with
        | 0 => fun _ => eq_refl
        | S k => fun hk => hvars k hk
        end hn)) as hiff.
      apply (proj1 hiff).
      exact hbody.
    + intros [x hbody].
      exists (proj1_sig x).
      split.
      * apply (proj2 (HF_ordinalLikeAt_spec V (foam_mem V M)
          (scons V (proj1_sig x) e) 0)).
        exact (proj2_sig x).
      * pose proof (IHa (upVarMap rho)
          (scons V (proj1_sig x) e) (scons _ x v)
          (fun n hn => match n as q return
            PA.Formula.Free q a ->
            scons V (proj1_sig x) e (upVarMap rho q) =
              proj1_sig (scons _ x v q) with
          | 0 => fun _ => eq_refl
          | S k => fun hk => hvars k hk
          end hn)) as hiff.
        apply (proj2 hiff).
        exact hbody.
Qed.
