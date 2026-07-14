/-
  SetTheory.PAHF.RawSemantics

  Raw PA semantics on the ordinal-like part of an arbitrary chosen
  first-order finite-adjunction model of HF.  The carrier is deliberately
  packaged only as `PA.PreModel`: a nonstandard first-order model must not be
  given the meta-level induction field carried by `PA.Model`.
-/
import PAHF.Interpretation

namespace SetTheory

namespace AckermannHF

namespace PAInHF

open Form

universe u

noncomputable section

/-! ## The chosen raw arithmetic algebra -/

/-- The ordinal-like objects of a first-order finite-adjunction model. -/
def FOFAMOrdinal {α : Type u} (M : FirstOrderFiniteAdjunctionModel α) : Type u :=
  {x : α // OrdinalLike M.mem x}

/-- A successor-recursion trace witnesses that `z` is `a + b`. -/
def fofamAddRelation {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a b z : α) : Prop :=
  ∃ f,
    FirstOrderAdjunctionModel.SuccRecApprox
      M.toFirstOrderAdjunctionModel a f b ∧
    M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel b z) f

theorem fofamAddRelation_total {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    ∃ z, fofamAddRelation M a.val b.val z := by
  rcases FirstOrderFiniteAdjunctionModel.succRecTotal_of_ordinalLike
      M a.val b.val b.property with ⟨f, z, hf, hz⟩
  exact ⟨z, f, hf, hz⟩

noncomputable def fofamAddValue {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) : α :=
  Classical.choose (fofamAddRelation_total M a b)

theorem fofamAddValue_spec {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    fofamAddRelation M a.val b.val (fofamAddValue M a b) :=
  Classical.choose_spec (fofamAddRelation_total M a b)

/-- Chosen addition on the ordinal-like carrier. -/
noncomputable def fofamOrdinalAdd {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (a b : FOFAMOrdinal M) : FOFAMOrdinal M :=
  ⟨fofamAddValue M a b, by
    rcases fofamAddValue_spec M a b with ⟨f, hf, hz⟩
    exact FirstOrderFiniteAdjunctionModel.succRecApprox_value_ordinalLike
      M a.property b.property hf hz⟩

theorem fofamOrdinalAdd_spec {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    fofamAddRelation M a.val b.val (fofamOrdinalAdd M a b).val := by
  change fofamAddRelation M a.val b.val (fofamAddValue M a b)
  exact fofamAddValue_spec M a b

/-- A multiplication-recursion trace witnesses that `z` is `a * b`. -/
def fofamMulRelation {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (a b z : α) : Prop :=
  ∃ f,
    MulRecApprox M.toFirstOrderAdjunctionModel a f b ∧
    M.mem (FirstOrderAdjunctionModel.kpair
      M.toFirstOrderAdjunctionModel b z) f

theorem fofamMulRelation_total {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    ∃ z, fofamMulRelation M a.val b.val z := by
  rcases mulRecTotal_of_ordinalLike_finite_model
      M a.val b.val a.property b.property with ⟨f, z, hf, hz⟩
  exact ⟨z, f, hf, hz⟩

noncomputable def fofamMulValue {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) : α :=
  Classical.choose (fofamMulRelation_total M a b)

theorem fofamMulValue_spec {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    fofamMulRelation M a.val b.val (fofamMulValue M a b) :=
  Classical.choose_spec (fofamMulRelation_total M a b)

/-- Chosen multiplication on the ordinal-like carrier. -/
noncomputable def fofamOrdinalMul {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (a b : FOFAMOrdinal M) : FOFAMOrdinal M :=
  ⟨fofamMulValue M a b, by
    rcases fofamMulValue_spec M a b with ⟨f, hf, hz⟩
    exact mulRecApprox_value_ordinalLike
      M a.property b.property hf hz⟩

theorem fofamOrdinalMul_spec {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (a b : FOFAMOrdinal M) :
    fofamMulRelation M a.val b.val (fofamOrdinalMul M a b).val := by
  change fofamMulRelation M a.val b.val (fofamMulValue M a b)
  exact fofamMulValue_spec M a b

def fofamOrdinalZero {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) : FOFAMOrdinal M :=
  ⟨M.empty,
    FirstOrderAdjunctionModel.ordinalLike_empty
      M.toFirstOrderAdjunctionModel⟩

def fofamOrdinalSucc {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (a : FOFAMOrdinal M) : FOFAMOrdinal M :=
  ⟨M.adjoin a.val a.val,
    FirstOrderAdjunctionModel.ordinalLike_adjoin_self
      M.toFirstOrderAdjunctionModel a.property rfl⟩

/-- The raw arithmetic structure extracted from `M`.  No arithmetic laws and
no meta-level induction principle are smuggled into this bundle. -/
noncomputable def fofamPAPreModel {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) : PA.PreModel (FOFAMOrdinal M) where
  zero := fofamOrdinalZero M
  succ := fofamOrdinalSucc M
  add := fofamOrdinalAdd M
  mul := fofamOrdinalMul M

@[simp] theorem fofamPAPreModel_zero {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    (fofamPAPreModel M).zero = fofamOrdinalZero M := rfl

@[simp] theorem fofamPAPreModel_succ {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    (fofamPAPreModel M).succ = fofamOrdinalSucc M := rfl

@[simp] theorem fofamPAPreModel_add {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    (fofamPAPreModel M).add = fofamOrdinalAdd M := rfl

@[simp] theorem fofamPAPreModel_mul {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) :
    (fofamPAPreModel M).mul = fofamOrdinalMul M := rfl

/-- Coq-parity name for ordinary `PA.Term.eval` in the raw model. -/
abbrev fofamPATermEval {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e : Nat → FOFAMOrdinal M) (t : PA.Term) : FOFAMOrdinal M :=
  PA.Term.eval (fofamPAPreModel M) e t

/-- Coq-parity name for ordinary `PA.Formula.Sat` in the raw model. -/
abbrev fofamPAFormulaSat {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (e : Nat → FOFAMOrdinal M) (phi : PA.Formula) : Prop :=
  PA.Formula.Sat (fofamPAPreModel M) e phi

/-! ## The chosen evaluator is exactly the translated term graph -/

/-- Every raw term value is realized by its HF graph. -/
theorem fofamPATermEval_graph {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term) :
    ∀ (ρ : Nat → Nat) (e : Nat → α) (v : Nat → FOFAMOrdinal M),
      (∀ n, PA.Term.Free n t → e (ρ n) = (v n).val) →
      Sat M.mem (scons (fofamPATermEval M v t).val e)
        (termGraphAt (fun n => ρ n + 1) 0 t) := by
  induction t with
  | var n =>
      intro ρ e v hvars
      change (v n).val = e (ρ n)
      exact (hvars n rfl).symm
  | zero =>
      intro ρ e v _hvars
      apply (FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel
        (scons (fofamPATermEval M v PA.Term.zero).val e) 0).mpr
      rfl
  | succ t ih =>
      intro ρ e v hvars
      let x := fofamPATermEval M v t
      let sx := fofamOrdinalSucc M x
      have hxGraph : Sat M.mem (scons x.val e)
          (termGraphAt (fun n => ρ n + 1) 0 t) :=
        ih ρ e v hvars
      change Sat M.mem (scons sx.val e)
        (termGraphAt (fun n => ρ n + 1) 0 (PA.Term.succ t))
      refine ⟨x.val, ?_, ?_⟩
      · exact Sat_termGraphAt_insert_after_output t ρ e x.val sx.val hxGraph
      · apply (FirstOrderAdjunctionModel.HF_succAt_spec
          M.toFirstOrderAdjunctionModel
          (scons x.val (scons sx.val e)) 1 0).mpr
        rfl
  | add a b iha ihb =>
      intro ρ e v hvars
      let x := fofamPATermEval M v a
      let y := fofamPATermEval M v b
      let z := fofamOrdinalAdd M x y
      have hxGraph : Sat M.mem (scons x.val e)
          (termGraphAt (fun n => ρ n + 1) 0 a) :=
        iha ρ e v (fun n hn => hvars n (Or.inl hn))
      have hyGraph : Sat M.mem (scons y.val e)
          (termGraphAt (fun n => ρ n + 1) 0 b) :=
        ihb ρ e v (fun n hn => hvars n (Or.inr hn))
      rcases fofamOrdinalAdd_spec M x y with ⟨f, hf, hz⟩
      let E : Nat → α := scons y.val (scons x.val (scons z.val e))
      have hxGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 2) 1 a) := by
        have h1 : Sat M.mem (scons x.val (scons z.val e))
            (termGraphAt (fun n => ρ n + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a ρ e x.val z.val hxGraph
        have h2 : Sat M.mem E
            (termGraphAt (fun n => (ρ n + 2) + 1) 1 a) :=
          Sat_termGraphAt_shift_front a (fun n => ρ n + 2) 0
            (scons x.val (scons z.val e)) y.val h1
        simpa [E, Nat.add_assoc] using h2
      have hyGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 2) 0 b) := by
        have h1 : Sat M.mem (scons y.val (scons z.val e))
            (termGraphAt (fun n => ρ n + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b ρ e y.val z.val hyGraph
        have h2 : Sat M.mem E
            (termGraphAt (fun n => (ρ n + 1) + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b (fun n => ρ n + 1)
            (scons z.val e) y.val x.val h1
        simpa [E, Nat.add_assoc] using h2
      change Sat M.mem (scons z.val e)
        (termGraphAt (fun n => ρ n + 1) 0 (PA.Term.add a b))
      refine ⟨x.val, y.val, hxGraphE, hyGraphE, ?_⟩
      apply addGraphAt_of_succRecApprox_model M.toFirstOrderAdjunctionModel
        E 2 1 0 (f := f)
      · exact hf
      · exact hz
  | mul a b iha ihb =>
      intro ρ e v hvars
      let x := fofamPATermEval M v a
      let y := fofamPATermEval M v b
      let z := fofamOrdinalMul M x y
      have hxGraph : Sat M.mem (scons x.val e)
          (termGraphAt (fun n => ρ n + 1) 0 a) :=
        iha ρ e v (fun n hn => hvars n (Or.inl hn))
      have hyGraph : Sat M.mem (scons y.val e)
          (termGraphAt (fun n => ρ n + 1) 0 b) :=
        ihb ρ e v (fun n hn => hvars n (Or.inr hn))
      rcases fofamOrdinalMul_spec M x y with ⟨f, hf, hz⟩
      let E : Nat → α :=
        scons z.val (scons x.val (scons y.val (scons z.val e)))
      have hxGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 3) 1 a) := by
        have h1 : Sat M.mem (scons x.val (scons z.val e))
            (termGraphAt (fun n => ρ n + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a ρ e x.val z.val hxGraph
        have h2 : Sat M.mem (scons x.val (scons y.val (scons z.val e)))
            (termGraphAt (fun n => (ρ n + 1) + 2) 0 a) :=
          Sat_termGraphAt_insert_after_output a (fun n => ρ n + 1)
            (scons z.val e) x.val y.val h1
        have h3 : Sat M.mem E
            (termGraphAt (fun n => ((ρ n + 1) + 2) + 1) 1 a) :=
          Sat_termGraphAt_shift_front a (fun n => (ρ n + 1) + 2) 0
            (scons x.val (scons y.val (scons z.val e))) z.val h2
        simpa [E, Nat.add_assoc] using h3
      have hyGraphE : Sat M.mem E
          (termGraphAt (fun n => (ρ n + 1) + 3) 2 b) := by
        have h1 : Sat M.mem (scons y.val (scons z.val e))
            (termGraphAt (fun n => ρ n + 2) 0 b) :=
          Sat_termGraphAt_insert_after_output b ρ e y.val z.val hyGraph
        have h2 : Sat M.mem (scons x.val (scons y.val (scons z.val e)))
            (termGraphAt (fun n => (ρ n + 2) + 1) 1 b) :=
          Sat_termGraphAt_shift_front b (fun n => ρ n + 2) 0
            (scons y.val (scons z.val e)) x.val h1
        have h3 : Sat M.mem E
            (termGraphAt (fun n => ((ρ n + 2) + 1) + 1) 2 b) :=
          Sat_termGraphAt_shift_front b (fun n => (ρ n + 2) + 1) 1
            (scons x.val (scons y.val (scons z.val e))) z.val h2
        simpa [E, Nat.add_assoc] using h3
      change Sat M.mem (scons z.val e)
        (termGraphAt (fun n => ρ n + 1) 0 (PA.Term.mul a b))
      refine ⟨y.val, x.val, z.val, hxGraphE, hyGraphE, rfl, ?_⟩
      apply mulGraphAt_of_mulRecApprox_model M.toFirstOrderAdjunctionModel
        E 0 1 2 (f := f)
      · exact hf
      · exact hz

/-- Any satisfied graph with the right free inputs has the chosen evaluator
value at its output slot. -/
theorem fofamPATermEval_graph_value {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term)
    (ρ : Nat → Nat) (out : Nat) (e : Nat → α)
    (v : Nat → FOFAMOrdinal M)
    (hvars : ∀ n, PA.Term.Free n t → e (ρ n) = (v n).val)
    (hgraph : Sat M.mem e (termGraphAt ρ out t)) :
    e out = (fofamPATermEval M v t).val := by
  let eCanon : Nat → α := fun n => (v n).val
  have hcanon : Sat M.mem
      (scons (fofamPATermEval M v t).val eCanon)
      (termGraphAt (fun n => n + 1) 0 t) :=
    fofamPATermEval_graph M t (fun n => n) eCanon v
      (fun _ _ => rfl)
  apply termGraphAt_outputs_eq_finite_model M t
      (ρ₁ := ρ) (ρ₂ := fun n => n + 1)
      (out₁ := out) (out₂ := 0)
      (e₁ := e)
      (e₂ := scons (fofamPATermEval M v t).val eCanon)
  · intro n hn
    simpa [eCanon, scons] using hvars n hn
  · intro n hn
    rw [hvars n hn]
    exact (v n).property
  · exact hgraph
  · exact hcanon

/-- A translated term graph is precisely equality with the chosen raw value.
The reverse implication uses semantic graph transport, so the statement works
at arbitrary output and variable slots rather than only in the canonical head
environment. -/
theorem fofamPATermEval_graph_iff {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (t : PA.Term)
    (ρ : Nat → Nat) (out : Nat) (e : Nat → α)
    (v : Nat → FOFAMOrdinal M)
    (hvars : ∀ n, PA.Term.Free n t → e (ρ n) = (v n).val) :
    Sat M.mem e (termGraphAt ρ out t) ↔
      e out = (fofamPATermEval M v t).val := by
  constructor
  · exact fofamPATermEval_graph_value M t ρ out e v hvars
  · intro hout
    have hcanon := fofamPATermEval_graph M t ρ e v hvars
    apply termGraphAt_transport_model M.toFirstOrderAdjunctionModel t
      (ρ₁ := fun n => ρ n + 1) (ρ₂ := ρ)
      (out₁ := 0) (out₂ := out)
      (e₁ := scons (fofamPATermEval M v t).val e) (e₂ := e)
    · exact hout.symm
    · intro n hn
      rfl
    · exact hcanon

/-! ## Formula translation is raw satisfaction -/

/-- The PA-to-HF formula translation is exactly Tarski satisfaction in the
raw ordinal `PreModel`.  Quantifiers are the only genuinely semantic cases:
`domainForm` converts an ambient HF witness to and from `FOFAMOrdinal`. -/
theorem formulaAt_iff_fofamPAFormulaSat {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α) (phi : PA.Formula) :
    ∀ (ρ : Nat → Nat) (e : Nat → α) (v : Nat → FOFAMOrdinal M),
      (∀ n, PA.Formula.Free n phi → e (ρ n) = (v n).val) →
      (Sat M.mem e (formulaAt ρ phi) ↔ fofamPAFormulaSat M v phi) := by
  induction phi with
  | eq a b =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      constructor
      · rintro ⟨x, y, ha, hb, hxy⟩
        let E : Nat → α := scons y (scons x e)
        have hxa : x = (fofamPATermEval M v a).val := by
          have hvarsA : ∀ n, PA.Term.Free n a →
              E (ρ n + 2) = (v n).val := by
            intro n hn
            simpa [E, scons] using hvars n (Or.inl hn)
          exact (fofamPATermEval_graph_iff M a
            (fun n => ρ n + 2) 1 E v hvarsA).mp ha
        have hyb : y = (fofamPATermEval M v b).val := by
          have hvarsB : ∀ n, PA.Term.Free n b →
              E (ρ n + 2) = (v n).val := by
            intro n hn
            simpa [E, scons] using hvars n (Or.inr hn)
          exact (fofamPATermEval_graph_iff M b
            (fun n => ρ n + 2) 0 E v hvarsB).mp hb
        apply Subtype.ext
        exact hxa.symm.trans (hxy.trans hyb)
      · intro hab
        let va := fofamPATermEval M v a
        let vb := fofamPATermEval M v b
        let E : Nat → α := scons vb.val (scons va.val e)
        refine ⟨va.val, vb.val, ?_, ?_, ?_⟩
        · have hvarsA : ∀ n, PA.Term.Free n a →
              E (ρ n + 2) = (v n).val := by
            intro n hn
            simpa [E, scons] using hvars n (Or.inl hn)
          apply (fofamPATermEval_graph_iff M a
            (fun n => ρ n + 2) 1 E v hvarsA).mpr
          rfl
        · have hvarsB : ∀ n, PA.Term.Free n b →
              E (ρ n + 2) = (v n).val := by
            intro n hn
            simpa [E, scons] using hvars n (Or.inr hn)
          apply (fofamPATermEval_graph_iff M b
            (fun n => ρ n + 2) 0 E v hvarsB).mpr
          rfl
        · exact congrArg Subtype.val hab
  | bot =>
      intro ρ e v hvars
      exact Iff.rfl
  | imp a b iha ihb =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      have ha := iha ρ e v (fun n hn => hvars n (Or.inl hn))
      have hb := ihb ρ e v (fun n hn => hvars n (Or.inr hn))
      exact ⟨
        fun hab haRaw => hb.mp (hab (ha.mpr haRaw)),
        fun hab haHF => hb.mpr (hab (ha.mp haHF))⟩
  | and a b iha ihb =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      have ha := iha ρ e v (fun n hn => hvars n (Or.inl hn))
      have hb := ihb ρ e v (fun n hn => hvars n (Or.inr hn))
      exact and_congr ha hb
  | or a b iha ihb =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      have ha := iha ρ e v (fun n hn => hvars n (Or.inl hn))
      have hb := ihb ρ e v (fun n hn => hvars n (Or.inr hn))
      exact or_congr ha hb
  | all a ih =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      constructor
      · intro hall x
        have hiff := ih (upVarMap ρ) (scons x.val e) (scons x v)
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ n => simpa [upVarMap, scons] using hvars n hn)
        apply hiff.mp
        apply hall x.val
        apply (HF_ordinalLikeAt_spec (scons x.val e) 0).mpr
        exact x.property
      · intro hall d hdDomain
        have hdOrd : OrdinalLike M.mem d :=
          (HF_ordinalLikeAt_spec (scons d e) 0).mp hdDomain
        let x : FOFAMOrdinal M := ⟨d, hdOrd⟩
        have hiff := ih (upVarMap ρ) (scons d e) (scons x v)
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ n => simpa [upVarMap, scons] using hvars n hn)
        exact hiff.mpr (hall x)
  | ex a ih =>
      intro ρ e v hvars
      simp only [formulaAt, Sat, PA.Formula.Sat]
      constructor
      · rintro ⟨d, hdDomain, hbody⟩
        have hdOrd : OrdinalLike M.mem d :=
          (HF_ordinalLikeAt_spec (scons d e) 0).mp hdDomain
        let x : FOFAMOrdinal M := ⟨d, hdOrd⟩
        refine ⟨x, ?_⟩
        have hiff := ih (upVarMap ρ) (scons d e) (scons x v)
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ n => simpa [upVarMap, scons] using hvars n hn)
        exact hiff.mp hbody
      · rintro ⟨x, hbody⟩
        refine ⟨x.val, ?_, ?_⟩
        · apply (HF_ordinalLikeAt_spec (scons x.val e) 0).mpr
          exact x.property
        · have hiff := ih (upVarMap ρ) (scons x.val e) (scons x v)
            (fun n hn => by
              cases n with
              | zero => rfl
              | succ n => simpa [upVarMap, scons] using hvars n hn)
          exact hiff.mpr hbody

/-! ## PA axioms and derivations are valid in the raw algebra -/

/-- Raw natural deduction is sound because `PA.Formula.soundness` requires
only a `PreModel`, not any arithmetic laws. -/
theorem fofam_PA_Prov_soundness {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.Prov G phi) :
    ∀ e : Nat → FOFAMOrdinal M,
      (∀ psi, psi ∈ G → fofamPAFormulaSat M e psi) →
      fofamPAFormulaSat M e phi :=
  PA.Formula.soundness (fofamPAPreModel M) h

/-- Every sealed PA axiom is true in the raw ordinal algebra extracted from
an arbitrary first-order finite-adjunction model. -/
theorem fofam_PA_Ax_s_valid {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    (phi : PA.Formula) (e : Nat → FOFAMOrdinal M) :
    PA.Formula.Ax_s phi → fofamPAFormulaSat M e phi := by
  intro hphi
  let eVal : Nat → α := fun n => (e n).val
  apply (formulaAt_iff_fofamPAFormulaSat M phi
    (fun n => n) eVal e (fun _ _ => rfl)).mp
  rcases hphi with rfl | rfl | rfl | rfl | rfl | rfl | ⟨psi, rfl⟩
  · apply formulaAt_sealPA_valid PA.Formula.succInj
    intro ρ env
    exact formulaAt_succInj_of_irrefl
      (FirstOrderAdjunctionModel.mem_irrefl M.toFirstOrderAdjunctionModel)
      ρ env
  · apply formulaAt_sealPA_valid PA.Formula.zeroNotSucc
    intro ρ env
    exact formulaAt_zeroNotSucc_valid ρ env
  · apply formulaAt_sealPA_valid PA.Formula.addZero
    intro ρ env
    exact formulaAt_addZero_valid_model M.toFirstOrderAdjunctionModel ρ env
  · apply formulaAt_sealPA_valid PA.Formula.addSucc
    intro ρ env
    exact formulaAt_addSucc_valid_finite_model M ρ env
  · apply formulaAt_sealPA_valid PA.Formula.mulZero
    intro ρ env
    exact formulaAt_mulZero_valid_model M.toFirstOrderAdjunctionModel ρ env
  · apply formulaAt_sealPA_valid PA.Formula.mulSucc
    intro ρ env
    exact formulaAt_mulSucc_valid_finite_model M ρ env
  · apply formulaAt_sealPA_valid (PA.Formula.inductionForm psi)
    intro ρ env
    exact formulaAt_induction_valid_finite_model M psi ρ env

/-- Relative PA provability is sound directly in the raw ordinal algebra.
No `PA.Model` instance, and therefore no unjustified meta-level induction
field, is introduced. -/
theorem fofam_PA_BProv_soundness {α : Type u}
    (M : FirstOrderFiniteAdjunctionModel α)
    {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.BProv PA.Formula.Ax_s G phi) :
    ∀ e : Nat → FOFAMOrdinal M,
      (∀ psi, psi ∈ G → fofamPAFormulaSat M e psi) →
      fofamPAFormulaSat M e phi := by
  intro e hG
  exact PA.Formula.soundness_BProv (fofamPAPreModel M) h e
    (fun ax hax => fofam_PA_Ax_s_valid M ax e hax) hG

end

end PAInHF

end AckermannHF

end SetTheory
