import PAListCoding.Hyperoperation
import PAListCoding.TetrationAssembly

/-!
# The variable-rank hyperoperator is Diophantine

The semantic evaluator in `Hyperoperation` reduces every exponentiation-or-
higher call to reachability in a fixed binary relation.  This file proves the
four branches of that relation Diophantine, applies the unconditional exact-
iteration compiler, and then adds the elementary ranks zero through two.

The public graph is result-first:

```text
(result, rank, base, argument)
```

and uses the conventional numbering in which ranks three, four, and five are
exponentiation, tetration, and pentation respectively.
-/

namespace PAListCoding

open Fin2
open scoped Dioph

private theorem and_dioph {α : Type} {P Q : (α → ℕ) → Prop}
    (dP : Dioph {v | P v}) (dQ : Dioph {v | Q v}) :
    Dioph {v | P v ∧ Q v} := by
  apply Dioph.ext (Dioph.inter dP dQ)
  intro v
  rfl

private theorem or_dioph {α : Type} {P Q : (α → ℕ) → Prop}
    (dP : Dioph {v | P v}) (dQ : Dioph {v | Q v}) :
    Dioph {v | P v ∨ Q v} := by
  apply Dioph.ext (Dioph.union dP dQ)
  intro v
  rfl

/-! ## Polynomial state constructors -/

theorem hyperPair_diophFn {α : Type} {x y : (α → ℕ) → ℕ}
    (dx : Dioph.DiophFn x) (dy : Dioph.DiophFn y) :
    Dioph.DiophFn (fun v => hyperPair (x v) (y v)) := by
  have dsum : Dioph.DiophFn (fun v => x v + y v) :=
    Dioph.add_dioph dx dy
  simpa only [hyperPair] using
    Dioph.add_dioph (Dioph.mul_dioph dsum dsum) dy

theorem hyperStackCons_diophFn {α : Type} {rank stack : (α → ℕ) → ℕ}
    (drank : Dioph.DiophFn rank) (dstack : Dioph.DiophFn stack) :
    Dioph.DiophFn (fun v => hyperStackCons (rank v) (stack v)) := by
  have done : Dioph.DiophFn (fun _v : α → ℕ => 1) :=
    Dioph.const_dioph 1
  simpa only [hyperStackCons] using
    Dioph.add_dioph (hyperPair_diophFn drank dstack) done

theorem hyperEvalCode_diophFn {α : Type}
    {base rank argument stack : (α → ℕ) → ℕ}
    (dbase : Dioph.DiophFn base) (drank : Dioph.DiophFn rank)
    (dargument : Dioph.DiophFn argument) (dstack : Dioph.DiophFn stack) :
    Dioph.DiophFn
      (fun v => hyperEvalCode (base v) (rank v) (argument v) (stack v)) := by
  have dzero : Dioph.DiophFn (fun _v : α → ℕ => 0) :=
    Dioph.const_dioph 0
  have dargumentStack := hyperPair_diophFn dargument dstack
  have drankWork := hyperPair_diophFn drank dargumentStack
  have dtagged := hyperPair_diophFn dzero drankWork
  simpa only [hyperEvalCode] using hyperPair_diophFn dbase dtagged

theorem hyperReturnCode_diophFn {α : Type}
    {base value stack : (α → ℕ) → ℕ}
    (dbase : Dioph.DiophFn base) (dvalue : Dioph.DiophFn value)
    (dstack : Dioph.DiophFn stack) :
    Dioph.DiophFn
      (fun v => hyperReturnCode (base v) (value v) (stack v)) := by
  have done : Dioph.DiophFn (fun _v : α → ℕ => 1) :=
    Dioph.const_dioph 1
  have dvalueStack := hyperPair_diophFn dvalue dstack
  have dtagged := hyperPair_diophFn done dvalueStack
  simpa only [hyperReturnCode] using hyperPair_diophFn dbase dtagged

/-! ## The four machine branches -/

private abbrev HyperWire := Fin 4

private def hyperWireValues (rank base argument stack : ℕ) :
    HyperWire → ℕ :=
  ![rank, base, argument, stack]

/-- A single four-number witness tuple is shared by all transition branches:
rank, base, argument-or-value, and stack. -/
def HyperStepCertificate (source target : ℕ) : Prop :=
  ∃ w : HyperWire → ℕ,
    (source = hyperEvalCode (w 1) 0 (w 2) (w 3) ∧
      target = hyperReturnCode (w 1) ((w 1) ^ (w 2)) (w 3)) ∨
    (source = hyperEvalCode (w 1) (w 0 + 1) 0 (w 3) ∧
      target = hyperReturnCode (w 1) 1 (w 3)) ∨
    (source = hyperEvalCode (w 1) (w 0 + 1) (w 2 + 1) (w 3) ∧
      target = hyperEvalCode (w 1) (w 0 + 1) (w 2)
        (hyperStackCons (w 0) (w 3))) ∨
    (source = hyperReturnCode (w 1) (w 2)
        (hyperStackCons (w 0) (w 3)) ∧
      target = hyperEvalCode (w 1) (w 0) (w 2) (w 3))

theorem hyperStep_iff_certificate (source target : ℕ) :
    HyperStep source target ↔ HyperStepCertificate source target := by
  constructor
  · rintro (hpower | hzero | hsucc | hreturn)
    · rcases hpower with ⟨base, argument, stack, hsource, htarget⟩
      exact ⟨hyperWireValues 0 base argument stack,
        Or.inl (by simpa [hyperWireValues] using And.intro hsource htarget)⟩
    · rcases hzero with ⟨rank, base, stack, hsource, htarget⟩
      exact ⟨hyperWireValues rank base 0 stack,
        Or.inr <| Or.inl <| by
          simpa [hyperWireValues] using And.intro hsource htarget⟩
    · rcases hsucc with ⟨rank, base, argument, stack, hsource, htarget⟩
      exact ⟨hyperWireValues rank base argument stack,
        Or.inr <| Or.inr <| Or.inl <| by
          simpa [hyperWireValues] using And.intro hsource htarget⟩
    · rcases hreturn with ⟨rank, base, value, stack, hsource, htarget⟩
      exact ⟨hyperWireValues rank base value stack,
        Or.inr <| Or.inr <| Or.inr <| by
          simpa [hyperWireValues] using And.intro hsource htarget⟩
  · rintro ⟨w, hpower | hzero | hsucc | hreturn⟩
    · exact Or.inl ⟨w 1, w 2, w 3, hpower⟩
    · exact Or.inr <| Or.inl ⟨w 0, w 1, w 3, hzero⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨w 0, w 1, w 2, w 3, hsucc⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨w 0, w 1, w 2, w 3, hreturn⟩

/-- The fixed evaluator transition is Diophantine.  The rank-zero branch uses
Matiyasevich exponentiation; every other expression is polynomial. -/
theorem hyperStep_diophantine :
    Dioph {v : Vector3 ℕ 2 | HyperStep (v &0) (v &1)} := by
  let source : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inl &0)
  let target : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inl &1)
  let rank : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inr 0)
  let base : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inr 1)
  let argument : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inr 2)
  let stack : ((Fin2 2 ⊕ HyperWire) → ℕ) → ℕ :=
    fun v => v (Sum.inr 3)
  have dsource : Dioph.DiophFn source := Dioph.proj_dioph (Sum.inl &0)
  have dtarget : Dioph.DiophFn target := Dioph.proj_dioph (Sum.inl &1)
  have drank : Dioph.DiophFn rank := Dioph.proj_dioph (Sum.inr 0)
  have dbase : Dioph.DiophFn base := Dioph.proj_dioph (Sum.inr 1)
  have dargument : Dioph.DiophFn argument := Dioph.proj_dioph (Sum.inr 2)
  have dstack : Dioph.DiophFn stack := Dioph.proj_dioph (Sum.inr 3)
  have dzero : Dioph.DiophFn
      (fun _v : (Fin2 2 ⊕ HyperWire) → ℕ => 0) :=
    Dioph.const_dioph 0
  have done : Dioph.DiophFn
      (fun _v : (Fin2 2 ⊕ HyperWire) → ℕ => 1) :=
    Dioph.const_dioph 1
  have drankSucc : Dioph.DiophFn (fun v => rank v + 1) :=
    Dioph.add_dioph drank done
  have dargumentSucc : Dioph.DiophFn (fun v => argument v + 1) :=
    Dioph.add_dioph dargument done
  have dpower : Dioph.DiophFn (fun v => (base v) ^ (argument v)) :=
    Dioph.pow_dioph dbase dargument
  have dcons : Dioph.DiophFn
      (fun v => hyperStackCons (rank v) (stack v)) :=
    hyperStackCons_diophFn drank dstack

  have devalPower := hyperEvalCode_diophFn dbase dzero dargument dstack
  have dreturnPower := hyperReturnCode_diophFn dbase dpower dstack
  have devalZero := hyperEvalCode_diophFn dbase drankSucc dzero dstack
  have dreturnOne := hyperReturnCode_diophFn dbase done dstack
  have devalSucc :=
    hyperEvalCode_diophFn dbase drankSucc dargumentSucc dstack
  have devalPushed := hyperEvalCode_diophFn dbase drankSucc dargument dcons
  have dreturnPushed := hyperReturnCode_diophFn dbase dargument dcons
  have devalPopped := hyperEvalCode_diophFn dbase drank dargument dstack

  have dPowerCase : Dioph {v : (Fin2 2 ⊕ HyperWire) → ℕ |
      source v = hyperEvalCode (base v) 0 (argument v) (stack v) ∧
      target v = hyperReturnCode (base v) ((base v) ^ (argument v))
        (stack v)} :=
    and_dioph (Dioph.eq_dioph dsource devalPower)
      (Dioph.eq_dioph dtarget dreturnPower)
  have dZeroCase : Dioph {v : (Fin2 2 ⊕ HyperWire) → ℕ |
      source v = hyperEvalCode (base v) (rank v + 1) 0 (stack v) ∧
      target v = hyperReturnCode (base v) 1 (stack v)} :=
    and_dioph (Dioph.eq_dioph dsource devalZero)
      (Dioph.eq_dioph dtarget dreturnOne)
  have dSuccCase : Dioph {v : (Fin2 2 ⊕ HyperWire) → ℕ |
      source v = hyperEvalCode (base v) (rank v + 1) (argument v + 1)
        (stack v) ∧
      target v = hyperEvalCode (base v) (rank v + 1) (argument v)
        (hyperStackCons (rank v) (stack v))} :=
    and_dioph (Dioph.eq_dioph dsource devalSucc)
      (Dioph.eq_dioph dtarget devalPushed)
  have dReturnCase : Dioph {v : (Fin2 2 ⊕ HyperWire) → ℕ |
      source v = hyperReturnCode (base v) (argument v)
        (hyperStackCons (rank v) (stack v)) ∧
      target v = hyperEvalCode (base v) (rank v) (argument v) (stack v)} :=
    and_dioph (Dioph.eq_dioph dsource dreturnPushed)
      (Dioph.eq_dioph dtarget devalPopped)
  have dBody : Dioph {v : (Fin2 2 ⊕ HyperWire) → ℕ |
      (source v = hyperEvalCode (base v) 0 (argument v) (stack v) ∧
        target v = hyperReturnCode (base v) ((base v) ^ (argument v))
          (stack v)) ∨
      (source v = hyperEvalCode (base v) (rank v + 1) 0 (stack v) ∧
        target v = hyperReturnCode (base v) 1 (stack v)) ∨
      (source v = hyperEvalCode (base v) (rank v + 1) (argument v + 1)
          (stack v) ∧
        target v = hyperEvalCode (base v) (rank v + 1) (argument v)
          (hyperStackCons (rank v) (stack v))) ∨
      (source v = hyperReturnCode (base v) (argument v)
          (hyperStackCons (rank v) (stack v)) ∧
        target v = hyperEvalCode (base v) (rank v) (argument v) (stack v))} :=
    or_dioph dPowerCase <| or_dioph dZeroCase <|
      or_dioph dSuccCase dReturnCase
  have dCertificate : Dioph {v : Vector3 ℕ 2 |
      HyperStepCertificate (v &0) (v &1)} := by
    apply Dioph.ext (Dioph.ex_dioph dBody)
    intro v
    rfl
  apply Dioph.ext dCertificate
  intro v
  exact (hyperStep_iff_certificate (v &0) (v &1)).symm

/-! ## Unconditional reachability compilation -/

private theorem hyperOnesClosed : CipherRelations.OnesSubstitutionClosed := by
  intro α len q ones shifted dlen dq dones dshifted
  exact CipherOnes.onesCodes_dioph dlen dq dones dshifted

private theorem hyperCodeClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.Code :=
  CipherRelations.code_closed_of_ones hyperOnesClosed

private theorem hyperFixedConstClosed :
    ∀ k, CircuitDioph.TernarySubstitutionClosed
      (fun len q code => SparseCipher.ConstCode len q k code) :=
  CipherRelations.constCode_fixed_closed_of_ones hyperOnesClosed

private theorem hyperConstClosed :
    BoundedCipherDioph.QuaternarySubstitutionClosed
      SparseCipher.ConstCode := by
  change CipherRelations.QuaternarySubstitutionClosed SparseCipher.ConstCode
  exact CipherRelations.constCode_closed_of_ones hyperOnesClosed

private theorem hyperIndexClosed :
    CircuitDioph.TernarySubstitutionClosed SparseCipher.IndexCode :=
  CipherRelations.indexCode_closed_of_ones hyperOnesClosed

private theorem hyperMulClosed :
    CircuitDioph.QuinarySubstitutionClosed BoundedCipher.MulRel :=
  CipherRelations.mulRel_closed_of_ones hyperOnesClosed

private def singletonWitness (n : ℕ) : Unit → ℕ := fun _ => n

/-- Existential reachability in a fixed Diophantine transition relation is
Diophantine under arbitrary Diophantine endpoint substitutions. -/
private theorem existsExactIter_dioph {α : Type} {R : ℕ → ℕ → Prop}
    {start finish : (α → ℕ) → ℕ}
    (dR : Dioph {v : Vector3 ℕ 2 | R (v &0) (v &1)})
    (dstart : Dioph.DiophFn start) (dfinish : Dioph.DiophFn finish) :
    Dioph {v : α → ℕ |
      ∃ steps, ExactIter R steps (start v) (finish v)} := by
  have dstart' : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => start (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dstart
  have dfinish' : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => finish (v ∘ Sum.inl)) :=
    Dioph.reindex_diophFn Sum.inl dfinish
  have dsteps : Dioph.DiophFn
      (fun v : (α ⊕ Unit) → ℕ => v (Sum.inr ())) :=
    Dioph.proj_dioph (Sum.inr ())
  have diter : Dioph {v : (α ⊕ Unit) → ℕ |
      ExactIter R (v (Sum.inr ()))
        (start (v ∘ Sum.inl)) (finish (v ∘ Sum.inl))} :=
    IterationDioph.exactIter_dioph hyperCodeClosed hyperFixedConstClosed
      hyperConstClosed hyperIndexClosed hyperMulClosed dR
      dsteps dstart' dfinish'
  have dex : Dioph {v : α → ℕ |
      ∃ w : Unit → ℕ, ExactIter R (w ()) (start v) (finish v)} := by
    apply Dioph.ext (Dioph.ex_dioph diter)
    intro v
    rfl
  apply Dioph.ext dex
  intro v
  constructor
  · rintro ⟨w, hrun⟩
    exact ⟨w (), hrun⟩
  · rintro ⟨steps, hrun⟩
    exact ⟨singletonWitness steps, hrun⟩

/-! ## The uniform core graph -/

/-- Result-first graph for the uniform exponentiation-and-above hierarchy. -/
def NaturalHyperoperationCoreGraph : Set (Vector3 ℕ 4) :=
  {v | v &0 = hyperoperationCore (v &1) (v &2) (v &3)}

theorem naturalHyperoperationCoreGraph_diophantine :
    Dioph NaturalHyperoperationCoreGraph := by
  have dresult : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &0) := D&0
  have drank : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &1) := D&1
  have dbase : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &2) := D&2
  have dargument : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &3) := D&3
  have dzero : Dioph.DiophFn (fun _v : Vector3 ℕ 4 => 0) :=
    Dioph.const_dioph 0
  have dstart : Dioph.DiophFn
      (fun v : Vector3 ℕ 4 => hyperEvalCode (v &2) (v &1) (v &3) 0) :=
    hyperEvalCode_diophFn dbase drank dargument dzero
  have dfinish : Dioph.DiophFn
      (fun v : Vector3 ℕ 4 => hyperReturnCode (v &2) (v &0) 0) :=
    hyperReturnCode_diophFn dbase dresult dzero
  have dreach : Dioph {v : Vector3 ℕ 4 |
      ∃ steps, ExactIter HyperStep steps
        (hyperEvalCode (v &2) (v &1) (v &3) 0)
        (hyperReturnCode (v &2) (v &0) 0)} :=
    existsExactIter_dioph hyperStep_diophantine dstart dfinish
  apply Dioph.ext dreach
  intro v
  exact (hyperoperationCore_eq_iff_exists_exactIter
    (v &0) (v &1) (v &2) (v &3)).symm

/-! ## Conventional ranks zero through infinity -/

/-- Arithmetic case split matching the conventional public rank numbering. -/
def HyperoperatorCases (result rank base argument : ℕ) : Prop :=
  (rank = 0 ∧ result = argument + 1) ∨
  (rank = 1 ∧ result = base + argument) ∨
  (rank = 2 ∧ result = base * argument) ∨
  ∃ coreRank, rank = coreRank + 3 ∧
    result = hyperoperationCore coreRank base argument

theorem hyperoperator_eq_iff_cases (result rank base argument : ℕ) :
    result = hyperoperator rank base argument ↔
      HyperoperatorCases result rank base argument := by
  rcases rank with _ | rank
  · simp [HyperoperatorCases, hyperoperator]
  rcases rank with _ | rank
  · simp [HyperoperatorCases, hyperoperator]
  rcases rank with _ | rank
  · simp [HyperoperatorCases, hyperoperator]
  · constructor
    · intro hresult
      exact Or.inr <| Or.inr <| Or.inr
        ⟨rank, rfl, by simpa [hyperoperator] using hresult⟩
    · rintro (_hzero | _hone | _htwo | ⟨coreRank, hrank, hresult⟩)
      · omega
      · omega
      · omega
      · have : rank = coreRank := by omega
        subst coreRank
        simpa [hyperoperator] using hresult

private def coreGraphEmbedding :
    Fin2 4 → (Fin2 4 ⊕ Unit)
  | Fin2.fz => Sum.inl &0
  | Fin2.fs Fin2.fz => Sum.inr ()
  | Fin2.fs (Fin2.fs Fin2.fz) => Sum.inl &2
  | Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz)) => Sum.inl &3

private def coreRankWitness (rank : ℕ) : Unit → ℕ := fun _ => rank

theorem hyperoperatorCases_diophantine :
    Dioph {v : Vector3 ℕ 4 |
      HyperoperatorCases (v &0) (v &1) (v &2) (v &3)} := by
  have dresult : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &0) := D&0
  have drank : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &1) := D&1
  have dbase : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &2) := D&2
  have dargument : Dioph.DiophFn (fun v : Vector3 ℕ 4 => v &3) := D&3
  have dzero : Dioph.DiophFn (fun _v : Vector3 ℕ 4 => 0) :=
    Dioph.const_dioph 0
  have done : Dioph.DiophFn (fun _v : Vector3 ℕ 4 => 1) :=
    Dioph.const_dioph 1
  have dtwo : Dioph.DiophFn (fun _v : Vector3 ℕ 4 => 2) :=
    Dioph.const_dioph 2
  have dthree : Dioph.DiophFn (fun _v : Vector3 ℕ 4 => 3) :=
    Dioph.const_dioph 3
  have dargumentSucc : Dioph.DiophFn (fun v => v &3 + 1) :=
    Dioph.add_dioph dargument done
  have dbaseAddArgument : Dioph.DiophFn (fun v => v &2 + v &3) :=
    Dioph.add_dioph dbase dargument
  have dbaseMulArgument : Dioph.DiophFn (fun v => v &2 * v &3) :=
    Dioph.mul_dioph dbase dargument
  have dZero : Dioph {v : Vector3 ℕ 4 |
      v &1 = 0 ∧ v &0 = v &3 + 1} :=
    and_dioph (Dioph.eq_dioph drank dzero)
      (Dioph.eq_dioph dresult dargumentSucc)
  have dOne : Dioph {v : Vector3 ℕ 4 |
      v &1 = 1 ∧ v &0 = v &2 + v &3} :=
    and_dioph (Dioph.eq_dioph drank done)
      (Dioph.eq_dioph dresult dbaseAddArgument)
  have dTwo : Dioph {v : Vector3 ℕ 4 |
      v &1 = 2 ∧ v &0 = v &2 * v &3} :=
    and_dioph (Dioph.eq_dioph drank dtwo)
      (Dioph.eq_dioph dresult dbaseMulArgument)

  have dresult' : Dioph.DiophFn
      (fun v : (Fin2 4 ⊕ Unit) → ℕ => v (Sum.inl &0)) :=
    Dioph.proj_dioph (Sum.inl &0)
  have drank' : Dioph.DiophFn
      (fun v : (Fin2 4 ⊕ Unit) → ℕ => v (Sum.inl &1)) :=
    Dioph.proj_dioph (Sum.inl &1)
  have dcoreRank : Dioph.DiophFn
      (fun v : (Fin2 4 ⊕ Unit) → ℕ => v (Sum.inr ())) :=
    Dioph.proj_dioph (Sum.inr ())
  have dthree' : Dioph.DiophFn
      (fun _v : (Fin2 4 ⊕ Unit) → ℕ => 3) :=
    Dioph.const_dioph 3
  have dcorePlusThree : Dioph.DiophFn
      (fun v : (Fin2 4 ⊕ Unit) → ℕ => v (Sum.inr ()) + 3) :=
    Dioph.add_dioph dcoreRank dthree'
  have dcoreGraph : Dioph {v : (Fin2 4 ⊕ Unit) → ℕ |
      v (Sum.inl &0) = hyperoperationCore (v (Sum.inr ()))
        (v (Sum.inl &2)) (v (Sum.inl &3))} := by
    apply Dioph.ext <|
      Dioph.reindex_dioph (Fin2 4 ⊕ Unit) coreGraphEmbedding
        naturalHyperoperationCoreGraph_diophantine
    intro v
    change
      (v ∘ coreGraphEmbedding) &0 =
          hyperoperationCore ((v ∘ coreGraphEmbedding) &1)
            ((v ∘ coreGraphEmbedding) &2) ((v ∘ coreGraphEmbedding) &3) ↔ _
    rfl
  have dHighBody : Dioph {v : (Fin2 4 ⊕ Unit) → ℕ |
      v (Sum.inl &1) = v (Sum.inr ()) + 3 ∧
      v (Sum.inl &0) = hyperoperationCore (v (Sum.inr ()))
        (v (Sum.inl &2)) (v (Sum.inl &3))} :=
    and_dioph (Dioph.eq_dioph drank' dcorePlusThree) dcoreGraph
  have dHighFunctions : Dioph {v : Vector3 ℕ 4 |
      ∃ w : Unit → ℕ,
        v &1 = w () + 3 ∧
        v &0 = hyperoperationCore (w ()) (v &2) (v &3)} := by
    apply Dioph.ext (Dioph.ex_dioph dHighBody)
    intro v
    rfl
  have dHigh : Dioph {v : Vector3 ℕ 4 |
      ∃ coreRank, v &1 = coreRank + 3 ∧
        v &0 = hyperoperationCore coreRank (v &2) (v &3)} := by
    apply Dioph.ext dHighFunctions
    intro v
    constructor
    · rintro ⟨w, h⟩
      exact ⟨w (), h⟩
    · rintro ⟨coreRank, h⟩
      exact ⟨coreRankWitness coreRank, h⟩
  exact or_dioph dZero <| or_dioph dOne <| or_dioph dTwo dHigh

/-- The three-input hyperoperator function, ordered rank, base, argument. -/
def NaturalHyperoperatorFunction (v : Vector3 ℕ 3) : ℕ :=
  hyperoperator (v &0) (v &1) (v &2)

/-- Result-first graph `(result, rank, base, argument)`. -/
def NaturalHyperoperatorGraph : Set (Vector3 ℕ 4) :=
  {v | v &0 = hyperoperator (v &1) (v &2) (v &3)}

/-- The conventional variable-rank natural hyperoperator graph is
Diophantine. -/
theorem naturalHyperoperatorGraph_diophantine :
    Dioph NaturalHyperoperatorGraph := by
  apply Dioph.ext hyperoperatorCases_diophantine
  intro v
  exact (hyperoperator_eq_iff_cases (v &0) (v &1) (v &2) (v &3)).symm

/-- The standard three-argument hyperoperator is a Diophantine function. -/
theorem naturalHyperoperator_diophantineFunction :
    Dioph.DiophFn NaturalHyperoperatorFunction := by
  apply (Dioph.diophFn_vec NaturalHyperoperatorFunction).2
  apply Dioph.ext naturalHyperoperatorGraph_diophantine
  intro v
  change
    (v &0 = hyperoperator (v &1) (v &2) (v &3)) ↔
      (hyperoperator (v &1) (v &2) (v &3) = v &0)
  exact eq_comm

/-- Unfolded witness contract: one integer polynomial and a fixed tuple of
existential natural variables define the full result-first graph. -/
theorem naturalHyperoperator_polynomial_exists :
    ∃ (β : Type) (p : Poly (Fin2 4 ⊕ β)),
      ∀ v : Vector3 ℕ 4,
        v &0 = hyperoperator (v &1) (v &2) (v &3) ↔
          ∃ t : β → ℕ, p (Sum.elim v t) = 0 :=
  naturalHyperoperatorGraph_diophantine

end PAListCoding
