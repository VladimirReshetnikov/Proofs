/-
  ClassicalCompleteness.lean

  Textbook interfaces for Gödel's completeness theorem, backed by the
  repository's independent Henkin construction in `Completeness.lean`.

  The underlying first-order language is the fixed countable language of
  equality and one binary relation used throughout this development.
-/
import FirstOrder.Compactness

namespace SetTheory.FirstOrderClassicalCompleteness

open Form
open FirstOrderCompactness

/-- Semantic consequence from a finite context. -/
def SemanticConsequence (G : List Form) (phi : Form) : Prop :=
  ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
    (∀ g ∈ G, Sat m v g) → Sat m v phi

/-- Syntactic consequence in the repository's natural-deduction calculus. -/
def SyntacticConsequence (G : List Form) (phi : Form) : Prop :=
  Prov G phi

/-- Validity is semantic consequence from the empty context. -/
def LogicallyValid (phi : Form) : Prop :=
  SemanticConsequence [] phi

/-- Semantic consequence from a possibly infinite theory. -/
def TheorySemanticConsequence (T : Form → Prop) (phi : Form) : Prop :=
  ∀ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
    (∀ g, T g → Sat m v g) → Sat m v phi

/-- A derivation from an infinite theory has explicit finite axiom support. -/
def TheorySyntacticConsequence (T : Form → Prop) (phi : Form) : Prop :=
  BProv T [] phi

/-- Syntactic consistency of a theory: falsity is not derivable from it. -/
def TheoryConsistent (T : Form → Prop) : Prop :=
  BCon T []

/-- **Gödel completeness, finite-context form:** semantic consequence implies
syntactic consequence.  This stronger open-formula formulation quantifies
over assignments as well as structures. -/
theorem godel_completeness (G : List Form) (phi : Form) :
    SemanticConsequence G phi → SyntacticConsequence G phi :=
  completeness G phi

/-- Soundness and completeness identify derivability with semantic
consequence. -/
theorem godel_soundness_and_completeness (G : List Form) (phi : Form) :
    SyntacticConsequence G phi ↔ SemanticConsequence G phi :=
  prov_iff_valid G phi

/-- Gödel's original validity formulation: every logically valid formula is
derivable without assumptions. -/
theorem godel_original_completeness (phi : Form) :
    LogicallyValid phi → Prov [] phi :=
  godel_completeness [] phi

/-- **Gödel completeness for arbitrary sentence theories:** if every model
of `T` satisfies `phi`, then a finite subset of `T` proves `phi`. -/
theorem godel_completeness_for_theories (T : Form → Prop) (phi : Form)
    (hT : Sentences T) :
    TheorySemanticConsequence T phi → TheorySyntacticConsequence T phi := by
  intro h
  exact completeness_inf_context T [] phi hT
    (fun Dom m v hmodel _ => h Dom m v hmodel)

/-- Soundness and completeness for an arbitrary sentence theory. -/
theorem godel_soundness_and_completeness_for_theories
    (T : Form → Prop) (phi : Form) (hT : Sentences T) :
    TheorySyntacticConsequence T phi ↔ TheorySemanticConsequence T phi := by
  constructor
  · intro hp Dom m v hmodel
    exact soundness_BProv hp v hmodel (fun g hg => nomatch hg)
  · exact godel_completeness_for_theories T phi hT

/-- **Model-existence form of Gödel completeness:** every syntactically
consistent theory of sentences has a model. -/
theorem godel_model_existence (T : Form → Prop) (hT : Sentences T) :
    TheoryConsistent T → TheoryHasModel T := by
  intro hcon
  obtain ⟨Dom, m, v, hmodel, _⟩ := model_of_BCon T [] hT hcon
  exact ⟨Dom, m, v, hmodel⟩

end SetTheory.FirstOrderClassicalCompleteness
