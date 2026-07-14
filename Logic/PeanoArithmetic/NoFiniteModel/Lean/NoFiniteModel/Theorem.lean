import NoFiniteModel.FiniteTypes
import PAHF.PASyntax

/-!
# Peano arithmetic has no finite model

In every shallow PA model from `PAHF.PASyntax`, successor is injective and
zero is not a successor.  On a finite carrier, however, an injective endomap
is surjective.  Applying surjectivity to zero gives the contradiction.
-/

namespace LeanProofs
namespace NoFinitePAModel

open Function

universe u

/-- A finite carrier cannot support an injective self-map whose range omits a
distinguished element.  This is the exact model-independent obstruction used
for PA successor and zero. -/
theorem finite_carrier_cannot_have_injective_successor_missing_zero
    {α : Type u} (hfinite : IsFiniteType α) (zero : α) (succ : α → α)
    (hsucc_injective : Function.Injective succ)
    (hzero_not_succ : ∀ a, succ a ≠ zero) : False := by
  have hsurj : Function.Surjective succ :=
    finite_self_surjective_of_injective hfinite succ hsucc_injective
  obtain ⟨a, ha⟩ := hsurj zero
  exact hzero_not_succ a ha

/-- The carrier of every shallow PA model is not equivalent to any `Fin n`. -/
theorem model_carrier_not_finite {α : Type u} (M : SetTheory.PA.Model α) :
    ¬ IsFiniteType α := by
  intro hfinite
  exact finite_carrier_cannot_have_injective_successor_missing_zero
    hfinite M.zero M.succ (fun _ _ h => M.succ_injective h) M.zero_not_succ

/-- Headline theorem: there is no finite carrier equipped with a shallow
model of Peano arithmetic. -/
theorem no_finite_PA_model :
    ¬ ∃ (α : Type u), ∃ _M : SetTheory.PA.Model α, IsFiniteType α := by
  rintro ⟨α, M, hfinite⟩
  exact model_carrier_not_finite M hfinite

/-- Equivalent packaging with finiteness placed before the model witness. -/
theorem no_finite_type_supports_PA_model :
    ¬ ∃ (α : Type u), IsFiniteType α ∧ Nonempty (SetTheory.PA.Model α) := by
  rintro ⟨α, hfinite, ⟨M⟩⟩
  exact model_carrier_not_finite M hfinite

end NoFinitePAModel
end LeanProofs
