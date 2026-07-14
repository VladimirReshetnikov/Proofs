import NoFiniteModel.Theorem

/-! Concrete consequences of the no-finite-PA-model theorem. -/

namespace LeanProofs
namespace NoFinitePAModel

/-- No finite ordinal `Fin n` carries a shallow PA model. -/
theorem no_PA_model_on_fin (n : Nat) :
    ¬ Nonempty (SetTheory.PA.Model (Fin n)) := by
  rintro ⟨M⟩
  exact model_carrier_not_finite M (fin_isFiniteType n)

/-- In particular, even a one-element carrier cannot be a PA model. -/
example : ¬ Nonempty (SetTheory.PA.Model (Fin 1)) :=
  no_PA_model_on_fin 1

/-- The standard natural-number PA model gives a direct certified instance
of an infinite carrier in the explicit sense. -/
theorem nat_not_finite : ¬ IsFiniteType Nat :=
  model_carrier_not_finite SetTheory.PA.natModel

end NoFinitePAModel
end LeanProofs
