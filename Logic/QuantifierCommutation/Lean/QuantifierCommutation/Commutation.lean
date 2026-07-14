/-!
# Commuting like adjacent quantifiers

Adjacent universal quantifiers commute, as do adjacent existential
quantifiers.  Both equivalences are constructive and allow the two bound
variables to range over unrelated types.
-/

namespace LeanProofs
namespace QuantifierCommutation

/-- Adjacent universal quantifiers commute constructively. -/
theorem forall_forall_commute {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    (∀ x, ∀ y, R x y) ↔ (∀ y, ∀ x, R x y) :=
  ⟨fun h y x => h x y, fun h x y => h y x⟩

/-- Adjacent existential quantifiers commute constructively. -/
theorem exists_exists_commute {α : Sort u} {β : Sort v}
    (R : α → β → Prop) :
    (∃ x, ∃ y, R x y) ↔ (∃ y, ∃ x, R x y) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨y, x, hxy⟩
  · rintro ⟨y, x, hxy⟩
    exact ⟨x, y, hxy⟩

end QuantifierCommutation
end LeanProofs
