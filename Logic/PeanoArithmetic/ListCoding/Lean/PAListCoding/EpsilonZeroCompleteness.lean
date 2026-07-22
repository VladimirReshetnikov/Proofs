import PAListCoding.EpsilonZero

/-!
# Completeness of the epsilon-zero notation codes

`EpsilonZero` proves the soundness direction: every valid natural code
denotes an ordinal below `ε₀`.  This file proves the converse.  The proof
performs hereditary Cantor decomposition at base `ω`; both the leading
exponent and the remainder are strictly smaller than the original ordinal,
so well-founded induction supplies notations for them.
-/

namespace PAListCoding.EpsilonZero

open Ordinal
open scoped Ordinal

/-- Every set-theoretic ordinal below `ε₀` has a normal hereditary-CNF
notation.  The coefficient obtained by division by the leading power of
`omega` is a positive ordinary natural because it is strictly below `omega`.
-/
theorem exists_nonote_repr_of_lt_epsilonZero (alpha : Ordinal)
    (halpha : alpha < ε₀) :
    ∃ o : NONote, NONote.repr o = alpha := by
  revert halpha
  induction alpha using WellFoundedLT.induction with
  | ind alpha ih =>
      intro halpha
      by_cases hzero : alpha = 0
      · subst alpha
        exact ⟨⟨0, ONote.NF.zero⟩, rfl⟩
      · let exponent : Ordinal := log ω alpha
        let leading : Ordinal := ω ^ exponent
        let remainder : Ordinal := alpha % leading
        have halpha_opow : alpha < ω ^ alpha := by
          apply lt_of_not_ge
          intro hopow
          exact (not_le_of_gt halpha)
            (epsilon_zero_le_of_omega0_opow_le hopow)
        have hexponent : exponent < alpha := by
          rw [show exponent = log ω alpha from rfl]
          exact (lt_opow_iff_log_lt one_lt_omega0 hzero).mp halpha_opow
        have hremainder : remainder < alpha := by
          exact mod_opow_log_lt_self ω hzero
        obtain ⟨e, he⟩ := ih exponent hexponent (hexponent.trans halpha)
        obtain ⟨r, hr⟩ := ih remainder hremainder (hremainder.trans halpha)
        change ONote.repr e.1 = exponent at he
        change ONote.repr r.1 = remainder at hr
        have hquotient_lt : alpha / leading < ω := by
          exact div_opow_log_lt alpha one_lt_omega0
        obtain ⟨n, hn⟩ := lt_omega0.mp hquotient_lt
        have hleading_ne : leading ≠ 0 := by
          dsimp [leading]
          exact opow_ne_zero exponent omega0_ne_zero
        have hquotient_pos : 0 < alpha / leading := by
          apply (div_pos hleading_ne).2
          exact opow_log_le_self ω hzero
        have hnpos : 0 < n := by
          rw [hn] at hquotient_pos
          exact_mod_cast hquotient_pos
        let coefficient : ℕ+ := ⟨n, hnpos⟩
        have hrbelow : ONote.NFBelow r.1 (ONote.repr e.1) := by
          apply ONote.NF.below_of_lt'
          rw [he, hr]
          simpa [remainder, leading] using mod_lt alpha hleading_ne
          exact r.2
        let result : NONote :=
          ⟨.oadd e.1 coefficient r.1, ONote.NF.oadd e.2 coefficient hrbelow⟩
        refine ⟨result, ?_⟩
        change ω ^ ONote.repr e.1 * (coefficient : ℕ) + ONote.repr r.1 = alpha
        rw [he, hr]
        change leading * (coefficient : ℕ) + remainder = alpha
        have hcoefficient : ((coefficient : ℕ) : Ordinal) = alpha / leading := by
          simpa [coefficient] using hn.symm
        rw [hcoefficient]
        exact div_add_mod alpha leading

/-- Consequently the denotation map from valid natural codes has exactly the
ordinals below `ε₀` as its range. -/
theorem exists_valid_code_denote_iff (alpha : Ordinal) :
    (∃ c : ℕ, ValidOrdinalCode c ∧ denote c = alpha) ↔ alpha < ε₀ := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact valid_denote_lt_epsilonZero hc
  · intro halpha
    obtain ⟨o, ho⟩ := exists_nonote_repr_of_lt_epsilonZero alpha halpha
    exact ⟨codeOf o, codeOf_valid o, (denote_codeOf o).trans ho⟩

end PAListCoding.EpsilonZero
