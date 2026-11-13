/-
Refutation for the cell-width bound of the finite-cell selection (Lean route of
`L:occupation-rayleigh-selection`, `notes/integrated_occupation_ceiling.tex` lines 149-193 at
a284420), package theorem `StratonovichHAMSecondMoment.OccupationCeilingExact.idx_close`
(`|s - j(s)/(N+1)| ≤ 1/(N+1)` for `s ∈ [0,1]`).

Wrong variant: the sharper width `1/(N+2)`.  Counterexample: `N = 1`, `s = 1`: the cell index
is `min(⌊2⌋, 1) = 1`, so `|1 - 1/2| = 1/2 > 1/3`.  `cell_width_contrast` is the package bound at
the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCeilingExact

set_option autoImplicit false

namespace Refutations.OccupationCeilingExact

open StratonovichHAMSecondMoment

/-- The index of `s = 1` among two cells is `1`. -/
theorem idx_one_one : ((OccupationCeilingExact.idx 1 1 : ℕ) : ℝ) = 1 := by
  simp [OccupationCeilingExact.idx]

/-- The cell width `1/(N+2)` is false. -/
theorem cell_width_refuted :
    ¬ (∀ (N : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        |s - ((OccupationCeilingExact.idx N s : ℕ) : ℝ) / ((N : ℝ) + 1)| ≤
          1 / ((N : ℝ) + 2)) := by
  intro h
  have h1 := h 1 1 ⟨by norm_num, le_rfl⟩
  rw [idx_one_one] at h1
  norm_num [abs_of_pos] at h1

/-- The package bound at the same point. -/
theorem cell_width_contrast :
    |(1 : ℝ) - ((OccupationCeilingExact.idx 1 1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1)| ≤
      1 / (((1 : ℕ) : ℝ) + 1) :=
  OccupationCeilingExact.idx_close ⟨by norm_num, le_rfl⟩

end Refutations.OccupationCeilingExact
