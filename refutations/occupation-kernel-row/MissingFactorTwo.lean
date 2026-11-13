/-
Refutation for the constant in `E:occupation-kernel-row`
(`notes/integrated_spatial_occupation.tex`, lines 365-368 at a284420), package
theorem `StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row`
and package definitions `row`, `Rstar`.

Wrong variant: the row maximum is `∫_0^{1/2} K_⋆` (the factor `2` of
`R_⋆ = 2∫_0^{1/2} K_⋆` dropped), stated for every admissible `a`, `D`.  At
`a = 1/2`, `D = 1` the package theorem gives the greatest row value `R_⋆ > 0`,
which exceeds `R_⋆ / 2`, so `R_⋆ / 2` is not the greatest row value.
`missing_factor_two_contrast` is the package statement at the same point.
No junk value is used.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationKernelRow

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.OccupationKernelRow

open StratonovichHAMSecondMoment.OccupationKernelRow

/-- Refuted variant: "for all `0 < a < 1`, `D > 0`, the row maximum is
`∫_0^{1/2} K_⋆ = R_⋆ / 2`". -/
theorem missing_factor_two_false :
    ¬ ∀ a D : ℝ, 0 < a → a < 1 → 0 < D →
      IsGreatest (row a D '' Icc (0 : ℝ) 1) (∫ u in (0 : ℝ)..(1 / 2), Kstar a D u) := by
  intro h
  obtain ⟨-, -, -, -, -, -, hG, -, hpos⟩ :=
    occupation_kernel_row (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  have h1 := h (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  have hle : Rstar (1 / 2) 1 ≤ ∫ u in (0 : ℝ)..(1 / 2), Kstar (1 / 2) 1 u := h1.2 hG.1
  have hR : Rstar (1 / 2) 1 = 2 * ∫ u in (0 : ℝ)..(1 / 2), Kstar (1 / 2) 1 u := rfl
  linarith

/-- Contrast: the package statement at `a = 1/2`, `D = 1`. -/
theorem missing_factor_two_contrast :
    IsGreatest (row (1 / 2) 1 '' Icc (0 : ℝ) 1) (Rstar (1 / 2) 1) ∧ 0 < Rstar (1 / 2) 1 :=
  let h := occupation_kernel_row (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end Refutations.OccupationKernelRow
