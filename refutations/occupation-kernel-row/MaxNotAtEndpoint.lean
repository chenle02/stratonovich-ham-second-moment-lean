/-
Refutation for the row-maximum part of `L:occupation-kernel-row`
(`notes/integrated_spatial_occupation.tex`, lines 361-379 at a284420, display
`E:occupation-kernel-row`, lines 365-368), package theorem
`StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row` and
package definitions `Kstar`, `row`, `Rstar`, `Phi`.

Wrong variant: the row maximum is attained at the endpoint `s = 0` (the value
`∫_0^1 K_⋆(-t) dt = Φ(1)`), as for a kernel that is not decreasing.  At
`a = 1/2`, `D = 1` the endpoint row is strictly smaller than the row at
`s = 1/2`: `Φ(1) - Φ(1/2) = ∫_0^{1/2} K_⋆(x + 1/2) dx < ∫_0^{1/2} K_⋆(x) dx`
because `K_⋆` strictly decreases on `(0,∞)`.  So `row 0` is not the greatest row
value.  `max_at_endpoint_contrast` applies the package theorem: the endpoint
row is bounded by `R_⋆`.  No junk value is used (every integral used is of an
integrable function, by `Kstar_intervalIntegrable`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationKernelRow

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.OccupationKernelRow

open StratonovichHAMSecondMoment.OccupationKernelRow

/-- The endpoint row is strictly below the row at `s = 1/2` (`a = 1/2`, `D = 1`). -/
theorem row_zero_lt_row_half : row (1 / 2) 1 0 < row (1 / 2) 1 (1 / 2) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have ha1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hD : (0 : ℝ) < 1 := one_pos
  have hI : ∀ b c : ℝ, IntervalIntegrable (Kstar (1 / 2) 1) volume b c :=
    fun b c => Kstar_intervalIntegrable _ _ b c ha ha1 hD
  rw [row_eq_Phi _ _ _ ha ha1 hD, row_eq_Phi _ _ _ ha ha1 hD]
  have h0 : Phi (1 / 2) 1 0 = 0 := intervalIntegral.integral_same
  have e1 : Phi (1 / 2) 1 1 = Phi (1 / 2) 1 (1 / 2) +
      ∫ u in (1 / 2 : ℝ)..1, Kstar (1 / 2) 1 u :=
    (intervalIntegral.integral_add_adjacent_intervals (hI 0 (1 / 2)) (hI (1 / 2) 1)).symm
  have e2 : ∫ u in (1 / 2 : ℝ)..1, Kstar (1 / 2) 1 u =
      ∫ x in (0 : ℝ)..(1 / 2), Kstar (1 / 2) 1 (x + 1 / 2) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => Kstar (1 / 2) 1 x) (1 / 2)]
    norm_num
  have hshift : IntervalIntegrable (fun x => Kstar (1 / 2) 1 (x + 1 / 2)) volume 0 (1 / 2) := by
    have h := (hI (1 / 2) 1).comp_add_right (1 / 2) (by finiteness)
    norm_num at h
    exact h
  have hlt : 0 < ∫ x in (0 : ℝ)..(1 / 2),
      (Kstar (1 / 2) 1 x - Kstar (1 / 2) 1 (x + 1 / 2)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hI 0 (1 / 2)).sub hshift) ?_
      (by norm_num)
    intro x hx
    rw [sub_pos]
    exact Kstar_strictAntiOn _ _ ha hD hx.1 (show (0 : ℝ) < x + 1 / 2 by linarith [hx.1])
      (by linarith)
  rw [intervalIntegral.integral_sub (hI 0 (1 / 2)) hshift] at hlt
  norm_num at hlt ⊢
  rw [h0, e1, e2]
  have : Phi (1 / 2) 1 (1 / 2) = ∫ x in (0 : ℝ)..(1 / 2), Kstar (1 / 2) 1 x := rfl
  linarith

/-- Refuted variant: "the row maximum on `[0,1]` is the endpoint value `row 0`". -/
theorem max_at_endpoint_false :
    ¬ IsGreatest (row (1 / 2) 1 '' Icc (0 : ℝ) 1) (row (1 / 2) 1 0) := by
  intro h
  have := h.2 ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  exact absurd this (not_le.2 row_zero_lt_row_half)

/-- Contrast: the package theorem bounds the endpoint row by `R_⋆`. -/
theorem max_at_endpoint_contrast : row (1 / 2) 1 0 ≤ Rstar (1 / 2) 1 :=
  (occupation_kernel_row (1 / 2) 1 (by norm_num) (by norm_num) one_pos).2.2.2.2.2.2.1.2
    ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

end Refutations.OccupationKernelRow
