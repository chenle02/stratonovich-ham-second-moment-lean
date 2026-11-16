import StratonovichHAMSecondMoment.AlphaOneConvolution

/-!
Refutation for the radial bound `0 ≤ I_a(h,v) ≤ π/2` in the proof of
`L:alpha-one-convolution` (main TeX lines 5702-5703), package theorem
`StratonovichHAMSecondMoment.AlphaOneConvolution.alpha_one_radial`.

Wrong variant: the constant `π/2` replaced by `π/8` (a factor-four error, i.e. the
bound `πV/8` instead of `πV/2` after integration against `σ`). Witness: `a = 1/4`,
`h = 1`, `v = 0`, where `I_a(h,0) = π (g_h * p_{2a})(0) ≥ π h p_{2a}(h) = π e^{-1}/√π`,
and `e^{-1}/√π ≥ 0.36/2 > 1/8`. No junk value is involved: the radial integrand is
integrable (`alpha_one_radial`) and the lower bound is a genuine integral bound
(`boxConv_zero_ge`).
The contrast theorem places the witness value strictly between the wrong and the
correct constants.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.AlphaOneConvolution

open StratonovichHAMSecondMoment.AlphaOneConvolution

theorem gauss1_quarter_one : 1 / 8 < gauss1 (1 / 4) 1 := by
  unfold gauss1
  have hpi : 4 * π * (1 / 4) = π := by ring
  rw [hpi, Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt π ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_le_four]
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have he : (0.36 : ℝ) < Real.exp (-(1 ^ 2 / (4 * (1 / 4)))) := by
    have := Real.exp_neg_one_gt_d9
    norm_num at this ⊢; linarith
  have h1 : (1 / 2 : ℝ) ≤ (Real.sqrt π)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs0]; linarith
  nlinarith [Real.exp_pos (-(1 ^ 2 / (4 * (1 / 4) : ℝ)))]

/-- Contrast: `π/8 < I_{1/4}(1,0) ≤ π/2`. -/
theorem wrong_radial_constant_contrast :
    π / 8 < Ia (1 / 4) 1 0 ∧ Ia (1 / 4) 1 0 ≤ π / 2 := by
  obtain ⟨-, -, hId, -, hle⟩ := alpha_one_radial (1 / 4) 1 0 (by norm_num) zero_le_one
  refine ⟨?_, hle⟩
  have hb := boxConv_zero_ge (1 / 4) 1 (by norm_num) zero_le_one
  rw [hId]
  have := gauss1_quarter_one
  nlinarith [Real.pi_pos]

/-- The wrong variant `I_a(h,v) ≤ π/8` is false. -/
theorem wrong_radial_constant :
    ¬ ∀ a h v : ℝ, 0 < a → 0 ≤ h → Ia a h v ≤ π / 8 := by
  intro H
  have := H (1 / 4) 1 0 (by norm_num) zero_le_one
  linarith [wrong_radial_constant_contrast.1]

end Refutations.AlphaOneConvolution
