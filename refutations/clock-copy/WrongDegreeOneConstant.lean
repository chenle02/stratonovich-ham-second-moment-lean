import StratonovichHAMSecondMoment.ClockCopy

/-!
Refutation for `E:degree-one-clock-loss` (main TeX lines 7774-7777), package
theorem `StratonovichHAMSecondMoment.ClockCopy.degree_one` (and the last
conjunct of `clock_copy_obstruction_paper`): `J_{Γ,1}(θ) = (2-2^a) K_Γ(θ)`
when `α = 1`.

Wrong variant: the constant `2^a - 1` in place of `2 - 2^a`, same binders and
hypotheses. Witness: `d = 1`, `μ` = Lebesgue measure on `ℝ¹` (homogeneous of
degree `1`, `μ{0} = 0`, `∫(1+|ξ|²)⁻¹ dμ < ∞`; this is the spectral measure of
the white covariance up to the factor `(2π)⁻¹`), `a = 1/2`, `θ = 1`. There
`K_Γ(1) = ∫ w_1 > 0` (package `weight_pos`, `weight_integrable`), and
`2 - √2 ≠ √2 - 1`. No junk value is used.
The contrast theorem applies the package theorem at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Module

namespace Refutations.ClockCopy

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.TimeFractional
  StratonovichHAMSecondMoment.SpectralHomog StratonovichHAMSecondMoment.DampedNorms
  StratonovichHAMSecondMoment.ClockCopy

theorem volume_homog : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

theorem volume_hR :
    Integrable (fun ξ : Rd 1 => 1 / (1 + ‖ξ‖ ^ 2)) (volume : Measure (Rd 1)) :=
  integrable_inv_one_add_sq volume_homog (by norm_num)

theorem volume_K_pos : 0 < N2sq (1 / 2) 1 (volume : Measure (Rd 1)) := by
  rw [K_eq_integral_weight _ volume_hR (measure_zero volume_homog one_pos) (1 / 2) 1
    (by norm_num) (by norm_num) one_pos]
  exact integral_pos_of_ae_pos (weight_integrable _ volume_hR _ _ (by norm_num) (by norm_num)
      one_pos) (by simp)
    (ae_L0_pos.mono fun l hl => weight_pos _ volume_hR (NeZero.ne _) _ _ l (by norm_num)
      one_pos hl)

theorem two_rpow_half : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm

/-- Contrast: at the witness, `J_{Γ,1}(1) ≠ (2^a - 1) K_Γ(1)`. -/
theorem degree_one_contrast :
    J (1 / 2) 1 (volume : Measure (Rd 1)) 1 ≠
      ((2 : ℝ) ^ (1 / 2 : ℝ) - 1) * N2sq (1 / 2) 1 (volume : Measure (Rd 1)) := by
  rw [degree_one _ volume_hR (measure_zero volume_homog one_pos) volume_homog (1 / 2) 1
    (by norm_num) (by norm_num) one_pos, two_rpow_half]
  intro h
  have hK := volume_K_pos
  have h2 : (2 - Real.sqrt 2) = (Real.sqrt 2 - 1) :=
    mul_right_cancel₀ hK.ne' h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

/-- The constant `2^a - 1` in `E:degree-one-clock-loss` is false. -/
theorem degree_one_wrong_constant :
    ¬ (∀ (μ : Measure (Rd 1)) [SFinite μ],
      Integrable (fun ξ : Rd 1 => 1 / (1 + ‖ξ‖ ^ 2)) μ → μ {0} = 0 →
        SpectralHomogeneous μ 1 → ∀ a θ : ℝ, 0 < a → a < 1 → 0 < θ →
        J a θ μ 1 = (2 ^ a - 1) * N2sq a θ μ) := by
  intro h
  exact degree_one_contrast (h volume volume_hR (measure_zero volume_homog one_pos)
    volume_homog (1 / 2) 1 (by norm_num) (by norm_num) one_pos)

end Refutations.ClockCopy
