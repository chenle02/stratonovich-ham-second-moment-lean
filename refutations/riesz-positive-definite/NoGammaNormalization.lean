/-
Refutation for `StratonovichHAMSecondMoment.RieszPositiveDefinite.mixOne_spec` (the Gaussian
mixture `|u|^{-e} = Γ(e/2)^{-1} ∫_0^∞ s^{e/2-1} e^{-su²} ds` of main TeX lines 7255-7258,
7361-7364 and 7975-7978 at 39f2597a).

Wrong variant: the mixture formula with the normalization `Γ(e/2)^{-1}` dropped,
`∫_0^∞ s^{e/2-1} e^{-su²} ds = |u|^{-e}` for all `u ≠ 0`, at `e = 1`.  Counterexample:
`u = 1`, where the integral is `Γ(1/2) = √π ≠ 1`.
Class (a): perturbation of the manuscript claim (the displayed mixture) inside the
manuscript's domain (the isotropic Riesz exponent `e = 1` of lines 7971-7977, `u ≠ 0`). 
`no_gamma_normalization_contrast` is the package
identity (with the normalization) at the same point.  No junk values.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszPositiveDefinite

set_option autoImplicit false

namespace Refutations.RieszPositiveDefinite

open MeasureTheory Set Real StratonovichHAMSecondMoment.RieszPositiveDefinite

/-- The normalized mixture at `e = 1`, `u = 1`: `∫ e^{-s} mixOne 1 (ds) = 1`. -/
theorem no_gamma_normalization_contrast :
    ∫ s, Real.exp (-s * (1 : ℝ) ^ 2) ∂mixOne 1 = |(1 : ℝ)| ^ (-(1 : ℝ)) :=
  (mixOne_spec zero_le_one one_ne_zero).2

/-- Without `Γ(e/2)^{-1}` the mixture identity fails (at `e = 1`, `u = 1`). -/
theorem no_gamma_normalization_refuted :
    ¬ (∀ u : ℝ, u ≠ 0 →
      ∫ s in Ioi 0, s ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(u ^ 2 * s)) = |u| ^ (-(1 : ℝ))) := by
  intro h
  have h1 := h 1 one_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)] at h1
  norm_num [Real.Gamma_one_half_eq] at h1
  have hpi : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
  have := Real.sqrt_lt_sqrt zero_le_one hpi
  rw [Real.sqrt_one] at this
  linarith

end Refutations.RieszPositiveDefinite
