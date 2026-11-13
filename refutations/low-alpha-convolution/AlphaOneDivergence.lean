/-
Refutation for the layer-cake step of `L:low-alpha-convolution` (main TeX
lines 4723-4732 at a284420), package theorem
`StratonovichHAMSecondMoment.LowAlphaConvolution.lintegral_rpow_Ioc`.

Wrong variant: dropping the hypothesis `α < 1`.  The layer-cake integral
`V ∫_0^h u^{-α} du` is then infinite: at `α = 1`, `u ↦ u^{-1}` is not
integrable on `(0, 1]`.  (This is why the manuscript treats `α = 1` separately,
`L:alpha-one-convolution`.)  `alpha_one_contrast` is the package identity at
`α = 1/2`, `h = 1`: `∫_0^1 u^{-1/2} du = 2`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaConvolution

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.LowAlphaConvolution

open StratonovichHAMSecondMoment.LowAlphaConvolution

/-- At `α = 1` the layer-cake integrand `u^{-α}` is not integrable on `(0, 1]`. -/
theorem alpha_one_refuted :
    ¬ IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ))) (Ioc 0 1) := by
  intro h
  have h' : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ))) (Ioo 0 1) :=
    h.mono_set Ioo_subset_Ioc_self
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 h'
  norm_num at this

/-- The package identity at `α = 1/2`, `h = 1`. -/
theorem alpha_one_contrast :
    ∫⁻ t in Ioc 0 1, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) = ENNReal.ofReal 2 := by
  rw [lintegral_rpow_Ioc (by norm_num) zero_le_one]
  norm_num

end Refutations.LowAlphaConvolution
