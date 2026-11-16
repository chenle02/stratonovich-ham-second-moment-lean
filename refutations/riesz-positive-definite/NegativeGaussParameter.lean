/-
Refutation for `StratonovichHAMSecondMoment.RieszPositiveDefinite.integrable_gauss` and the
role of the hypothesis `∀ᵐ s ∂ν, ∀ j, 0 ≤ s j` of `nnr_of_mixture` (the mixing measures of
main TeX lines 7255-7264 are carried by `s > 0`, resp. `s = 0` for a zero exponent).

Wrong variant: the Gaussian `g_s(x) = e^{-s x²}` on `ℝ¹` is integrable for every parameter
`s`.  Counterexample: `s = -1`, where `g_s ≥ 1` on a space of infinite volume.
Class (b): Lean-route-only control (the Gaussian step of the route needs positive parameters,
which the damping `δ > 0` and the support condition on the mixing measure provide).
`negative_gauss_parameter_contrast` is the package lemma at `s = 1`.  No junk values.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszPositiveDefinite

set_option autoImplicit false

namespace Refutations.RieszPositiveDefinite

open MeasureTheory Set Real StratonovichHAMSecondMoment.RieszPositiveDefinite
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- The Gaussian with parameter `1` is integrable. -/
theorem negative_gauss_parameter_contrast : Integrable (gauss (fun _ : Fin 1 => (1 : ℝ))) :=
  integrable_gauss fun _ => one_pos

/-- The Gaussian with parameter `-1` is not integrable. -/
theorem negative_gauss_parameter_refuted :
    ¬ (∀ s : Fin 1 → ℝ, Integrable (gauss s)) := by
  intro h
  have hI := h fun _ => -1
  have hge : ∀ x : Rd 1, 1 ≤ ‖gauss (fun _ => (-1 : ℝ)) x‖ₑ := by
    intro x
    rw [← ofReal_norm, Real.norm_of_nonneg (gauss_pos _ _).le, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gauss, Fin.prod_univ_one]
    exact Real.one_le_exp (by nlinarith [sq_nonneg (x 0)])
  have hfin := hI.2
  unfold HasFiniteIntegral at hfin
  have hle : ∫⁻ _x : Rd 1, (1 : ENNReal) ≤ ∫⁻ x, ‖gauss (fun _ => (-1 : ℝ)) x‖ₑ :=
    lintegral_mono hge
  rw [lintegral_const, one_mul, measure_univ_of_isAddLeftInvariant] at hle
  exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)

end Refutations.RieszPositiveDefinite
