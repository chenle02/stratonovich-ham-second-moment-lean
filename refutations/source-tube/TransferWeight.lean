/-
Refutation for `P:tube-rayleigh-transfer`
(`notes/integrated_gaussian_tubes.tex` lines 225-271 at edf7085f), package
theorem `StratonovichHAMSecondMoment.SourceTube.tube_rayleigh_transfer_zero`.

Class (a): manuscript-claim perturbation in the manuscript domain.
Wrong variant: the Rayleigh weight `r/δ` in `E:tube-rayleigh-transfer` replaced
by `r` (dropping the normalization of the Rayleigh density, TeX line 246).
Counterexample (zero law): `δ = 1/2`, `X = 0` on a one-point probability space,
`F = G = 0`: the left side is `1`, the perturbed right side is
`∫_0^∞ r e^{-r²} dr = δ = 1/2`.
`weight_contrast` is the package inequality at the same point.  No junk-value
reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment SourceTube

namespace Refutations.SourceTube

/-- The transfer with the weight `r` in place of `r/δ` is false. -/
theorem weight_refuted :
    ¬ (∀ (F G : ℝ → ℝ), MonotoneOn G (Ici 0) → F 0 ≤ G 0 →
        ∫⁻ _ω, ENNReal.ofReal (Real.exp (F ((fun _ : Unit => (0 : ℝ)) _ω) / (1 / 2)))
            ∂(Measure.dirac ()) ≤
          ∫⁻ r in Ioi 0, ENNReal.ofReal (r * Real.exp ((G r - r ^ 2 / 2) / (1 / 2)))) := by
  intro h
  have := h (fun _ => 0) (fun _ => 0) (fun _ _ _ _ _ => le_rfl) le_rfl
  rw [lintegral_dirac] at this
  have hr : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r *
      Real.exp (((fun _ : ℝ => (0 : ℝ)) r - r ^ 2 / 2) / (1 / 2))) = ENNReal.ofReal (1 / 2) := by
    rw [← mul_one (ENNReal.ofReal (1 / 2)), ← lintegral_rayleigh_one (δ := 1 / 2)
      (by norm_num), ← lintegral_const_mul _ (measurable_rayleighDensity _).ennreal_ofReal]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [rayleighDensity]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have : (0 - r ^ 2 / 2) / (1 / 2 : ℝ) = -r ^ 2 / (2 * (1 / 2)) := by ring
    rw [this]
    ring
  rw [hr] at this
  simp only [div_eq_mul_inv, zero_mul, Real.exp_zero, ENNReal.ofReal_one] at this
  rw [ENNReal.one_le_ofReal] at this
  norm_num at this

/-- The package inequality (weight `r/δ`) at the same point. -/
theorem weight_contrast :
    ∫⁻ _ω, ENNReal.ofReal (Real.exp ((fun _ : ℝ => (0 : ℝ)) ((fun _ : Unit => (0 : ℝ)) _ω) /
        (1 / 2))) ∂(Measure.dirac ()) ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / (1 / 2) *
        Real.exp (((fun _ : ℝ => (0 : ℝ)) r - r ^ 2 / 2) / (1 / 2))) :=
  tube_rayleigh_transfer_zero (P := Measure.dirac ()) (fun _ : Unit => (0 : ℝ))
    (Filter.Eventually.of_forall fun _ => rfl) (1 / 2) (by norm_num) (fun _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ => le_rfl) le_rfl

end Refutations.SourceTube
