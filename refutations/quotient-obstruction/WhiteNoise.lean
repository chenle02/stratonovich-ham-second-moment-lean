/-
Refutation for `P:masked-quotient-obstruction`
(`notes/integrated_covariance_foundation.tex` line 270 at a284420: "This is not
spatial white noise in dimension two"), package definition
`StratonovichHAMSecondMoment.QuotientObstruction.Gamma0`.

Wrong variant: `Γ = δ₀(dx₁) dx₂` is Lebesgue measure on `ℝ²` (spatial white
noise).
Counterexample: the second coordinate axis `{x₁ = 0}` has `Γ`-mass `∞`
(`white_noise_contrast`, from the package's `lineMeasure_apply`) and Lebesgue
measure `0`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.QuotientObstruction

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open StratonovichHAMSecondMoment HomogHypothesis QuotientObstruction

namespace Refutations.QuotientObstruction

/-- The axis `{x₁ = 0}` is a Lebesgue null set. -/
theorem volume_axis : (volume : Measure (Rd 2)) {x | x 0 = 0} = 0 := by
  have hS : MeasurableSet {x : Rd 2 | x 0 = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [← measurePreserving_plane.measure_preimage hS.nullMeasurableSet]
  have : plane ⁻¹' {x : Rd 2 | x 0 = 0} = {(0 : ℝ)} ×ˢ univ := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The package measure gives the axis infinite mass. -/
theorem white_noise_contrast : Gamma0 {x | x 0 = 0} = ∞ := by
  rw [Gamma0, lineMeasure_apply norm_e2]
  have : (fun t : ℝ => t • e2) ⁻¹' {x : Rd 2 | x 0 = 0} = univ := by
    ext t; simp [smul_e2]
  rw [this, Real.volume_univ]

/-- `Γ = δ₀(dx₁) dx₂` is not Lebesgue measure on `ℝ²`. -/
theorem white_noise_refuted : ¬ (Gamma0 = (volume : Measure (Rd 2))) := by
  intro h
  have h1 := white_noise_contrast
  rw [h, volume_axis] at h1
  exact ENNReal.zero_ne_top h1

end Refutations.QuotientObstruction
