/-
Refutation for the scaling of the `d = 3` wave Green measure, package theorem
`StratonovichHAMSecondMoment.WaveGreen.scaling_three`
(`G_s(sA) = s G_1(A)`, main TeX lines 5186-5187).

Wrong variant: the scaling of the surface measure itself,
`G_s(sA) = s² G_1(A)` for all `s > 0` and measurable `A` (forgetting the
factor `1/(4πs)` in `G_s = σ_s/(4πs)`).
Counterexample: `s = 2`, `A = ℝ³` (so `sA = ℝ³`): `G_2(ℝ³) = 2`, while
`4 G_1(ℝ³) = 4`.  `surface_scaling_contrast` is the package scaling at the same
point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreen

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment.WaveGreen
open scoped Pointwise

namespace Refutations.WaveGreen

/-- The `d = 3` wave Green measure does not scale like surface measure. -/
theorem surface_scaling_refuted :
    ¬ (∀ s : ℝ, 0 < s → ∀ A : Set (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3),
        MeasurableSet A → waveGreen 3 s (s • A) = ENNReal.ofReal (s ^ 2) * waveGreen 3 1 A) := by
  intro h
  have h1 := h 2 two_pos univ MeasurableSet.univ
  rw [smul_set_univ₀ two_ne_zero, mass_three 2 two_pos, mass_three 1 one_pos,
    ← ENNReal.ofReal_mul (by norm_num)] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h1
  norm_num at this

/-- The package scaling at the counterexample point `s = 2`, `A = ℝ³`. -/
theorem surface_scaling_contrast :
    waveGreen 3 2 ((2 : ℝ) • (univ : Set (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3))) =
      ENNReal.ofReal 2 * waveGreen 3 1 univ :=
  scaling_three 2 two_pos univ MeasurableSet.univ

end Refutations.WaveGreen
