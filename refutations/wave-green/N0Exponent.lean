/-
Refutation for `N₀(θ) = θ^{-2}` with the wave Green measures, package theorem
`StratonovichHAMSecondMoment.WaveGreen.N0_waveGreen` (main TeX lines 809-810,
from the mass identity at line 881).

Wrong variant: exponent `-1`, `N₀(θ) = θ^{-1}` for all `θ > 0` (as if
`G_s(ℝ^d)` were constant in `s`).  Counterexample: `d = 1`, `θ = 2`:
`N₀(2) = 1/4 ≠ 1/2`.  `n0_exponent_contrast` is the package value at the same
point.  No junk-value reliance (the integrand is integrable, by the package
theorem).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreen

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment.WaveGreen
open StratonovichHAMSecondMoment.DampedNormsHomog

namespace Refutations.WaveGreen

/-- `N₀(θ)` for the wave Green measures is not `θ^{-1}`. -/
theorem n0_exponent_refuted :
    ¬ (∀ θ : ℝ, 0 < θ → N0 (waveGreen 1) θ = θ ^ (-(1 : ℝ))) := by
  intro h
  have h1 := h 2 two_pos
  rw [(N0_waveGreen 1 (Or.inl rfl) 2 two_pos).2] at h1
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)] at h1
  norm_num at h1

/-- The package value at the counterexample point `θ = 2`. -/
theorem n0_exponent_contrast : N0 (waveGreen 1) 2 = 2 ^ (-(2 : ℝ)) :=
  (N0_waveGreen 1 (Or.inl rfl) 2 two_pos).2

end Refutations.WaveGreen
