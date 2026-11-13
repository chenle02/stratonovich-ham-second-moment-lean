/-
Refutation for the `d = 2` wave Green mass, package theorem
`StratonovichHAMSecondMoment.WaveGreen.mass_two` (`G_s(ℝ²) = s`, main TeX lines
5182-5187, Chen (2.5)).

Wrong variant: a mass growing like the area of the support, `G_s(ℝ²) = s²` for
all `s > 0`.  Counterexample: `s = 2`, where the package mass is `2 ≠ 4`.
`area_mass_two_contrast` is the package mass at the same point.
No junk-value reliance (`s = 2 > 0`; the density is evaluated only inside the
ball, where `s² - |x|² > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreen

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment.WaveGreen

namespace Refutations.WaveGreen

/-- The `d = 2` wave Green measure does not have mass `s²`. -/
theorem area_mass_two_refuted :
    ¬ (∀ s : ℝ, 0 < s → waveGreen 2 s univ = ENNReal.ofReal (s ^ 2)) := by
  intro h
  have h1 := h 2 two_pos
  rw [mass_two 2 two_pos] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h1
  norm_num at this

/-- The package mass at the counterexample point `s = 2`. -/
theorem area_mass_two_contrast : waveGreen 2 2 univ = ENNReal.ofReal 2 :=
  mass_two 2 two_pos

end Refutations.WaveGreen
