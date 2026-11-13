/-
Refutation for the `d = 1` wave Green mass, package theorem
`StratonovichHAMSecondMoment.WaveGreen.mass_one` (`G_s(ℝ) = s`, main TeX lines
746, 881).

Wrong variant: the normalization without the factor `1/2`, i.e. a mass of `2s`
(`G_s(ℝ) = 2s` for all `s > 0`, the mass of `1_{|x|<s} dx`).
Counterexample: `s = 1`, where the package mass is `1 ≠ 2`.
`mass_without_half_contrast` is the package mass at the same point.
No junk-value reliance (`s = 1 > 0`, `d = 1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreen

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment.WaveGreen

namespace Refutations.WaveGreen

/-- The `d = 1` wave Green measure does not have mass `2s`. -/
theorem mass_without_half_refuted :
    ¬ (∀ s : ℝ, 0 < s → waveGreen 1 s univ = ENNReal.ofReal (2 * s)) := by
  intro h
  have h1 := h 1 one_pos
  rw [mass_one 1 one_pos, mul_one] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h1
  norm_num at this

/-- The package mass at the counterexample point `s = 1`. -/
theorem mass_without_half_contrast : waveGreen 1 1 univ = ENNReal.ofReal 1 :=
  mass_one 1 one_pos

end Refutations.WaveGreen
