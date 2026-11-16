/-
Refutation for the pair integral `∫_{[0,t]²} |s-r|^{-α₀} ds dr = Z t^{2-α₀}`,
`Z = 2/((1-α₀)(2-α₀))` (main TeX lines 5495-5497 and `E:d1-constants`,
line 5325, at 39f2597a).  Package theorem
`StratonovichHAMSecondMoment.TwoSimplexTime.lintegral_timeCov_square` (moved from
`D1Upper` at the L13 integration).

Wrong variant: the constant halved, `∫∫ ≤ (Z/2) t^{2-α₀}` (as if only one
ordering `r < s` were integrated).  Counterexample in the manuscript domain:
`α₀ = 1/2`, `t = 1`, where the integral equals `Z > Z/2`.
`timeConstantHalf_contrast` is the package identity.  Class (a):
manuscript-claim perturbation in the manuscript domain.  No junk-value
reliance (the `ℝ≥0∞` kernel is `∞` only on the null diagonal).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.D1Upper

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment DiagramModel D1Upper
open StratonovichHAMSecondMoment.TwoSimplexTime (Zc Zc_pos lintegral_timeCov_square)

namespace Refutations.D1Upper.TimeConstantHalf

/-- The package: the exact value `Z t^{2-α₀}`. -/
theorem timeConstantHalf_contrast : ∀ a t : ℝ, 0 < a → a < 1 → 0 < t →
    ∫⁻ p, timeCov a p.1 p.2 ∂((volume.restrict (Icc 0 t)).prod (volume.restrict (Icc 0 t))) =
      ENNReal.ofReal (Zc a * t ^ (2 - a)) :=
  fun _ _ _ ha1 ht => lintegral_timeCov_square ha1 ht.le

/-- The constant `Z/2` is false. -/
theorem timeConstantHalf_refuted : ¬ (∀ a t : ℝ, 0 < a → a < 1 → 0 < t →
    ∫⁻ p, timeCov a p.1 p.2 ∂((volume.restrict (Icc 0 t)).prod (volume.restrict (Icc 0 t))) ≤
      ENNReal.ofReal (Zc a / 2 * t ^ (2 - a))) := by
  intro H
  have h := H (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  rw [lintegral_timeCov_square (by norm_num) zero_le_one] at h
  have hZ := Zc_pos (α₀ := 1 / 2) (by norm_num)
  simp only [Real.one_rpow, mul_one] at h
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  linarith

end Refutations.D1Upper.TimeConstantHalf
