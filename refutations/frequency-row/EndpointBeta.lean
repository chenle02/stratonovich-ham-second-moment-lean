/-
Refutation for the endpoint of `E:variance-beta-range` in `C:frequency-time`
(TeX lines 143-145 and 163: "No endpoint value of `β` is used"), package theorem
`StratonovichHAMSecondMoment.FrequencyRow.scale_time_le` and package definition
`StratonovichHAMSecondMoment.FrequencyRow.scaleProfile`.

Wrong variant: the strict inequality `2β < 2 - a` replaced by the endpoint
`2β = 2 - a` at `α = 1`. Then `h^{2-a} B_1(h) ≤ c h^{2β}` would say
`1 + log(1/h) ≤ c` for all `0 < h ≤ 1`, which fails at `h = e^{-(|c|+1)}`.
No junk value is involved (`h > 0`, `h^{2-a} > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FrequencyRow

set_option autoImplicit false

open StratonovichHAMSecondMoment.FrequencyRow (scaleProfile scale_time_le)

namespace Refutations.FrequencyRow

/-- At the endpoint `2β = 2 - a`, `α = 1`, the scale step is false (for any `a`). -/
theorem endpoint_beta_fails (a : ℝ) :
    ¬ ∃ c : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → h ^ (2 - a) * scaleProfile 1 h ≤ c * h ^ (2 - a) := by
  rintro ⟨c, hc⟩
  set h : ℝ := Real.exp (-(|c| + 1)) with hh
  have h0 : 0 < h := Real.exp_pos _
  have h1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg c])
  have := hc h h0 h1
  have hp : 0 < h ^ (2 - a) := Real.rpow_pos_of_pos h0 _
  have hB : scaleProfile 1 h = 1 + (|c| + 1) := by
    simp [scaleProfile, hh, Real.log_inv, Real.log_exp]
  rw [hB, mul_comm] at this
  have := le_of_mul_le_mul_right this hp
  linarith [le_abs_self c]

/-- The package theorem strictly inside the range (`α = 1`, `a = 1/2`, `β = 1/2`). -/
theorem scale_time_contrast :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      h ^ (2 - (1 / 2 : ℝ)) * scaleProfile 1 h ≤ c * h ^ (2 * (1 / 2 : ℝ)) :=
  scale_time_le (by norm_num) (by norm_num)

end Refutations.FrequencyRow
