/-
Refutation for
`StratonovichHAMSecondMoment.MaskedContinuousWave.frequencyPair_shift_le`
(`L:masked-continuous-wave`, TeX lines 417-419 at a284420: "the changes in
`h(r±ρ)` have magnitude at most two, since `h ≤ 1`").

Wrong variant: `frequencyPair_shift_le` with the hypothesis `h ≤ 1` dropped.
Witness `a = 0`, `h = 3`, `r = 1`, `ρ = 0`, `r' = ρ' = 0`:
`𝒬_3(0,0) = 2`, while `3^{1-0} 𝒬_3(1,0) = 6/√10 < 2`. So the standing
assumption `h ≤ 1` (TeX line 297) is used. No junk value is involved. The
contrast theorem applies `frequencyPair_shift_le` at `h = 1` with the same
frequencies.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedContinuousWave

set_option autoImplicit false

namespace Refutations.MaskedContinuousWave

open StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedContinuousWave

/-- Dropping `h ≤ 1` from `frequencyPair_shift_le` is false. -/
theorem shift_large_h :
    ¬ ∀ a h r ρ r' ρ' : ℝ, a < 1 → 0 ≤ h → |r - r'| ≤ 1 → |ρ - ρ'| ≤ 1 →
      frequencyPair a h r' ρ' ≤ 3 ^ (1 - a) * frequencyPair a h r ρ := by
  intro H
  have h1 := H 0 3 1 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [frequencyPair, bracket] at h1
  norm_num at h1
  rw [Real.rpow_neg_one] at h1
  have h10 : (3 : ℝ) < √10 := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < √10 := by positivity
  have : 3 * ((√10)⁻¹ + (√10)⁻¹) < 2 := by
    rw [← two_mul, ← mul_assoc, mul_comm 3 2, mul_assoc, ← div_eq_mul_inv]
    rw [mul_lt_iff_lt_one_right (by norm_num), div_lt_one hpos]
    exact h10
  linarith

/-- Contrast: at `h = 1` (the manuscript's range) the comparison holds for the
same frequencies. -/
theorem shift_large_h_contrast :
    frequencyPair 0 1 0 0 ≤ 3 ^ (1 - (0 : ℝ)) * frequencyPair 0 1 1 0 :=
  frequencyPair_shift_le (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)

end Refutations.MaskedContinuousWave
