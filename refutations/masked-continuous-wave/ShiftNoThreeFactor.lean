/-
Refutation for
`StratonovichHAMSecondMoment.MaskedContinuousWave.frequencyPair_shift_le`
(`L:masked-continuous-wave`, TeX lines 417-419 at a284420: shifted brackets
cost a factor `3^{1-a}`).

Wrong variant: the frequency comparison with the factor `3^{1-a}` dropped,
`𝒬_h(r',ρ') ≤ 𝒬_h(r,ρ)`, keeping every other hypothesis of
`frequencyPair_shift_le` (`a < 1`, `0 ≤ h ≤ 1`, `|r-r'|, |ρ-ρ'| ≤ 1`).
Witness `a = 0`, `h = 1`, `r = 1`, `ρ = 0`, `r' = ρ' = 0`:
`𝒬_1(0,0) = 2 > √2 = 2⟨1⟩^{-1} = 𝒬_1(1,0)`. This is the case `b_r` with
`r < 1` moved to frequency `0`, so some factor above one is necessary. No junk
value is involved (`rpow` of positive brackets). The contrast theorem applies
`frequencyPair_shift_le` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedContinuousWave

set_option autoImplicit false

namespace Refutations.MaskedContinuousWave

open StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedContinuousWave

/-- Dropping `3^{1-a}` from `frequencyPair_shift_le` is false. -/
theorem shift_no_three_factor :
    ¬ ∀ a h r ρ r' ρ' : ℝ, a < 1 → 0 ≤ h → h ≤ 1 → |r - r'| ≤ 1 → |ρ - ρ'| ≤ 1 →
      frequencyPair a h r' ρ' ≤ frequencyPair a h r ρ := by
  intro H
  have h1 := H 0 1 1 0 0 0 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
  simp only [frequencyPair, bracket] at h1
  norm_num at h1
  rw [Real.rpow_neg_one] at h1
  have : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hinv : (√2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
  linarith

/-- Contrast: with the factor `3^{1-a}` the comparison holds at the same point. -/
theorem shift_no_three_factor_contrast :
    frequencyPair 0 1 0 0 ≤ 3 ^ (1 - (0 : ℝ)) * frequencyPair 0 1 1 0 :=
  frequencyPair_shift_le (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)

end Refutations.MaskedContinuousWave
