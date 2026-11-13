/-
Refutation for the critical case `α = 1` of the far series bound in
`P:frequency-row` (TeX lines 117-135), package theorem
`StratonovichHAMSecondMoment.FrequencyRow.rowSeries_tsum_le` and package
definitions `StratonovichHAMSecondMoment.FrequencyRow.rowSeries`,
`StratonovichHAMSecondMoment.FrequencyRow.scaleProfile`.

Wrong variant: the profile `B_1(h) = 1 + log(1/h)` replaced by `1` (no
logarithm). At `α = 1`, `a = 1/2` the series `S(h) = ∑_j ⟨h 2^j⟩^{-1/2}` has at
least `N + 1` terms `≥ 1/2` when `h = 2^{-N}`, so it is unbounded as `h ↓ 0`.
The series is summable (`summable_rowSeries`), so the `tsum` is not Lean's junk
value `0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FrequencyRow

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket)
open StratonovichHAMSecondMoment.FrequencyRow (rowSeries scaleProfile rowSeries_tsum_le
  summable_rowSeries rowSeries_nonneg)

namespace Refutations.FrequencyRow

theorem term_ge_half (N n : ℕ) (hn : n ≤ N) :
    1 / 2 ≤ rowSeries 1 (1 / 2) ((2 : ℝ) ^ N)⁻¹ n := by
  unfold rowSeries
  have hx : 0 ≤ ((2 : ℝ) ^ N)⁻¹ * 2 ^ n := by positivity
  have hx1 : ((2 : ℝ) ^ N)⁻¹ * 2 ^ n ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact pow_le_pow_right₀ (by norm_num) hn
  have hb : bracket (((2 : ℝ) ^ N)⁻¹ * 2 ^ n) ≤ 4 := by
    unfold bracket
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hb0 := StratonovichHAMSecondMoment.FrequencyRow.bracket_pos (((2 : ℝ) ^ N)⁻¹ * 2 ^ n)
  have h4 : (4 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp only [sub_self, Real.rpow_zero, one_pow, one_mul]
  calc (1 / 2 : ℝ) = (4 : ℝ) ^ ((1 / 2 : ℝ) - 1) := h4.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hb0 hb (by norm_num)

/-- With the profile `1` instead of `1 + log(1/h)` the critical series bound is false. -/
theorem critical_series_unbounded :
    ¬ ∃ K : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∑' n, rowSeries 1 (1 / 2) h n ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K)
  have h0 : (0 : ℝ) < ((2 : ℝ) ^ N)⁻¹ := by positivity
  have h1 : ((2 : ℝ) ^ N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hS := summable_rowSeries (α := 1) (a := 1 / 2) (by norm_num) (by norm_num) h0
  have hsum : ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ≤
      ∑ n ∈ Finset.range (N + 1), rowSeries 1 (1 / 2) ((2 : ℝ) ^ N)⁻¹ n :=
    Finset.sum_le_sum fun n hn => term_ge_half N n (by simpa [Nat.lt_succ_iff] using hn)
  have htsum := hS.sum_le_tsum (Finset.range (N + 1)) fun n _ => rowSeries_nonneg _ _ _ n
  have := hK _ h0 h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- The package theorem at `α = 1`, `a = 1/2`: the bound holds with the logarithmic profile. -/
theorem critical_series_contrast :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∑' n, rowSeries 1 (1 / 2) h n ≤ K * scaleProfile 1 h :=
  rowSeries_tsum_le (by norm_num) (by norm_num)

end Refutations.FrequencyRow
