/-
Refutation for the series bound `S_ν(x) ≤ exp(ν x^{1/ν})` of `SeriesType`,
package theorem
`StratonovichHAMSecondMoment.SeriesType.seriesNu_summable_le` (hypothesis
`ν ≥ 1`; used at main TeX lines 4678-4684, 6054-6059, 6740-6745, 7255-7257).

Wrong variant: the same bound with the hypothesis `ν ≥ 1` dropped (only
`ν > 0`). Counterexample: `ν = 1/2`, `x = 1`: the first three terms already
give `1 + 1 + 1/√2 > 1.7 > e^{1/2}` (as `e < 2.89 = 1.7^2`). `dropped_nu_ge_one_contrast` is the
correct bound in that regime, the `β < 1` Hölder variant
`seriesNu_holder_le` at `β = 1/2`, `x = 1`.
No junk-value reliance (`k! > 0`, `x = 1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SeriesType

set_option autoImplicit false

open Real Finset
open scoped Nat

namespace Refutations.SeriesType

/-- The bound `S_ν(x) ≤ exp(ν x^{1/ν})` fails without `ν ≥ 1`. -/
theorem dropped_nu_ge_one_refuted :
    ¬ (∀ ν x : ℝ, 0 < ν → 0 ≤ x →
        Summable (fun k : ℕ => x ^ k / (k ! : ℝ) ^ ν) ∧
          ∑' k : ℕ, x ^ k / (k ! : ℝ) ^ ν ≤ Real.exp (ν * x ^ (1 / ν))) := by
  intro h
  obtain ⟨hs, hle⟩ := h (1 / 2) 1 (by norm_num) (by norm_num)
  have hnn : ∀ k : ℕ, 0 ≤ (1 : ℝ) ^ k / (k ! : ℝ) ^ ((1 : ℝ) / 2) := fun k => by positivity
  have hpart := hs.sum_le_tsum (range 3) (fun k _ => hnn k)
  have hsum : ∑ k ∈ range 3, (1 : ℝ) ^ k / (k ! : ℝ) ^ ((1 : ℝ) / 2) =
      2 + 1 / Real.sqrt 2 := by
    simp [sum_range_succ, Nat.factorial, Real.sqrt_eq_rpow]
    ring
  have hsq : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hinv : (2 : ℝ) / 3 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (Real.sqrt_pos.2 (by norm_num))]; linarith
  have he : Real.exp ((1 : ℝ) / 2 * 1 ^ ((1 : ℝ) / (1 / 2))) < 1.7 := by
    rw [Real.one_rpow, mul_one]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-- The correct bound at the same point (`β = 1/2`, `x = 1`), from the
package's Hölder variant: `∑ 1/(k!)^{1/2} ≤ 2^{1/2} e^{1}`. -/
theorem dropped_nu_ge_one_contrast :
    ∑' k : ℕ, (1 : ℝ) ^ k / (k ! : ℝ) ^ ((1 : ℝ) / 2) ≤
      (2 : ℝ) ^ (1 - (1 : ℝ) / 2) * Real.exp (2 * (1 / 2) * (1 : ℝ) ^ (1 / ((1 : ℝ) / 2))) :=
  (StratonovichHAMSecondMoment.SeriesType.seriesNu_holder_le (by norm_num) (by norm_num)
    (by norm_num)).2

end Refutations.SeriesType
