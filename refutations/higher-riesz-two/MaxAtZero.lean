/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszTwo.F3_max` (manuscript
`L:higher-riesz`, main TeX lines 6134-6146 at edf7085f): the maximum of the
`d = 3` closed form is not its limit value `1` at `ρ = 0` (the TeX notes the
formula is continuous at zero; the maximum sits at `ρ = 1`).

Wrong variant: `F3 v ρ ≤ 1` for all `0 < v < 1` and `ρ > 0`.
Counterexample: `v = 1/2`, `ρ = 1`, where `F3 = 2^{1/2} > 1`.
`max_at_zero_contrast` is the package bound at `α = 3/2` (`v = 1/2`), which
holds with the constant `2^{-1/2}/(1/2)`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszTwo

set_option autoImplicit false

namespace Refutations.HigherRieszTwo

open StratonovichHAMSecondMoment.HigherRieszTwo

/-- The package bound at `α = 3/2`, `ρ = 1`. -/
theorem max_at_zero_contrast :
    F3 (2 - 3 / 2) 1 ≤ (2 : ℝ) ^ (1 - 3 / 2 : ℝ) / (2 - 3 / 2) :=
  ((F3_max (by norm_num) (by norm_num)).1 1 one_pos).trans_eq
    (F3_max (by norm_num) (by norm_num)).2

/-- `F3 ≤ 1` (the value at `ρ → 0`) is false. -/
theorem max_at_zero_refuted :
    ¬ (∀ v ρ : ℝ, 0 < v → v < 1 → 0 < ρ → F3 v ρ ≤ 1) := by
  intro h
  have h1 := h (2 - 3 / 2) 1 (by norm_num) (by norm_num) one_pos
  rw [(F3_max (α := 3 / 2) (by norm_num) (by norm_num)).2] at h1
  have e : (2 : ℝ) ^ (1 - 3 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      Real.sqrt_eq_rpow]
  rw [e] at h1
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have : (Real.sqrt 2)⁻¹ / (2 - 3 / 2) = 2 / Real.sqrt 2 := by
    field_simp; norm_num
  rw [this, div_le_one hs0] at h1
  linarith

end Refutations.HigherRieszTwo
