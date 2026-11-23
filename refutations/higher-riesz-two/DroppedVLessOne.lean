/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszTwo.F3_num_le`
(auxiliary to the Lean proof route of the `d = 3` maximum in `L:higher-riesz`,
main TeX lines 6134-6146 at edf7085f, where `v = 2 - α ∈ (0,1)`): the chord
bound `(1+ρ)^v - |1-ρ|^v ≤ 2^v ρ` needs `v < 1` (i.e. `α > 1`).

Wrong variant: the bound for every `v > 0` (`v < 1` dropped).
Counterexample: `v = 3/2`, `ρ = 1/2`: `(3/2)^{3/2} - (1/2)^{3/2} > 2^{3/2}/2`,
equivalently `(3/2)√3 - 1/2 > 2`, i.e. `√3 > 5/3`.
`dropped_v_less_one_contrast` is the package bound at `v = 1/2`, `ρ = 1/2`.
No junk-value reliance (all bases positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszTwo

set_option autoImplicit false

namespace Refutations.HigherRieszTwo

open StratonovichHAMSecondMoment.HigherRieszTwo

/-- The package bound at `v = 1/2`, `ρ = 1/2`. -/
theorem dropped_v_less_one_contrast :
    (1 + 1 / 2 : ℝ) ^ (1 / 2 : ℝ) - |1 - 1 / 2| ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) * (1 / 2) :=
  F3_num_le (by norm_num) (by norm_num) (by norm_num)

/-- `x^{3/2} = x √x` for `x > 0`. -/
private theorem rpow_three_halves {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The chord bound without `v < 1` is false. -/
theorem dropped_v_less_one_refuted :
    ¬ (∀ v ρ : ℝ, 0 < v → 0 < ρ → (1 + ρ) ^ v - |1 - ρ| ^ v ≤ 2 ^ v * ρ) := by
  intro h
  have h1 := h (3 / 2) (1 / 2) (by norm_num) (by norm_num)
  rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num, rpow_three_halves (by norm_num),
    rpow_three_halves (by norm_num), rpow_three_halves (by norm_num)] at h1
  have e1 : Real.sqrt (1 + 1 / 2) = Real.sqrt 3 / Real.sqrt 2 := by
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.sqrt_div' 3 (by norm_num : (0 : ℝ) ≤ 2)]
  have e2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  rw [e1, e2] at h1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h3 : (5 : ℝ) / 3 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have : (1 + 1 / 2 : ℝ) * (Real.sqrt 3 / Real.sqrt 2) - 1 / 2 * (1 / Real.sqrt 2) -
      2 * Real.sqrt 2 * (1 / 2) = ((3 / 2) * Real.sqrt 3 - 1 / 2 - 2) / Real.sqrt 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hpos : 0 < ((3 / 2) * Real.sqrt 3 - 1 / 2 - 2) / Real.sqrt 2 :=
    div_pos (by linarith) hs2
  linarith

end Refutations.HigherRieszTwo
