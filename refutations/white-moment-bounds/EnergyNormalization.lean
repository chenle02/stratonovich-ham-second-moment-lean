import StratonovichHAMSecondMoment.WhiteMomentBounds

/-!
Refutation for the use of the named input `StratonovichHAMSecondMoment.WhiteMomentBounds.
WhiteSpatialEnergy` (`𝓔_sp = c²/6`, `P:white-spatial-energy`,
`notes/integrated_white_evaluation.tex`, 39f2597a, lines 79-133) in
`white_moment_bounds_paper`: the closed form `2^m F₀(𝓔_sp) = (2/3)√c` (lines 159-161) pins the
energy normalization.

Wrong variant: the closed form survives with the energy `c²/3` (the factor `1/2` of the kinetic
term `b/2` dropped, i.e. the maximum of `cA - 3A²/2` read as `cA - 3A²/4`):
`2^m F₀(c²/3) = (2/3)√c`.  Counterexample: `c = 1`: `F₀` is strictly increasing, and
`F₀(1/3) = 2^{1/4} F₀(1/6)` by its homogeneity, so the left side is `2^{1/4}(2/3) ≠ 2/3`.  No
junk-value reliance.  `energy_normalization_contrast` is the package value at `c²/6`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.WhiteMomentBounds

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.WhiteModel

/-- `2^m F₀(c²/3) ≠ (2/3)√c` at `c = 1`. -/
theorem energy_normalization_refuted :
    ¬ (∀ c : ℝ, 0 < c →
        (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialFourLinear.F0 1 (c ^ 2 / 3) =
          2 / 3 * Real.sqrt c) := by
  intro h
  have h1 := h 1 one_pos
  have h0 := two_pow_F0_white (c := 1) zero_le_one
  have hmul := SpatialBracket.F0_mul (alpha := 1) (t := 2) (E := 1 ^ 2 / 6) (by norm_num)
    (by norm_num) (by norm_num)
  rw [show (2 : ℝ) * (1 ^ 2 / 6) = 1 ^ 2 / 3 by norm_num] at hmul
  have hgt : (1 : ℝ) < 2 ^ ((2 - 1) / 2 * (1 / ((3 : ℝ) - 1))) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hm : (0 : ℝ) < 2 ^ (((4 : ℝ) - 1) / (3 - 1)) := Real.rpow_pos_of_pos two_pos _
  rw [hmul] at h1
  have hs : (0 : ℝ) < 2 / 3 * Real.sqrt 1 := by rw [Real.sqrt_one]; norm_num
  have : (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) *
      (2 ^ ((2 - 1) / 2 * (1 / ((3 : ℝ) - 1))) * SpatialFourLinear.F0 1 (1 ^ 2 / 6)) =
      2 ^ ((2 - 1) / 2 * (1 / ((3 : ℝ) - 1))) *
        ((2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialFourLinear.F0 1 (1 ^ 2 / 6)) := by ring
  rw [this, h0] at h1
  nlinarith

/-- Contrast: `2^m F₀(c²/6) = (2/3)√c` at `c = 1`. -/
theorem energy_normalization_contrast :
    (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialFourLinear.F0 1 (1 ^ 2 / 6) =
      2 / 3 * Real.sqrt 1 :=
  two_pow_F0_white zero_le_one

end Refutations.WhiteMomentBounds
