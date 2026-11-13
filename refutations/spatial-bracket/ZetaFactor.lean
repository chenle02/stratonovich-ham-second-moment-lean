/-
Refutation for the second form of `E:occupation-score-ceiling`, package theorem
`StratonovichHAMSecondMoment.SpatialBracket.ceilingValue_eq_zeta`
(`integrated_occupation_ceiling.tex` lines 214-215 at a284420:
`U_𝔠 = 𝔠^m (2ζ)^{α/(2k)} F_0(D_ζ C^{2/(2-α)})`).

Wrong variant: the factor `(2ζ)^{α/(2k)}` is dropped, `U_𝔠 = 𝔠^m F_0(D_ζ C^{2/(2-α)})` for
every `ζ > 0`.  Counterexample: `α = 1`, `𝔠 = C = 1`, `ζ = 1`: the package identity gives
`U_1 = 2^{1/4} F_0(D_1)` with `F_0(D_1) > 0`, so the variant would force `2^{1/4} = 1`.
`zeta_factor_contrast` is the package identity at that point.
No junk-value reliance (`F_0(D_1) > 0` is proved).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialBracket

set_option autoImplicit false

open Real StratonovichHAMSecondMoment StratonovichHAMSecondMoment.SpatialBracket

namespace Refutations.SpatialBracket

/-- The package identity at `α = 1`, `𝔠 = C = ζ = 1`. -/
theorem zeta_factor_contrast :
    ceilingValue 1 1 1 = (1 : ℝ) ^ ((4 - 1 : ℝ) / (3 - 1)) *
      (2 * 1 : ℝ) ^ ((1 : ℝ) / (2 * (3 - 1))) *
      SpatialFourLinear.F0 1 (Dzeta 1 1 * (1 : ℝ) ^ ((2 : ℝ) / (2 - 1))) :=
  ceilingValue_eq_zeta (by norm_num) (by norm_num) zero_le_one one_pos

/-- Dropping the factor `(2ζ)^{α/(2k)}` from the second form is false. -/
theorem zeta_factor_refuted :
    ¬ (∀ c C ζ : ℝ, 0 < ζ → 0 ≤ C →
      ceilingValue 1 c C =
        c ^ ((4 - 1 : ℝ) / (3 - 1)) *
          SpatialFourLinear.F0 1 (Dzeta 1 ζ * C ^ ((2 : ℝ) / (2 - 1)))) := by
  intro h
  have h1 := h 1 1 1 one_pos zero_le_one
  rw [zeta_factor_contrast] at h1
  have hD : 0 < Dzeta 1 1 * (1 : ℝ) ^ ((2 : ℝ) / (2 - 1)) := by
    unfold Dzeta; norm_num
  have hF : 0 < SpatialFourLinear.F0 1 (Dzeta 1 1 * (1 : ℝ) ^ ((2 : ℝ) / (2 - 1))) := by
    rw [← Fb_zero_eq_F0 (by norm_num)]
    exact Fb_pos (by norm_num) (by norm_num) (by norm_num) hD
  generalize SpatialFourLinear.F0 1 (Dzeta 1 1 * (1 : ℝ) ^ ((2 : ℝ) / (2 - 1))) = X at h1 hF
  have h2 : (2 * 1 : ℝ) ^ ((1 : ℝ) / (2 * (3 - 1))) = 1 := by
    rw [one_rpow, one_mul, one_mul] at h1
    exact (mul_eq_right₀ hF.ne').1 h1
  have h3 : (1 : ℝ) < (2 * 1 : ℝ) ^ ((1 : ℝ) / (2 * (3 - 1))) :=
    one_lt_rpow (by norm_num) (by norm_num)
  linarith

end Refutations.SpatialBracket
