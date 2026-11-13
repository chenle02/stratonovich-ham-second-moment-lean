import StratonovichHAMSecondMoment.TimeFractional

/-!
Refutation for `StratonovichHAMSecondMoment.TimeFractional.Psi_le_rpow`
(the bound `Ψ_a(r,v) ≤ r^{-a}` stated after `E:averaged-clock-kernel`, main
TeX line 7713): the exponent `-a` cannot be replaced by `a`.

The wrong variant is the package statement (same binders and hypotheses) with
`r^{-a}` replaced by `r^a`. Witness: `a = 1/2`, `r = 1/4`, `v = 0`, where
`Ψ_a(r,0) = r^{-a} = 2 > 1/2 = r^a` (`Psi_zero`). No junk value is used:
`r > 0` and the integrand of `Ψ` is integrable there.
The contrast theorem applies the package (`Psi_zero`) at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.TimeFractional

open StratonovichHAMSecondMoment.TimeFractional

theorem quarter_rpow_half : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
  rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- Contrast: at the witness, `r^a < Ψ_a(r,0)`. -/
theorem psi_exponent_contrast : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) < Psi (1 / 2) (1 / 4) 0 := by
  rw [Psi_zero _ _ (by norm_num) (by norm_num), Real.rpow_neg (by norm_num),
    quarter_rpow_half]
  norm_num

/-- The wrong variant `Ψ_a(r,v) ≤ r^a` is false. -/
theorem psi_wrong_exponent :
    ¬ (∀ a r v : ℝ, 0 < a → 0 < r → 0 ≤ v → Psi a r v ≤ r ^ a) := by
  intro h
  have := h (1 / 2) (1 / 4) 0 (by norm_num) (by norm_num) le_rfl
  exact absurd this (not_le.2 psi_exponent_contrast)

end Refutations.TimeFractional
