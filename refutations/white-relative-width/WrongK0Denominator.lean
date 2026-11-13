import StratonovichHAMSecondMoment.WhiteRelativeWidth

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteRelativeWidth.boundK0_mul_boundMass`,
the proof display of `C:white-relative-width` (TeX lines 148--152).

Wrong variant: the product identity with `K_0(a)` mistyped as `2^a/(1+a)` instead of
`2^a/(1-a)`.  Counterexample: `a = 1/2`; the mistyped product is `(1-a)/(1+a) = 1/3`
times the package product, which is positive.  `wrong_k0_denominator_contrast` is the
package identity at the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Real

namespace Refutations.WhiteRelativeWidth

open StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- `K_0(a) = 2^a/(1+a)` does not give the product formula of the proof. -/
theorem wrong_k0_denominator_refuted :
    ¬ (∀ a : ℝ, 0 < a → a < 1 →
        2 ^ a / (1 + a) * boundMass a =
          sqrt π / (2 * Gamma (1 + a / 2) * Gamma ((3 - a) / 2))) := by
  intro h
  have h1 := h (1 / 2) (by norm_num) (by norm_num)
  have h2 := boundK0_mul_boundMass (a := 1 / 2) (by norm_num) (by norm_num)
  rw [← h1] at h2
  have hM := boundMass_pos (a := 1 / 2) (by norm_num) (by norm_num)
  have h2a : 0 < (2:ℝ) ^ (1 / 2 : ℝ) := rpow_pos_of_pos two_pos _
  unfold boundK0 at h2
  have : (2:ℝ) ^ (1 / 2 : ℝ) / (1 - 1 / 2) * boundMass (1 / 2) =
      3 * ((2:ℝ) ^ (1 / 2 : ℝ) / (1 + 1 / 2) * boundMass (1 / 2)) := by ring
  rw [this] at h2
  have hp : 0 < (2:ℝ) ^ (1 / 2 : ℝ) / (1 + 1 / 2) * boundMass (1 / 2) := by positivity
  linarith

/-- Contrast: the package identity at `a = 1/2` with the correct `K_0`. -/
theorem wrong_k0_denominator_contrast :
    boundK0 (1 / 2) * boundMass (1 / 2) =
      sqrt π / (2 * Gamma (1 + 1 / 2 / 2) * Gamma ((3 - 1 / 2) / 2)) :=
  boundK0_mul_boundMass (by norm_num) (by norm_num)

end Refutations.WhiteRelativeWidth
