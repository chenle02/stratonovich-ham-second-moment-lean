import StratonovichHAMSecondMoment.StaticPhaseCauchy

/-!
Refutation for `StratonovichHAMSecondMoment.StaticPhaseCauchy.phase_weight_le` (pointwise
form of the norm comparison `‖z‖_{1/h} ≤ n ‖z‖_{n/h}` of `P:static-phase-all-orders`,
main TeX line 2632 at a284420).

Wrong variant: the multiplier comparison with `n` in place of `n²` (forgetting that the
norm comparison by `n` is a comparison of squared norms by `n²`).  Counterexample:
`n = 2`, `h = 1`, `r = 0`: `1 ≤ 2 · (1/4)` is false.  No junk-value reliance.
`weight_square_contrast` is the package inequality at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.StaticPhaseCauchy

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-- The multiplier comparison fails with `n` in place of `n²`. -/
theorem weight_square_refuted :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ h r : ℝ, 0 < h → 0 ≤ r →
        ((1 / h) ^ 2 + r)⁻¹ ≤ (n : ℝ) * ((n / h) ^ 2 + r)⁻¹) := by
  intro H
  have h := H 2 (by norm_num) 1 0 one_pos le_rfl
  norm_num at h

/-- Contrast: the package inequality (with `n²`) at the same point. -/
theorem weight_square_contrast :
    ((1 / (1 : ℝ)) ^ 2 + 0)⁻¹ ≤ ((2 : ℕ) : ℝ) ^ 2 * (((2 : ℕ) / (1 : ℝ)) ^ 2 + 0)⁻¹ :=
  (phase_weight_le (by norm_num) one_pos le_rfl).1

end Refutations.StaticPhaseCauchy
