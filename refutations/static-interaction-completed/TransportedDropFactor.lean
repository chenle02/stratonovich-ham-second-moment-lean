import StratonovichHAMSecondMoment.StaticInteractionCompleted

/-!
Refutation for `StratonovichHAMSecondMoment.StaticInteractionCompleted.transported_le` (the
transported order bound in the proof of `C:static-interaction`, main TeX lines 3272-3292 at
edf7085f).

Wrong variant: the conclusion `‖T x‖ ≤ √e · a · N` without the comparison factor `1/(λh)`,
while the hypotheses keep `‖x‖ ≤ (λh)⁻¹ z`.  Counterexample: `E = ℝ`, `T = id`, `x = 2`,
`λh = 1/2`, `z = a = N1 = N = 1`: `‖T x‖ = 2 > √e`.  No junk-value reliance.
`transported_drop_factor_contrast` is the package bound at the same point (`≤ 2√e`).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.StaticInteractionCompleted

open StratonovichHAMSecondMoment.StaticInteractionCompleted

theorem id_norm_le_sqrt_e : ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ √(Real.exp 1) :=
  ContinuousLinearMap.norm_id_le.trans
    (Real.one_le_sqrt.2 (Real.one_le_exp (by norm_num)))

/-- The transported bound fails without the factor `1/(λh)`. -/
theorem transported_drop_factor_refuted :
    ¬ (∀ (T : ℝ →L[ℝ] ℝ), ‖T‖ ≤ √(Real.exp 1) → ∀ (z a N1 N lh : ℝ), 0 ≤ a → 0 < lh →
        ∀ x : ℝ, ‖x‖ ≤ lh⁻¹ * z → z ≤ a * N1 → N1 ≤ N → ‖T x‖ ≤ √(Real.exp 1) * a * N) := by
  intro H
  have h := H (ContinuousLinearMap.id ℝ ℝ) id_norm_le_sqrt_e 1 1 1 1 (1 / 2) (by norm_num)
    (by norm_num) 2 (by norm_num) (by norm_num) le_rfl
  simp only [ContinuousLinearMap.id_apply, mul_one, Real.norm_eq_abs] at h
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have hs : √(Real.exp 1) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  norm_num at h
  linarith

/-- Contrast: the package bound at the same point. -/
theorem transported_drop_factor_contrast :
    ‖ContinuousLinearMap.id ℝ ℝ (2 : ℝ)‖ ≤ √(Real.exp 1) / (1 / 2) * 1 * 1 :=
  transported_le _ id_norm_le_sqrt_e (z := 1) (N1 := 1) (by norm_num) (by norm_num) 2
    (by norm_num) (by norm_num) le_rfl

end Refutations.StaticInteractionCompleted
