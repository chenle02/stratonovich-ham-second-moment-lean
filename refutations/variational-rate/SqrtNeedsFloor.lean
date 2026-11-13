/-
Refutation for the role of the positive floor in the rate Lipschitz bound of
`P:variational-unmasked-rate` (`notes/integrated_unmasked_variational.tex`
lines 154-160 at a284420), package theorem
`StratonovichHAMSecondMoment.VariationalRate.abs_sqrt_sub_le`, which needs
`a, b ≥ ε > 0`.

Wrong variant: the floor dropped, i.e. a Lipschitz constant `L` for the
square root on `[0, ∞)`: `|√a - √b| ≤ L |a - b|` for all `a, b ≥ 0`.
Counterexample: `b = 0`, `a = 1/(4(L+1)²)`: `√a = 1/(2(L+1)) > L a`.
`sqrt_floor_contrast` is the package bound with the floor `ε = a` at the same
`a` and `b = a`.  No junk-value reliance (`a > 0`, `√0 = 0` is the true
value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalRate

set_option autoImplicit false

namespace Refutations.VariationalRate

/-- The square root is not Lipschitz on `[0, ∞)`. -/
theorem sqrt_needs_floor_refuted :
    ¬ (∃ L : ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        |Real.sqrt a - Real.sqrt b| ≤ L * |a - b|) := by
  rintro ⟨L, h⟩
  have hL : 0 ≤ L := by
    have := h 1 0 zero_le_one le_rfl
    simp at this; linarith
  set t : ℝ := 1 / (2 * (L + 1)) with ht
  have htp : 0 < t := by positivity
  have h1 := h (t ^ 2) 0 (sq_nonneg _) le_rfl
  rw [Real.sqrt_sq htp.le, Real.sqrt_zero, sub_zero, sub_zero, abs_of_pos htp,
    abs_of_pos (by positivity)] at h1
  have hlt : L * t < 1 := by
    rw [ht, mul_one_div, div_lt_one (by positivity)]; linarith
  nlinarith

/-- The package bound with the floor `ε = a = b = 1/4`. -/
theorem sqrt_floor_contrast :
    |Real.sqrt (1 / 4) - Real.sqrt (1 / 4)| ≤ |(1 / 4 : ℝ) - 1 / 4| / (2 * Real.sqrt (1 / 4)) :=
  StratonovichHAMSecondMoment.VariationalRate.abs_sqrt_sub_le (by norm_num) le_rfl le_rfl

end Refutations.VariationalRate
