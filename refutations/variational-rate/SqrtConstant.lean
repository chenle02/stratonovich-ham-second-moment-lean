/-
Refutation for the rate Lipschitz constant of `P:variational-unmasked-rate`
(`notes/integrated_unmasked_variational.tex` line 158 at a284420:
`|λ_s - λ_t| ≤ C_Ψ/(2√ε₀) |s - t|`), package theorem
`StratonovichHAMSecondMoment.VariationalRate.abs_sqrt_sub_le`
(`|√a - √b| ≤ |a - b|/(2√ε)` for `a, b ≥ ε > 0`).

Wrong variant: the constant `1/(2√ε)` replaced by `1/(4√ε)`.
Counterexample: `ε = a = 1`, `b = 4`: `|1 - 2| = 1 > 3/4`.
`sqrt_constant_contrast` is the package bound at the same point
(`1 ≤ 3/2`).  No junk-value reliance (all square roots of positive reals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalRate

set_option autoImplicit false

namespace Refutations.VariationalRate

/-- The constant `1/(4√ε)` is too small. -/
theorem sqrt_constant_refuted :
    ¬ (∀ ε a b : ℝ, 0 < ε → ε ≤ a → ε ≤ b →
        |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (4 * Real.sqrt ε)) := by
  intro h
  have h1 := h 1 1 4 one_pos le_rfl (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, Real.sqrt_one] at h1
  norm_num at h1

/-- The package bound at the same point. -/
theorem sqrt_constant_contrast :
    |Real.sqrt 1 - Real.sqrt 4| ≤ |(1 : ℝ) - 4| / (2 * Real.sqrt 1) :=
  StratonovichHAMSecondMoment.VariationalRate.abs_sqrt_sub_le one_pos le_rfl (by norm_num)

end Refutations.VariationalRate
