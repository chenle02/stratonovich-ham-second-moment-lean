import StratonovichHAMSecondMoment.FockSandwichModel

/-!
Refutation for the hypothesis `0 < ρ` of `StratonovichHAMSecondMoment.FockSandwichModel.mulR_mulI`
and `invSqrtShift_eq` (the square root of `A_0 + ρ²` has the explicit inverse
`(ρ² + |η|² 1_b)^{-1/2}`).

Wrong variant: drop `ρ > 0` and claim `symI ρ b η · symR ρ b η = 1` for all `ρ`.
Counterexample: `ρ = 0`, `η = 0`, where both symbols are `0` (Lean's `1/0 = 0`).  Class (c):
control of Lean's totalized arithmetic (the TeX takes `ρ > 0` throughout).
`inverse_shift_contrast` is the identity at `ρ = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockSandwichModel

open StratonovichHAMSecondMoment.FockSandwichModel
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Without the shift, the explicit inverse fails at `η = 0`. -/
theorem inverse_needs_shift_refuted :
    ¬ ∀ (ρ b : ℝ) (η : Rd 1), symI ρ b η * symR ρ b η = 1 := by
  intro H
  have h := H 0 0 0
  simp [symI, symR, symS, symA] at h

/-- Contrast: at `ρ = 1` the symbols are inverse. -/
theorem inverse_shift_contrast (b : ℝ) (η : Rd 1) : symI 1 b η * symR 1 b η = 1 := by
  have hpos : 0 < Real.sqrt (symS 1 b η) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) (sq_le_symS 1 b η))
  rw [symI, symR, one_div, inv_mul_cancel₀ hpos.ne']

end Refutations.FockSandwichModel
