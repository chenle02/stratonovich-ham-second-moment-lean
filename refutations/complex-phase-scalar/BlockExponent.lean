/-
Refutation for the final constant of `L:complex-phase` (main TeX lines
2457-2459 at a284420), package theorem
`StratonovichHAMSecondMoment.ComplexPhaseScalar.block_constant_le`
(`(39+12x)e^x ≤ 39(1+x)e^x ≤ 100 e^{2x}`, `x = λh ≥ 0`).

Wrong variant: the exponent `λh` instead of `2λh` on the right,
`(39+12x)e^x ≤ 100 e^x`.  Counterexample: `x = 6`, `39 + 72 = 111 > 100`.
`block_exponent_contrast` applies the package theorem at `x = 6`.  No junk-value
reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ComplexPhaseScalar

set_option autoImplicit false

namespace Refutations.ComplexPhaseScalar

/-- The block sum is not bounded by `100 e^{λh}`. -/
theorem block_exponent_one_refuted :
    ¬ (∀ x : ℝ, 0 ≤ x → (39 + 12 * x) * Real.exp x ≤ 100 * Real.exp x) := by
  intro h
  have h1 := h 6 (by norm_num)
  have he := Real.exp_pos (6 : ℝ)
  nlinarith

/-- The package bound at `x = 6`. -/
theorem block_exponent_contrast :
    (39 + 12 * (6 : ℝ)) * Real.exp 6 ≤ 100 * Real.exp (2 * 6) :=
  (StratonovichHAMSecondMoment.ComplexPhaseScalar.block_constant_le (by norm_num)).1.trans
    (StratonovichHAMSecondMoment.ComplexPhaseScalar.block_constant_le (by norm_num)).2

end Refutations.ComplexPhaseScalar
