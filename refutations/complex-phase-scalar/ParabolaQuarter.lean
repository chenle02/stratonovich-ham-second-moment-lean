/-
Refutation for the parabola constant of `L:complex-phase` (main TeX lines
2391-2392 at a284420), package theorem
`StratonovichHAMSecondMoment.ComplexPhaseScalar.parabola_coeff_le`
(`4δ²/(1-δ) ≤ 1/3` for `0 ≤ δ ≤ 1/4`).

Wrong variant: the hypothesis `δ ≤ 1/4` (from `δ_a = min{1/4, ...}`) dropped,
keeping only `0 ≤ δ < 1`.  Counterexample: `δ = 1/2`, `4δ²/(1-δ) = 2 > 1/3`.
`parabola_coeff_contrast` applies the package theorem at `δ = 1/4`, where the
constant `1/3` is attained.  No junk-value reliance (`1 - δ > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ComplexPhaseScalar

set_option autoImplicit false

namespace Refutations.ComplexPhaseScalar

/-- Without `δ ≤ 1/4` the parabola constant `1/3` fails. -/
theorem parabola_coeff_without_quarter_refuted :
    ¬ (∀ δ : ℝ, 0 ≤ δ → δ < 1 → 4 * δ ^ 2 / (1 - δ) ≤ 1 / 3) := by
  intro h
  have h1 := h (1 / 2) (by norm_num) (by norm_num)
  norm_num at h1

/-- The package bound at `δ = 1/4`, with equality. -/
theorem parabola_coeff_contrast :
    4 * (1 / 4 : ℝ) ^ 2 / (1 - 1 / 4) ≤ 1 / 3 ∧ 4 * (1 / 4 : ℝ) ^ 2 / (1 - 1 / 4) = 1 / 3 :=
  ⟨StratonovichHAMSecondMoment.ComplexPhaseScalar.parabola_coeff_le (by norm_num) (by norm_num),
    by norm_num⟩

end Refutations.ComplexPhaseScalar
