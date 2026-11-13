/-
Refutation for the Neumann bound of `L:interval-complex` (main TeX lines
2939-2940 at a284420), package theorem
`StratonovichHAMSecondMoment.ComplexPhaseScalar.neumann_root_comparison`
(`‖Q - 1‖ ≤ 1/6` gives `‖Q⁻¹‖ ≤ 6/5`).

Wrong variant: the inverse bound `1` instead of `6/5`.  Counterexample in the
complete normed ring `ℝ`: `Q = 5/6`, `‖Q - 1‖ = 1/6`, `Q⁻¹ = 6/5 > 1`.
`neumann_inverse_contrast` applies the package theorem at the same point; the
constant `6/5` is attained there.  No junk-value reliance (`Ring.inverse` is
evaluated at the unit `5/6`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ComplexPhaseScalar

set_option autoImplicit false

namespace Refutations.ComplexPhaseScalar

/-- The Neumann inverse bound `1` (instead of `6/5`) is false. -/
theorem neumann_inverse_le_one_refuted :
    ¬ (∀ Q : ℝ, ‖Q - 1‖ ≤ 1 / 6 → ‖Ring.inverse Q‖ ≤ 1) := by
  intro h
  have h1 := h (5 / 6) (by rw [Real.norm_eq_abs, abs_le]; constructor <;> norm_num)
  rw [Ring.inverse_eq_inv', Real.norm_eq_abs] at h1
  norm_num [abs_of_pos] at h1

/-- The package bound at `Q = 5/6`, and its equality there. -/
theorem neumann_inverse_contrast :
    ‖Ring.inverse (5 / 6 : ℝ)‖ ≤ 6 / 5 ∧ ‖Ring.inverse (5 / 6 : ℝ)‖ = 6 / 5 := by
  refine ⟨(StratonovichHAMSecondMoment.ComplexPhaseScalar.neumann_root_comparison
    (by rw [norm_one]) (by rw [Real.norm_eq_abs, abs_le]; constructor <;> norm_num)).2.2, ?_⟩
  rw [Ring.inverse_eq_inv', Real.norm_eq_abs]
  norm_num [abs_of_pos]

end Refutations.ComplexPhaseScalar
