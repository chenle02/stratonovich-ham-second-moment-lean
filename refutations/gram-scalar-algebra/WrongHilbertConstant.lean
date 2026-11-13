import StratonovichHAMSecondMoment.GramScalarAlgebra

/-!
Refutation for `StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_le` (the
inequality half of `hilbert_square`), manuscript label `L:gram-scalar-algebra`
(`E:gram-hilbert-square`).

Wrong variant: `hilbert_square_le` with the bound `‖z‖²/2` replaced by `‖z‖²/4`, stated
in the exact shape of the package theorem with the space quantified over `Type`. At
`H = ℝ`, `Φ = z = 1` the claim reads `1/2 ≤ 1/4`. The contrast theorem applies the
package `hilbert_square_le` at this point: there the correct bound `1/2 ≤ 1/2` holds
with equality.

Expected outcome: compiles (refuted).
-/

namespace Refutations.GramScalarAlgebra

/-- `hilbert_square_le` with the constant `1/4` in place of `1/2` is false. -/
theorem wrong_hilbert_constant :
    ¬ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Φ z : H),
      inner ℝ Φ z - ‖Φ‖ ^ 2 / 2 ≤ ‖z‖ ^ 2 / 4 := by
  intro h
  have := h ℝ 1 1
  rw [real_inner_self_eq_norm_sq] at this
  norm_num at this

/-- Contrast: at `Φ = z = 1` in `ℝ` the package `hilbert_square_le` holds, while the
variant's bound fails. -/
theorem wrong_hilbert_constant_contrast :
    inner ℝ (1 : ℝ) 1 - ‖(1 : ℝ)‖ ^ 2 / 2 ≤ ‖(1 : ℝ)‖ ^ 2 / 2 ∧
      ¬ (inner ℝ (1 : ℝ) 1 - ‖(1 : ℝ)‖ ^ 2 / 2 ≤ ‖(1 : ℝ)‖ ^ 2 / 4) := by
  refine ⟨StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_le (1 : ℝ) 1, ?_⟩
  rw [real_inner_self_eq_norm_sq]
  norm_num

end Refutations.GramScalarAlgebra
