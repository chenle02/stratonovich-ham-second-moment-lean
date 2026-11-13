import StratonovichHAMSecondMoment.GramScalarAlgebra

/-!
Refutation for `StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual`, manuscript
label `L:gram-scalar-algebra` (`E:gram-sqrt-dual`).

Wrong variant: `sqrt_dual` with the hypothesis `0 < w` replaced by `w < 0`, stated in
the exact shape of the package theorem otherwise. At `ℓ = 1`, `w = -1`, `t = 1` the
claim reads `2 ≤ -2`. The contrast theorem shows that `t ≥ 0` holds at this point and
that `0 < w` fails there, the latter derived from the package `sqrt_dual`.

Expected outcome: compiles (refuted).
-/

namespace Refutations.GramScalarAlgebra

/-- `sqrt_dual` with `w < 0` in place of `0 < w` is false. -/
theorem negative_weight :
    ¬ ∀ ell w t : ℝ, w < 0 → 0 ≤ t →
      2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t := by
  intro h
  have := h 1 (-1) 1 (by norm_num) (by norm_num)
  norm_num at this

/-- Contrast: at `ℓ = 1`, `w = -1`, `t = 1` the kept hypothesis `0 ≤ t` holds and the
package hypothesis `0 < w` fails, as the package `sqrt_dual` would otherwise give
`2 ≤ -2`. -/
theorem negative_weight_contrast : (0 : ℝ) ≤ 1 ∧ ¬ ((0 : ℝ) < -1) := by
  refine ⟨zero_le_one, fun hw => ?_⟩
  have := StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual 1 (-1) 1 hw zero_le_one
  norm_num at this

end Refutations.GramScalarAlgebra
