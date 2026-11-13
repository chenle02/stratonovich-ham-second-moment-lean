import StratonovichHAMSecondMoment.GramScalarAlgebra

/-!
Refutation for `StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual`, manuscript
label `L:gram-scalar-algebra` (`E:gram-sqrt-dual`).

Wrong variant: `sqrt_dual` with the hypothesis `t ≥ 0` dropped, stated in the exact
shape of the package theorem otherwise. It relies on Mathlib's junk value
`Real.sqrt t = 0` for `t < 0`: at `ℓ = 0`, `w = 1`, `t = -1` the claim reads
`0 ≤ -1`. The contrast theorem shows that `w > 0` holds at this point and that
`t ≥ 0` fails there, the latter derived from the package `sqrt_dual`.

Expected outcome: compiles (refuted).
-/

namespace Refutations.GramScalarAlgebra

/-- `sqrt_dual` without `0 ≤ t` is false. -/
theorem negative_time :
    ¬ ∀ ell w t : ℝ, 0 < w →
      2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t := by
  intro h
  have := h 0 1 (-1) (by norm_num)
  norm_num at this

/-- Contrast: at `ℓ = 0`, `w = 1`, `t = -1` the kept hypothesis `0 < w` holds and the
dropped hypothesis `0 ≤ t` fails, as the package `sqrt_dual` would otherwise give
`0 ≤ -1`. -/
theorem negative_time_contrast : (0 : ℝ) < 1 ∧ ¬ ((0 : ℝ) ≤ -1) := by
  refine ⟨one_pos, fun ht => ?_⟩
  have := StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual 0 1 (-1) one_pos ht
  norm_num at this

end Refutations.GramScalarAlgebra
