import StratonovichHAMSecondMoment.DampedSmoothing

/-!
Refutation for the hypothesis `0 < ε` in the multiplier membership
`IsMultiplier (gaussMult (ε/2))` of
`StratonovichHAMSecondMoment.DampedSmoothing.spatial_smoothing_multiplier` (covariance
smoothing of `L:damped-homogeneous-norms`, main TeX lines 1052-1053; class of multipliers
with values in `[0,1]`, lines 1033-1036).

Class (c), control of a broader Lean generalization outside the manuscript domain: for
`ε < 0` the formula `e^{-ε|ξ|²/2}` exceeds `1` off the origin, so it is not in the
class.  Witness: `ε = -2`, `ξ = e₁` in `ℝ¹`, value `e > 1`.

Wrong variant: the membership for every real `ε`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.DampedSmoothing

open StratonovichHAMSecondMoment
open DampedMultiplier (gaussMult coe_gaussMult isMultiplier_gaussMult IsMultiplier)

/-- Contrast: membership at `ε = 2`, and `gaussMult (-1) e₁ = e > 1`. -/
theorem negative_eps_multiplier_contrast :
    IsMultiplier (gaussMult (d := 1) (2 / 2)) ∧
      1 < gaussMult (d := 1) (-2 / 2) (EuclideanSpace.single 0 1) := by
  refine ⟨isMultiplier_gaussMult _ (by norm_num), ?_⟩
  have hn : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : HomogHypothesis.Rd 1)‖ = 1 := by
    simp
  rw [← NNReal.coe_lt_coe, coe_gaussMult, NNReal.coe_one, hn]
  exact lt_of_eq_of_lt Real.exp_zero.symm (Real.exp_lt_exp.2 (by norm_num))

/-- The wrong variant (membership for every real `ε`) is false. -/
theorem negative_eps_multiplier :
    ¬ ∀ ε : ℝ, IsMultiplier (gaussMult (d := 1) (ε / 2)) := by
  intro H
  exact absurd ((H (-2)).2 (EuclideanSpace.single 0 1))
    (not_le.2 negative_eps_multiplier_contrast.2)

end Refutations.DampedSmoothing
