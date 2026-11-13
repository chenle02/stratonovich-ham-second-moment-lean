import StratonovichHAMSecondMoment.HermiteFock

/-!
Refutation for `StratonovichHAMSecondMoment.HermiteFock.vacuum_insertion_isometry`
(`E‖∑_i g_i w_i‖² = ∑_i ‖w_i‖²`, the phase insertion on a vacuum color, main TeX lines
2878-2880 at a284420).

Wrong variant: `(∑_i ‖w_i‖)²` on the right (forgetting the independence of the modes).
Counterexample: two modes, `w = (1, 1)`: the package gives `2`, the wrong variant `4`.
No junk-value reliance.  `vacuum_contrast` is the package value.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.HermiteFock

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HermiteFock

/-- The vacuum insertion is not `(∑ ‖w_i‖)²`. -/
theorem vacuum_square_of_sum_refuted :
    ¬ (∀ w : Fin 2 → ℂ, ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • w i‖ ^ 2 ∂GaussianIBP.stdPi 2 =
        (∑ i, ‖w i‖) ^ 2) := by
  intro H
  have h := H (fun _ => 1)
  rw [(vacuum_insertion_isometry (fun _ : Fin 2 => (1 : ℂ))).2] at h
  norm_num at h

/-- Contrast: the package value `2` at `w = (1, 1)`. -/
theorem vacuum_contrast :
    ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • (fun _ : Fin 2 => (1 : ℂ)) i‖ ^ 2 ∂GaussianIBP.stdPi 2 = 2 := by
  rw [(vacuum_insertion_isometry (fun _ : Fin 2 => (1 : ℂ))).2]; norm_num

end Refutations.HermiteFock
