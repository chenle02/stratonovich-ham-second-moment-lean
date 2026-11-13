import StratonovichHAMSecondMoment.WhiteClockLaplace

/-!
Refutation for `StratonovichHAMSecondMoment.WhiteClockLaplace.crossValue_diag` (and the
diagonal clause of `white_clock_laplace_paper`), manuscript statement
`K_×(θ,θ) = Γ_E(1-a)/(4θ^{3-a})` of `L:white-clock-laplace` (TeX lines 7660--7661).

Wrong variant: the diagonal value with constant `2` instead of `4`,
`K_×(θ,θ) = Γ_E(1-a)/(2θ^{3-a})`.  Counterexample: `a = 1/2`, `θ = 1`; the package
gives `Γ_E(1/2)/4 > 0`, which is not `Γ_E(1/2)/2`.  `diagonal_constant_contrast` is the
package value at the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.WhiteClockLaplace

open StratonovichHAMSecondMoment.WhiteClockLaplace

/-- The diagonal value with constant `2` is false. -/
theorem diagonal_constant_refuted :
    ¬ (∀ a θ : ℝ, 0 < a → a < 1 → 0 < θ →
        ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), crossIntegrand a θ θ (s, t) =
          Gamma (1 - a) / (2 * θ ^ (3 - a))) := by
  intro h
  have h1 := h (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  rw [(cross_transform_iterated (by norm_num) (by norm_num) one_pos one_pos).2,
    crossValue_diag _ one_pos, one_rpow] at h1
  have hG := Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1 - 1 / 2)
  linarith

/-- Contrast: the package diagonal value at `a = 1/2`, `θ = 1`. -/
theorem diagonal_constant_contrast :
    ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), crossIntegrand (1 / 2) 1 1 (s, t) =
      Gamma (1 - 1 / 2) / (4 * (1:ℝ) ^ (3 - 1 / 2 : ℝ)) :=
  (cross_transform_iterated (by norm_num) (by norm_num) one_pos one_pos).2.trans
    (crossValue_diag _ one_pos)

end Refutations.WhiteClockLaplace
