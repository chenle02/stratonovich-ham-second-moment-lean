import StratonovichHAMSecondMoment.StaticPhaseCauchy

/-!
Refutation for `StratonovichHAMSecondMoment.StaticPhaseCauchy.norm_taylorCoeff_le` (Cauchy's
estimate in the proof of `P:static-phase-all-orders`, main TeX lines 2616-2624 at
a284420).

Wrong variant: the coefficient bound with `ρ^(n+1)` in place of `ρ^n` (an off-by-one in
the power of the radius).  Counterexample: `F = 1` (constant, values in `ℂ`), `n = 0`,
`ρ = 2`, `M = 1`: the coefficient is `1`, the wrong bound `1/2`.  No junk-value reliance.
`cauchy_power_contrast` is the package estimate at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.StaticPhaseCauchy

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-- Cauchy's estimate fails with `ρ^(n+1)`. -/
theorem cauchy_power_refuted :
    ¬ (∀ (F : ℂ → ℂ), Differentiable ℂ F → ∀ ρ M : ℝ, 0 < ρ →
        (∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M) →
        ∀ n : ℕ, ‖taylorCoeff F n‖ ≤ M / ρ ^ (n + 1)) := by
  intro H
  have h := H (fun _ => 1) (differentiable_const 1) 2 1 (by norm_num)
    (fun z _ => by simp) 0
  simp [taylorCoeff] at h
  norm_num at h

/-- Contrast: the package estimate at the same point. -/
theorem cauchy_power_contrast : ‖taylorCoeff (fun _ : ℂ => (1 : ℂ)) 0‖ ≤ 1 / 2 ^ 0 :=
  norm_taylorCoeff_le (differentiable_const 1) (by norm_num) (fun z _ => by simp) 0

end Refutations.StaticPhaseCauchy
