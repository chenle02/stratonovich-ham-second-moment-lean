/-
Refutation for the phase-weight change of `L:interval-complex` (main TeX lines
2966-2970 at a284420), package theorem
`StratonovichHAMSecondMoment.ComplexPhaseScalar.phase_weight_change`
(`(ρ_new²+x)⁻¹ ≤ max{1, ρ_old/ρ_new}² (ρ_old²+x)⁻¹`, the multiplier form of
`‖z‖_{ρ_new} ≤ max{1, ρ_old/ρ_new} ‖z‖_{ρ_old}` for squared norms).

Wrong variant: the factor `max{1, ρ_old/ρ_new}` unsquared in the multiplier
(i.e. the loss factor applied to squared norms).  Counterexample:
`ρ_old = 2`, `ρ_new = 1`, `x = 0`: `1 ≤ 2 · 1/4` is false.
`phase_weight_contrast` applies the package theorem at the same point, with
equality.  No junk-value reliance (all denominators positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ComplexPhaseScalar

set_option autoImplicit false

namespace Refutations.ComplexPhaseScalar

/-- The unsquared loss factor in the multiplier inequality is false. -/
theorem phase_weight_unsquared_refuted :
    ¬ (∀ ρo ρn x : ℝ, 0 < ρo → 0 < ρn → 0 ≤ x →
        (ρn ^ 2 + x)⁻¹ ≤ max 1 (ρo / ρn) * (ρo ^ 2 + x)⁻¹) := by
  intro h
  have h1 := h 2 1 0 (by norm_num) (by norm_num) le_rfl
  rw [show max (1 : ℝ) (2 / 1) = 2 by norm_num] at h1
  norm_num at h1

/-- The package bound at `ρ_old = 2`, `ρ_new = 1`, `x = 0`. -/
theorem phase_weight_contrast :
    ((1 : ℝ) ^ 2 + 0)⁻¹ ≤ (max 1 ((2 : ℝ) / 1)) ^ 2 * ((2 : ℝ) ^ 2 + 0)⁻¹ :=
  StratonovichHAMSecondMoment.ComplexPhaseScalar.phase_weight_change (by norm_num) (by norm_num)
    le_rfl

end Refutations.ComplexPhaseScalar
