import StratonovichHAMSecondMoment.ClockCopy

/-!
Refutation for the strict inequality `J_{Γ,1}(θ) < K_Γ(θ)` of
`P:clock-copy-obstruction` (`E:clock-copy-obstruction`, main TeX lines
7764-7773), package wrapper
`StratonovichHAMSecondMoment.ClockCopy.clock_copy_obstruction_paper`.

Wrong variant: the hypothesis `Γ ≠ 0` (equivalently `μ ≠ 0`) dropped, with the
remaining analytic hypotheses of the general package theorems kept
(`∫(1+|ξ|²)⁻¹ dμ < ∞`, `μ{0} = 0`, `0 < a < 1`, `θ > 0`). Witness: `μ = 0`
on `ℝ¹`, where `J_{Γ,1}(θ) = K_Γ(θ) = 0`, so the strict inequality fails.
The values `0` come from integrals over the zero measure (not from a
non-integrable junk integral).
The contrast theorem applies the package identities `J_one_eq` and
`K_eq_integral_weight` at the witness: both sides equal integrals of the
zero weight.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Refutations.ClockCopy

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.SpectralHomog
  StratonovichHAMSecondMoment.DampedNorms StratonovichHAMSecondMoment.ClockCopy

theorem weight_zero_measure (a θ l : ℝ) : weight a θ (0 : Measure (Rd 1)) l = 0 := by
  simp [weight, StratonovichHAMSecondMoment.SpectralHomog.resolvent]

/-- Contrast: at `μ = 0` the package identities give `J_{Γ,1}(θ) = K_Γ(θ)`. -/
theorem dropped_nonzero_contrast :
    J (1 / 2) 1 (0 : Measure (Rd 1)) 1 = N2sq (1 / 2) 1 (0 : Measure (Rd 1)) := by
  have hR : Integrable (fun ξ : Rd 1 => 1 / (1 + ‖ξ‖ ^ 2)) (0 : Measure (Rd 1)) :=
    integrable_zero_measure
  rw [(J_one_eq (0 : Measure (Rd 1)) hR (1 / 2) 1 (by norm_num) (by norm_num) one_pos).2,
    K_eq_integral_weight (0 : Measure (Rd 1)) hR (by simp) (1 / 2) 1 (by norm_num)
      (by norm_num) one_pos]
  simp [filteredWeight, weight_zero_measure]

/-- Dropping `Γ ≠ 0` makes the strict inequality false. -/
theorem strict_fails_without_nonzero :
    ¬ (∀ (μ : Measure (Rd 1)) [SFinite μ],
      Integrable (fun ξ : Rd 1 => 1 / (1 + ‖ξ‖ ^ 2)) μ → μ {0} = 0 →
        ∀ a θ : ℝ, 0 < a → a < 1 → 0 < θ → J a θ μ 1 < N2sq a θ μ) := by
  intro h
  have := h 0 integrable_zero_measure (by simp) (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  rw [dropped_nonzero_contrast] at this
  exact lt_irrefl _ this

end Refutations.ClockCopy
