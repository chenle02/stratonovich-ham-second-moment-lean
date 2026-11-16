namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For symbols g1, g2 of temperate growth and T tempered: the multiplier of g1 + g2 applied to T is the sum of the two multipliers applied to T. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.fourierMultiplier_add {g₁ g₂ : Rd d → ℂ} (h₁ : g₁.HasTemperateGrowth)
    (h₂ : g₂.HasTemperateGrowth) (T : 𝓢'(Rd d, ℂ)) :
    fourierMultiplierCLM ℂ (g₁ + g₂) T =
      fourierMultiplierCLM ℂ g₁ T + fourierMultiplierCLM ℂ g₂ T := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
