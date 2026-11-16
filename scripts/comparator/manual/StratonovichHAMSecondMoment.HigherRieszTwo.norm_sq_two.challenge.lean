namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK)
open WaveGreen (waveGreen)
-- Statement copied from the source (the printed type writes the coordinate `x 0` through `PiLp`'s coercion to functions (a `fun _ => ℝ` family), the declaration at type `ℝ`).
-- The section variables of the source, as there:
variable {d : ℕ}
/-- For x in R^2: |x|^2 = x_0^2 + x_1^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.HigherRieszTwo.norm_sq_two (x : Rd 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
