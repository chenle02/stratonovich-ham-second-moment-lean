namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
-- Statement copied from the source (the printed type writes the coordinate `x 0` through `PiLp`'s coercion to functions (a `fun _ => ℝ` family), the declaration at type `ℝ`).
/-- For x in R^(n+1): |x| = sqrt(x_0^2 + |(splitFirst n x).2|^2). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveGreenFourier.norm_splitFirst (n : ℕ) (x : Rd (n + 1)) :
    ‖x‖ = √((x 0) ^ 2 + ‖(splitFirst n x).2‖ ^ 2) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.WaveGreenFourier.norm_splitFirst
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
