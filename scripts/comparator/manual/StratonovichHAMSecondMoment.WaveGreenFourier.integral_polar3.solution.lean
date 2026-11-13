namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
-- Statement copied from the source (the printed type writes the sphere's subtype as `Subtype`, the declaration as `Set.Elem`).
/-- For integrable f : R^3 -> C: int f = int over the unit sphere (measure volume.toSphere) of int over (0, inf) of r^2 f(r omega) dr. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveGreenFourier.integral_polar3 (f : Rd 3 → ℂ) (hf : Integrable f) :
    ∫ x, f x = ∫ ω : sphere (0 : Rd 3) 1,
      (∫ r in Ioi (0 : ℝ), r ^ 2 • f (r • (ω : Rd 3))) ∂(volume : Measure (Rd 3)).toSphere := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.WaveGreenFourier.integral_polar3
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
