namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
-- Statement copied from the source (the printed type writes the sphere's subtype as `Subtype`, the declaration as `Set.Elem`).
/-- For |e| = 1 in R^3 and f : R -> E (real normed space) integrable on [-1, 1]: omega -> f(<e,omega>) is toSphere-integrable and its integral over the unit sphere equals (2 pi) times the integral of f over [-1, 1]. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveGreenFourier.integral_sphere_inner (e : Rd 3) (he : ‖e‖ = 1) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) :
    Integrable (fun ω : sphere (0 : Rd 3) 1 => f (inner ℝ e (ω : Rd 3)))
        (volume : Measure (Rd 3)).toSphere ∧
      ∫ ω : sphere (0 : Rd 3) 1, f (inner ℝ e (ω : Rd 3)) ∂(volume : Measure (Rd 3)).toSphere =
        (2 * π) • ∫ t in Icc (-1 : ℝ) 1, f t := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
