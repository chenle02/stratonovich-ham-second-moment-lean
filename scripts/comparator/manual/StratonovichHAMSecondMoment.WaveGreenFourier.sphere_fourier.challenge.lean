namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
-- Statement copied from the source (the printed type writes the sphere's subtype as `Subtype`, the declaration as `Set.Elem`).
/-- For xi in R^3: omega -> exp(i <xi,omega>) is integrable on the unit sphere for volume.toSphere and its integral equals 4 pi sinc |xi| (sinc 0 = 1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveGreenFourier.sphere_fourier (ξ : Rd 3) :
    Integrable (fun ω : sphere (0 : Rd 3) 1 =>
        Complex.exp (Complex.I * ((inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ)))
        (volume : Measure (Rd 3)).toSphere ∧
      ∫ ω : sphere (0 : Rd 3) 1, Complex.exp (Complex.I * ((inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ))
          ∂(volume : Measure (Rd 3)).toSphere = ((4 * π * Real.sinc ‖ξ‖ : ℝ) : ℂ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveGreenFourier
