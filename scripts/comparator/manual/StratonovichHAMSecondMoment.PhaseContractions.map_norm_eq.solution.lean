namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions
open MeasureTheory Set Real Filter Metric
open scoped ENNReal Pointwise
open HomogHypothesis SpectralHomog MaskedSpectralGrowth SpectralMassIdentity WaveKernel WaveGreen
-- Statement copied from the source (the printed type elaborates the measurable space on `ℝ` as `Real.measurableSpace`, the declaration through `MeasureSpace.toMeasurableSpace`).
/-- For locally finite nu on R^d with nu(cA) = c^beta nu(A), beta > 0: the image of nu under y -> |y| is (ofReal beta * nu(ball 0 1)) times Lebesgue on (0, inf) with density r^(beta-1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PhaseContractions.map_norm_eq {d : ℕ} (ν : Measure (Rd d)) [IsLocallyFiniteMeasure ν] {β : ℝ}
    (hβ : 0 < β) (hs : SpectralHomogeneous ν β) :
    ν.map (fun y => ‖y‖) = (ENNReal.ofReal β * ν (ball (0 : Rd d) 1)) •
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => ENNReal.ofReal (r ^ (β - 1))) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.PhaseContractions.map_norm_eq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions
