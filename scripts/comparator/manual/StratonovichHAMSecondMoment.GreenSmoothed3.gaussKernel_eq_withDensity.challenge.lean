-- Printed type replaced by the source's statement (the printed one elaborates another instance path for the measure or metric instance, so CheckFidelity's Expr equality fails).
/-- For eta > 0 and every d: DampedMultiplier.gaussKernel eta (the centered Gaussian N(0, eta I) on R^d) equals volume.withDensity (ofReal (heatDens eta)); proved by equality of characteristic functions. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.GreenSmoothed3.gaussKernel_eq_withDensity :
    ∀ {d : ℕ} {η : ℝ}, 0 < η →
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.gaussKernel (d := d) η =
        MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaConvolution.heatDens η x) := by
  sorry
