-- Printed type replaced by the source's statement (the printed one elaborates another instance path for the measure or metric instance, so CheckFidelity's Expr equality fails).
/-- For all eta, s, z: green3s eta s z = ofReal(s/(4 pi)) * int^- ofReal(heatDens eta (z - s omega)) over the unit sphere measure (volume.toSphere), i.e. the sphere form of waveGreen 3 (model M1). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.GreenSmoothed3.green3s_eq_sphere :
    ∀ (η s : ℝ) (z : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd 3),
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GreenSmoothed3.green3s η s z = ENNReal.ofReal (s / (4 * Real.pi)) *
        ∫⁻ ω, ENNReal.ofReal (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaConvolution.heatDens η (z - s • (ω : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)))
          ∂(MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)).toSphere := by
  exact @_root_.StratonovichHAMSecondMoment.GreenSmoothed3.green3s_eq_sphere
