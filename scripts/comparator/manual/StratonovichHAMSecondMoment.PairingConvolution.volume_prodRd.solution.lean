-- Printed type replaced by the source's statement (the printed one elaborates another instance path for the measure or metric instance, so CheckFidelity's Expr equality fails).
/-- Lebesgue measure on R x R^d is the product of the Lebesgue measures. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.PairingConvolution.volume_prodRd :
    ∀ {d : ℕ},
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)) =
        (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)) := by
  exact @_root_.StratonovichHAMSecondMoment.PairingConvolution.volume_prodRd
