-- Printed type with the printed `have this := ...; ↑this` written as the source's `show HR d from ...` with its target type.
open scoped ContDiff in
/-- ||[phi] - u||_(H^s) = ||coord s phi - coordinate(u)||_(L^2) (definitional). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.norm_toHsob_sub :
    ∀ {d : ℕ} (s : ℝ) (φ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ)
      (u : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.Hsob d s),
      ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.toHsob s φ - u‖ =
        ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.coord s φ - ((show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from u) : MeasureTheory.Lp ℂ (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)))‖ := by
  sorry
