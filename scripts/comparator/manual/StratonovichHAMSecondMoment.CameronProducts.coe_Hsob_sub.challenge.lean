-- Printed type with the printed `have this := ...; ↑this` written as the source's `show HR d from ...` with its target type.
open scoped ContDiff in
/-- The Fourier coordinate of u - v in H^s is the difference of the coordinates (definitional). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.coe_Hsob_sub :
    ∀ {d : ℕ} {s : ℝ} (u v : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.Hsob d s),
      ((show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from u - v) : MeasureTheory.Lp ℂ (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d))) =
        ((show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from u) : MeasureTheory.Lp ℂ (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d))) - (show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from v) := by
  sorry
