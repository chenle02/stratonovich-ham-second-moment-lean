-- Printed type with the printed `have this := ...; ↑this` written as the source's `show HR d from ...` with its target type.
open scoped ContDiff in
/-- For a real test phi: the coordinate of toHhalf phi is coord (1/2) phi. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.toHhalf_coe :
    ∀ {d : ℕ} {φ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ},
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsTestFunction φ →
        ((show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.toHhalf φ) : MeasureTheory.Lp ℂ (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d))) =
          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.coord (1 / 2 : ℝ) φ := by
  exact @_root_.StratonovichHAMSecondMoment.UniformMeanInterface.toHhalf_coe
