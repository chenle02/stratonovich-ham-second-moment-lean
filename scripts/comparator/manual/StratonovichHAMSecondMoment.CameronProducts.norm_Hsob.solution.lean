-- Printed type with the printed `have this := ...; ↑this` written as the source's `show HR d from ...` with its target type.
open scoped ContDiff in
/-- For u in H^s: ||u|| is the L^2 norm of its Fourier coordinate (definitional). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.norm_Hsob :
    ∀ {d : ℕ} (s : ℝ) (u : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.Hsob d s),
      ‖u‖ = ‖((show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface.HR d from u) : MeasureTheory.Lp ℂ (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d)))‖ := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronProducts.norm_Hsob
