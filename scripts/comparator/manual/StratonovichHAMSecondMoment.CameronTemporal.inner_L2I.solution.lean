-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For f, g in L^2(I): <f, g> = int_I f g. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronTemporal.inner_L2I :
    ∀ (f g : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.L2I),
      Inner.inner ℝ f g =
        ∫ (s : ℝ),
          (f : ℝ → ℝ) s *
            (g : ℝ → ℝ)
              s ∂StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronTemporal.inner_L2I
