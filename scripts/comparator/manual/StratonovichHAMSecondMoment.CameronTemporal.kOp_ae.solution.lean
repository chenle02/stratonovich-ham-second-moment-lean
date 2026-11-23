-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For a Schur kernel k and f in L^2(I): kOp f = (s -> int_I k(s,t) f(t) dt) a.e. on I (the L^2-kernel form of item B1). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronTemporal.kOp_ae :
    ∀ {k : ℝ × ℝ → ℝ} {A : ℝ} (hk : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronTemporal.SchurKernel k A)
      (f : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.L2I),
      (((StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronTemporal.kOp hk : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.L2I → StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronInterface.L2I) f) : ℝ → ℝ) =ᵐ[StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure]
        fun (x : ℝ) =>
        ∫ (y : ℝ),
          k (x, y) *
            (f : ℝ → ℝ)
              y ∂StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CameronTemporal.kOp_ae
