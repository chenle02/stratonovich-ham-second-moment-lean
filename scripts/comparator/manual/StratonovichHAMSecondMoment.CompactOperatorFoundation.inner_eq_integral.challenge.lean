-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- In real L^2(mu): <v, f> = int v f dmu. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.inner_eq_integral.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      (v f : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)),
      Inner.inner ℝ v f = ∫ (x : α), (v : α → ℝ) x * (f : α → ℝ) x ∂μ := by
  sorry
