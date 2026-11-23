-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- In real L^2(mu): ||v||^2 = int v^2 dmu. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.norm_sq_eq_integral.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      (v : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)),
      ‖v‖ ^ (2 : ℕ) = ∫ (x : α), (v : α → ℝ) x ^ (2 : ℕ) ∂μ := by
  sorry
