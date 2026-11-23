-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For sigma-finite mu, k in L^2(mu x mu) and f in L^2(mu): x -> int k(x,y) f(y) dmu(y) is a.e. strongly measurable. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.aestronglyMeasurable_kernel_integral.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      [MeasureTheory.SigmaFinite μ] {k : α × α → ℝ},
      MeasureTheory.MemLp k (2 : ENNReal) (μ.prod μ) →
        ∀ (f : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)),
          MeasureTheory.AEStronglyMeasurable (β := ℝ)
            (fun (x : α) => ∫ (y : α), k (x, y) * (f : α → ℝ) y ∂μ) μ := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CompactOperatorFoundation.aestronglyMeasurable_kernel_integral
