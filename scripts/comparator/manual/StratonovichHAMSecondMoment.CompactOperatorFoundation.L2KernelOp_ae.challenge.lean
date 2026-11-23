-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For k in L^2(mu x mu) and f in L^2(mu): (L2KernelOp f)(x) = int k(x,y) f(y) dmu(y) for mu-a.e. x. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.L2KernelOp_ae.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      [inst_1 : MeasureTheory.SigmaFinite μ] {k : α × α → ℝ}
      (hk : MeasureTheory.MemLp k (2 : ENNReal) (μ.prod μ)) (f : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)),
      (((StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CompactOperatorFoundation.L2KernelOp hk : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ) → ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)) f) : α → ℝ) =ᵐ[μ]
        fun (x : α) => ∫ (y : α), k (x, y) * (f : α → ℝ) y ∂μ := by
  sorry
