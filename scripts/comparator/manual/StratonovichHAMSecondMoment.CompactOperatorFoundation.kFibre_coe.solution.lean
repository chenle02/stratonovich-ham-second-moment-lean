-- Printed type with the implicit measure of `kFibre`, which the printer omits, written as the source's `(μ := μ)`.
open scoped ContDiff in
/-- If k(x, .) is in L^2(mu), then kFibre k x = k(x, .) mu-a.e. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.kFibre_coe.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {k : α × α → ℝ} {x : α},
      MeasureTheory.MemLp (ε := ℝ) (fun (y : α) => k (x, y)) (2 : ENNReal) μ →
        ((StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CompactOperatorFoundation.kFibre (μ := μ) k x : MeasureTheory.Lp ℝ (2 : ENNReal) μ) : α → ℝ) =ᵐ[μ] fun (y : α) =>
          k (x, y) := by
  bridge_auto _root_.StratonovichHAMSecondMoment.CompactOperatorFoundation.kFibre_coe
