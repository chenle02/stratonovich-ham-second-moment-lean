-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For sigma-finite mu, k in L^2(mu x mu) and bounded T on L^2(mu) with (T f)(x) = int k(x,y) f(y) dmu(y) a.e. for every f: T is compact (Bessel on the fibres and Fubini give sum_i ||T b_i||^2 <= ||k||_2^2). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CompactOperatorFoundation.isCompactOperator_of_L2_kernel.{u_1} :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      [MeasureTheory.SigmaFinite μ]
      (T : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ) →L[ℝ] ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ))
      (k : α × α → ℝ),
      MeasureTheory.MemLp k (2 : ENNReal) (μ.prod μ) →
        (∀ (f : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)),
            (((T : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ) → ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)) f) : α → ℝ) =ᵐ[μ]
              fun (x : α) => ∫ (y : α), k (x, y) * (f : α → ℝ) y ∂μ) →
          IsCompactOperator (M₁ := ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)) (M₂ :=
            ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ))
            (⇑T : ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ) → ↥(MeasureTheory.Lp ℝ (2 : ENNReal) μ)) := by
  sorry
