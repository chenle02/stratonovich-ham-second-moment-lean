-- Printed type with the coercions `↑↑V ξ`, `↑↑U ξ` given their target type, as in the source's `V ξ`.
open scoped ContDiff in
/-- The real inner product of L^2(R^d; C) is <U, V> = int Re(V conj U). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.real_inner_Lp :
    ∀ {d : ℕ} (U V : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) MeasureTheory.MeasureSpace.volume)),
      Inner.inner ℝ U V =
        @MeasureTheory.integral _ _ _ _ MeasureTheory.MeasureSpace.toMeasurableSpace
          MeasureTheory.MeasureSpace.volume
          fun (ξ : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) =>
          (HMul.hMul (β := ℂ) ((V : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℂ) ξ) ((starRingEnd ℂ) ((U : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℂ) ξ) : ℂ)).re := by
  sorry
