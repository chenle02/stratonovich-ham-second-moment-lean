-- Written as in the source: the printed type elaborates another instance path or universe order.
open scoped ContDiff in
/-- For r > 0 and real sigma: int |x|^r N(0, sigma^2)(dx) = |sigma|^r m_r. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanTensor.lintegral_gaussianReal_sq :
    ∀ {r : ℝ},
      (0 : ℝ) < r →
        ∀ (σ : ℝ),
          ∫⁻ (x : ℝ), ‖x‖ₑ ^ r ∂(ProbabilityTheory.gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
            ‖σ‖ₑ ^ r * StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanTensor.gaussMoment r := by
  sorry
