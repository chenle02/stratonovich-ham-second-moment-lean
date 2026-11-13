namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
open MeasureTheory Filter Topology
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}.
/-- Under the hypotheses of uniform_series_tail_paper, if also the integral of (tsum_n Y e d n)^2 d mu is <= B1 for all e, d > 0, then the integral of (tsum_n X n)^2 d mu is <= B1 (IsProbabilityMeasure mu carried, unused). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_second_moment_paper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℝ → ℝ → ℕ → Lp ℝ 2 μ) (X : ℕ → Lp ℝ 2 μ) (r B B₁ : ℝ) (hr : 1 < r)
    (hTW : ∀ ε δ : ℝ, 0 < ε → 0 < δ → TerminalWickInput μ (Y ε δ) r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B)
    (hX : ∀ n, Tendsto (fun p : ℝ × ℝ => Y p.1 p.2 n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n)))
    (hB₁ : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B₁) :
    ∫ ω, ((∑' n, X n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B₁ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
