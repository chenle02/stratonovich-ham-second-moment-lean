namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
open MeasureTheory Filter Topology
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}.
/-- Prob. measure mu (unused), Y e d n, X n in Lp R 2 mu, r > 1. If for e, d > 0: TerminalWickInput mu (Y e d) r, E(tsum r^n Y e d n)^2 <= B; Y e d n -> X n as (e,d) -> (0+,0+) jointly: sum ||X n|| < inf, tsum Y -> tsum X, E:uniform-series-tail for Y and X, sum ||Y e d n|| < inf. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_paper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℝ → ℝ → ℕ → Lp ℝ 2 μ) (X : ℕ → Lp ℝ 2 μ) (r B : ℝ) (hr : 1 < r)
    (hTW : ∀ ε δ : ℝ, 0 < ε → 0 < δ → TerminalWickInput μ (Y ε δ) r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B)
    (hX : ∀ n, Tendsto (fun p : ℝ × ℝ => Y p.1 p.2 n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Tendsto (fun p : ℝ × ℝ => ∑' n, Y p.1 p.2 n)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n, ‖Y ε δ n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, Y ε δ (n + (N + 1))‖ ≤ Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤
        Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → Summable fun n => ‖Y ε δ n‖) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
