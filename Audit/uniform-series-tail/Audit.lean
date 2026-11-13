module
import StratonovichHAMSecondMoment.UniformSeriesTail
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.UniformSeriesTail.norm_sq_le_of_inner_nonneg
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.norm_sq_le_of_inner_nonneg
#check @StratonovichHAMSecondMoment.UniformSeriesTail.term_bound
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.term_bound
#check @StratonovichHAMSecondMoment.UniformSeriesTail.hasSum_geometric_tail
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.hasSum_geometric_tail
#check @StratonovichHAMSecondMoment.UniformSeriesTail.summable_geometric_mul
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.summable_geometric_mul
#check @StratonovichHAMSecondMoment.UniformSeriesTail.tail_bound
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.tail_bound
#check @StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail
#check @StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_second_moment
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_second_moment
#check @StratonovichHAMSecondMoment.UniformSeriesTail.integral_mul_eq_inner
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.integral_mul_eq_inner
#check @StratonovichHAMSecondMoment.UniformSeriesTail.integral_sq_eq_norm_sq
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.integral_sq_eq_norm_sq
#check @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput
#check @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.mk
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.mk
#check @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.abs_summable
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.abs_summable
#check @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.mixed_moment_nonneg
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput.mixed_moment_nonneg
#check @StratonovichHAMSecondMoment.UniformSeriesTail.eventually_pos_pair
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.eventually_pos_pair
#check @StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_paper
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_paper
#check @StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_second_moment_paper
#print axioms StratonovichHAMSecondMoment.UniformSeriesTail.uniform_series_tail_second_moment_paper

open MeasureTheory Filter Topology StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.UniformSeriesTail

open StratonovichHAMSecondMoment.UniformSeriesTail

/-- Consumer of the wrapper: under the hypotheses of `L:uniform-series-tail`,
the limit `u = Σ X_n` has `‖u‖₂ ≤ B^{1/2}/(1 - r^{-1})` (the `N = -1` analogue,
from the term bounds by the triangle inequality), and the regularized solutions
converge to it. -/
private theorem audit_consumer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℝ → ℝ → ℕ → Lp ℝ 2 μ) (X : ℕ → Lp ℝ 2 μ)
    (r B : ℝ) (hr : 1 < r)
    (hTW : ∀ ε δ : ℝ, 0 < ε → 0 < δ → TerminalWickInput μ (Y ε δ) r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • Y ε δ n : Lp ℝ 2 μ) ω) ^ 2 ∂μ ≤ B)
    (hX : ∀ n, Tendsto (fun p : ℝ × ℝ => Y p.1 p.2 n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n))) :
    ‖∑' n, X n‖ ≤ ∑' n : ℕ, Real.sqrt B * (r ^ n)⁻¹ ∧
      Tendsto (fun p : ℝ × ℝ => ∑' n, Y p.1 p.2 n)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (∑' n, X n)) := by
  obtain ⟨_, hlim, _, hXb, _⟩ := uniform_series_tail_paper Y X r B hr hTW hB hX
  exact ⟨(norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hXb
      (summable_geometric_mul hr))).trans
      (Summable.tsum_le_tsum hXb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hXb
        (summable_geometric_mul hr)) (summable_geometric_mul hr)), hlim⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.UniformSeriesTail
