namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
open scoped BesselPotentialSpace
/-- For real s and u in H^s(R^d) (complex): there are phi n in H^s with Schwartz distributions and phi n -> u. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.exists_schwartz_tendsto (s : ℝ) (u : H^{s}(Rd d)) :
    ∃ φ : ℕ → H^{s}(Rd d), (∀ n, ∃ χ : 𝓢(Rd d, ℂ), (φ n).toDistr = (χ : 𝓢'(Rd d, ℂ))) ∧
      Tendsto φ atTop (𝓝 u) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
