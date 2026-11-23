namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
-- Statement copied from the source (the printed type elaborates the instance on `Rd d` by another path, equal only up to unfolding).
-- The section variable used, written as a binder: {d : ℕ}.
/-- For a complex Schwartz h: |<2 pi xi>^sigma F h|_(L^2)^2 = int |msWeight sigma xi F h(xi)|^2 dxi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.norm_toLp_smulLeft_sq {d : ℕ} (σ : ℝ) (h : 𝓢(Rd d, ℂ)) : ‖(SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 h)).toLp 2 (volume : Measure (Rd d))‖ ^ 2 = ∫ ξ, ‖msWeight σ ξ * 𝓕 h ξ‖ ^ 2 := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanInterface.norm_toLp_smulLeft_sq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
