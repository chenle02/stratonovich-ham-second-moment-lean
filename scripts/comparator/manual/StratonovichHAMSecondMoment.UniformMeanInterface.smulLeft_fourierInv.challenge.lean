namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
-- Statement copied from the source (the printed type elaborates the instance on `Rd d` by another path, equal only up to unfolding).
-- The section variable used, written as a binder: {d : ℕ}.
/-- For a complex Schwartz psi: <2 pi xi>^sigma F F^(-1) (<2 pi xi>^(-sigma) psi) = psi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.smulLeft_fourierInv {d : ℕ} (σ : ℝ) (ψ : 𝓢(Rd d, ℂ)) : SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ))) = ψ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
