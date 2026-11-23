namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
-- Statement copied from the source (the printed type elaborates the instance on `Rd d` by another path, equal only up to unfolding).
-- The section variable used, written as a binder: {d : ℕ}.
/-- The coordinate of the cut error equals coord sigma (cutRe ...) + i coord sigma (cutIm ...) - psi in L^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.toLp_smulLeft_cutErr {d : ℕ} (σ : ℝ) (ψ : 𝓢(Rd d, ℂ)) (n : ℕ) : (SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 (cutErr (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n))).toLp 2 (volume : Measure (Rd d)) = coord σ (cutRe (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n) + Complex.I • coord σ (cutIm (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (msWeight (-σ)) ψ)) n) - ψ.toLp 2 (volume : Measure (Rd d)) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformMeanInterface.toLp_smulLeft_cutErr
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
