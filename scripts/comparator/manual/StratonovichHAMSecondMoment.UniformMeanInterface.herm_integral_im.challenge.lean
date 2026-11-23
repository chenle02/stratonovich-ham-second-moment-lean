namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
-- Statement copied from the source (the printed type elaborates the instance on `Rd d` by another path, equal only up to unfolding).
-- The section variable used, written as a binder: {d : ℕ}.
/-- For X, Y in herm d: int Im(Y conj X) = 0 (the complex pairing of Hermitian classes is real). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.herm_integral_im {d : ℕ} {X Y : Lp ℂ 2 (volume : Measure (Rd d))} (hX : X ∈ herm d) (hY : Y ∈ herm d) : ∫ ξ, ((Y : Rd d → ℂ) ξ * conj ((X : Rd d → ℂ) ξ)).im = 0 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
