namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real LineDeriv
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
-- Statement copied from the source (the printed type elaborates the instance on `Rd d` by another path, equal only up to unfolding).
-- The section variable used, written as a binder: {d : ℕ}.
/-- Membership in herm d: X(-xi) = conj X(xi) for a.e. xi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanInterface.mem_herm_iff {d : ℕ} {X : Lp ℂ 2 (volume : Measure (Rd d))} : X ∈ herm d ↔ ∀ᵐ ξ, (X : Rd d → ℂ) (-ξ) = conj ((X : Rd d → ℂ) ξ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformMeanInterface
