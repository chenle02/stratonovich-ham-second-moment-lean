namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
open MeasureTheory Filter Topology
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}.
/-- For any measure mu and f, g in Lp R 2 mu: the Bochner integral of f(w) * g(w) d mu equals the L2 inner product inner f g. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformSeriesTail.integral_mul_eq_inner {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f g : Lp ℝ 2 μ) :
    ∫ ω, f ω * g ω ∂μ = inner ℝ f g := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.UniformSeriesTail.integral_mul_eq_inner
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
