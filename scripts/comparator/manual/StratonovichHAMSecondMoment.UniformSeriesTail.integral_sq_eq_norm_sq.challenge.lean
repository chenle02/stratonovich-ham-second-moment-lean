namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
open MeasureTheory Filter Topology
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}.
/-- For any measure mu and f in Lp R 2 mu: the Bochner integral of f(w)^2 d mu equals ||f||^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformSeriesTail.integral_sq_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Lp ℝ 2 μ) :
    ∫ ω, (f ω) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail
