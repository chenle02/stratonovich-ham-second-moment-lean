namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
/-- For f in Lp C 2 mu: |f| ^ 2 = toReal of the lower integral of |f a|_e ^ 2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.norm_sq_Lp (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ).toReal := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
