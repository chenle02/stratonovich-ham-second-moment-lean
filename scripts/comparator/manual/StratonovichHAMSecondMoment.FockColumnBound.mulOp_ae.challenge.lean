namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
/-- For measurable real a with |a x| <= B for all x and f in Lp C 2 mu: mulOp a f = a * f mu-a.e. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.mulOp_ae (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B)
    (f : Lp ℂ 2 μ) : (mulOp (μ := μ) a ha B hB f : α → ℂ) =ᵐ[μ] fun x => (a x : ℂ) * f x := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
