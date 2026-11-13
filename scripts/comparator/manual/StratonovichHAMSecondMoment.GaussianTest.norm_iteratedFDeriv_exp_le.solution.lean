namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
open MeasureTheory Real
open scoped Nat ContDiff
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For all natural i and real y, the norm of the i-th iterated Frechet derivative of Real.exp at y is <= exp y. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.GaussianTest.norm_iteratedFDeriv_exp_le (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ ≤ Real.exp y := by
  exact _root_.StratonovichHAMSecondMoment.GaussianTest.norm_iteratedFDeriv_exp_le i y
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
