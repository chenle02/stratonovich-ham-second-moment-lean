namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
open MeasureTheory Real
open scoped Nat ContDiff
-- Statement copied from the source (the printed `↑⊤` does not elaborate back to `∞`); section variables written as binders.
/-- For every real c, gauss c is C^infinity on a real inner product space. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.GaussianTest.contDiff_gauss.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℝ) :
    ContDiff ℝ ∞ (gauss (E := E) c) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
