namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ComplexOrder
-- Statement copied from the source (the printed type is only definitionally equal to the
-- declaration's); the section variables written as binders.
/-- B (Y^j 1 Y^0) = B Y^j. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteGaussianMatrix.word_one.{u_1} {n : Type u_1} [Fintype n] [DecidableEq n] (B Y : Matrix n n ℂ) (j : ℕ) :
    B * (Y ^ j * 1 * Y ^ 0) = B * Y ^ j := by
  exact _root_.StratonovichHAMSecondMoment.FiniteGaussianMatrix.word_one B Y j
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
