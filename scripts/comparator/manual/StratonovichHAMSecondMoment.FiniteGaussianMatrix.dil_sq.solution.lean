namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ComplexOrder
-- Statement copied from the source (the printed type is only definitionally equal to the
-- declaration's); the section variables written as binders.
/-- dil(M)^2 = fromBlocks (M M^*) 0 0 (M^* M). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteGaussianMatrix.dil_sq.{u_1, u_2} {o : Type u_1} {n : Type u_2} [Fintype o] [Fintype n] [DecidableEq o] [DecidableEq n]
    (M : Matrix o n ℂ) : dil M ^ 2 = fromBlocks (M * Mᴴ) 0 0 (Mᴴ * M) := by
  exact _root_.StratonovichHAMSecondMoment.FiniteGaussianMatrix.dil_sq M
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
