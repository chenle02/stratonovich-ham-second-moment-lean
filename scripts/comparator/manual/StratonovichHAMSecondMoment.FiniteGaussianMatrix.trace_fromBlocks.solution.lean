namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ComplexOrder
-- Statement copied from the source (the printed type is only definitionally equal to the
-- declaration's); the section variables written as binders.
/-- Tr(fromBlocks P Q R S) = Tr P + Tr S. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_fromBlocks.{u_1, u_2} {o : Type u_1} {n : Type u_2} [Fintype o] [Fintype n] (P : Matrix o o ℂ)
    (Q : Matrix o n ℂ) (R : Matrix n o ℂ) (S : Matrix n n ℂ) :
    trace (fromBlocks P Q R S) = trace P + trace S := by
  exact _root_.StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_fromBlocks P Q R S
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
