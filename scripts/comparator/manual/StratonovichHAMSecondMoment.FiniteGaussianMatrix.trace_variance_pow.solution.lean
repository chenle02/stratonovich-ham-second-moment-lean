namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ComplexOrder
-- Statement copied from the source (the printed type is only definitionally equal to the
-- declaration's); the section variables written as binders.
/-- For natural m: Re Tr((sum_k dil(A_k)^2)^m) = Re Tr(vOut A ^ m) + Re Tr(vIn A ^ m). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_variance_pow.{u_1, u_2} {o : Type u_1} {n : Type u_2} [Fintype o] [Fintype n] [DecidableEq o]
    [DecidableEq n] {N : ℕ} (A : Fin N → Matrix o n ℂ) (m : ℕ) :
    (trace ((∑ k, dil (A k) ^ 2) ^ m)).re =
      (trace (vOut A ^ m)).re + (trace (vIn A ^ m)).re := by
  exact _root_.StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_variance_pow A m
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteGaussianMatrix
