namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
open MeasureTheory Real
open scoped Nat ContDiff
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For c > 0 and natural k, n there is C with norm(x)^k * norm(iteratedFDeriv R n (gauss c) x) <= C for all x (real inner product space E). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.GaussianTest.gauss_decay.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (E := E) c) x‖ ≤ C := by
  exact _root_.StratonovichHAMSecondMoment.GaussianTest.gauss_decay hc k n
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
