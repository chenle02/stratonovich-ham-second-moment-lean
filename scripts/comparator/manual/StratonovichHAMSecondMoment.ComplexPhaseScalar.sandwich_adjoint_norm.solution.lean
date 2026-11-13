namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
open Real Set MeasureTheory Filter Topology
open StratonovichHAMSecondMoment.StaticPhaseCauchy
-- Statement copied from the source (the printed type elaborates the semiring structure of `ℂ` as `Complex.instSemiring`, the declaration through `RCLike`).
-- The section variables and scoped opens of the source, as there:
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- If A0 is positive and rho > 0, then for every V: ||invSqrtShift A0 rho * adjoint V * invSqrtShift A0 rho|| = ||invSqrtShift A0 rho * V * invSqrtShift A0 rho||. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ComplexPhaseScalar.sandwich_adjoint_norm {A0 : H →L[ℂ] H} (hA0 : A0.IsPositive) {ρ : ℝ} (hρ : 0 < ρ)
    (V : H →L[ℂ] H) :
    ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ =
      ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ComplexPhaseScalar.sandwich_adjoint_norm
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
