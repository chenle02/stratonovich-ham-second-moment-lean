namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
open Real Set MeasureTheory Filter Topology
open StratonovichHAMSecondMoment.StaticPhaseCauchy
-- Statement copied from the source (the printed type elaborates the semiring structure of `ℂ` as `Complex.instSemiring`, the declaration through `RCLike`).
-- The section variables and scoped opens of the source, as there:
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- If A0 is positive, 0 < a < 1, ||A_rho^(-1/2) V A_rho^(-1/2)|| <= D rho^(a-2) for rho > 0, Lam > 0, D <= deltaA a Lam^(2-a) and h >= 0, then V^* has the same sandwich bound and PhaseRangeBounds a (deltaA a) Lam h w holds on numRange (A0 - V). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ComplexPhaseScalar.interval_complex_range_paper (A0 V : H →L[ℂ] H) (hA0 : A0.IsPositive) {a D : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsand : ∀ ρ > 0, ‖invSqrtShift A0 ρ * V * invSqrtShift A0 ρ‖ ≤ D * ρ ^ (a - 2))
    {Λ : ℝ} (hΛ : 0 < Λ) (hD : D ≤ deltaA a * Λ ^ (2 - a)) {h : ℝ} (hh : 0 ≤ h) :
    (∀ ρ > 0, ‖invSqrtShift A0 ρ * ContinuousLinearMap.adjoint V * invSqrtShift A0 ρ‖ ≤
        D * ρ ^ (a - 2)) ∧
      ∀ w ∈ numRange (A0 - V), PhaseRangeBounds a (deltaA a) Λ h w := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ComplexPhaseScalar
