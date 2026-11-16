namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
/-- For rho > 0 and f in L^2(Lebesgue on R^d): |sqrtResolvent rho f| <= rho^(-1) * |f|. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.sqrtResolvent_norm_le {ρ : ℝ} (hρ : 0 < ρ) (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ‖sqrtResolvent ρ hρ f‖ ≤ ρ⁻¹ * ‖f‖ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
